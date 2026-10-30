pub mod anomalies;
pub mod clause_cache;
pub mod counting;
pub mod heuristics;
pub mod multiple_queries;
pub mod node;
pub mod stream;
use core::num;
use std::{collections::{BTreeSet, HashMap, HashSet, VecDeque}, hash::Hash, io::{BufRead, Cursor}, time::Duration};
use std::collections::BinaryHeap;
use anomalies::sat;
use bitvec::{index, ptr::swap, vec};
use counting::features;
use gmp_mpfr_sys::mpfr::ZERO_KIND;
use itertools::{Either, Interleave};
use nom::sequence::tuple;
use petgraph::Direction::Incoming;
use rand::{seq::SliceRandom, thread_rng};
use rand_distr::num_traits::{real, zero, ToPrimitive};
use rug::{Assign, Complete,Integer};
use std::time::Instant;

use self::{clause_cache::ClauseCache, node::Node};
use node::NodeType::*;

use std::path::Path;
use std::fs::File;
use std::io::{self};

#[derive(Clone, Debug)]
/// A Ddnnf holds all the nodes as a vector, also includes meta data and further information that is used for optimations
pub struct Ddnnf {
    /// The actual nodes of the d-DNNF in postorder
    pub nodes: Vec<Node>,
    /// The saved state to enable undoing and adapting the d-DNNF. Avoid exposing this field outside of this source file!
    cached_state: Option<ClauseCache>,
    /// Literals for upwards propagation
    pub literals: HashMap<i32, usize>, // <var_number of the Literal, and the corresponding indize>
    true_nodes: Vec<usize>, // Indices of true nodes. In some cases those nodes needed to have special treatment
    /// The core/dead features of the model corresponding with this ddnnf
    pub core: HashSet<i32>,
    /// An interim save for the marking algorithm
    pub md: Vec<usize>,
    pub number_of_variables: u32,
    /// The number of threads
    pub max_worker: u16,
    // pub node_count: i128,
    // pub edge_count: i128,

    pub not_use_lpe: bool,
    pub not_use_bhm: bool,
    pub not_use_znp: bool,
    
    pub literals_list: HashMap<usize, i32>,
    pub core_list: HashSet<i32>,

    pub weight_list: Vec<i32>,

    pub limit_solution_num: i32,

    pub v_m: u32,
    pub v_n: u32,
    pub v_t: u32,
}

impl Default for Ddnnf {
    fn default() -> Self {
        Ddnnf {
            nodes: Vec::new(),
            cached_state: None,
            literals: HashMap::new(),
            true_nodes: Vec::new(),
            core: HashSet::new(),
            md: Vec::new(),
            number_of_variables: 0,
            max_worker: 4,
            literals_list: HashMap::new(),
            core_list: HashSet::new(),
            weight_list: Vec::new(),
            limit_solution_num: 0,
            not_use_lpe: false,
            not_use_bhm: false,
            not_use_znp: false,
            v_m: 0,
            v_n: 0,
            v_t: 0,
        }
    }
}

impl Ddnnf {
    /// Creates a new ddnnf including dead and core features
    pub fn new(
        nodes: Vec<Node>,
        literals: HashMap<i32, usize>,
        true_nodes: Vec<usize>,
        number_of_variables: u32,
        clauses: Option<BTreeSet<BTreeSet<i32>>>,
    ) -> Ddnnf {
        let mut ddnnf = Ddnnf {
            nodes,
            cached_state: None,
            literals,
            true_nodes,
            core: HashSet::new(),
            md: Vec::new(),
            number_of_variables,
            max_worker: 4,
            literals_list: HashMap::new(),
            core_list: HashSet::new(),
            weight_list: Vec::new(),
            limit_solution_num: 0,
            not_use_lpe: false,
            not_use_bhm: false,
            not_use_znp: false,
            v_m: 0,
            v_n: 0,
            v_t: 0,
        };
        ddnnf.get_core();
        if let Some(c) = clauses {
            ddnnf.update_cached_state(Either::Right(c), Some(number_of_variables));
        }
        ddnnf
    }

    /// Checks if the creation of a cached state is valid.
    /// That is only the case if the input format was CNF.
    pub fn can_save_state(&self) -> bool {
        self.cached_state.is_some()
    }

    /// Either initialises the ClauseCache by saving the clauses and its corresponding clauses
    /// or updates the state accordingly.
    pub fn update_cached_state(
        &mut self,
        clause_info: Either<(Vec<BTreeSet<i32>>, Vec<BTreeSet<i32>>), BTreeSet<BTreeSet<i32>>>, // Left(edit operation) or Right(clauses)
        total_features: Option<u32>,
    ) -> bool {
        match self.cached_state.as_mut() {
            Some(state) => match clause_info.left() {
                Some((add, rmv)) => {
                    if total_features.is_none()
                        || !state.apply_edits_and_replace(add, rmv, total_features.unwrap())
                    {
                        return false;
                    }
                    // The old d-DNNF got replaced by the new one.
                    // Consequently, the current higher level d-DNNF becomes the older one.
                    // We swap their field data to keep the order without needing to deal with recursivly building up
                    // obselete d-DNNFs that trash the RAM.
                    self.swap();
                }
                None => return false,
            },
            None => match clause_info.right() {
                Some(clauses) => {
                    let mut state = ClauseCache::default();
                    state.initialize(clauses, total_features.unwrap());
                    self.cached_state = Some(state);
                }
                None => return false,
            },
        }
        true
    }

    fn swap(&mut self) {
        if let Some(cached_state) = self.cached_state.as_mut() {
            if let Some(save_state) = cached_state.old_state.as_mut() {
                std::mem::swap(&mut self.nodes, &mut save_state.nodes);
                std::mem::swap(&mut self.literals, &mut save_state.literals);
                std::mem::swap(&mut self.true_nodes, &mut save_state.true_nodes);
                std::mem::swap(&mut self.core, &mut save_state.core);
                std::mem::swap(&mut self.md, &mut save_state.md);
                std::mem::swap(
                    &mut self.number_of_variables,
                    &mut save_state.number_of_variables,
                );
                std::mem::swap(&mut self.max_worker, &mut save_state.max_worker);
            }
        }
    }

    // Performes an undo operation resulting in swaping the current d-DNNF with its older version.
    // Hence, the perviously older version becomes the current one and the current one becomes the older version.
    // A second undo operation in a row is equivalent to a redo. Can fail if there is no old d-DNNF available.
    pub fn undo_on_cached_state(&mut self) -> bool {
        match self.cached_state.as_mut() {
            Some(state) => {
                state.setup_for_undo();
                self.swap();
                //std::mem::swap(self, &mut state.to_owned().get_old_state().unwrap());
                true
            }
            None => false,
        }
    }

    // Returns the current count of the root node in the ddnnf.
    // That value is the same during all computations
    pub fn rc(&self) -> Integer {
        self.nodes[self.nodes.len() - 1].count.clone()
    }

    // Returns the current temp count of the root node in the ddnnf.
    // That value is changed during computations
    fn rt(&self) -> Integer {
        self.nodes[self.nodes.len() - 1].temp.clone()
    }

    /// Determines the positions of the inverted featueres
    pub fn map_features_opposing_indexes(&self, features: &[i32]) -> Vec<usize> {
        let mut indexes = Vec::with_capacity(features.len());
        for number in features {
            if let Some(i) = self.literals.get(&-number).cloned() {
                indexes.push(i);
            }
        }
        indexes
    }

    pub fn debug(&mut self){
        // return;
        println!("node:");
        for idx in 0..std::cmp::min(100,self.nodes.len()){
            print!("{}: ",idx);
            print!("{:?} ",self.nodes[idx].ntype);
            for index in 0..self.nodes[idx].parents.len(){
                print!(" {}",self.nodes[idx].parents[index]);
            }
            println!();
        }
        // println!("{:?}",self.nodes.len());
        // let mut uselessAndNodeNum = 0;
        // let mut uselessOrNodeNum = 0;
        // for i in 0..self.nodes.len() {
        //     match &self.nodes[i].ntype {
        //         And { children } => {
        //             for child in children {
        //                 if self.nodes[*child].parents.len() != 1{
        //                     continue;
        //                 }
        //                 match self.nodes[*child].ntype {
        //                     And {..} => {
        //                         uselessAndNodeNum += 1;
        //                     }
        //                     _ => {}
        //                 }
        //             }
        //         }
        //         Or {children} => {
        //             for child in children {
        //                 if self.nodes[*child].parents.len() != 1{
        //                     continue;
        //                 }
        //                 match self.nodes[*child].ntype {
        //                     Or {..} => {
        //                         uselessOrNodeNum += 1;
        //                     }
        //                     _ => {}
        //                 }
        //             }
        //         }
        //         _ => {}
        //     }
        //  }
        // println!("uselessAndNodeNum = {:?}",uselessAndNodeNum);
        // println!("uselessOrNodeNum = {:?}",uselessOrNodeNum);
    }

    pub fn clean_partial_config_counter(
        &mut self,
        features: &[i32],
    ) -> (Integer, Duration) {
        let start = Instant::now();
        if self.query_is_not_sat(features) {
            return (Integer::ZERO, start.elapsed());
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        if indexes.is_empty() {
            return (self.rc(),  start.elapsed());
        }

        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return (Integer::ZERO, start.elapsed());
        }
        if self.md.len() > 1 {
            for idx in (0..self.md.len() -1).rev() {
                let index = self.md[idx];
                if self.nodes[index].is_zero == true {
                    continue;
                }
                let mut flag = true;
                for id in 0..self.nodes[index].parents.len() {
                    let parent = self.nodes[index].parents[id];
                    flag &= self.nodes[parent].is_zero;
                }
                if flag == true {
                    self.nodes[index].is_zero = flag;
                    self.nodes[index].temp = Integer::ZERO;
                }
            }
        }
        for idx in 0..self.md.len() {
            // self.node_count += 1;
            let i = self.md[idx];
            if self.nodes[i].is_zero{
                continue;
            }
            match &self.nodes[i].ntype {
                And { children } => {
                    let marked_children = children
                        .iter()
                        .filter(|&&child| self.nodes[child].marker)
                        .collect::<Vec<&usize>>();
                    self.nodes[i].temp = if marked_children.len() <= children.len() / 2 {
                        marked_children.iter().fold(
                            self.nodes[i].count.clone(),
                            |mut acc, &&index| {
                                let node = &self.nodes[index];
                                if node.count != 0 {
                                    acc /= &node.count;
                                }
                                acc *= &node.temp;
                                // self.edge_count += 1;
                                acc
                            },
                        )
                    } else {
                        Integer::product(children.iter().map(|&index| {
                            let node = &self.nodes[index];
                            // self.edge_count += 1;
                            if node.marker {
                                &node.temp
                            } else {
                                &node.count
                            }
                        }))
                        .complete()
                    }
                }
                Or { children } => {
                    self.nodes[i].temp = Integer::sum(children.iter().map(|&index| {
                        let node = &self.nodes[index];
                        // self.edge_count += 1;
                        if node.marker {
                            &node.temp
                        } else {
                            &node.count
                        }
                    }))
                    .complete()
                }
                False => self.nodes[i].temp.assign(0),
                _ => self.nodes[i].temp.assign(1), // True and Literal
            }
        }

        // reset everything
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();

        return (self.rt(), start.elapsed());
    }


    pub fn new_my_partial_config_counter(
        &mut self,
        features: &[i32],
    ) -> (Integer, BTreeSet<i32>, Vec<Vec<i32>>, Duration) {

        let start = Instant::now();
        if self.query_is_not_sat(features) {
            // println!("!!!");
            return (Integer::ZERO, BTreeSet::new(), Vec::new(), start.elapsed());
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        if indexes.is_empty() {
            let mut core_list = BTreeSet::new();
            for i in self.core.clone() {
                core_list.insert(i);
            }
            if self.limit_solution_num != -1 && self.rc() != 0 {
                return (
                    self.rc(),
                    core_list,
                    self.new_my_partial_config_counter_all(&features),
                    start.elapsed(),
                );
            }
            return (self.rc(), core_list, Vec::new(), start.elapsed());
        }
        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return (Integer::ZERO, BTreeSet::new(), Vec::new(), start.elapsed());
        }
        // if self.md.len() > 1 {
        let mut core_list = self.core.clone();
        let mut vis: Vec<bool> = Vec::new();
        vis.resize(self.nodes.len(), false);
        vis[self.nodes.len() - 1] = true;
        // println!("{}",self.nodes.len() -1);
        for index in (0..self.nodes.len()).rev() {
            // println!("{},{}",index,vis[index]);
            if !vis[index] || self.nodes[index].is_zero {
                match &self.nodes[index].ntype {
                    Literal { literal } => {
                        if !vis[index] {
                            core_list.insert((literal) * (-1));
                        }
                    }
                    _ => {}
                }
                continue;
            }
            match &self.nodes[index].ntype {
                And { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                Or { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                _ => {}
            }
        }

        self.core_list = core_list;
        for idx in 0..self.nodes.len() {
            self.nodes[idx].temp = Integer::ZERO;
        }
        for idx in 0..self.md.len() {
            if !vis[self.md[idx]] {
                continue;
            }
            // self.node_count += 1;
            let i = self.md[idx];
            match &self.nodes[i].ntype {
                And { children } => {
                    let marked_children = children
                        .iter()
                        .filter(|&&child| self.nodes[child].marker)
                        .collect::<Vec<&usize>>();
                    self.nodes[i].temp = if marked_children.len() <= children.len() / 2 {
                        marked_children.iter().fold(
                            self.nodes[i].count.clone(),
                            |mut acc, &&index| {
                                let node = &self.nodes[index];
                                if node.count != 0 {
                                    acc /= &node.count;
                                }
                                acc *= &node.temp;
                                // self.edge_count += 1;
                                acc
                            },
                        )
                    } else {
                        Integer::product(children.iter().map(|&index| {
                            let node = &self.nodes[index];
                            // self.edge_count += 1;
                            if node.marker {
                                &node.temp
                            } else {
                                &node.count
                            }
                        }))
                        .complete()
                    }
                }
                Or { children } => {
                    self.nodes[i].temp = Integer::sum(children.iter().map(|&index| {
                        let node = &self.nodes[index];
                        // self.edge_count += 1;
                        if node.marker {
                            &node.temp
                        } else {
                            &node.count
                        }
                    }))
                    .complete()
                }
                False => self.nodes[i].temp.assign(0),
                _ => self.nodes[i].temp.assign(1), // True and Literal
            }
        }

        // reset everything
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();

        let mut res: BTreeSet<i32> = BTreeSet::new();
        for core in self.core_list.clone() {
            res.insert(core);
        }
        let mut solution_list: Vec<Vec<i32>> = Vec::new();
        let count = self.rt();
        if self.limit_solution_num != -1 && self.rt() > 0 {
            solution_list = self.new_my_partial_config_counter_all(&features);
        }
        
        for index in 0..self.nodes.len() {
            self.nodes[index].temp = Integer::ZERO;
        }

        return (count, res, solution_list, start.elapsed());
    }




    pub fn new_my_partial_config_counter_all(&mut self, features: &[i32]) -> Vec<Vec<i32>> {
        
        for i in 0..self.nodes.len() {
            self.nodes[i].temp = Integer::ZERO;
        }
        if self.query_is_not_sat(features) {
            return Vec::new();
        }

        if self.limit_solution_num == 0 {
            return Vec::new();
        }

        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);

        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            self.cleanup_markers(&indexes);
            return Vec::new();
        }

        let mut vis: Vec<bool> = vec![false; self.nodes.len()];
        vis[self.nodes.len() - 1] = true; 
        let mut count = 0;
        for index in (0..self.nodes.len()).rev() {
            if !vis[index] || self.nodes[index].is_zero {
                continue;
            }
            count += 1;
            match &self.nodes[index].ntype {
                And { children } | Or { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                _ => {}
            }
        }

        let mut visNum: Vec<i32> = vec![0; self.nodes.len()];
        for index in 0..self.nodes.len() {
            if !vis[index] {
                continue;
            }
            match &self.nodes[index].ntype {
                And { children } | Or { children } => {
                    for child in children {
                        if vis[*child] {
                            visNum[index] += visNum[*child];
                        }
                    }
                }
                _ => {
                    visNum[index] = 1;
                }
            }
        }

        let limit = if self.limit_solution_num <= 0 {
            usize::MAX / 2 
        } else {
            self.limit_solution_num as usize
        };


        let mut solution_cache: Vec<Option<Vec<Vec<i32>>>> = vec![None; self.nodes.len()];
        let start = Instant::now();
        let mut full_idx = self.nodes.len() - 1;
        let mut is_full = false;
        let mut solutions = self.generate_solutions_recursive(
            self.nodes.len() - 1, 
            &mut solution_cache,
            &vis,
            limit,
            &visNum,
            &mut is_full,
            &mut full_idx,
        );
        
        let mut enum_cache: Vec<Vec<i32>> = vec![Vec::new(); self.nodes.len()];
        // println!("{:?}",solution_cache);
        // println!("full_idx:{:?}",full_idx);
        
        let mut now_idx = full_idx;
        if full_idx != self.nodes.len() - 1 {
            while true {
                let raw_idx = now_idx;
                now_idx = self.nodes[now_idx].parents.first().unwrap().clone();
                match &self.nodes[now_idx].ntype {
                    And{children} => {
                        for child in children {
                            if *child == full_idx {
                                continue;
                            }
                            let res = self.enum_dfs(child,&mut enum_cache);
                            enum_cache[now_idx].extend(&res);
                        }
                    }
                    Or {..} => {
                        enum_cache[now_idx] = enum_cache[raw_idx].clone();
                    }
                    _ => {}
                }
                if enum_cache[now_idx].is_empty() {
                    enum_cache[now_idx] = enum_cache[raw_idx].clone()
                }
                if now_idx == self.nodes.len() - 1 {
                    break;
                }
            }
            solutions = solution_cache[full_idx].clone().unwrap();
            // println!("{:?}",solutions);
            for solution in &mut solutions {
                solution.extend(enum_cache[self.nodes.len()-1].clone());
            }
            // println!("{:?}",enum_cache);
        }

        self.cleanup_markers(&indexes);

        return solutions;
    }


    fn enum_dfs(&self, idx: &usize, enum_cache: &mut Vec<Vec<i32>>) -> Vec<i32> {
        if enum_cache[*idx].len() != 0 {
            return enum_cache[*idx].clone();
        }
        match &self.nodes[*idx].ntype {
            And { children } => {
                for child in children {
                    let res = self.enum_dfs(child, enum_cache);
                    enum_cache[*idx].extend(&res);
                }
            }
            Or {children} => {
                for child in children {
                    let res = self.enum_dfs(child, enum_cache);
                    enum_cache[*idx].extend(&res);
                    break;
                }
            }
            Literal { literal } => {
                enum_cache[*idx].push(*literal);
            }
            _=>{}
        }
        return enum_cache[*idx].clone();
    }

    fn generate_solutions_recursive(
        &self,
        node_idx: usize,
        cache: &mut Vec<Option<Vec<Vec<i32>>>>,
        vis: &[bool],
        limit: usize,
        visNum: &Vec<i32>,
        is_full: &mut bool,
        full_idx: &mut usize,
    ) -> Vec<Vec<i32>> {
        if *is_full == true {
            return Vec::new();
        }
        if !vis[node_idx] || self.nodes[node_idx].is_zero {
            return Vec::new();
        }

        if let Some(ref solutions) = cache[node_idx] {
            return solutions.clone();
        }

        let solutions = match &self.nodes[node_idx].ntype {
            Literal { literal } => {
                vec![vec![*literal]]
            }
            And { children } => {
                self.combine_and_solutions(children, cache, vis, limit,visNum,is_full,full_idx)
            }
            Or { children } => {
                self.combine_or_solutions(children, cache, vis, limit,visNum,is_full,full_idx)
            }
            True => {
                vec![vec![]]
            }
            False => {
                Vec::new()
            }
        };

        cache[node_idx] = Some(solutions.clone());
        if solutions.len() == limit {
            *is_full = true;
            *full_idx = node_idx;
        }
        solutions
    }

    fn combine_and_solutions(
        &self,
        children: &[usize],
        cache: &mut Vec<Option<Vec<Vec<i32>>>>,
        vis: &[bool],
        limit: usize,
        visNum: &Vec<i32>,
        is_full: &mut bool,
        full_idx: &mut usize,
    ) -> Vec<Vec<i32>> {
        if *is_full == true {
            return Vec::new();
        }
        if children.is_empty() {
            return Vec::new();
        }

        let mut child_indices: Vec<_> = children
            .iter()
            .copied()
            .filter(|&idx| vis[idx] && !self.nodes[idx].is_zero)
            .collect();
        
        // child_indices.sort_by(|a,b| self.nodes[*a].temp.cmp(&self.nodes[*b].temp) );
        // child_indices.sort_by(|a,b| visNum[*a].cmp(&visNum[*b]) );
        child_indices.sort_by(|b,a| (self.nodes[*b].temp.clone() * visNum[*a]).cmp(&(self.nodes[*a].temp.clone() * visNum[*b])) );

        // child_indices.shuffle(&mut thread_rng());


        if child_indices.is_empty() {
            return Vec::new();
        }

        let result = self.generate_solutions_recursive(child_indices[0], cache, vis, limit,visNum,is_full,full_idx);
        if result.is_empty() || child_indices.len() == 1 {
            return result; 
        }

        let mut capacity = result.len();
        let mut child_capacities = result.len();

        let mut child_solutions = Vec::with_capacity(child_indices.len() - 1);
        for &child in &child_indices[1..] {
            let solutions = self.generate_solutions_recursive(child, cache, vis, limit,visNum,is_full,full_idx);
            if solutions.is_empty() {
                return Vec::new(); 
            }
            child_capacities += solutions.len();
            capacity = std::cmp::min(capacity * solutions.len(), limit);
            child_solutions.push(solutions);
        }

        if *is_full == true {
            return Vec::new();
        }

        let capacity = std::cmp::min(capacity, limit);
        let mut new_result = Vec::with_capacity(capacity);
        let start = Instant::now();
        self.combine_solutions_recursive(
            &result,
            &child_solutions,
            &mut new_result,
            &mut Vec::with_capacity(child_capacities),
            0,
            limit,
        );

        new_result
    }

    fn combine_solutions_recursive(
        &self,
        base_solutions: &[Vec<i32>],
        child_solutions: &[Vec<Vec<i32>>],
        result: &mut Vec<Vec<i32>>,
        current: &mut Vec<i32>,
        depth: usize,
        limit: usize,
    ) {
        if result.len() >= limit {
            return;
        }

        if depth == 0 {
            for base in base_solutions {
                if result.len() >= limit {
                    break;
                }

                current.clear();
                current.extend_from_slice(base);

                if child_solutions.is_empty() {
                    result.push(current.clone());
                } else {
                    self.combine_solutions_recursive(
                        base_solutions,
                        child_solutions,
                        result,
                        current,
                        depth + 1,
                        limit,
                    );
                }
            }
        } else if depth <= child_solutions.len() {
            let child_idx = depth - 1;
            for child_sol in &child_solutions[child_idx] {
                if result.len() >= limit {
                    break;
                }

                let current_len = current.len();

                current.extend_from_slice(child_sol);

                if depth == child_solutions.len() {
                    result.push(current.clone());
                } else {
                    self.combine_solutions_recursive(
                        base_solutions,
                        child_solutions,
                        result,
                        current,
                        depth + 1,
                        limit,
                    );
                }

                current.truncate(current_len);
            }
        }
    }

    fn combine_or_solutions(
        &self,
        children: &[usize],
        cache: &mut Vec<Option<Vec<Vec<i32>>>>,
        vis: &[bool],
        limit: usize,
        visNum: &Vec<i32>,
        is_full: &mut bool,
        full_idx: &mut usize,
    ) -> Vec<Vec<i32>> {
        if *is_full == true {
            return Vec::new();
        }
        if children.is_empty() {
            return Vec::new();
        }

        let mut result = Vec::with_capacity(
            std::cmp::min(children.len() * 4, limit), 
        );

        let mut child_indices: Vec<_> = children
            .iter()
            .copied()
            .filter(|&idx| vis[idx] && !self.nodes[idx].is_zero)
            .collect();

        if child_indices.is_empty() {
            return Vec::new();
        }
        // child_indices.sort_by(|a,b| self.nodes[*a].temp.cmp(&self.nodes[*b].temp) );
        // child_indices.sort_by(|a,b| visNum[*b].cmp(&visNum[*a]) );
        child_indices.sort_by(|b,a| (self.nodes[*b].temp.clone() * visNum[*a]).cmp(&(self.nodes[*a].temp.clone() * visNum[*b])) );

        // child_indices.shuffle(&mut thread_rng());
        for &child in &child_indices {
            if result.len() >= limit {
                break; 
            }

            let child_solutions =
                self.generate_solutions_recursive(child, cache, vis, limit ,visNum,is_full,full_idx);

            let remaining = limit - result.len();
            if child_solutions.len() <= remaining {
                result.extend(child_solutions);
            } else {
                result.extend(child_solutions.into_iter().take(remaining));
            }
        }

        result
    }

    fn cleanup_markers(&mut self, indexes: &[usize]) {
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for &index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();
    }

    pub fn my_zero_checker(&mut self, features: &[i32]) -> bool {
        if self.rc() == 0 {
            return false;
        }
        if self.query_is_not_sat(features) {
            // println!("!!!");
            return false;
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        if indexes.is_empty() {
            return true;
        }
        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return false;
        } else {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return true;
        }
    }


    pub fn old_my_weighted_dp(&mut self, features: &[i32]) -> (Vec<(Integer, Vec<i32>)>) {
        if self.query_is_not_sat(features) || self.rc() == 0 {
            return Vec::new();
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return Vec::new();
        }
        let len = self.nodes.len();
        let mut dp: Vec<Vec<(Integer, Vec<i32>)>> = Vec::new();
        for i in 0..len {
            dp.push(Vec::new());
        }
        let mut heap: BinaryHeap<(Integer, usize, usize)> = BinaryHeap::new();
        for idx in 0..self.nodes.len() {
            if self.nodes[idx].is_zero == true {
                continue;
            }
            let mut res: Vec<(Integer, Vec<i32>)> = Vec::new();
            heap.clear();

            match &self.nodes[idx].ntype {
                And { children } => {
                    for son in children.iter() {
                        if res.is_empty() {
                            res = dp[*son].clone();
                            continue;
                        }
                        if (dp[*son].is_empty()) {
                            continue;
                        }
                        let mut fp = 0;
                        let mut sp = 0;
                        let mut w = Integer::ZERO;
                        heap.push((res[fp].0.clone() + dp[*son][sp].0.clone(), fp, sp));
                        let mut n_res: Vec<(Integer, Vec<i32>)> = Vec::new();
                        let mut set: HashSet<(usize, usize)> = HashSet::new();
                        for k in 0..self.limit_solution_num as usize {
                            if heap.is_empty() {
                                break;
                            }
                            (w, fp, sp) = heap.pop().unwrap();
                            if set.contains(&(fp, sp)) {
                                continue;
                            } else {
                                set.insert((fp, sp));
                            }
                            let mut n_v: Vec<i32> = res[fp].1.clone();
                            n_v.extend(&dp[*son][sp].1);
                            n_res.push((w, n_v));

                            if fp + 1 < res.len() {
                                heap.push((
                                    res[fp + 1].0.clone() + dp[*son][sp].0.clone(),
                                    fp + 1,
                                    sp,
                                ));
                            }
                            if sp + 1 < dp[*son].len() {
                                heap.push((
                                    res[fp].0.clone() + dp[*son][sp + 1].0.clone(),
                                    fp,
                                    sp + 1,
                                ));
                            }
                        }
                        res = n_res;
                    }
                }
                Or { children } => {
                    for son in children.iter() {
                        for j in 0..dp[*son].len() {
                            let (w, _vec) = &dp[*son][j];
                            heap.push((w.clone(), *son, j));
                        }
                    }
                    while let Some((_, son, j)) = heap.pop() {
                        if res.len() >= self.limit_solution_num as usize {
                            break;
                        }
                        let (w, v) = &dp[son][j];
                        res.push((w.clone(), v.clone()));
                    }
                }
                Literal { literal } => {
                    // solution.push(*literal);
                    let mut v = Vec::new();
                    v.push(*literal);
                    if *literal > 0 {
                        let mut max_weight = Integer::ZERO;
                        max_weight += self.weight_list[*literal as usize].clone();
                        res.push((max_weight, v));
                    } else {
                        res.push((Integer::ZERO, v));
                    }
                }
                _ => {}
            }
            dp[idx] = res;
        }
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();
        // println!("max_weight:{:?}",dp[len-1].clone());
        return dp[len - 1].clone();
    }



    pub fn my_weighted_dp(&mut self, features: &[i32]) -> (Vec<(Integer, Vec<i32>)>) {
        if self.query_is_not_sat(features) || self.rc() == 0 {
            return Vec::new();
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return Vec::new();
        }

        let len = self.nodes.len();
        let mut dp: Vec<Vec<(Integer, Vec<i32>)>> = Vec::new();
        for i in 0..len {
            dp.push(Vec::new());
        }

        let mut heap: BinaryHeap<(Integer, Vec<usize>)> = BinaryHeap::new();
        let mut set: HashSet<Vec<usize>> = HashSet::new();
        let mut or_heap: BinaryHeap<(Integer, Vec<i32>)> = BinaryHeap::new();

        for idx in 0..self.nodes.len() {
            if self.nodes[idx].is_zero == true {
                continue;
            }
            let mut res: Vec<(Integer, Vec<i32>)> = Vec::new();
            heap.clear();
            or_heap.clear();
            set.clear();

            match &self.nodes[idx].ntype {
                And { children } => {

                    let mut none_zero_children:Vec<usize> = Vec::new();
                    for child in children {
                        if self.nodes[*child].is_zero == true || dp[*child].len() == 0 {
                            continue;
                        }
                        none_zero_children.push(*child);
                    }

                    let mut value: Integer = Integer::ZERO.clone();
                    let mut plist: Vec<usize> = Vec::new();
                    for son in none_zero_children.iter() {
                        plist.push(0);
                        value += dp[*son][0].0.clone();
                    }

                    heap.push((value,plist));

                    for _ in 0..self.limit_solution_num {
                        if heap.is_empty() {
                            break;
                        }
                        (value, plist) = heap.pop().unwrap();
                        
                        let mut new_list: Vec<i32> = Vec::new();
                        for j in 0..plist.len() {
                            new_list.extend_from_slice(&dp[none_zero_children[j]][plist[j]].1);
                        }
                        res.push((value.clone(),new_list));
                        
                        if res.len() == self.limit_solution_num as usize {
                            break;
                        }
                        
                        for j in 0..none_zero_children.len() {
                            let child = none_zero_children[j];
                            let mut new_plist = plist.clone();
                            if new_plist[j] + 1 == dp[child].len() {
                                continue;
                            }
                            let mut new_value = value.clone();

                            new_value -= dp[child][new_plist[j]].0.clone();
                            new_value += dp[child][new_plist[j]+1].0.clone();
                            new_plist[j] += 1;
                            if !set.contains(&new_plist) {
                                heap.push((new_value,new_plist.clone()));
                                set.insert(new_plist);
                            }
                            

                        }

                    }
                }
                Or { children } => {
                    for son in children.iter() {
                        for j in 0..dp[*son].len() {
                            let (w, _vec) = dp[*son][j].clone();
                            or_heap.push((w, _vec));
                        }
                    }
                    while let Some((w, list)) = or_heap.pop() {
                        if res.len() >= self.limit_solution_num as usize {
                            break;
                        }
                        res.push((w, list));
                    }
                }
                Literal { literal } => {
                    // solution.push(*literal);
                    let mut v = Vec::new();
                    v.push(*literal);
                    if *literal > 0 {
                        let mut max_weight = Integer::ZERO;
                        max_weight += self.weight_list[*literal as usize].clone();
                        res.push((max_weight, v));
                    } else {
                        res.push((Integer::ZERO, v));
                    }
                }
                _ => {}
            }
            // println!("{:?}",res);
            dp[idx] = res;
        }
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();
        // println!("max_weight:{:?}",dp[len-1].clone());
        return dp[len - 1].clone();
    }
    

    pub fn my_execute_query(
        &mut self,
        features: &[i32],
    ) -> (Integer, BTreeSet<i32>, Vec<Vec<i32>>, Duration) {
        let start = Instant::now();
        let res = match features.len() {
            // 0 => (self.rc(), BTreeSet::new(), Vec::new(), start.elapsed()),
            // 1 => self.card_of_feature_with_marker(features[0]),
            // 1..= 100 => {
            // }
            _ => self.new_my_partial_config_counter(features),
        };

        return res;
    }

    pub fn my_execute_partial_config(
        &mut self,
        features: &[i32],
    ) -> (Integer, Duration) {
        let start = Instant::now();
        let res = match features.len() {
            0 => (self.rc(), start.elapsed()),
            1 => (self.card_of_feature_with_marker(features[0]),start.elapsed()),
            _ => self.clean_partial_config_counter(features),
        };

        return res;
    }

    pub fn my_execute_project(
        &mut self,
        features: &[i32],
    ) -> (Integer, Duration) {
        let start = Instant::now();
        self.limit_solution_num = 200;
        let res1 = self.new_my_project_query_unexc(features,&vec![],100);
        // let res2 = self.my_project_query_unexc(features,&vec![],100);
        // println!("{:?} {:?}",res1,res2);
        return res1;
    }

    pub fn CNFjudger(features: &[i32], addtionCNF: &Vec<Vec<i32>>) -> bool{
        // println!("feature: {:?}, addtionCNF:{:?} ",features,addtionCNF);
        let mut maxIdx = 0;
        for f in features {
            maxIdx = std::cmp::max(maxIdx,f.abs());
        }
        let mut flag = vec![0; (maxIdx + 1) as usize];
        for f in features {
            if *f < 0 {
                flag[f.abs() as usize ] = -1;
            }else{
                flag[*f as usize] = 1;
            }
        }
        for clause in addtionCNF {
            if clause.len() == 0 {
                continue;
            }
            let mut sum = 0;
            let mut len = 0;
            for var in clause {
                len += 1;
                if var.abs() > maxIdx {
                    continue;
                }
                if *var < 0 {
                    sum += flag[var.abs() as usize] * (-1);
                }else{
                    sum += flag[*var as usize];
                }
            }
            sum *= -1;
            if sum == len {
                // println!("false");
                return false;
            }
        }
        return true;
    }

    pub fn my_project_query_unexc(&mut self, features: &[i32], neg_feature: &[i32], exact_mc_threshold: usize) -> (Integer, Duration) {
        
        if self.rc() == 0 {
            return (Integer::ZERO, Instant::now().elapsed());
        }

        // self.debug();
        let neg_feature: Vec<i32> = self.reduce_query(neg_feature);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&neg_feature);

        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut vis: Vec<bool> = Vec::new();
        vis.resize(self.nodes.len(), false);
        vis[self.nodes.len() - 1] = true;
        // println!("{}",self.nodes.len() -1);
        for index in (0..self.nodes.len()).rev() {
            // println!("{},{}",index,vis[index]);
            if !vis[index] || self.nodes[index].is_zero {
                continue;
            }
            match &self.nodes[index].ntype {
                And { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                Or { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                _ => {}
            }
        }


        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();


        for idx in 0..self.nodes.len() {
            self.nodes[idx].temp = Integer::ZERO;
        }

        let mut zero_literal: Vec<bool> = vec![false; 2*(self.number_of_variables as usize + 1)];
        for number in features {
            zero_literal[*number as usize + self.number_of_variables as usize] = true;
            zero_literal[((*number * (-1)) + self.number_of_variables as i32) as usize] = true;
            
        }
        let mut indexes: Vec<usize> = Vec::new();
        let mut have_zero = vec![false;self.nodes.len()];
        for number in 0..2*(self.number_of_variables) + 1 {
            if zero_literal[number as usize] == false {
                let num: i32 = number as i32 - self.number_of_variables as i32;
                if let Some(i) = self.literals.get(&num).cloned() {
                    indexes.push(i);
                    have_zero[i] = true;
                }
            }
        }
        self.mark_assumptions(&indexes);
        
        for idx in 0..self.md.len() {
            let index = self.md[idx];
            have_zero[index] = true;
        }
        // self.debug();
        // println!("{:?}",have_zero);

        for &index in &self.md {
            self.nodes[index].marker = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
        }
        self.md.clear();
        
        let start = Instant::now();
        let mut indexes = Vec::with_capacity(features.len());
        for number in features {
            if let Some(i) = self.literals.get(&number).cloned() {
                indexes.push(i);
            }
            if let Some(i) = self.literals.get(&-number).cloned() {
                indexes.push(i);
            }
        }

        self.mark_assumptions(&indexes);


        let mut need_list = vec![false;self.nodes.len()];
        let mut or_list:Vec<usize> = Vec::new();
        for idx in 0..self.md.len() {
            let index = self.md[idx];
            match &self.nodes[index].ntype {
                Or{..} => {
                    need_list[index] = true;
                    or_list.push(index);
                }
                _ => {}
            }
        }
        for idx in (0..self.nodes.len()).rev() {
            let index = idx;
            if !need_list[index] {
                continue;
            }
            match &self.nodes[index].ntype {
                Or {children} => {
                    for child in children {
                        need_list[*child] = true;
                    }
                }
                And {children} => {
                    for child in children {
                        need_list[*child] = true;
                    }
                }
                _ => {}
            }
        }


        let mut list: Vec<Vec<Vec<i32>>> = Vec::new();
        for i in 0..self.nodes.len() {
            list.push(Vec::new());
        }

        
        let limit = exact_mc_threshold;


        let mut node_list: Vec<usize> = Vec::new();
        for &index in &indexes {
            node_list.push(index);
        }
        for i in 0..self.md.len() {
            node_list.push(self.md[i]);
        }
        let mut node_num = 0;
        for idx in 0..node_list.len() {
            let index = node_list[idx];
            if !vis[index] {
                continue;
            }
            match self.nodes[index].ntype.clone() {
                And { children } => {
                    let mut temp = Integer::ZERO;
                    let mut flag = true;
                    for child in &children {
                        if !vis[*child] {
                            continue;
                        }
                        if temp == 0 {
                            temp = self.nodes[*child].temp.clone();
                        }else if self.nodes[*child].temp != 0 {
                            temp *= self.nodes[*child].temp.clone();
                        }

                        if self.nodes[*child].temp != list[*child].len() {
                            flag = false;
                        }
                    }
                    self.nodes[index].temp = temp;

                    if flag && self.nodes[index].temp <= limit  {
                        if !need_list[index] {
                            node_num += 1;
                            continue;
                        }
                        for child in &children {
                            if !vis[*child] {
                                continue;
                            }
                            if list[index].is_empty() {
                                list[index] = list[*child].clone();
                            }else if(list[*child].len() != 0){
                                let mut new_slist: Vec<Vec<i32>> = Vec::new();
                                for s1 in &list[index] {
                                    for s2 in &list[*child] {
                                        let mut s = s1.clone();
                                        s.extend_from_slice(s2);
                                        s.sort();
                                        new_slist.push(s);
                                    }
                                }
                                list[index] = new_slist;
                            }
                        }
                    }

                }
                Or { children } => {
                    let mut temp = Integer::ZERO;
                    let mut flag = true;
                    for child in &children {
                        if !vis[*child] {
                            continue;
                        }
                        temp += self.nodes[*child].temp.clone();
                        if self.nodes[*child].temp != list[*child].len() {
                            flag = false;
                        }
                    }
                    self.nodes[index].temp = temp;

                    if flag  {
                        if !need_list[index] {
                            node_num += 1;
                            continue;
                        }
                        let mut s: HashSet<Vec<i32>> = HashSet::new();
                        for child in children {
                            if !vis[child] {
                                continue;
                            }
                            for temp in &list[child] {
                                s.insert(temp.clone());
                            }
                        }
                        for solution in s {
                            list[index].push(solution);
                        }
                        temp = Integer::from(list[index].len());
                        if temp > limit {
                            list[index].clear();
                        }
                        self.nodes[index].temp = temp;
                    }
                }
                Literal {literal} => {
                    let mut s : Vec<Vec<i32>> = Vec::new();
                    if literal < 0{
                        s.push(vec![]);
                    }else{
                        s.push(vec![literal.clone()]);
                    }
                    list[index] = s;
                    self.nodes[index].temp = Integer::ONE.clone();
                }
                _ => {}
            }
        }
        // println!("need_count_node_num = {:?}",node_num);
        let res = self.rt();
        for idx in 0..self.nodes.len(){
            self.nodes[idx].marker = false;
            self.nodes[idx].temp = Integer::ZERO;
        }
        self.md.clear();
        return (res,start.elapsed());
    }















    pub fn my_project_query_unexc_dev(&mut self, features: &[i32], neg_feature: &[i32], exact_mc_threshold: usize) -> (Integer, Duration) {

        // self.debug();
        let neg_feature: Vec<i32> = self.reduce_query(neg_feature);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&neg_feature);

        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut vis: Vec<bool> = Vec::new();
        vis.resize(self.nodes.len(), false);
        vis[self.nodes.len() - 1] = true;
        // println!("{}",self.nodes.len() -1);
        for index in (0..self.nodes.len()).rev() {
            // println!("{},{}",index,vis[index]);
            if !vis[index] || self.nodes[index].is_zero {
                continue;
            }
            match &self.nodes[index].ntype {
                And { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                Or { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                _ => {}
            }
        }


        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();


        for idx in 0..self.nodes.len() {
            self.nodes[idx].temp = Integer::ZERO;
        }

        let start = Instant::now();
        let mut indexes = Vec::with_capacity(features.len());
        for number in features {
            if let Some(i) = self.literals.get(&number).cloned() {
                indexes.push(i);
            }
            if let Some(i) = self.literals.get(&-number).cloned() {
                indexes.push(i);
            }
        }

        self.mark_assumptions(&indexes);

        let mut list: Vec<Vec<Vec<i32>>> = Vec::new();
        let mut cache_id_list:Vec<Vec<usize>> = Vec::new();
        let mut map: HashMap<Vec<usize>,Vec<Vec<i32>>> = HashMap::new();
        for i in 0..self.nodes.len() {
            list.push(Vec::new());
            cache_id_list.push(Vec::new());
        }

        
        let limit = exact_mc_threshold;


        let mut node_list: Vec<usize> = Vec::new();
        for &index in &indexes {
            node_list.push(index);
        }
        for i in 0..self.md.len() {
            node_list.push(self.md[i]);
        }

        for idx in 0..node_list.len() {
            let index = node_list[idx];
            if !vis[index] {
                continue;
            }
            match self.nodes[index].ntype.clone() {
                And { children } => {
                    let mut temp = Integer::ZERO;
                    for child in &children {
                        if !vis[*child] {
                            continue;
                        }
                        if temp == 0 {
                            temp = self.nodes[*child].temp.clone();
                        }else if self.nodes[*child].temp != 0 {
                            temp *= self.nodes[*child].temp.clone();
                        }
                    }
                    self.nodes[index].temp = temp;

                    if self.nodes[index].temp <= limit {
                        let mut id_list:Vec<usize> = Vec::new();
                        for child in &children {
                            if !vis[*child] {
                                continue;
                            }
                            id_list.extend_from_slice(&cache_id_list[*child]);
                        }
                        cache_id_list[index] = id_list;
                    }
                }
                Or { children } => {
                    let mut flag:bool = false;
                    let mut temp: Integer = Integer::ZERO;
                    let mut child_num = 0;
                    for child in &children {
                        if !vis[*child] {
                            continue;
                        }
                        child_num += 1;
                        if cache_id_list[*child].is_empty() {
                            flag = true;
                        }
                        temp += self.nodes[*child].temp.clone();
                    }
                    if flag {
                        self.nodes[index].temp = temp;
                        continue;
                    }
                    if child_num == 1 {
                        self.nodes[index].temp = temp;
                        for child in &children {
                            if !vis[*child] {
                                continue;
                            }
                            cache_id_list[index] = cache_id_list[*child].clone();
                        }
                        continue;
                    }
                    let mut id_set: HashMap<usize,usize> = HashMap::new();
                    let mut unsolved_id_list: Vec<Vec<usize>> = Vec::new();
                    let mut id_list: Vec<usize> = Vec::new();

                    for child in &children {
                        if !vis[*child] {
                            continue;
                        }
                        for id in &cache_id_list[*child] {
                            if id_set.contains_key(id) {
                                id_set.insert(*id, id_set.get(id).unwrap() + 1);
                            }else{
                                id_set.insert(*id,1);
                            }
                        }
                    }
                    let mut repeat_len: Integer = Integer::ONE.clone();
                    for (key,value) in &id_set {
                        if *value == children.len(){
                            id_list.push(*key);
                            repeat_len *= self.nodes[*key].temp.clone();
                        }
                    }
                    
                    for child in &children {
                        if !vis[*child] {
                            continue;
                        }
                        let mut list: Vec<usize> = Vec::new();
                        for id in &cache_id_list[*child] {
                            if *id_set.get(id).unwrap() != children.len() {
                                list.push(*id);
                            }
                        }
                        unsolved_id_list.push(list);
                    }

                    let mut result: HashSet<Vec<i32>> = HashSet::new();
                    
                    
                    let mut repeat_num: i32 = 0;
                    for temp_list in &unsolved_id_list {
                        let mut current: Vec<i32> = Vec::new();
                        if map.contains_key(temp_list) {
                            for temp in map.get(temp_list).unwrap() {
                                if !result.contains(temp) {
                                    result.insert(temp.clone());
                                }else{
                                    repeat_num += 1;
                                }
                            }
                            continue;
                        }
                        let mut solution_list: Vec<Vec<i32>> = Vec::new();
                        self.cartesian_product(&list, &temp_list, &mut solution_list,&mut result, &mut current, 0,&mut repeat_num);
                        map.insert(temp_list.clone(), solution_list);
                    }
                    
                    for solution in &result {
                        list[index].push(solution.clone());
                    }
                    self.nodes[index].temp = temp - repeat_num * repeat_len;
                    if !result.is_empty() {
                        id_list.push(index);
                    }
                    cache_id_list[index] = id_list;
                }
                Literal {literal} => {
                    let mut s : Vec<Vec<i32>> = Vec::new();
                    if literal < 0{
                        s.push(vec![]);
                    }else{
                        s.push(vec![literal.clone()]);
                    }
                    list[index] = s;
                    cache_id_list[index] = [index].to_vec();
                    self.nodes[index].temp = Integer::ONE.clone();
                }
                _ => {}
            }
        }
        let res = self.rt();
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].temp = Integer::ZERO;
        }
        self.md.clear();
        return (res,start.elapsed());
    }







    pub fn cartesian_product(
      &self,
      list: &Vec<Vec<Vec<i32>>>,
      id_list: &Vec<usize>,
      solution_list: &mut Vec<Vec<i32>>,
      result: &mut HashSet<Vec<i32>>,
      current: &mut Vec<i32>,
      depth: usize,
      repeat_num: &mut i32,
    )  {
        if depth == id_list.len() {
            let mut temp = current.clone();
            temp.sort_unstable();
            if !result.contains(&temp) {
                result.insert(temp.clone());
                solution_list.push(temp);
            }else{
                *repeat_num += 1;
            }
            return;
        }
        for solution in &list[id_list[depth]] {
            let current_len = current.len();
            current.extend_from_slice(solution);
            self.cartesian_product(list, id_list,solution_list, result, current, depth + 1,repeat_num);
            current.truncate(current_len);
        }
    }










    




    pub fn new_my_project_query_unexc(&mut self, features: &[i32], neg_feature: &[i32], exact_mc_threshold: usize) -> (Integer, Duration) {

        if self.rc() == 0 {
            return (Integer::ZERO, Instant::now().elapsed());
        }

        // self.debug();
        let neg_feature: Vec<i32> = self.reduce_query(neg_feature);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&neg_feature);

        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        let mut vis: Vec<bool> = Vec::new();
        vis.resize(self.nodes.len(), false);
        vis[self.nodes.len() - 1] = true;
        for index in (0..self.nodes.len()).rev() {
            if !vis[index] || self.nodes[index].is_zero {
                continue;
            }
            match &self.nodes[index].ntype {
                And { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                Or { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                _ => {}
            }
        }


        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();

        let mut zero_literal: Vec<bool> = vec![false; 2*(self.number_of_variables as usize + 1)];
        for number in features {
            zero_literal[*number as usize + self.number_of_variables as usize] = true;
            zero_literal[((*number * (-1)) + self.number_of_variables as i32) as usize] = true;
            
        }
        let mut indexes: Vec<usize> = Vec::new();
        let mut have_zero = vec![false;self.nodes.len()];
        for number in 0..2*(self.number_of_variables) + 1 {
            if zero_literal[number as usize] == false {
                let num: i32 = number as i32 - self.number_of_variables as i32;
                if let Some(i) = self.literals.get(&num).cloned() {
                    indexes.push(i);
                    have_zero[i] = true;
                }
            }
        }
        self.mark_assumptions(&indexes);
        
        for idx in 0..self.md.len() {
            let index = self.md[idx];
            have_zero[index] = true;
        }
        // self.debug();
        // println!("{:?}",have_zero);

        for &index in &self.md {
            self.nodes[index].marker = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
        }
        self.md.clear();


        for idx in 0..self.nodes.len() {
            self.nodes[idx].temp = Integer::ZERO;
        }

        let start = Instant::now();
        let mut indexes = Vec::with_capacity(features.len());
        for number in features {
            if let Some(i) = self.literals.get(&number).cloned() {
                indexes.push(i);
            }
            if let Some(i) = self.literals.get(&-number).cloned() {
                indexes.push(i);
            }
        }

        self.mark_assumptions(&indexes);

         let mut need_list = vec![false;self.nodes.len()];
         let mut or_list:Vec<usize> = Vec::new();
         for idx in 0..self.md.len() {
             let index = self.md[idx];
             match &self.nodes[index].ntype {
                 Or{..} => {
                     need_list[index] = true;
                     or_list.push(index);
                 }
                 _ => {}
             }
         }
         for idx in (0..self.nodes.len()).rev() {
             let index = idx;
             if !need_list[index] {
                 continue;
             }
             match &self.nodes[index].ntype {
                 Or {children} => {
                     for child in children {
                         need_list[*child] = true;
                     }
                 }
                 And {children} => {
                     for child in children {
                         need_list[*child] = true;
                     }
                 }
                 _ => {}
             }
         }
        
        

        let mut list: Vec<HashSet<Vec<i32>>> = Vec::new();
        for i in 0..self.nodes.len() {
            list.push(HashSet::new());
        }

        for idx in 0..self.nodes.len() {
            self.nodes[idx].temp = Integer::ZERO;
        }
        for idx in indexes {
            self.nodes[idx].temp = Integer::ONE.clone();
        }
        for idx in 0..self.md.len() {
            if !vis[self.md[idx]] {
                continue;
            }
            let i = self.md[idx];
            match &self.nodes[i].ntype {
                And { children } => {          
                    let mut temp = Integer::ONE.clone();      
                    for child in children.clone() {
                        if self.nodes[child].marker == false || !vis[child]{
                            continue;
                        }
                        temp *= self.nodes[child].temp.clone();
                    }
                    self.nodes[i].temp = temp;
                }
                Or { children } => {
                    let mut temp = Integer::ZERO.clone();      
                    for child in children.clone() {
                        if self.nodes[child].marker == false || !vis[child]{
                            continue;
                        }
                        temp += self.nodes[child].temp.clone();                       
                    }
                    self.nodes[i].temp = temp;
                }
                False => self.nodes[i].temp.assign(0),
                _ => self.nodes[i].temp.assign(1), // True and Literal
            }
        }

        
        let mut pdList: Vec<Integer> = vec![Integer::ZERO; self.nodes.len()];
        pdList[self.nodes.len() - 1] = Integer::ONE.clone();
        
        let mut orList: Vec<(usize,Integer)> = Vec::new();
        
        let mut node_num = 0;

        for idx in 0..self.md.len() {
            let idx = self.md.len() - idx - 1;
            if !vis[self.md[idx]] {
                continue;
            }

            let index = self.md[idx];
            match &self.nodes[index].ntype {
                And {children} => {
                    for child in children {
                        if !vis[*child] || self.nodes[*child].marker == false{
                            continue;
                        }
                        pdList[*child] = (self.nodes[index].temp.clone() / self.nodes[*child].temp.clone()) * pdList[index].clone();
                    }
                }
                Or {children} => {
                    for child in children {
                        if !vis[*child] || self.nodes[*child].marker == false{
                            continue;
                        }
                        pdList[*child] = pdList[index].clone();
                    }
                    if need_list[index] == false {
                        node_num +=1 ;
                        continue;
                    }
                    orList.push((index,pdList[index].clone()));
                }
                _ => {}
            }
        }
        orList.sort_by(|a,b| b.1.cmp(&a.1));

        let mut real_temp = vec![Integer::ZERO; self.nodes.len()];
        for idx in 0..self.nodes.len() {
            real_temp[idx] = self.nodes[idx].temp.clone();
        }

        let mut list: Vec<Vec<Vec<i32>>> = vec![Vec::new(); self.nodes.len()];


        let mut q: VecDeque<usize> = VecDeque::new();
        let mut tvis: Vec<bool> = vec![false; self.nodes.len()];
        let mut isCount: Vec<bool> = vec![false; self.nodes.len()];
        
        // let mar = exact_mc_threshold / orList.len();
        let mut limit: Integer = Integer::from(exact_mc_threshold); 

        let mut max_pd = Integer::ZERO;
        if !orList.is_empty() {
            max_pd = orList[0].1.clone();
        }

        let start = Instant::now();
        let time_limit = Duration::from_millis(50);

        for (index,pd) in orList {

            if isCount[index] {
                continue;
            }
            
            let mut node_list: Vec<usize> = Vec::new();
            
            q.push_back(index);
            tvis[index] = true;
            while !q.is_empty() {
                let top = q.pop_front().unwrap();
                node_list.push(top);
                match &self.nodes[top].ntype {
                    And {children} | Or {children} => {
                        for child in children {
                            if tvis[*child] || !vis[*child] || self.nodes[*child].marker == false {
                                continue;
                            }
                            q.push_back(*child);
                            tvis[*child] = true;
                        }
                    }
                    _ => {}
                }
            }
            node_list.sort();

            limit = self.nodes[index].temp.clone();
            

            for idx in 0..node_list.len() {
                let index = node_list[idx];
                if !vis[index] || isCount[index] {
                    continue;
                }
                isCount[index] = true;
                match self.nodes[index].ntype.clone() {
                    And { children } => {
                        let mut temp = Integer::ZERO;
                        let mut flag = true;
                        for child in &children {
                            if !vis[*child] {
                                continue;
                            }
                            if temp == 0 {
                                temp = self.nodes[*child].temp.clone();
                            }else if self.nodes[*child].temp != 0 {
                                temp *= self.nodes[*child].temp.clone();
                            }
    
                            if self.nodes[*child].temp != list[*child].len() {
                                flag = false;
                            }
                        }
                        self.nodes[index].temp = temp;
    
                        if flag && self.nodes[index].temp <= limit && need_list[index]{
                            for child in &children {
                                if !vis[*child] {
                                    continue;
                                }
                                if list[index].is_empty() {
                                    list[index] = list[*child].clone();
                                }else if(list[*child].len() != 0){
                                    let mut new_slist: Vec<Vec<i32>> = Vec::new();
                                    for s1 in &list[index] {
                                        for s2 in &list[*child] {
                                            let mut s = s1.clone();
                                            s.extend_from_slice(s2);
                                            s.sort();
                                            new_slist.push(s);
                                        }
                                    }
                                    list[index] = new_slist;
                                }
                            }
                        }
    
                    }
                    Or { children } => {
                        let mut temp = Integer::ZERO;
                        let mut flag = true;
                        for child in &children {
                            if !vis[*child] {
                                continue;
                            }
                            temp += self.nodes[*child].temp.clone();
                            if self.nodes[*child].temp != list[*child].len() {
                                flag = false;
                            }
                        }
                        
                        
                        if flag && need_list[index]{
                            let mut s: HashSet<Vec<i32>> = HashSet::new();
                            for child in children {
                                if !vis[child] {
                                    continue;
                                }
                                for temp in &list[child] {
                                    s.insert(temp.clone());
                                }
                            }
                            for solution in s {
                                list[index].push(solution);
                            }
                            temp = Integer::from(list[index].len());
                            if temp > limit {
                                list[index].clear();
                            }
                            self.nodes[index].temp = temp;
                        }else{
                            self.nodes[index].temp = temp;
                        }
                    }
                    Literal {literal} => {
                        let mut s : Vec<Vec<i32>> = Vec::new();
                        if literal < 0{
                            s.push(vec![]);
                        }else{
                            s.push(vec![literal.clone()]);
                        }
                        list[index] = s;
                        self.nodes[index].temp = Integer::ONE.clone();
                    }
                    _ => {}
                }
                if start.elapsed() > time_limit {
                    break;
                }
            }
            if start.elapsed() > time_limit {
                break;
            }
            // println!("{:?} {:?}",start.elapsed(), self.nodes[index].temp);
        }

        // println!("node_num = {:?}",node_num);

        let mut tempList: Vec<Integer> = Vec::new();
        for i in 0..self.nodes.len() {
            tempList.push(self.nodes[i].temp.clone());
        }
        // println!("{:?}",tempList);
        // self.debug();
        for idx in 0..self.md.len() {
            let idx = self.md[idx];
            if !vis[idx] || isCount[idx] {
                continue;
            }
            let mut temp = Integer::ZERO;
            match &self.nodes[idx].ntype {
                And { children } => {                
                    for child in children.clone() {
                        if self.nodes[child].marker == false || !vis[child]{
                            continue;
                        }
                        if temp == 0 {
                            temp = self.nodes[child].temp.clone();
                        }else{
                            temp *= self.nodes[child].temp.clone();
                        }                       
                    }
                }
                Or { children } => {
                    for child in children.clone() {
                        if self.nodes[child].marker == false || !vis[child]{
                            continue;
                        }
                        temp += self.nodes[child].temp.clone();                     
                    }
                }
                _ => {}
            }
            self.nodes[idx].temp = temp;
        }

        
        let res = self.rt();
        for index in 0..self.nodes.len() {
            self.nodes[index].marker = false;
            self.nodes[index].temp = Integer::ZERO;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();
        return (res,start.elapsed());
    }









pub fn my_project_query(&mut self, features: &[i32], neg_feature: &[i32]) -> (Vec<Vec<i32>>, Duration) {
    if self.rc() == 0 {
        return (Vec::new(), Instant::now().elapsed());
    }
    // self.debug();
    let neg_feature: Vec<i32> = self.reduce_query(neg_feature);
    let indexes: Vec<usize> = self.map_features_opposing_indexes(&neg_feature);

    self.mark_assumptions(&indexes);

    for &index in &indexes {
        self.nodes[index].is_zero = true;
        self.nodes[index].temp = Integer::ZERO;
        // println!("{}",index);
        for idx in 0..self.nodes[index].parents.len() {
            let parent = self.nodes[index].parents[idx];
            match &self.nodes[parent].ntype {
                And { .. } => {
                    self.nodes[parent].is_zero = true;
                    self.nodes[parent].temp = Integer::ZERO;
                }
                Or { children } => {
                    if children.len() == 1 {
                        self.nodes[parent].is_zero = true;
                    }
                    if !self.nodes[parent].or_flag {
                        self.nodes[parent].or_flag = true;
                    } else {
                        self.nodes[parent].is_zero = true;
                    }
                }
                _ => {}
            }
        }
    }

    for idx in 0..self.md.len() {
        let index = self.md[idx];
        if self.nodes[index].is_zero == false {
            continue;
        }
        for idx in 0..self.nodes[index].parents.len() {
            let parent = self.nodes[index].parents[idx];
            match &self.nodes[parent].ntype {
                And { .. } => {
                    self.nodes[parent].is_zero = true;
                    self.nodes[parent].temp = Integer::ZERO;
                }
                Or { children } => {
                    if children.len() == 1 {
                        self.nodes[parent].is_zero = true;
                    }
                    if !self.nodes[parent].or_flag {
                        self.nodes[parent].or_flag = true;
                    } else {
                        self.nodes[parent].is_zero = true;
                    }
                }
                _ => {}
            }
        }
    }
    let mut vis: Vec<bool> = Vec::new();
    vis.resize(self.nodes.len(), false);
    vis[self.nodes.len() - 1] = true;
    // println!("{}",self.nodes.len() -1);
    for index in (0..self.nodes.len()).rev() {
        // println!("{},{}",index,vis[index]);
        if !vis[index] || self.nodes[index].is_zero {
            continue;
        }
        match &self.nodes[index].ntype {
            And { children } => {
                for child in children {
                    if !self.nodes[*child].is_zero {
                        vis[*child] = true;
                    }
                }
            }
            Or { children } => {
                for child in children {
                    if !self.nodes[*child].is_zero {
                        vis[*child] = true;
                    }
                }
            }
            _ => {}
        }
    }


    for &index in &self.md {
        self.nodes[index].marker = false;
        self.nodes[index].is_zero = false;
        self.nodes[index].or_flag = false;
    }
    for index in indexes {
        self.nodes[index].marker = false;
        self.nodes[index].is_zero = false;
        self.nodes[index].or_flag = false;
    }
    self.md.clear();

    let mut varSet: HashSet<i32> = HashSet::new();
    for f in features {
        varSet.insert(*f);
    }
    // println!("{:?}",varSet);

    let start = Instant::now();

    let mut features_list: Vec<i32> = Vec::new();
    for f in varSet {
        features_list.push(f.clone());
        features_list.push(f.clone() * -1);
    }

    let indexes: Vec<usize> = self.map_features_opposing_indexes(&features_list);
    self.mark_assumptions(&indexes);

    for &index in &indexes {
        self.nodes[index].marker = true;
    }


    let limit =  self.limit_solution_num as usize;

    let mut solution_cache: Vec<Option<Vec<Vec<i32>>>> = vec![None; self.nodes.len()];

    let solutions = self.generate_project_solutions_recursive(
        self.nodes.len() - 1,
        &mut solution_cache,
        &vis,
        limit,
    );
    // println!("{:?}",solution_cache);
    for &index in &self.md {
        self.nodes[index].marker = false;
        self.nodes[index].is_zero = false;
        self.nodes[index].or_flag = false;
    }
    for index in indexes {
        self.nodes[index].marker = false;
        self.nodes[index].is_zero = false;
        self.nodes[index].or_flag = false;
    }
    self.md.clear();
    
    return (solutions, start.elapsed());
}





fn generate_project_solutions_recursive(
    &self,
    node_idx: usize,
    cache: &mut Vec<Option<Vec<Vec<i32>>>>,
    vis: &[bool],
    limit: usize,
) -> Vec<Vec<i32>> {
    // println!("{:?}",node_idx);
    if !vis[node_idx] || self.nodes[node_idx].marker == false {
        return Vec::new();
    }
    // println!("{:?}",node_idx);

    if let Some(ref solutions) = cache[node_idx] {
        return solutions.clone();
    }

    let solutions = match &self.nodes[node_idx].ntype {
        Literal { literal } => {
            if *literal > 0 {
                vec![vec![*literal]]
            }else {
                vec![vec![]]
            }
            
        }
        And { children } => {
            // println!("and: {:?}",children);
            self.combine_and_solutions_project(children, cache, vis, limit)
        }
        Or { children } => {
            // println!("or:{:?}",children);
            self.combine_or_solutions_project(children, cache, vis, limit)
        }
        True => {
            vec![vec![]]
        }
        False => {
            Vec::new()
        }
    };

    cache[node_idx] = Some(solutions.clone());
    // println!("{:?}",solutions);
    solutions
}

fn combine_and_solutions_project(
    &self,
    children: &[usize],
    cache: &mut Vec<Option<Vec<Vec<i32>>>>,
    vis: &[bool],
    limit: usize,
) -> Vec<Vec<i32>> {
    let child_indices: Vec<_> = children
        .iter()
        .copied()
        .filter(|&idx| vis[idx] && self.nodes[idx].marker)
        .collect();

    if child_indices.is_empty() {
        return Vec::new();
    }

    let result = self.generate_project_solutions_recursive(child_indices[0], cache, vis, limit);
    if result.is_empty() || child_indices.len() == 1 {
        return result; 
    }

    let mut capacity = result.len();
    let mut child_capacities = Vec::with_capacity(child_indices.len() - 1);

    let mut child_solutions = Vec::with_capacity(child_indices.len() - 1);
    for &child in &child_indices[1..] {
        let solutions = self.generate_project_solutions_recursive(child, cache, vis, limit);
        if solutions.is_empty() {
            return Vec::new(); 
        }
        child_capacities.push(solutions.len());
        capacity = std::cmp::min(capacity * solutions.len(), limit);
        child_solutions.push(solutions);
    }
    let capacity = std::cmp::min(capacity, limit);
    let mut new_result = Vec::with_capacity(capacity);

    self.combine_solutions_recursive_project(
        &result,
        &child_solutions,
        &mut new_result,
        &mut Vec::with_capacity(children.len() * 2), 
        0,
        limit,
    );
    // println!("new_result: {:?}",new_result);
    new_result
}

fn combine_solutions_recursive_project(
    &self,
    base_solutions: &[Vec<i32>],
    child_solutions: &[Vec<Vec<i32>>],
    result: &mut Vec<Vec<i32>>,
    current: &mut Vec<i32>,
    depth: usize,
    limit: usize,
) {
    if result.len() >= limit {
        return;
    }

    if depth == 0 {
        for base in base_solutions {
            if result.len() >= limit {
                break;
            }
            current.clear();
            current.extend_from_slice(base);
            // current.sort_unstable();

            if child_solutions.is_empty() {
                let mut temp = current.clone();
                temp.sort_unstable();
                result.push(temp);
            } else {
                self.combine_solutions_recursive_project(
                    base_solutions,
                    child_solutions,
                    result,
                    current,
                    depth + 1,
                    limit,
                );
            }
        }
    } else if depth <= child_solutions.len() {
        let child_idx = depth - 1;
        for child_sol in &child_solutions[child_idx] {
            if result.len() >= limit {
                break;
            }

            let current_len = current.len();

            current.extend_from_slice(child_sol);

            if depth == child_solutions.len() {
                let mut temp = current.clone();
                temp.sort_unstable();
                result.push(temp);
            } else {
                // println!("{:?}",current);
                self.combine_solutions_recursive_project(
                    base_solutions,
                    child_solutions,
                    result,
                    current,
                    depth + 1,
                    limit,
                );
            }

            current.truncate(current_len);
        }
        // println!("deep:{:?},result:{:?},child_solutions:{:?}",depth,result,child_solutions[depth-1]);
    }
    
}

fn combine_or_solutions_project(
    &self,
    children: &[usize],
    cache: &mut Vec<Option<Vec<Vec<i32>>>>,
    vis: &[bool],
    limit: usize,
) -> Vec<Vec<i32>> {
    if children.is_empty() {
        return Vec::new();
    }

    let mut result = Vec::with_capacity(
        std::cmp::min(children.len() * 4, limit), 
    );
    let mut set: HashSet<Vec<i32>> = HashSet::new();

    let child_indices: Vec<_> = children
        .iter()
        .copied()
        .filter(|&idx| vis[idx] && self.nodes[idx].marker)
        .collect();

    if child_indices.is_empty() {
        return Vec::new();
    }

    for &child in &child_indices {
        if result.len() >= limit {
            break;
        }

        let child_solutions =
            self.generate_project_solutions_recursive(child, cache, vis, limit );

        for solution in child_solutions {
            if set.contains(&solution) {
                continue;
            }else{
                if result.len() >= limit {
                    break;
                }else{
                    result.push(solution.clone());
                    set.insert(solution);
                }
            }
        }
    }

    result
}

    pub fn init_weight(&mut self, weight_file_path: String) {
        let path = Path::new(&weight_file_path);
        let file = File::open(path).unwrap();
        let reader = io::BufReader::new(file);

        //println!("num_of_feature:{}", self.number_of_variables);
        for i in 0..self.number_of_variables + 1 {
            self.weight_list.push(0);
        }

        for line in reader.lines() {
            let line = line.unwrap();
            let parts: Vec<&str> = line.split_whitespace().collect();
            let feature: i32 = parts[0].parse().expect("Not a number");
            let weight: i32 = parts[1].parse().expect("Not a number");
            self.weight_list[feature as usize] += weight;
        }
    }

    pub fn init_weight_from_vec(&mut self, weights: Vec<i32>) {
        self.weight_list.clear();
        self.weight_list.push(0);
        self.weight_list.extend_from_slice(&weights);

        if self.weight_list.len() <= self.number_of_variables as usize {
            for _ in self.weight_list.len()..=self.number_of_variables as usize {
                self.weight_list.push(1);
            }
        }
    }


    pub fn my_weighted_query(&mut self, features: &[i32]) -> (Vec<(Integer, Vec<i32>)>, Duration) {
        let start = Instant::now();
        let mut res: Vec<(Integer, Vec<i32>)> = Vec::new();
        res = self.my_weighted_dp(features);
        for idx in 0..res.len() {
            res[idx].1.sort_by_key(|&x| x.abs());
        }
        return (res, start.elapsed());
    }

    pub fn old_my_weighted_query(&mut self, features: &[i32]) -> (Vec<(Integer, Vec<i32>)>, Duration) {
        let start = Instant::now();
        let mut res: Vec<(Integer, Vec<i32>)> = Vec::new();
        res = self.old_my_weighted_dp(features);
        for idx in 0..res.len() {
            res[idx].1.sort_by_key(|&x| x.abs());
        }
        return (res, start.elapsed());
    }
    pub fn raw_execute_query(&mut self, features: &[i32]) -> Integer {
        match features.len() {
            0 => self.rc(),
            1 => self.card_of_feature_with_marker(features[0]),
            2..=20 => {
                self.operate_on_partial_config_marker(features, Ddnnf::calc_count_marked_node)
            }
            _ => self.operate_on_partial_config_default(features, Ddnnf::calc_count),
        }
    }
    pub fn execute_query(&mut self, features: &[i32]) -> Integer {
        match features.len() {
            0 => self.rc(),
            1 => self.card_of_feature_with_marker(features[0]),
            _ => self.clean_partial_config_counter(features).0,
        }
    }











    pub fn my_partial_config_counter(&mut self, features: &[i32]) -> Integer{
        if self.query_is_not_sat(features) {
            return Integer::ZERO;
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        if indexes.is_empty() {
            return self.rc();
        }

        self.mark_assumptions(&indexes);

        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    _ => {}
                }
            }
        }
        
        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    _ => {}
                }
            }
        }

        let mut vis: Vec<bool> = Vec::new();
        vis.resize(self.nodes.len(), false);
        vis[self.nodes.len() - 1] = true;
        // println!("{}",self.nodes.len() -1);
        for index in (0..self.nodes.len()).rev() {
            if !vis[index] || self.nodes[index].is_zero {
                continue;
            }
            match &self.nodes[index].ntype {
                And { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                Or { children } => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }
                }
                _ => {}
            }
        }
        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
            }
            self.md.clear();
            return Integer::ZERO;
        }
        // println!("self.md.len = {}",self.md.len());
        
        for idx in 0..self.md.len() {
            if self.nodes[self.md[idx]].is_zero == true {
                continue;
            }
            // self.node_count += 1;
            let i = self.md[idx];
            match &self.nodes[i].ntype {
                And { children } => {
                    let marked_children = children
                        .iter()
                        .filter(|&&child| self.nodes[child].marker)
                        .collect::<Vec<&usize>>();
                    self.nodes[i].temp = if marked_children.len() <= children.len() / 2 {
                        marked_children
                            .iter()
                            .fold(self.nodes[i].count.clone(), |mut acc, &&index| {
                                let node = &self.nodes[index];
                                if node.count != 0 {
                                    acc /= &node.count;
                                }
                                acc *= &node.temp;
                                // self.edge_count += 1;
                                acc
                            })
                    } else {
                        Integer::product(children.iter().map(|&index| {
                            let node = &self.nodes[index];
                            // self.edge_count += 1;
                            if node.marker {
                                &node.temp
                            } else {
                                &node.count
                            }
                        }))
                        .complete()
                    }
                }
                Or { children } => {
                    self.nodes[i].temp = Integer::sum(children.iter().map(|&index| {
                        let node = &self.nodes[index];
                        // self.edge_count += 1;
                        if node.marker {
                            &node.temp
                        } else {
                            &node.count
                        }
                    }))
                    .complete()
                }
                False => self.nodes[i].temp.assign(0),
                _ => self.nodes[i].temp.assign(1), // True and Literal
            }
        }
        
        // reset everything
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
        }
        self.md.clear();
        // println!("The node_count is:{}",self.node_count);
        // println!("The edge_count is:{}",self.edge_count);
        // println!();
        // println!("solution_num: {}",self.rt());
        return self.rt();
    }

}
