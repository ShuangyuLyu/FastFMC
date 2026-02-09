use crate::{Ddnnf, NodeType::*};

impl Ddnnf {
    /// Computes if a node is satisfiable with the marking algorithm:
    /// For each feature of the query, we search for its complementary literal.
    /// Each complementary literal gets annoted similar to the marking algorithm for counting.
    /// For each node, we check whether the node can be satisfiable.
    ///      1) If that node has to be satisfiable, we stop
    ///      2) If that node is unsatisfiable we continue with its parents til we either
    ///          reach the root (declaring the whole query as unsatisfiable) or reach nodes that
    ///         are satisfiable.
    /// If any of those literal propagations reaches the root, the query is unsatisfiable.
    /// Vice versa the query is satisfiable.
    #[inline]
    pub fn sat(&mut self, features: &[i32]) -> bool {
        self.sat_propagate(features, &mut vec![false; self.nodes.len()], None)
    }

    /// Does the exact same as 'sat' with the difference of choosing the marking Vec by ourself.
    /// That allows reusing that vector and therefore enabeling an efficient method to do decision propogation.
    /// If wanted, one can supply an marking Vec<bool>, that can be reused in following method calls to propagate satisfiability.
    /// The root_index does not have to be the root of the DAG. Instead it can be any node. If 'None' is supplied we use the root of the DAG.
    #[inline]
    pub fn sat_propagate(
        &self,
        features: &[i32],
        mark: &mut Vec<bool>,
        root_index: Option<usize>,
    ) -> bool {
        let root_index = root_index.unwrap_or(self.nodes.len() - 1);

        if features.iter().any(|f| self.makes_query_unsat(f)) {
            return false;
        }

        for feature in features {
            if let Some(&index) = self.literals.get(&-feature) {
                self.propagate_mark(index, mark);
                // if the root is unsatisfiable after any of the literals in the query,
                // then the whole query must be unsatisfiable too.
                if mark[root_index] {
                    return false;
                }
            }
        }

        // the result is the marking of the root node
        !mark[root_index]
    }

    // marks a node and decides whether we have to continue the marking with its parent nodes
    #[inline]
    fn propagate_mark(&self, index: usize, mark: &mut Vec<bool>) {
        // if the node is already marked, we looked at its path and can stop
        if mark[index] {
            return;
        }

        if let Or { children } = &self.nodes[index].ntype {
            // An Or node is only unsatisfiable if all of its children are either marked
            // or have an count of zero (that handle False nodes).
            if !children
                .iter()
                .all(|&c| mark[c] || self.nodes[c].count == 0)
            {
                return;
            }
        }

        mark[index] = true;
        // check the marking for all parents
        self.nodes[index]
            .parents
            .iter()
            .for_each(|&p| self.propagate_mark(p, mark))
    }
}

/// Creates a new marking vector that can wrapped be used as 'mark' parameter for 'sat_propagate'.
#[inline]
pub fn new_sat_mark_state(number_of_nodes: usize) -> Vec<bool> {
    vec![false; number_of_nodes]
}

