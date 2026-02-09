# FastFMC: An Optimized Reuse-DNNF-Based Method for Efficient Feature Model Counting

## How to Obtain FastFMC
The directory `FastFMC/` contains the FastFMC source code and a Python script `run.py` for users to run FastFMC in an end-to-end manner.

### Prerequisites
Ensure the following tools are available in the `FastFMC/tools/` directory: [`coprocessor`](https://github.com/nmanthey/riss-solver) and [`d4v2`](https://github.com/crillab/d4v2).

### FastFMC Requirements
- [Rust](https://rust-lang.org)
- [Boost](https://boost.org)
- [GMP](https://gmplib.org)
- [Mt-KaHyPar](https://github.com/kahypar/mt-kahypar)
- GCC or Clang

### Instructions for Building FastFMC

```bash
cd FastFMC/FastFMC
cargo build --release --bin FastFMC
```
The executable binary file FastFMC will be generated in the path: `FastFMC/FastFMC/target/release/`

### Python Script Usage
The usage of run.py is as follows.
```bash
cd FastFMC
python run.py [CNF_file] <optional_parameters>
```

### Core Parameters

| Argument | Type | Required | Description |
|----------|------|----------|-------------|
| `cnf_file` | string | Yes | Input CNF file path |
| `config_file` | string | No | Configuration file path (optional) |
| `--output-dir` | string | No | Output directory (default: current directory) |
| `--mu` | integer | No | The value of μ (default: 10) |

### Optional Flags
| Flag |  Description |
|----------|-------------|
| `--not-use-lpe` | Disable local pattern elimination |
| `--not-use-bhm` | Disable biclique heuristic merging |
| `--not-use-znp` | Disable zero-node pruning |

### Input File Formats

#### CNF File Format
The input CNF file must be in standard DIMACS format:

```
p cnf <variable_count> <clause_count>
1 2 0
-1 3 0
-2 -3 0
1 -2 3 0
```

#### Configuration File Format (Optional)
When using a config file, each line represents a query:

```
1 -2 3
-4 5
-1 2
```



### Example1

Here's the first example of running the script with a CNF file and configuration file:

```bash
python run.py example/example.cnf example/example.config --output-dir . --mu 100 --not-use-lpe --not-use-bhm --not-use-znp
```

```
Executing: coprocessor preprocessing
Command: ./tools/coprocessor -enabled_cp3 -up -subsimp -no-bve -no-bce -no-dense -dimacs=./reduced_example.cnf example/example.cnf
✓ coprocessor preprocessing completed
============================================================
Executing: d4v2 compilation
Command: ./tools/d4v2 -i ./reduced_example.cnf -m ddnnf-compiler --dump-ddnnf ./example.nnf
✓ d4v2 compilation completed
============================================================
Extracting variable count from example/example.cnf...
✓ Found variable count: 1272
Executing: FastFMC model counting
Command: ./FastFMC/target/release/FastFMC ./example.nnf -t 1272 --n 100 --not-use-lpe --not-use-bhm --not-use-znp -q example/example.config ./example
✓ FastFMC model counting completed

FastFMC output:
raw smooth time = 1.999147416s
Ddnnf overall count: 98826262955116540654594658579507080173060213668622411355372612317123327888583768001824579847667155986221756840403183315918800


Computed values of all queries in example/example.config and the results are saved in ./example-queries.csv
It took 5.482305711 seconds. That is an average of 0.021929222844 seconds per query

============================================================
✓ All steps completed successfully!
Query results file: ./example-queries.csv
============================================================
```

### Example2

Here's the second example of running the script with a CNF file and configuration file with default configuration:

```bash
python3 run.py example/example.cnf example/example.config --output-dir .
```

```
Executing: coprocessor preprocessing
Command: ./tools/coprocessor -enabled_cp3 -up -subsimp -no-bve -no-bce -no-dense -dimacs=./reduced_example.cnf example/example.cnf
✓ coprocessor preprocessing completed
============================================================
Executing: d4v2 compilation
Command: ./tools/d4v2 -i ./reduced_example.cnf -m ddnnf-compiler --dump-ddnnf ./example.nnf
✓ d4v2 compilation completed
============================================================
Extracting variable count from example/example.cnf...
✓ Found variable count: 1272
Executing: FastFMC model counting
Command: ./FastFMC/target/release/FastFMC ./example.nnf -t 1272 --n 10 -q example/example.config ./example
✓ FastFMC model counting completed

FastFMC output:
smooth time = 250.649275ms
Ddnnf overall count: 98826262955116540654594658579507080173060213668622411355372612317123327888583768001824579847667155986221756840403183315918800


Computed values of all queries in example/example.config and the results are saved in ./example-queries.csv
It took 1.101957073 seconds. That is an average of 0.004407828292 seconds per query

============================================================
✓ All steps completed successfully!
Query results file: ./example-queries.csv
============================================================
```


## Benchmarks
The `benchmarks/` directory contains two subdirectories with testing benchmarks:

- All Benchmarks:

    The `benchmarks/all/` directory contains all 1856 benchmarks that can be used as input for testing. Detailed information about these benchmarks is provided in the file [benchmark_information_all.csv](benchmarks/benchmark_information_all.csv).

- Large-Scale Benchmarks:
  
    The `benchmarks/large-scale/` directory contains 665 large-scale benchmarks with at least 1000 features. Detailed information about these benchmarks is provided in the file [benchmark_information_large_scale.csv](benchmarks/benchmark_information_large_scale.csv).


## Experimental Results
The directory `experimental_results/` contains 10 folders and 1 pdf for presenting the results of all experiments. 

+ [ablation](experimental_results/ablation/): Results of FastFMC's alternative versions on all testing benchmarks. Contains ablation study results for LPE (Local Pattern Elimination), BHM (Biclique Heuristic Merging), ZNP (Zero-Node Pruning), and Simp (Simplification) components.
+ [countAntom](experimental_results/countAntom/): Results of countAntom tool on all testing benchmarks.
+ [d4-query](experimental_results/d4-query/): Results of d4-query tool on all testing benchmarks.
+ [ddnnife](experimental_results/ddnnife/): Results of ddnnife tool on all testing benchmarks.
+ [FastFMC](experimental_results/FastFMC/): Results of FastFMC on all testing benchmarks.
+ [Ganak](experimental_results/Ganak/): Results of Ganak tool on all testing benchmarks.
+ [hyper_parameter](experimental_results/hyper_parameter/): Results of FastFMC with different μ settings (μ=1, μ=10, μ=50, μ=100) on all testing benchmarks.
+ [query-ddnnf](experimental_results/query-ddnnf/): Results of query-ddnnf tool on all testing benchmarks.
+ [SharpSAT](experimental_results/SharpSAT/): Results of SharpSAT tool on all testing benchmarks.
+ [size](experimental_results/size/): Results of d-DNNF size comparison for FastFMC and its alternative versions on all testing benchmarks.
+ [evaluation_on_real_world_software_product_line_benchmarks](experimental_results/evaluation_on_real_world_software_product_line_benchmarks.pdf): This appendix presents the experimental results of FastFMC and its competitors on the real-world software product line benchmarks, covering both the offline and online phases.
