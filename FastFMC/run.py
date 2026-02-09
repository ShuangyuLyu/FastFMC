import os
import sys
import subprocess
import re
import argparse
from pathlib import Path


def run_command(cmd, description, capture_output=True):
    """Execute command and handle errors"""
    print(f"Executing: {description}")
    print(f"Command: {cmd}")
    
    try:
        if capture_output:
            result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
            if result.returncode == 0 or result.returncode == 10:
                print(f"✓ {description} completed")
                return result.stdout
            else:
                print(f"✗ {description} failed with return code: {result.returncode}")
                if result.stderr:
                    print(f"Error output: {result.stderr}")
        else:
            result = subprocess.run(cmd, shell=True)
            if result.returncode == 0:
                print(f"✓ {description} completed")
                return None
            else:
                print(f"✗ {description} failed with return code: {result.returncode}")
    except Exception as e:
        print(f"✗ {description} failed with exception: {e}")


def extract_variable_count(cnf_file):
    """Extract variable count from CNF file"""
    print(f"Extracting variable count from {cnf_file}...")
    
    try:
        with open(cnf_file, 'r', encoding='utf-8') as f:
            for line in f:
                line = line.strip()
                if line.startswith('p cnf'):
                    parts = line.split()
                    if len(parts) >= 4:
                        variable_count = int(parts[2])
                        print(f"✓ Found variable count: {variable_count}")
                        return variable_count
        
        print("✗ CNF file header not found")
        sys.exit(1)
    except FileNotFoundError:
        print(f"✗ File {cnf_file} does not exist")
        sys.exit(1)
    except Exception as e:
        print(f"✗ Error reading file: {e}")
        sys.exit(1)


def main():
    parser = argparse.ArgumentParser(description='FastFMC')
    parser.add_argument('cnf_file', help='Input CNF file path')
    parser.add_argument('config_file', nargs='?', help='Configuration file path (optional)')
    parser.add_argument('--output-dir', default='.', help='Output directory (default: current directory)')
    parser.add_argument('--mu', type=int, default=10, help='The value of 𝜇 (default: 10)')
    parser.add_argument('--not-use-lpe', action='store_true', help='Disable local pattern elimination')
    parser.add_argument('--not-use-bhm', action='store_true', help='Disable biclique heuristic merging')
    parser.add_argument('--not-use-znp', action='store_true', help='Disable zero-node pruning')
    
    
    args = parser.parse_args()
    
    # Check if input files exist
    if not os.path.exists(args.cnf_file):
        print(f"✗ CNF file does not exist: {args.cnf_file}")
        sys.exit(1)
    
    # Check config file if provided
    if args.config_file and not os.path.exists(args.config_file):
        print(f"✗ Configuration file does not exist: {args.config_file}")
        sys.exit(1)
    
    # Set output file paths
    cnf_basename = Path(args.cnf_file).stem
    reduced_cnf = os.path.join(args.output_dir, f"reduced_{cnf_basename}.cnf")
    nnf_file = os.path.join(args.output_dir, f"{cnf_basename}.nnf")
    query_res_file = os.path.join(args.output_dir, f"{cnf_basename}")

    # Step 0: Preprocess the input cnf file
    cmd0 = f'./tools/coprocessor -enabled_cp3 -up -subsimp -no-bve -no-bce -no-dense -dimacs={reduced_cnf} {args.cnf_file}'
    run_command(cmd0, "coprocessor preprocessing")
    print("=" * 60)


    # Step 1: Convert CNF to Decision-DNNF using d4v2
    cmd1 = f'./tools/d4v2 -i {reduced_cnf} -m ddnnf-compiler --dump-ddnnf {nnf_file}'
    run_command(cmd1, "d4v2 compilation")
    print("=" * 60)
    
    # Step 2: Extract variable count
    variable_count = extract_variable_count(args.cnf_file)
    
    # Step 3: Model counting using FastFMC
    cmd3 = f'./FastFMC/target/release/FastFMC {nnf_file} -t {variable_count}'
    
    if args.mu:
        cmd3 += f' --n {args.mu}'
    if args.not_use_lpe:
        cmd3 += f' --not-use-lpe'
    if args.not_use_bhm:
        cmd3 += f' --not-use-bhm'
    if args.not_use_znp:
        cmd3 += f' --not-use-znp'

    if args.config_file:
        cmd3 += f' -q {args.config_file}'
        if args.output_dir:
            cmd3 += f' {query_res_file}'

    output = run_command(cmd3, "FastFMC model counting")
    if output:
        print("\nFastFMC output:")
        print(output)

    if os.path.exists(reduced_cnf):
        os.remove(reduced_cnf)
    if os.path.exists(nnf_file):
        os.remove(nnf_file)

    print("=" * 60)
    print("✓ All steps completed successfully!")
    if args.config_file:
        print(f"Query results file: {query_res_file}-queries.csv")
    print("=" * 60)


if __name__ == "__main__":
    main() 