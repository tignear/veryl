#!/bin/bash
set -e

echo "=== Verilator Benchmark (Google Benchmark) ==="
if [ -f "./obj_dir/Vverilator_bench_Top" ]; then
    ./obj_dir/Vverilator_bench_Top
else
    echo "Error: Verilator binary not found."
    exit 1
fi

echo ""

echo "=== veryl-simulator Benchmark (Criterion) ==="
cd /app
# Run only the specific benchmark in the simulator crate
# Use -q to suppress cargo output, and -A warnings to hide any remaining lint noise
RUSTFLAGS="-A warnings" cargo bench -q -p veryl-simulator --profile fast-bench --bench simulation --offline -- --quiet
