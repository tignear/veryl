FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    verilator \
    curl \
    git \
    pkg-config \
    libssl-dev \
    libbenchmark-dev \
    && rm -rf /var/lib/apt/lists/*

# Install Rust
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

WORKDIR /app

# Copy the entire workspace
COPY . .

# Pre-build the simulator and benchmarks (O3, No LTO)
RUN RUSTFLAGS="-A warnings" cargo bench -p veryl-simulator --profile fast-bench --bench simulation --no-run

# Set up Verilator bench
WORKDIR /app/support/verilator_bench

# Generate SystemVerilog from Veryl source
RUN cargo run -r -p veryl -- build

# Build Verilator bench with Google Benchmark and O3 optimization
RUN verilator -O3 --cc target/Top.sv --exe sim_main.cpp --top-module verilator_bench_Top -CFLAGS "-O3" -LDFLAGS "-lbenchmark -lpthread"
RUN make -C obj_dir -f Vverilator_bench_Top.mk

# Script to run both
RUN chmod +x run_bench.sh

CMD ["./run_bench.sh"]
