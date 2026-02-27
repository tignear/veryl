# veryl-simulator

`veryl-simulator` is a simulation backend for [Veryl](https://github.com/veryl-lang/veryl).
It compiles Veryl code into a Cranelift IR (JIT) representation and executes it.

## Installation

Add `veryl-simulator` to your `Cargo.toml`:

```toml
[dependencies]
veryl-simulator = "0.17.2"
```

## Usage

### Logic Simulation (Event-driven)

The `Simulator` struct is the main entry point for manual, event-driven simulation. It specializes in direct control over inputs and clock edges.

```rust
use veryl_simulator::Simulator;

let code = r#"
module Top (
    clk: input clock,
    rst: input reset,
    a: input logic<32>,
    b: output logic<32>
) {
    always_ff (clk, rst) {
        if_reset { b = 0; }
        else     { b = a; }
    }
}
"#;

// 1. Initialize Simulator
let mut sim = Simulator::new(code, "Top");

// 2. Get port/event references
let clk = sim.event("clk");
let rst = sim.port("rst");
let a = sim.port("a");
let b = sim.port("b");

// 3. Drive inputs and trigger events
sim.modify(|io| {
    io.set(&rst, 1u8);
    io.set(&a, 100u32);
}).unwrap();
sim.tick(clk).unwrap(); // Trigger clock edge

sim.modify(|io| io.set(&rst, 0u8)).unwrap();
sim.tick(clk).unwrap();

// 4. Inspect results
assert_eq!(sim.get(&b), 100u32.into());
```

### Timed Simulation (Managed Scheduling)

For scenarios requiring periodic clocks and automated progress, use the `Simulation` wrapper.

```rust
use veryl_simulator::SimulatorBuilder;

let mut sim = SimulatorBuilder::new(code, "Top")
    .build_simulation()
    .unwrap();

// Add a clock with period 10 and initial delay 0
sim.add_clock("clk", 10, 0);

// Run until time 100
sim.run_until(100).unwrap();

println!("Current simulation time: {}", sim.time());
```

### High-Performance Signal Access

For performance-critical code sections, use `SignalRef` handles instead of `AbsoluteAddr`. This bypasses `HashMap` lookups, providing zero-overhead memory access.

```rust
// 1. Resolve a signal handle once (e.g., during initialization)
let a_ref = sim.signal("a");

// 2. Use the handle for high-performance access
let val = sim.get_signal(a_ref);

sim.modify(|io| {
    io.set_signal(a_ref, 42u32);
}).unwrap();
```

## API

### `SimulatorBuilder`

A fluent builder for configuring your simulation environment.

- `new(code: &str, top: &str) -> Self`: Start building.
- `build(self) -> Result<Simulator, ...>`: Returns the core logic engine.
- `build_simulation(self) -> Result<Simulation, ...>`: Returns the timed wrapper.
- `optimize(self, enable: bool) -> Self`: Toggle SIRT optimizations.

### `Simulator` (Logic Engine)

- `event(name: &str) -> EventRef`: Get an event (clock) reference.
- `port(name: &str) -> AbsoluteAddr`: Get a port address.
- `signal(name: &str) -> SignalRef`: Get a high-performance signal handle.
- `modify<F>(&mut self, f: F) -> Result<...>`: Apply input changes.
- `tick(&mut self, event: EventRef) -> Result<...>`: Manually trigger an event.
- `get(&self, addr: &AbsoluteAddr) -> BigUint`: Read a signal value.
- `get_signal(&self, signal: SignalRef) -> BigUint`: High-performance read.
- `dump(&mut self, timestamp: u64)`: Write current state to VCD.

### `Simulation` (Timed Wrapper)

- `add_clock(name: &str, period: u64, initial_delay: u64)`: Define a periodic clock with starting offset.
- `schedule(name: &str, time: u64, value: u64) -> Result<(), ...>`: Schedule a one-shot event at $t$.
- `run_until(&mut self, target_time: u64) -> Result<...>`: Advance time and process events.
- `time(&self) -> u64`: Get current simulation time.
- `simulator(&self) -> &Simulator`: Access the underlying engine.
- `simulator_mut(&mut self) -> &mut Simulator`: Mutably access the underlying engine.
