use crate::{
    EventRef, IOContext, RuntimeErrorCode,
    backend::JitBackend,
    ir::{Program, SignalRef},
};
use malachite_bigint::BigUint;

mod builder;
mod error;

pub use builder::{SimulatorBuilder, SimulatorOptions};
pub use error::SimulatorError;

/// The core logic evaluation engine.
///
/// Encapsulates the JIT-compiled backend, the original SIR program,
/// and an optional VCD writer. Provides low-level, event-driven control.
pub struct Simulator {
    pub(crate) backend: JitBackend,
    pub(crate) program: Program,
    pub(crate) vcd_writer: Option<crate::vcd::VcdWriter>,
}

impl std::fmt::Debug for Simulator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Simulator").finish()
    }
}

impl Simulator {
    pub fn builder<'a>(code: &'a str, top: &'a str) -> SimulatorBuilder<'a> {
        SimulatorBuilder::new(code, top)
    }

    pub(crate) fn with_backend_and_program(backend: JitBackend, program: Program) -> Self {
        Self {
            backend,
            program,
            vcd_writer: None,
        }
    }

    /// Captures the current state of all signals and writes them to the VCD file.
    pub fn dump(&mut self, timestamp: u64) {
        if let Some(ref mut writer) = self.vcd_writer {
            let backend = &self.backend;
            writer
                .dump(timestamp, |addr| {
                    let signal = backend.resolve_signal(addr);
                    backend.get(signal)
                })
                .unwrap();
        }
    }

    /// Modifies internal state via a callback and re-stabilizes combinational logic.
    pub fn modify<F>(&mut self, f: F) -> Result<(), RuntimeErrorCode>
    where
        F: FnOnce(&mut IOContext),
    {
        let mut ctx = IOContext {
            backend: &mut self.backend,
        };
        f(&mut ctx);
        // Re-evaluate combinational logic to propagate the new state.
        self.backend.eval_comb()?;
        Ok(())
    }

    /// Manually triggers a clock or event to process sequential logic.
    pub fn tick(&mut self, event: EventRef) -> Result<(), RuntimeErrorCode> {
        self.backend.eval_ff_at(event)?;
        self.backend.eval_comb()?;
        Ok(())
    }

    /// Resolves a signal path into a performance-optimized [`SignalRef`].
    /// This handle allows for direct memory access without `HashMap` lookups.
    pub fn signal(&self, path: &str) -> SignalRef {
        let addr = self.program.get_addr(&[], &[path]);
        self.backend.resolve_signal(&addr)
    }

    /// Resolve a port name to an [`EventRef`] handle.
    pub fn event(&self, port: &str) -> EventRef {
        let addr = self.program.get_addr(&[], &[port]);
        self.backend.resolve_event(&addr)
    }

    /// Retrieves the current value of a variable using a pre-resolved [`SignalRef`] handle.
    pub fn get(&self, signal: SignalRef) -> BigUint {
        self.backend.get(signal)
    }

    /// Retrieves the current 4-state value (value, mask) of a variable using a [`SignalRef`] handle.
    pub fn get_four_state(&self, signal: SignalRef) -> (BigUint, BigUint) {
        self.backend.get_four_state(signal)
    }

    /// Directly execute combinational logic evaluation.
    pub fn eval_comb(&mut self) -> Result<(), RuntimeErrorCode> {
        self.backend.eval_comb()?;
        Ok(())
    }
}
