use signal_hook::SigId;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

pub struct Interruptor {
    signal: SigId,
    flag: Arc<AtomicBool>,
}

impl Interruptor {
    pub fn register() -> std::io::Result<Self> {
        let flag = Arc::new(AtomicBool::new(false));

        Ok(Self {
            signal: signal_hook::flag::register(signal_hook::SIGINT, flag.clone())?,
            flag,
        })
    }

    pub fn check(&self) -> bool {
        self.flag.swap(false, Ordering::SeqCst)
    }
}

impl Drop for Interruptor {
    fn drop(&mut self) {
        signal_hook::unregister(self.signal);
    }
}
