mod affine;
mod big;
mod derivation;
mod map;
mod normalizer;
mod prefix;
mod scalar;
mod transducer;

fn main() {
    extern "C" {
        fn tm_prepare_runtime();
    }
    unsafe { tm_prepare_runtime() };
    if let Err(error) = run() {
        eprintln!("tm-metal: {error}");
        std::process::exit(1);
    }
}
fn run() -> Result<(), String> {
    let mut engine = map::Engine::new()?;
    let mut b = engine.blank_seed();
    let mut next = big::Big::new();
    let mut returns = 0u64;
    let mut report = std::time::Instant::now();
    println!("Starting from blank: K(2,{})", b.text(10));
    loop {
        let step = engine.step(&b, &mut next);
        if let Some(c) = step.halt_c {
            println!(
                "Halt on return {}: H({c},1,0x{}) -> F/0",
                returns + 1,
                next.text(16)
            );
            return Ok(());
        }
        std::mem::swap(&mut b, &mut next);
        returns += 1;
        if report.elapsed().as_secs() >= 30 {
            println!("{returns} returns; B has {} bits", b.bits());
            report = std::time::Instant::now();
        }
    }
}
