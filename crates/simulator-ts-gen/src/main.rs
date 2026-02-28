use clap::Parser as ClapParser;
use miette::{IntoDiagnostic, Result, bail};
use std::fs;
use std::path::PathBuf;
use veryl_analyzer::{Analyzer, Context, attribute_table, ir::Ir, symbol_table};
use veryl_metadata::Metadata;
use veryl_parser::Parser;
use veryl_simulator_ts_gen::generate_all;

#[derive(ClapParser)]
#[command(name = "veryl-gen-ts", about = "Generate TypeScript bindings from Veryl sources")]
struct Cli {
    /// Output directory for generated .d.ts and .js files
    #[arg(long, default_value = "generated")]
    out_dir: PathBuf,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    // Find and load Veryl.toml
    let metadata_path =
        Metadata::search_from_current().into_diagnostic()?;
    let mut metadata = Metadata::load(&metadata_path).into_diagnostic()?;

    // Gather source files
    let paths = metadata.paths::<PathBuf>(&[], true, true).into_diagnostic()?;
    if paths.is_empty() {
        bail!("No Veryl source files found");
    }

    // Parse and analyze pass 1
    symbol_table::clear();
    attribute_table::clear();

    let analyzer = Analyzer::new(&metadata);
    let mut parsers = Vec::new();

    for path in &paths {
        let input = fs::read_to_string(&path.src).into_diagnostic()?;
        let parser = Parser::parse(&input, &path.src)?;

        let mut errors = analyzer.analyze_pass1(&path.prj, &parser.veryl);
        if !errors.is_empty() {
            for e in errors.drain(..) {
                eprintln!("{e}");
            }
            bail!("Errors in analysis pass 1");
        }

        parsers.push((path.clone(), parser));
    }

    let mut errors = Analyzer::analyze_post_pass1();
    if !errors.is_empty() {
        for e in errors.drain(..) {
            eprintln!("{e}");
        }
        bail!("Errors in post-pass 1 analysis");
    }

    // Analyze pass 2 with IR collection
    let mut analyzer_context = Context::default();
    let mut ir = Ir::default();

    let mut has_errors = false;
    for (path, parser) in &parsers {
        let errors =
            analyzer.analyze_pass2(&path.prj, &parser.veryl, &mut analyzer_context, Some(&mut ir));
        for e in &errors {
            eprintln!("Warning: {e}");
        }
        if !errors.is_empty() {
            has_errors = true;
        }
    }

    let errors = Analyzer::analyze_post_pass2();
    for e in &errors {
        eprintln!("Warning: {e}");
    }
    if !errors.is_empty() {
        has_errors = true;
    }

    if has_errors {
        eprintln!("Note: some analysis warnings occurred; generating bindings for supported modules");
    }

    // Generate TypeScript bindings
    let modules = generate_all(&ir);
    if modules.is_empty() {
        eprintln!("Warning: no modules found in IR");
        return Ok(());
    }

    // Write output files
    fs::create_dir_all(&cli.out_dir).into_diagnostic()?;

    for module in &modules {
        let dts_path = cli.out_dir.join(format!("{}.d.ts", module.module_name));
        let js_path = cli.out_dir.join(format!("{}.js", module.module_name));

        fs::write(&dts_path, &module.dts_content).into_diagnostic()?;
        fs::write(&js_path, &module.js_content).into_diagnostic()?;

        eprintln!(
            "Generated {}.d.ts and {}.js",
            module.module_name, module.module_name
        );
    }

    eprintln!(
        "Done: {} module(s) written to {}",
        modules.len(),
        cli.out_dir.display()
    );

    Ok(())
}
