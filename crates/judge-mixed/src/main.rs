fn main() -> std::process::ExitCode {
    use std::io::Write;
    let mut args = std::env::args_os().skip(1);
    let operation = args.next();
    let operation = operation.as_deref().and_then(std::ffi::OsStr::to_str);
    if let Some(command @ ("classify-v1" | "document-paths-v1")) = operation {
        if args.next().is_some() {
            eprintln!("E_USAGE: {command} reads one JSON object from stdin");
            return 2.into();
        }
        let input = std::io::stdin().lock();
        let result = match command {
            "document-paths-v1" => chrono_judge_mixed::document_paths(input),
            _ => chrono_judge_mixed::classify_query(input),
        }
        .and_then(|value| {
            let mut out = std::io::stdout().lock();
            serde_json::to_writer(&mut out, &value).map_err(|e| e.to_string())?;
            out.flush().map_err(|e| e.to_string())
        });
        return match result {
            Ok(()) => std::process::ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("{error}");
                2.into()
            }
        };
    }
    std::process::ExitCode::from(chrono_harness::wire::judge_main(
        "chrono-judge-mixed",
        env!("CARGO_PKG_VERSION"),
        chrono_judge_mixed::judge,
    ))
}
