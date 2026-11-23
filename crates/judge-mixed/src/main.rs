fn main() -> std::process::ExitCode {
    use std::io::Write;
    use std::os::unix::process::CommandExt;
    use std::process::Command;
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    let mut args = arguments.iter();
    let operation = args.next();
    let operation = operation.and_then(|arg| arg.to_str());
    if let Some(
        command @ ("classify-v1" | "document-paths-v1" | "plan-classification-v1" | "report-v1"),
    ) = operation
    {
        if args.next().is_some() {
            eprintln!("E_USAGE: {command} reads one JSON object from stdin");
            return 2.into();
        }
        let input = std::io::stdin().lock();
        let result = match command {
            "document-paths-v1" => chrono_judge_mixed::document_paths(input),
            "plan-classification-v1" => chrono_judge_mixed::native::plan(input),
            "report-v1" => chrono_judge_mixed::native::report(input),
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
    let executable = match std::env::current_exe() {
        Ok(path) => path,
        Err(error) => {
            eprintln!("chrono-judge-mixed: {error}");
            return 2.into();
        }
    };
    let mut command = if operation == Some("prepare-classification-v1") && arguments.len() == 1 {
        let mut command = Command::new("chrono-judge-registration");
        command.arg("classification-inputs-v1").arg(&executable);
        command
    } else {
        let mut command = Command::new("chrono-harness");
        command
            .args([
                "judge-pipeline",
                "chrono-judge-mixed",
                env!("CARGO_PKG_VERSION"),
            ])
            .arg(&executable)
            .arg("prepare-classification-v1")
            .arg(&executable)
            .arg("report-v1")
            .args(arguments);
        command
    };
    let error = command.exec();
    eprintln!("{}: {error}", command.get_program().to_string_lossy());
    2.into()
}
