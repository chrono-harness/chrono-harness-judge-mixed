fn main() -> std::process::ExitCode {
    use std::io::Write;
    use std::os::unix::process::CommandExt;
    use std::process::Command;
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    if arguments == [std::ffi::OsStr::new("--version")] {
        println!("chrono-judge-mixed {}", env!("CARGO_PKG_VERSION"));
        return std::process::ExitCode::SUCCESS;
    }
    let mut args = arguments.iter();
    let operation = args.next();
    let operation = operation.and_then(|arg| arg.to_str());
    if let Some(selected) =
        operation.and_then(|name| chrono_judge_mixed::data_command(name, args.len()))
    {
        use chrono_judge_mixed::DataCommand;
        let command = match selected {
            Ok(command) => command,
            Err(label) => {
                eprintln!("E_USAGE: {label} reads one JSON object from stdin");
                return 2.into();
            }
        };
        let input = std::io::stdin().lock();
        let result = match command {
            DataCommand::Documents => chrono_judge_mixed::document_paths(input),
            DataCommand::Plan => chrono_judge_mixed::native::plan(input),
            DataCommand::Report => chrono_judge_mixed::native::report(input),
            DataCommand::Classify => chrono_judge_mixed::classify_query(input),
        };
        let written = chrono_judge_mixed::on_success(result, |value| {
            let mut out = std::io::stdout().lock();
            serde_json::to_writer(&mut out, &value).map_err(|e| e.to_string())?;
            Ok(out)
        });
        let flushed = chrono_judge_mixed::on_success(written, |mut out| {
            out.flush().map_err(|e| e.to_string())
        });
        let (status, error) = chrono_judge_mixed::data_exit(flushed);
        if let Some(error) = error {
            eprintln!("{error}");
        }
        return status.into();
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
