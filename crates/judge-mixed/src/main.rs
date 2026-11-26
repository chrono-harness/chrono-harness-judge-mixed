fn main() -> std::process::ExitCode {
    use std::io::Write;
    use std::os::unix::process::CommandExt;
    use std::process::Command;
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    let mut args = arguments.iter();
    let name = args.next().and_then(|arg| arg.to_str());
    let route = chrono_judge_mixed::route(name, args.len());
    let prepare = match route {
        chrono_judge_mixed::Route::Version => {
            println!("chrono-judge-mixed {}", env!("CARGO_PKG_VERSION"));
            return std::process::ExitCode::SUCCESS;
        }
        chrono_judge_mixed::Route::Prepare => true,
        chrono_judge_mixed::Route::Pipeline => false,
        chrono_judge_mixed::Route::Data(selected) => {
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
    };
    let (status, program, error) =
        chrono_judge_mixed::delegation_failure(std::env::current_exe, |executable| {
            let request = chrono_judge_mixed::invocation(
                prepare,
                &executable,
                env!("CARGO_PKG_VERSION"),
                &arguments,
            );
            let mut command = Command::new(request.program);
            command
                .args(request.prefix.iter().map(|arg| match arg {
                    chrono_judge_mixed::Argument::Text(text) => std::ffi::OsStr::new(text),
                    chrono_judge_mixed::Argument::Executable(path) => path.as_os_str(),
                }))
                .args(request.forwarded);
            (request.program, command.exec())
        });
    eprintln!("{program}: {error}");
    status.into()
}
