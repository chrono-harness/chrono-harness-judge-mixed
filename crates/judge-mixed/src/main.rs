#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::DataCommand;
#[cfg(not(verus_keep_ghost))]
use chrono_judge_mixed::DataCommand;
#[cfg(not(verus_keep_ghost))]
use vstd::prelude::verus;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

verus! {
/// Give the selected data command the original input and return its exact result.
pub fn run_data<I,T,D,P,R,C>(command: DataCommand, input:I, documents:D, plan:P, report:R, classify:C) -> (out:T)
    where D:FnOnce(I)->T, P:FnOnce(I)->T, R:FnOnce(I)->T, C:FnOnce(I)->T,
    requires match command {
        DataCommand::Documents=>documents.requires((input,)), DataCommand::Plan=>plan.requires((input,)),
        DataCommand::Report=>report.requires((input,)), DataCommand::Classify=>classify.requires((input,)),
    },
    ensures match command {
        DataCommand::Documents=>documents.ensures((input,),out), DataCommand::Plan=>plan.ensures((input,),out),
        DataCommand::Report=>report.ensures((input,),out), DataCommand::Classify=>classify.ensures((input,),out),
    },
{
    match command {
        DataCommand::Documents => documents(input),
        DataCommand::Plan => plan(input),
        DataCommand::Report => report(input),
        DataCommand::Classify => classify(input),
    }
}
}

#[cfg(not(verus_keep_ghost))]
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
            let command = match selected {
                Ok(command) => command,
                Err(label) => {
                    eprintln!("E_USAGE: {label} reads one JSON object from stdin");
                    return 2.into();
                }
            };
            let input = std::io::stdin().lock();
            let result = run_data(
                command,
                input,
                chrono_judge_mixed::document_paths,
                chrono_judge_mixed::native::plan,
                chrono_judge_mixed::native::report,
                chrono_judge_mixed::classify_query,
            );
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
