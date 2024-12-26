#![allow(non_snake_case)]

mod app;
mod opcodes_dictionary;

use rustyline::{error::ReadlineError, DefaultEditor};
use std::sync::atomic::Ordering;
use crate::app::LimboCliApp;

#[allow(clippy::arc_with_non_send_sync)]
fn main() -> anyhow::Result<()> {
    env_logger::init();

    let mut limboCliApp = LimboCliApp::new()?;

    let mut rustyLineEditor = DefaultEditor::new()?;

    let homeDirPath = dirs::home_dir().expect("Could not determine home directory");

    let historyFile = homeDirPath.join(".limbo_history");
    if historyFile.exists() {
        rustyLineEditor.load_history(historyFile.as_path())?;
    }

    loop {
        match  rustyLineEditor.readline(&limboCliApp.prompt) {
            Ok(line) => match limboCliApp.processInputLine(line.trim(), &mut rustyLineEditor) {
                Ok(_) => {}
                Err(e) => eprintln!("{}", e),
            },
            Err(ReadlineError::Interrupted) => {
                // At prompt, increment interrupt count
                if limboCliApp.interrupt_count.fetch_add(1, Ordering::SeqCst) >= 1 {
                    eprintln!("Interrupted. Exiting...");
                    let _ = limboCliApp.close_conn();
                    break;
                }

                println!("Use .quit to exit or press Ctrl-C again to force quit.");
                limboCliApp.reset_input();

                continue;
            }
            Err(ReadlineError::Eof) => {
                let _ = limboCliApp.close_conn();
                break;
            }
            Err(err) => {
                let _ = limboCliApp.close_conn();
                anyhow::bail!(err)
            }
        }
    }

    rustyLineEditor.save_history(historyFile.as_path())?;

    Ok(())
}
