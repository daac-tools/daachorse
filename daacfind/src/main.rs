use std::fs::File;
use std::io::{prelude::*, stdin, BufReader};
use std::path::PathBuf;
use std::str::FromStr;

use daachorse::DoubleArrayAhoCorasick;
use structopt::StructOpt;
use termcolor::{Color, ColorChoice, ColorSpec, StandardStream, WriteColor};

#[derive(Clone, Copy, Debug)]
enum ArgColor {
    Never,
    Always,
    Auto,
}

impl FromStr for ArgColor {
    type Err = &'static str;
    fn from_str(color: &str) -> Result<Self, Self::Err> {
        match color {
            "never" => Ok(Self::Never),
            "always" => Ok(Self::Always),
            "auto" => Ok(Self::Auto),
            _ => Err("Could not parse a color"),
        }
    }
}

#[derive(StructOpt, Debug)]
#[structopt(name = "daacfind", about = "A program to find patterns in files.")]
struct Opt {
    /// Match patterns separated with new lines.
    #[structopt(short)]
    patterns: Option<String>,

    /// A filename containing patterns.
    #[structopt(short = "f")]
    pattern_file: Option<String>,

    /// Suppresses printing filenames.
    #[structopt(short = "h", long)]
    no_filename: bool,

    /// Prints line numbers.
    #[structopt(short = "n", long)]
    line_number: bool,

    /// Highlights the matching texts. [never, always, auto]
    #[structopt(long, default_value = "never")]
    color: ArgColor,

    /// File paths.
    #[structopt(name = "FILE")]
    files: Vec<PathBuf>,
}

/// Finds patterns using the given PMA and prints lines to the given `stream`.
/// When no pattern is found, this function does not print any string.
fn find_and_output(
    pma: &DoubleArrayAhoCorasick,
    line: &str,
    filename: Option<&str>,
    line_no: Option<usize>,
    color: ArgColor,
    stream: &mut StandardStream,
) -> Result<(), std::io::Error> {
    match color {
        ArgColor::Never => {
            if pma.find_iter(line).next().is_some() {
                if let Some(filename) = filename {
                    write!(stream, "{}:", filename)?;
                }
                if let Some(line_no) = line_no {
                    write!(stream, "{}:", line_no)?;
                }
                writeln!(stream, "{}", line)?;
            }
        }
        ArgColor::Always | ArgColor::Auto => {
            let mut color_counts = vec![0isize; line.len() + 1];
            let mut matched = false;
            for m in pma.find_overlapping_no_suffix_iter(line) {
                matched = true;
                color_counts[m.start()] += 1;
                color_counts[m.end()] -= 1;
            }
            if matched {
                if let Some(filename) = filename {
                    write!(stream, "{}:", filename)?;
                }
                if let Some(line_no) = line_no {
                    write!(stream, "{}:", line_no)?;
                }
                let mut depth = 0;
                let mut prev_pos = 0;
                for (pos, c) in color_counts.into_iter().enumerate() {
                    let new_depth = depth + c;
                    if depth == 0 && new_depth != 0 {
                        stream.reset()?;
                        write!(stream, "{}", &line[prev_pos..pos])?;
                        prev_pos = pos;
                    } else if depth != 0 && new_depth == 0 {
                        stream.set_color(ColorSpec::new().set_fg(Some(Color::Red)))?;
                        write!(stream, "{}", &line[prev_pos..pos])?;
                        prev_pos = pos;
                    }
                    depth = new_depth;
                }
                stream.reset()?;
                writeln!(stream, "{}", &line[prev_pos..])?;
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let opt = Opt::from_args();

    // Builds a PMA from given patterns.
    let mut patterns = vec![];
    if let Some(filename) = opt.pattern_file {
        let buf = BufReader::new(File::open(filename)?);
        for line in buf.lines() {
            let line = line?;
            if !line.is_empty() {
                patterns.push(line);
            }
        }
    }
    if let Some(pats_string) = opt.patterns {
        for pattern in pats_string.split('\n') {
            if !pattern.is_empty() {
                patterns.push(pattern.to_string());
            }
        }
    }
    let pma = DoubleArrayAhoCorasick::new(patterns)?;

    // Initialize the stream of termcolor.
    let mut stdout = match opt.color {
        ArgColor::Never => StandardStream::stdout(ColorChoice::Never),
        ArgColor::Always => StandardStream::stdout(ColorChoice::Always),
        ArgColor::Auto => StandardStream::stdout(ColorChoice::Auto),
    };

    // For the standard input.
    if opt.files.is_empty() {
        for (i, line) in stdin().lock().lines().enumerate() {
            let line_number = if opt.line_number { Some(i) } else { None };
            find_and_output(&pma, &line?, None, line_number, opt.color, &mut stdout)?;
        }
    }

    // For the given files.
    for filename in &opt.files {
        match File::open(filename) {
            Ok(file) => {
                let buf = BufReader::new(file);
                let filename = filename.to_str().and_then(|filename| {
                    if opt.no_filename {
                        None
                    } else {
                        Some(filename)
                    }
                });
                for (i, line) in buf.lines().enumerate() {
                    let line_number = if opt.line_number { Some(i) } else { None };
                    let line = match line {
                        Ok(line) => line,
                        Err(err) => {
                            if let Some(filename) = filename {
                                eprintln!("{}: {:?}", filename, err);
                            } else {
                                eprintln!("{:?}", err);
                            }
                            break;
                        }
                    };
                    find_and_output(&pma, &line, filename, line_number, opt.color, &mut stdout)?;
                }
            }
            Err(err) => {
                if let Some(filename) = filename.to_str() {
                    eprintln!("{}: {:?}", filename, err);
                } else {
                    eprintln!("{:?}", err);
                }
            }
        }
    }

    Ok(())
}
