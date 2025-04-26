//! Standard library macros

/// Prints to the standard output.
///
/// Equivalent to the [`println!`] macro except that a newline is not printed at
/// the end of the message.
///
/// [`println!`]: crate::println
#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {
        $crate::io::__print_impl(format_args!($($arg)*));
    }
}

/// Prints to the standard output, with a newline.
#[macro_export]
macro_rules! println {
    () => { $crate::print!("\u{1B}[34m\n\u{1B}[m") };
    ($($arg:tt)*) => {
        // "\u{1B}[34m" sets text color to blue (ANSI escape code),
        // "{}" is for formatted content,
        // "\n" for newline,
        // "\u{1B}[m" resets color to default.
        $crate::io::__print_impl(format_args!("\u{1B}[34m{}\n\u{1B}[m", format_args!($($arg)*)));
    }
}
