//! bitbit provides functions to read and write streams one bit at a time.
//!
//! # Reading
//!
//! ```rust,ignore
//! let r = try!(File::open("somefile"));
//! let mut br = BitReader::new(r);
//!
//! let is_one = try!(br.read_bit());
//!
//! let byte = try!(br.read_byte());
//! ```

pub mod reader;
pub use reader::BitReader;
