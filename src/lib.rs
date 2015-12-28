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
//!
//! # Writing
//!
//! ```rust,ignore
//! let w = try!(File::create("somefile"));
//! let mut bw = BitWriter::new(w);
//!
//! try!(br.write_bit(true));
//!
//! try!(br.write_byte(0x55));
//! ```

pub mod reader;
pub use reader::BitReader;

pub mod writer;
pub use writer::BitWriter;
