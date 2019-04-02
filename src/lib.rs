//! bitbit provides functions to read and write streams one bit at a time.
//!
//! # Reading
//!
//! ```rust, ignore
//! let r = File::open("somefile")?;
//! let mut br = BitReader::new(r);
//!
//! let is_one = br.read_bit()?;
//!
//! let byte = br.read_byte()?;
//!
//! let num = br.read_bits(5)?;
//! ```
//! Using a buffered reader will improve performance:
//!
//! ```rust,ignore
//! let r = File::open("somefile")?;
//! let buff_reader = BufReader::new(r);
//! let mut br: BitReader<_, MSB> = BitReader::new(buff_reader);
//! ```
//!
//! # Writing
//!
//! ```rust, ignore
//! let w = File::create("somefile")?;
//! let mut bw = BitWriter::new(w);
//!
//! bw.write_bit(true)?;
//!
//! bw.write_byte(0x55)?;
//!
//! bw.write_bits(0x15, 5)?;
//!
//! bw.pad_to_byte();
//! ```
//! Using a buffered writer will improve performance
//!
//! ```rust, ignore
//! let w = File::create("somefile")?;
//! let mut buf_writer = BufWriter::new(w);
//! let mut bw = BitWriter::new(&mut buf_writer);
//! ...
//! buf_writer.flush();
//! ```

pub mod reader;
pub use reader::{BitReader, MSB, LSB};
pub mod writer;
pub use writer::BitWriter;
