use std::io::{Error, ErrorKind, Result, Write};

/// A `BitWriter` gives a way to write single bits to a stream.
pub struct BitWriter<W: Write> {
    byte: [u8; 1],
    shift: usize,
    w: W,
}

impl<W: Write> BitWriter<W> {
    /// Constructs a new `BitWriter<T>`.
    ///
    /// # Arguments
    ///
    /// * writer - an existing open file or stream (implementing `Write`).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let w = File::create("somefile")?;
    /// let mut bw = BitWriter::new(w);
    /// ```
    pub fn new(writer: W) -> BitWriter<W> {
        BitWriter {
            w: writer,
            byte: [0],
            shift: 0,
        }
    }

    /// Writes a single bit to a `BitWriter<T>`.
    ///
    /// # Arguments
    ///
    /// is_one - if `true`, a 1 will be written, otherwise 0 will be written.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// bw.write_bit(true)?;
    /// ```
    pub fn write_bit(&mut self, is_one: bool) -> Result<()> {
        self.byte[0] = self.byte[0] << 1;
        if is_one {
            self.byte[0] |= 0x1;
        }
        self.shift = self.shift + 1;
        if self.shift == 8 {
            let n = self.w.write(&self.byte)?;
            if n == 0 {
                return Err(Error::new(ErrorKind::WriteZero, "Zero-length write"));
            }
            self.byte[0] = 0;
            self.shift = 0;
        }
        Ok(())
    }

    /// Writes a byte to a `BitWriter<T>`.
    ///
    /// # Arguments
    ///
    /// byte - the byte to write.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// bw.write_byte(byte: u8)?;
    /// ```
    pub fn write_byte(&mut self, byte: u8) -> Result<()> {
        Ok(self.write_bits(byte as u32, 8)?)
    }

    /// Writes a number of bits from a `u32` to `BitWriter<T>`. Will not write more than 32 bits.
    ///
    /// # Arguments
    ///
    /// val - the value containing the bits to write
    /// nbits - the number of bits to write
    ///
    /// # Examples
    ///
    /// ```ignore
    /// bw.write_bits(0x15, 5)?;
    /// ```
    pub fn write_bits(&mut self, mut val: u32, mut nbits: usize) -> Result<()> {
        if nbits > 32 {
            nbits = 32
        }
        let mask: u32 = (1 << nbits - 1) as u32;
        for _ in 0..nbits {
            self.write_bit(val & mask != 0)?;
            val = val << 1;
        }
        Ok(())
    }

    /// Gets a reference to the underlying stream.
    pub fn get_ref(&self) -> &W {
        &self.w
    }

    /// Gets a mutable reference to the underlying stream.
    ///
    /// Since the underlying stream is written byte-at-a-time
    /// it can only safely be retrieved when
    /// at a byte boundary. Call `pad_to_byte()` before `get_mut()`.
    pub fn get_mut(&mut self) -> Result<&mut W> {
        if self.is_aligned() {
            Ok(&mut self.w)
        } else {
            Err(Error::new(
                ErrorKind::Other,
                "Underlying stream not aligned with bitwriter. \
                 Call `pad_to_byte()` before attempting to get \
                  a mutable reference to the underlying stream.\n\
                  Use `is_aligned()` to check if bitwriter is able to `get_mut()`",
            ))
        }
    }

    /// Zero pads current byte to end.
    /// Used when finished writing bits to a stream to ensure
    /// the content of last byte is written. Should be called before
    /// attempting to retrieve a mutable reference to the underlying stream.
    pub fn pad_to_byte(&mut self) -> Result<()> {
        if !self.is_aligned() {
            self.write_bits(0, 8 - self.shift)?;
        }
        Ok(())
    }

    /// Returns whether the current bitwriter is aligned to the byte boundary.
    pub fn is_aligned(&self) -> bool {
        self.shift == 0
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::Cursor;

    #[test]
    pub fn write_bit() {
        let w = Cursor::new(vec![0; 2]);
        let mut bw = BitWriter::new(w);

        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();

        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();

        assert_eq!(*bw.get_ref().get_ref(), [0x55, 0xaa]);
    }

    #[test]
    pub fn write_byte() {
        let w = Cursor::new(vec![0; 4]);
        let mut bw = BitWriter::new(w);

        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();

        bw.write_byte(0x56).unwrap();

        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();
        bw.write_bit(true).unwrap();
        bw.write_bit(false).unwrap();

        bw.write_byte(0x55).unwrap();
        bw.write_byte(0xaa).unwrap();

        assert_eq!(*bw.get_ref().get_ref(), [0x55, 0xaa, 0x55, 0xaa]);
    }

    #[test]
    pub fn write_bits() {
        let w = Cursor::new(vec![0; 1]);
        let mut bw = BitWriter::new(w);

        bw.write_bits(0x2, 3).unwrap();
        bw.write_bits(0x15, 5).unwrap();

        assert_eq!(*bw.get_ref().get_ref(), [0x55]);
    }

    #[test]
    pub fn pad_to_byte() {
        let w = Cursor::new(vec![0; 5]);
        let mut bw = BitWriter::new(w);
        let mut check = [0; 5];

        bw.pad_to_byte().unwrap();
        bw.write_bit(true).unwrap();
        bw.pad_to_byte().unwrap();
        check[0] = 0x80;

        bw.write_bits(0x5, 3).unwrap();
        bw.pad_to_byte().unwrap();
        check[1] = 0xA0;

        bw.write_bits(0x101, 9).unwrap();
        check[2] = 0x80;

        bw.pad_to_byte().unwrap();
        check[3] = 0x80;

        assert_eq!(*bw.get_ref().get_ref(), check);
    }

    #[test]
    pub fn write_get_mut_ref() {
        let w = Cursor::new(vec![0; 3]);
        let mut bw = BitWriter::new(w);

        assert!(bw.is_aligned());
        assert!(bw.get_mut().is_ok());

        bw.get_mut().unwrap().write(&vec![12u8]).unwrap();
        assert_eq!(bw.get_ref().get_ref(), &[12, 0, 0]);

        assert!(bw.is_aligned());
        assert!(bw.get_mut().is_ok());

        // Writing 4 bits only writes to the internal buffer
        // so the underlying stream has seen no change
        bw.write_bits(0b1010, 4).unwrap();

        assert!(!bw.is_aligned());
        assert!(bw.get_mut().is_err());

        // this will fill in the data so if the underlying
        // stream is changed the data wont be lost.
        bw.pad_to_byte().unwrap();

        bw.get_mut().unwrap().write(&vec![14u8]).unwrap();
        assert_eq!(bw.get_ref().get_ref(), &[12, 160, 14]);

        assert!(bw.is_aligned());
        assert!(bw.get_mut().is_ok());
    }
}
