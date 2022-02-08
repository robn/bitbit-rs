use std::io::*;

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
        if nbits > 32 { nbits = 32 }
        let mask: u32 = (1 << nbits - 1) as u32;
        for _ in 0..nbits {
            self.write_bit(val & mask != 0)?;
            val = val << 1;
        }
        Ok(())
    }

    /// Gets a reference to the underlying stream.
    pub fn get_ref(&mut self) -> &W {
        &self.w
    }

    /// Consumes the writer, returning the underlying stream.
    pub fn take(self) -> W { self.w }

    /// Zero pads current byte to end.
    /// Used when finished writing bits to a stream to ensure the content of last byte is written.
    pub fn pad_to_byte(&mut self) -> Result<()> {
        if self.shift != 0 {
            self.write_bits(0, 8 - self.shift)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use std::io::Cursor;
    use super::*;

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
}
