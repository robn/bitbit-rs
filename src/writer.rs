use std::io::*;

/// A `BitWriter` gives a way to write single bits to a stream.
pub struct BitWriter<W: Write> {
    byte:  [u8; 1],
    shift: usize,
    w:     W,
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
    /// let w = try!(File::create("somefile"));
    /// let mut bw = BitWriter::new(w);
    /// ```
    pub fn new(writer: W) -> BitWriter<W> {
        BitWriter {
            w:     writer,
            byte:  [0],
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
    /// try!(br.write_bit(true));
    /// ```
    pub fn write_bit(&mut self, is_one: bool) -> Result<()> {
        self.byte[0] = self.byte[0] << 1;
        if is_one {
            self.byte[0] |= 0x1;
        }
        self.shift = self.shift + 1;
        if self.shift == 8 {
            let n = try!(self.w.write(&self.byte));
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
    /// try!(br.write_byte(byte: u8));
    /// ```
    pub fn write_byte(&mut self, mut byte: u8) -> Result<()> {
        for _ in 0..8 {
            try!(self.write_bit(byte & 0x80 != 0));
            byte = byte << 1;
        }
        Ok(())
    }

    /// Gets a reference to the underlying stream.
    pub fn get_ref(&mut self) -> &W {
        &self.w
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

        assert_eq!(*bw.get_ref().get_ref(), [0x55,0xaa]);
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

        assert_eq!(*bw.get_ref().get_ref(), [0x55,0xaa,0x55,0xaa]);
    }
}
