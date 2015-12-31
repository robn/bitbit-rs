use std::io::*;

/// A `BitReader` gives a way to read single bits from a stream.
pub struct BitReader<R: Read> {
    byte:  [u8; 1],
    shift: usize,
    r:     R,
}

impl<R: Read> BitReader<R> {
    /// Constructs a new `BitReader<R>`.
    ///
    /// # Arguments
    ///
    /// * reader - an existing open file or stream (implementing `Read`).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let r = try!(File::open("somefile"));
    /// let mut br = BitReader::new(r);
    /// ```
    pub fn new(reader: R) -> BitReader<R> {
        BitReader {
            r:     reader,
            byte:  [0],
            shift: 8,
        }
    }

    /// Reads a single bit from a `BitReader<R>`. Returns `true` for a 1 bit, `false` for a 0 bit.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let is_one = try!(br.read_bit());
    /// ```
    pub fn read_bit(&mut self) -> Result<bool> {
        if self.shift == 8 {
            let n = try!(self.r.read(&mut self.byte));
            if n == 0 {
                return Err(Error::new(ErrorKind::UnexpectedEof, "Unexpected EOF"));
            }
            self.shift = 0;
        }
        let bit = self.byte[0] & 0x80 != 0;
        self.byte[0] = self.byte[0] << 1;
        self.shift = self.shift + 1;
        Ok(bit)
    }

    /// Reads 8 bits from a `BitReader<R>` and returns them as a single byte.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let byte = try!(br.read_byte());
    /// ```
    pub fn read_byte(&mut self) -> Result<u8> {
        Ok(try!(self.read_bits(8)) as u8)
    }

    /// Read a number of bits from a `BitReader<R>` and return them in a `u32`. Will not read more
    /// than 32 bits.
    ///
    /// # Arguments
    ///
    /// * bits - number of bits to read
    ///
    /// # Examples
    /// ```ignore
    /// let num = try!(br.read_bits(5));
    /// ```
    pub fn read_bits(&mut self, mut nbits: usize) -> Result<u32> {
        if nbits > 32 { nbits = 32 }
        let mut out: u32 = 0;
        for _ in 0..nbits {
            out = out << 1;
            if try!(self.read_bit()) {
                out = out | 0x1;
            }
        }
        Ok(out)
    }

    /// Gets a reference to the underlying stream.
    pub fn get_ref(&mut self) -> &R {
        &self.r
    }
}

#[cfg(test)]
mod test {
    use std::io::{Cursor, ErrorKind};
    use super::*;

    macro_rules! assert_eof {
        ($br: ident) => {
            match $br.read_bit() {
                Err(e) => match e.kind() {
                    ErrorKind::UnexpectedEof => (),
                    k => panic!("Expected EOF, got IO error: {:?}", k),
                },
                v => panic!("Expected EOF, got: {:?}", v),
            }
        }
    }

    #[test]
    pub fn read_bit() {
        let r = Cursor::new(vec![0x55,0xaa]);
        let mut br = BitReader::new(r);

        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);

        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);

        assert_eof!(br);
    }

    #[test]
    pub fn read_byte() {
        let r = Cursor::new(vec![0x55,0xaa,0x55,0xaa]);
        let mut br = BitReader::new(r);

        assert_eq!(br.read_byte().unwrap(), 0x55);
        assert_eq!(br.read_byte().unwrap(), 0xaa);

        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);

        assert_eq!(br.read_byte().unwrap(), 0x56);

        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);

        assert_eof!(br);
    }

    #[test]
    pub fn read_bits() {
        let r = Cursor::new(vec![0x55]);
        let mut br = BitReader::new(r);

        assert_eq!(br.read_bits(3).unwrap(), 0x2);
        assert_eq!(br.read_bits(5).unwrap(), 0x15);

        assert_eof!(br);
    }
}
