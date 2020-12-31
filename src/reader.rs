use std::io::*;
use std::marker::PhantomData;

pub trait Bit {
    // support for read_bit
    fn extract_bit(byte: u8) -> (bool, u8);

    // support for read_bits
    fn shift_bit(word: u32) -> u32;
    fn set_bit(word: u32) -> u32;
    fn shift_into_place(word: u32, nbits: usize) -> u32;
}

pub enum MSB {}

pub enum LSB {}

impl Bit for MSB {
    #[inline(always)]
    fn extract_bit(byte: u8) -> (bool, u8) {
        (byte & 0x80 != 0, byte << 1)
    }

    #[inline(always)]
    fn shift_bit(word: u32) -> u32 {
        word << 1
    }

    #[inline(always)]
    fn set_bit(word: u32) -> u32 {
        word | 0x1
    }

    #[inline(always)]
    fn shift_into_place(word: u32, _: usize) -> u32 {
        word
    }
}

impl Bit for LSB {
    #[inline(always)]
    fn extract_bit(byte: u8) -> (bool, u8) {
        (byte & 0x1 != 0, byte >> 1)
    }

    #[inline(always)]
    fn shift_bit(word: u32) -> u32 {
        word >> 1
    }

    #[inline(always)]
    fn set_bit(word: u32) -> u32 {
        word | 0x80000000
    }

    #[inline(always)]
    fn shift_into_place(word: u32, nbits: usize) -> u32 {
        word >> 32 - nbits
    }
}

/// A `BitReader` gives a way to read single bits from a stream.
pub struct BitReader<R: Read, B: Bit> {
    _marker: PhantomData<*const B>,
    byte: [u8; 1],
    shift: usize,
    r: R,
}

impl<R: Read, B: Bit> BitReader<R, B> {
    /// Constructs a new `BitReader`. Requires an implementation of  `Bit` type to determine which
    /// end of bytes to read bits from.
    ///
    /// # Arguments
    ///
    /// * reader - an existing open file or stream (implementing `Read`).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let r = File::open("somefile")?;
    /// let mut br: BitReader<_,MSB> = BitReader::new(r);
    /// ```
    pub fn new(reader: R) -> BitReader<R, B> {
        BitReader {
            _marker: PhantomData,
            r: reader,
            byte: [0],
            shift: 8,
        }
    }

    /// Reads a single bit from a `BitReader`. Returns `true` for a 1 bit, `false` for a 0 bit.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let is_one = br.read_bit()?;
    /// ```
    pub fn read_bit(&mut self) -> Result<bool> {
        if self.shift == 8 {
            let n = self.r.read(&mut self.byte)?;
            if n == 0 {
                return Err(Error::new(ErrorKind::UnexpectedEof, "Unexpected EOF"));
            }
            self.shift = 0;
        }
        let (bit, byte) = B::extract_bit(self.byte[0]);
        self.byte[0] = byte;
        self.shift = self.shift + 1;
        Ok(bit)
    }

    /// Reads 8 bits from a `BitReader` and returns them as a single byte.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// let byte = br.read_byte()?;
    /// ```
    pub fn read_byte(&mut self) -> Result<u8> {
        Ok(self.read_bits(8)? as u8)
    }

    /// Read a number of bits from a `BitReader` and return them in a `u32`. Will not read more
    /// than 32 bits.
    ///
    /// # Arguments
    ///
    /// * bits - number of bits to read
    ///
    /// # Examples
    /// ```ignore
    /// let num = br.read_bits(5)?;
    /// ```
    pub fn read_bits(&mut self, mut nbits: usize) -> Result<u32> {
        if nbits > 32 {
            nbits = 32
        }
        let mut out: u32 = 0;
        for _ in 0..nbits {
            out = B::shift_bit(out);
            if self.read_bit()? {
                out = B::set_bit(out);
            }
        }
        out = B::shift_into_place(out, nbits);
        Ok(out)
    }

    /// Gets a reference to the underlying stream.
    pub fn get_ref(&self) -> &R {
        &self.r
    }

    /// Gets a mutable reference to the underlying stream.
    ///
    /// Since the underlying stream is consumed byte-at-a-time
    /// it can only safely be retrieved when at a byte boundary.
    /// Call `read_to_byte()` before `get_mut()`. Should be called
    /// before attempting to retrieve a mutable reference to the
    /// underlying stream.
    pub fn get_mut(&mut self) -> Result<&mut R> {
        if self.is_aligned() {
            Ok(&mut self.r)
        } else {
            Err(Error::new(
                ErrorKind::Other,
                "Underlying stream not aligned with bitreader. \
                 Call `read_to_byte()` before attempting to get \
                  a mutable reference to the underlying stream.\n\
                  Use `is_aligned()` to check if bitreader is able to `get_mut()`",
            ))
        }
    }

    /// The opposite functionality of pad_to_byte.
    /// If any bits in the current byte have been read this function
    /// returns the value of the remaining bits and by doing so skips to the start of the next byte boundary.
    pub fn read_to_byte(&mut self) -> Result<u32> {
        if !self.is_aligned() {
            return Ok(self.read_bits(8 - self.shift)?);
        }
        Ok(0)
    }

    /// Returns whether the current bitreader is aligned to the byte boundary.
    ///
    /// Shift value of `8` would mean we have read 8 bits but have not consumed
    /// the next byte from the underlying stream. `0` means we haven't read
    /// anything but we have consumed the next byte.
    pub fn is_aligned(&self) -> bool {
        self.shift == 8
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::io::{Cursor, ErrorKind};

    macro_rules! assert_eof {
        ($br: ident) => {
            match $br.read_bit() {
                Err(e) => match e.kind() {
                    ErrorKind::UnexpectedEof => (),
                    k => panic!("Expected EOF, got IO error: {:?}", k),
                },
                v => panic!("Expected EOF, got: {:?}", v),
            }
        };
    }

    #[test]
    pub fn read_bit_msb() {
        let r = Cursor::new(vec![0x55, 0xaa]);
        let mut br: BitReader<_, MSB> = BitReader::new(r);

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
    pub fn read_byte_msb() {
        let r = Cursor::new(vec![0x55, 0xaa, 0x55, 0xaa]);
        let mut br: BitReader<_, MSB> = BitReader::new(r);

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
    pub fn read_bits_msb() {
        let r = Cursor::new(vec![0x55]);
        let mut br: BitReader<_, MSB> = BitReader::new(r);

        assert_eq!(br.read_bits(3).unwrap(), 0x2);
        assert_eq!(br.read_bits(5).unwrap(), 0x15);

        assert_eof!(br);
    }

    #[test]
    pub fn read_bit_lsb() {
        let r = Cursor::new(vec![0x55, 0xaa]);
        let mut br: BitReader<_, LSB> = BitReader::new(r);

        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);

        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);
        assert_eq!(br.read_bit().unwrap(), false);
        assert_eq!(br.read_bit().unwrap(), true);

        assert_eof!(br);
    }

    #[test]
    pub fn read_bits_lsb() {
        let r = Cursor::new(vec![0x55]);
        let mut br: BitReader<_, LSB> = BitReader::new(r);

        assert_eq!(br.read_bits(3).unwrap(), 0x5);
        assert_eq!(br.read_bits(5).unwrap(), 0xa);

        assert_eof!(br);
    }

    #[test]
    pub fn read_bits_padding_msb() {
        let r = Cursor::new(vec![0b10011001, 0b10001001]);
        let mut br: BitReader<_, MSB> = BitReader::new(r);
        assert_eq!(br.read_to_byte().unwrap(), 0);
        assert_eq!(br.read_bits(3).unwrap(), 4);
        assert_eq!(br.read_to_byte().unwrap(), 25);
        assert_eq!(br.read_to_byte().unwrap(), 0);
        assert_eq!(br.read_bits(4).unwrap(), 8);
        assert_eq!(br.read_bits(3).unwrap(), 4);
        assert_eq!(br.read_to_byte().unwrap(), 1);

        assert_eof!(br);
    }

    #[test]
    pub fn read_bits_padding_lsb() {
        let r = Cursor::new(vec![0b10011001, 0b10001001]);
        let mut br: BitReader<_, LSB> = BitReader::new(r);
        assert_eq!(br.read_to_byte().unwrap(), 0);
        assert_eq!(br.read_bits(3).unwrap(), 1);
        assert_eq!(br.read_to_byte().unwrap(), 19);
        assert_eq!(br.read_to_byte().unwrap(), 0);
        assert_eq!(br.read_bits(4).unwrap(), 9);
        assert_eq!(br.read_bits(3).unwrap(), 0);
        assert_eq!(br.read_to_byte().unwrap(), 1);

        assert_eof!(br);
    }


    #[test]
    pub fn read_get_mut() {
        let r = Cursor::new(vec![0b10011001, 0b10101001, 0b11111001, 0b01100101]);
        let mut br: BitReader<_, MSB> = BitReader::new(r);
        let mut buf = vec![0u8; 1];

        assert!(br.get_mut().is_ok());
        assert!(br.is_aligned());

        br.get_mut().unwrap().read(&mut buf).unwrap();
        assert_eq!(buf, [0b10011001]);

        // Reading 3 bits consumes an internal byte, so the next call
        // to read will start at the next byte boundary.
        assert_eq!(br.read_bits(3).unwrap(), 0b101);

        // Check that we are currently unaligned.
        assert!(!br.is_aligned());
        assert!(br.get_mut().is_err());
        assert!(matches!(
            br.get_mut().err().unwrap().kind(),
            ErrorKind::Other
        ));

        // In order for the last line of the test to be successful
        // you need to read_to_byte, otherwise we will read old values.
        br.read_to_byte().unwrap();

        assert!(br.get_mut().is_ok());
        assert!(br.is_aligned());

        br.get_mut().unwrap().read(&mut buf).unwrap();
        assert_eq!(buf, [0b11111001]);

        // without the previous read_to_byte this would fail
        assert_eq!(br.read_bits(4).unwrap(), 0b0110);
        assert_eq!(br.read_to_byte().unwrap(), 0b101);

        assert_eof!(br);
    }
}
