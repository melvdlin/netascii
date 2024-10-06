//! This crate provides Iterator adapters for encoding ([`Netascii`]) and decoding ([`Bytes`])
//! byte strings to and from netascii as according to [RFC 854](https://datatracker.ietf.org/doc/rfc854/).
//! More concretely, these adapters deal with the escaping of carriage return (CR) characters.
//!
//! This crate is fully `no_std`-compatible and does not require `alloc`.

#![cfg_attr(not(any(test, doctest)), no_std)]

use core::error::Error;
use core::fmt::Display;

/// An iterator adapter decoding the provided netascii source iterator.
///
/// Yields a [`CrError`] if an illegal carriage return is encountered.
/// An illegal carriage return is one not followed by either a line feed or NUL (`b'\0'`).
///
/// After a [`CrError`], decoding continues at the next byte after the illegal CR.
#[derive(Debug)]
#[derive(Clone)]
pub struct Bytes<I: Iterator<Item = u8>> {
    netascii: core::iter::Peekable<I>,
}

impl<I: Iterator<Item = u8>> Bytes<I> {
    pub fn from_netascii(netascii: impl IntoIterator<IntoIter = I>) -> Self {
        Self {
            netascii: netascii.into_iter().peekable(),
        }
    }
}

impl<I: Iterator<Item = u8>> Iterator for Bytes<I> {
    type Item = Result<u8, CrError>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(Ok(match self.netascii.next()? {
            | b'\r' => match self.netascii.peek().copied() {
                | Some(b'\n') => {
                    self.netascii.next();
                    b'\n'
                }
                | Some(b'\0') => {
                    self.netascii.next();
                    b'\r'
                }
                | _ => return Some(Err(CrError)),
            },
            | x => x,
        }))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (netascii_lower, netascii_upper) = self.netascii.size_hint();
        let lower = netascii_lower / 2;
        let upper = netascii_upper;

        (lower, upper)
    }
}

/// An error indicating that an illegal carriage return character
/// was encountered in the netascii source iterator.
///
/// See [`Bytes`] for more details on what constitutes an illegal CR.
#[derive(Debug)]
#[derive(Clone, Copy)]
#[derive(PartialEq, Eq)]
pub struct CrError;

impl Display for CrError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "lone CR encountered (must be followed by either LF or NUL)"
        )
    }
}

impl Error for CrError {}

/// An iterator adapter encoding the provided source iterator to netascii.
///
/// Inserts NUL (`b'\0'`) after every carriage return character not followed by a line feed.
#[derive(Debug)]
#[derive(Clone)]
pub struct Netascii<I: Iterator> {
    bytes: I,
    next: Option<u8>,
}

impl<I: Iterator<Item = u8>> Netascii<I> {
    pub fn from_bytes(bytes: impl IntoIterator<IntoIter = I>) -> Self {
        Self {
            bytes: bytes.into_iter(),
            next: None,
        }
    }
}

impl<I: Iterator<Item = u8>> Iterator for Netascii<I> {
    type Item = u8;

    fn next(&mut self) -> Option<Self::Item> {
        match self.next.take() {
            | Some(c) => Some(c),
            | None => Some(match self.bytes.next()? {
                | b'\r' => {
                    // we just took `next`
                    debug_assert_eq!(self.next, None);
                    self.next = Some(b'\0');
                    b'\r'
                }
                | b'\n' => {
                    // we just took `next`
                    debug_assert_eq!(self.next, None);
                    self.next = Some(b'\n');
                    b'\r'
                }
                | c => c,
            }),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (bytes_lower, bytes_upper) = self.bytes.size_hint();
        let inserting = if self.next.is_some() { 1 } else { 0 };
        let lower = bytes_lower.saturating_add(inserting);
        let upper = bytes_upper
            .map(|bytes_upper| bytes_upper.saturating_mul(2).saturating_add(inserting));
        (lower, upper)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inverse() {
        let lorem = *br"
        Lorem ipsum dolor sit amet,
        consectetur adipiscing elit.
        ";

        let netascii = Netascii::from_bytes(lorem);
        let bytes =
            Bytes::from_netascii(netascii).collect::<Result<Vec<u8>, CrError>>().unwrap();

        assert_eq!(&bytes, &lorem);
    }

    #[test]
    fn test_cr_decode() {
        let netascii = *b"lorem ipsum\r\n dolor sit\r\0 amet";
        let expected = *b"lorem ipsum\n dolor sit\r amet";

        let bytes =
            Bytes::from_netascii(netascii).collect::<Result<Vec<u8>, CrError>>().unwrap();

        assert_eq!(&bytes, &expected);
    }

    #[test]
    fn test_cr_encode() {
        let lorem = *b"lorem ipsum\n dolor sit\r amet";
        let expected = *b"lorem ipsum\r\n dolor sit\r\0 amet";

        let netascii = Netascii::from_bytes(lorem).collect::<Vec<u8>>();

        assert_eq!(&netascii, &expected);
    }

    #[test]
    fn test_no_same_repr_encode() {
        let lorem = *b"Lorem ipsum dolor sit amet, consectetur adipiscing elit.";
        let netascii = Netascii::from_bytes(lorem).collect::<Vec<u8>>();

        assert_eq!(&netascii, &lorem);
    }

    #[test]
    fn test_no_same_repr_decode() {
        let netascii = *b"Lorem ipsum dolor sit amet, consectetur adipiscing elit.";
        let decoded =
            Bytes::from_netascii(netascii).collect::<Result<Vec<u8>, CrError>>().unwrap();

        assert_eq!(&decoded, &netascii);
    }

    #[test]
    fn test_illegal_cr() {
        let netascii = *b"Lorem ipsum dolor sit\r amet, consectetur adipiscing elit.";
        let decoded = Bytes::from_netascii(netascii).collect::<Result<Vec<u8>, _>>();
        assert_eq!(Err(CrError), decoded);

        let netascii = *b"Lorem ipsum dolor sit\r\r amet, consectetur adipiscing elit.";
        let decoded = Bytes::from_netascii(netascii).collect::<Result<Vec<u8>, _>>();
        assert_eq!(Err(CrError), decoded);

        let netascii = *b"Lorem ipsum dolor sit\n\r amet, consectetur adipiscing elit.";
        let decoded = Bytes::from_netascii(netascii).collect::<Result<Vec<u8>, _>>();
        assert_eq!(Err(CrError), decoded);
    }

    #[test]
    fn test_encode_size_hint() {
        let lorem = *b"Lorem ipsum dolor sit amet, consectetur adipiscing elit.";
        let netascii = Netascii::from_bytes(lorem);

        assert!(netascii.size_hint().0 <= lorem.len());
        assert!(netascii.size_hint().1 >= Some(lorem.len() * 2));
    }

    #[test]
    fn test_decode_size_hint() {
        let netascii = *b"Lorem ipsum dolor sit amet, consectetur adipiscing elit.";
        let bytes = Bytes::from_netascii(netascii);

        assert!(bytes.size_hint().0 <= netascii.len() / 2);
        assert!(bytes.size_hint().1 >= Some(netascii.len()));
    }
}
