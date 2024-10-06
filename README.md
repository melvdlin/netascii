# netascii

This crate provides Iterator adapters to encode and decode byte strings to and from netascii
as according to [RFC 854](https://datatracker.ietf.org/doc/rfc854/).
More concretely, these adapters deal with the escaping of carriage return (CR) characters.

This crate is fully `no_std`-compatible and does not require `alloc`.
