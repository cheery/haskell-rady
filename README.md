Rady - regular language encoding/decoding with types
====================================================

Each [regular language] has a corresponding type presentation
for the information encoded in a matched string.

 1. For empty language, Ø, the corresponding type is `Void`.
 2. For empty string language, ε, `()`.
 3. For singleton language, a, `()`.
 4. For union, a|b, `Either ¤a ¤b`.
 5. For concatenation, ab, `(¤a,¤b)`.
 6. For interleaving, a&b, `(¤a,¤b)`.
 7. For kleene, a*, `[¤a]`

This module provides bunch of combinators
to construct regular language descriptors in haskell.
Once such a descriptor is created, it can be used to...

 * Decode data (parse) from lists into value of the corresponding type.
 * Loosely decode data (lparse), skipping rejected items.
 * Encode data (generate) into lists from value of the corresponding type.
 * Convert (can) the corresponding type
   into a similar type with units trimmed away.

The implementation here could use some further ideas.
In ideal case the 'Shape' could convert
into a regular language representation
that could be then given out from the program to present what it matches on.

Likewise it'd be fun to allow arbitrary patterns to be attached to a type
after the program has been compiled.

 [regular language]: https://en.wikipedia.org/wiki/Regular_language
