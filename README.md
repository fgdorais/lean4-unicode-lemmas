# UnicodeLemmas

## The Lean4 / Unicode family

This library is one of a small family of Lean 4 Unicode libraries. Each one has a narrow job, so
you only depend on what you need.

| Library | What it is for |
| --- | --- |
| [UnicodeBasic](https://github.com/fgdorais/lean4-unicode-basic) | The foundation. Fast lookups of commonly used character properties such as general category, case mappings, numeric values, scripts and names, from compact precompiled tables. Start here. |
| [UnicodeData](https://github.com/fgdorais/lean4-unicode-data) | Direct access to the Unicode Character Database files themselves, such as `UnicodeData.txt`, `PropList.txt`, `CaseFolding.txt` and `SpecialCasing.txt`. Heavier than UnicodeBasic, but complete, and handy for properties UnicodeBasic does not cover or for checking it against the source. |
| [UnicodeFormat](https://github.com/fgdorais/lean4-unicode-format) | Encoding and decoding: UTF-8, UTF-16 and UTF-32, the byte-level encoding schemes with byte order marks, strict and lossy decoding, and streaming iterators. |
| **UnicodeLemmas** (this library) | Proofs about UnicodeBasic properties, such as the fact that every cased character is alphabetic. |
| [UnicodeExtra](https://github.com/fgdorais/lean4-unicode-extra) | Unicode algorithms on whole strings that are too large or too specialized for UnicodeBasic, built on top of it. |
