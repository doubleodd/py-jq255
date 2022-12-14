# Reference Implementation of jq255e and jq255s

This is the reference implementation for the double-odd elliptic curves
jq255e and jq255s. It is meant for research purposes, NOT for production
use: while it computes correct results in all cases, it makes no attempt
at preventing side-channel attacks; in particular, timing attacks may
reveal information about points and scalars.

The `jq255.py` file contains the implementation itself, and is heavily
commented.

The `mktests.py` script uses `jq255.py` to generate the test vectors.
The produced test vectors are included, as `test-jq255e.txt` and
`test-jq255s.txt` (the files include comments that describe the meaning
of each value).

All this code _should_ work on any modern Python installation (3.4+).
