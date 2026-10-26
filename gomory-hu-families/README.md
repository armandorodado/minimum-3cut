# Scripts for "Candidate families for hard 3-cut instances"

Requirements: Python 3.9+, numpy, scipy, networkx. Run from this folder. Everything is exhaustive (no max-flow code); `cutlib.py` is the library from the ORL supplementary material.

| Script | What it checks | Time |
| --- | --- | --- |
| `lowerbound.py [m] [trials]` | Theorem A instance (default m = 4): same degrees for every partition, unique star Gomory–Hu tree, unique hard optimum = the partition, F(T) > OPT. Log: `lowerbound.log` | seconds |
| `cluster_lemma_check.py` | Lemmas A1 and A3 in exact rational arithmetic, m = 5..14 | about 8 min |
| `ratio.py m beta_scaled` | Best f(X)/OPT over non-cluster sets (Theorem B table), e.g. `ratio.py 4 12600`, `ratio.py 5 10100` | seconds |
| `bank.py`, `bank_lb.py`, `bank_lp.py seed` | Build the hard-instance banks (`bank.json`, `lpbank_<seed>.json`; merged `lpbank.json` is included) | minutes |
| `families.py bank.json` | Gomory–Hu, rooted, isolating, non-trivial-cut and light-cut (NI) families. Logs: `families_bank.log`, `families_lpbank.log` | minutes |
| `fam2.py bank.json` | Single-linkage and Stoer–Wagner families. Log: `fam2_bank.log` | seconds |
| `attack.py FAMILY [climbs] [steps] [seed]` | Hill-climbing search for a failure of a family | about 1 min per family |
| `lightstats.py` | Statistics of the light-cut family on both banks | minutes |
