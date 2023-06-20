# ML-Unification

1. First-order and higher-order pattern E-unification and E-matching for Isabelle with theorem certificates.
   In other words: unification/matching with adjustable fallback equality prover + certificates.
2. Resolution tactic with adjustable unifier
3. [Unification Hints](https://link.springer.com/chapter/10.1007/978-3-642-03359-9_8)

## Build

Requirements:
1. The Isabelle development version
2. The AFP development version
3. This [Isabelle/ML logging framework](https://github.com/kappelmann/logger-isabelle)

## Future Tasks

1. Add higher-order unifier E-unification and matching
2. Use more efficient data structures for unification hints
3. build assumption, erule and drule tactics with adjustable unifier
4. tests:
    - adapt tests to work for open terms
    - for unification hints: check if order of premises = order of solver


