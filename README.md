# Numerical Analysis

Formal developments and proofs of numerical analysis problems.

**Original Authors**: Aubry, Boldo, Clément, Faissole, Leclerc, Martin, Mayero, Mouhcine

This archive includes several Coq developments:
* *Lebesgue* directory is about the Lebesgue Integration of Nonnegative Functions
(see [paper](https://hal.inria.fr/hal-03471095),
[paper](https://hal.inria.fr/hal-03889276), and
[report](https://hal.inria.fr/hal-03105815));

* *Lebesgue/bochner_integral* directory is about the Bochner integral
(see [report](https://hal.inria.fr/hal-03516749));

* *LM* directory is about the Lax–Milgram theorem
(see [paper](https://hal.inria.fr/hal-01391578),
[paper](https://hal.inria.fr/hal-01630411), and
[report](https://hal.inria.fr/hal-01344090));

Opam package [*coq-num-analysis*](https://coq.inria.fr/opam/www/):
version 1.0 provides *Lebesgue*, and *LM*.

*Lebesgue* and *LM* are compiling in Coq 8.12 to 8.16.

## Dependencies:

- coq-mathcomp-ssreflect (prior to version 2)
- coq-mathcomp-bigenough
- coq-mathcomp-finmap
- coq-mathcomp-fingroup
- coq-coquelicot
- coq-mathcomp-algebra
- coq-mathcomp-multinomials
- coq-mathcomp-classical
- coq-flocq
