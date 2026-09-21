# argomac-lean

This directory is the complete starter for the BN254 scalar multiplication challenge.
It contains the ArgoMAC construction, proofs, and tests.
The Kriterion verifier reads `Submission.solution`.

The construction uses 92 digits and three shared permutation slots.
The complete homogeneous addition formulas require 13 point-adaptor families.
The paper needs corrected coordinate formulas and an updated adaptor count.

## Layout

| Path | Content |
| --- | --- |
| `Construction.lean`, `Construction/` | These files define the computable construction and machine components. |
| `Proof.lean`, `Proof/` | These files contain the construction proofs and simulator witnesses. |
| `Submission.lean` | This file connects the construction to the challenge obligation. |
| `tests/` | These files check the construction, parameters, simulator components, and axioms. |

The verifier copies the construction, proof, and submission files into its generated workspace.
The challenge baseline test also compiles `tests/AdaptivePrivacy.lean` and its imports.
The generated workspace uses Lean 4.33.1, Mathlib 4.33.1, and the challenge library.

## Verified construction

`Construction/SharedGarbling.lean` exposes the three-slot public interface.
The hash and pad roles share slots zero and one.
The third slot serves only the hash role.
The private coins exclude the public oracle.
`Proof/SharedOracle.lean` connects the fixed lazy oracle to the complete oracle proof model.

`Construction/OraclePrograms.lean` supplies the actual garbling and evaluation query programs.
Their bounds are 1,759,967 and 1,055,879 queries.
Their results equal the construction results for every complete public oracle.

`Proof/SharedGarbling.lean` proves correctness for every input and every private coin value.
The proof covers equal points, identity results, and off-curve rejection.
The selected labels satisfy the Lamport interface.
The canonical public encoding contains 9,806,076 bytes.

## Paper correspondence

The comparison uses BaBe.latex commit `e2dcf4d540b2708e13cd21090df759051119a116`.

| Item | Paper | Construction |
| --- | --- | --- |
| Digits | 92 | 92 |
| Shared slots per bucket | 3 | 3 |
| Point-adaptor families | 9 | 13 |
| Block formula | `π(L XOR t) XOR (L XOR t)` | `π(L XOR t) XOR (L XOR t)` |

`Proof/Privacy/PaperConstruction.lean` proves the block formula and tweak relations.
The point tweaks range from 0 through 91.
Curve gates use tweak 92.
The challenge's [PAPER_CORRECTIONS.md](https://github.com/Kriterion-cc/kriterion-challenge/blob/aaf278948a4127f99ee6752c7cec4b9f9bd43615/bn254-scalar-multiplication/PAPER_CORRECTIONS.md) records the coordinate counterexamples.

## Simulator proofs

The real and ideal games use the same fixed lazy oracle.
The oracle serves each adversary query directly.
The simulator uses fixed instructions for oracle queries, lookups, and fresh programs.
A refused program aborts the ideal game.
The proof accounts for this abort with the existing collision event.

`Proof/Privacy/Source/StrictGateSource.lean` proves the strict source privacy bound.
`StrictSourceSampling.lean` replaces ideal private draws with finite samplers.
`StrictWirePrivacy.lean` transfers these bounds to the public challenge obligation.
The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

`Proof/Privacy/Simulator/Arithmetic/` connects each source phase to the closed machine.
The simulator uses one instruction table and two stage limits.
Their sum stays below `2^60`.
The private samplers use at most 256 attempts per draw.
The source uses 917,653 private draws across both stages.
The sampling error contributes to the privacy allowance.

## Validation

The Lake configuration pins the challenge library to an exact commit.
You can run these commands from the repository root:

```sh
lake exe cache get
lake build
lake env lean tests/ProofAudit.lean
lake build BaselineTests
lake env lean tests/AxiomAudit.lean
```

The build commands check the exported proofs and the complete submission.
The challenge also runs these checks through `lake test`.
The axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`.
No completed proof uses an assumed adaptive privacy theorem.
