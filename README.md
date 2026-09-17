# argomac-lean

This repository contains the ArgoMAC construction for BN254 scalar multiplication.
The Kriterion verifier reads `Submission.solution`.

## Status

This revision does not yet satisfy the revised challenge.
`Submission.lean` has two open proof goals.
The first goal needs a complete simulator machine.
The second goal needs the combined adaptive privacy bound.
The challenge budget remains provisional.
The [challenge draft](https://github.com/Kriterion-cc/kriterion-challenge/pull/1) defines the revised obligation.

The construction uses 92 digits and three shared permutation slots.
The construction retains complete homogeneous addition formulas.
Those formulas require 13 point-adaptor families.
The paper needs corrected coordinate formulas and an updated adaptor count.

## Layout

| Path | Content |
| --- | --- |
| `Construction.lean`, `Construction/` | These files define the computable construction and machine components. |
| `Proof.lean`, `Proof/` | These files contain the construction proofs and simulator proofs. |
| `Submission.lean` | This file connects the construction to the challenge obligation. |
| `tests/` | These files check the construction, parameters, simulator components, and axioms. |

The verifier copies the construction, proof, and submission files into its generated workspace.
The challenge baseline test also compiles `tests/AdaptivePrivacy.lean` and its imports.
The generated workspace uses Lean 4.33.1, Mathlib 4.33.1, and the challenge library.

## Verified construction

`Construction/SharedGarbling.lean` exposes the three-slot public interface.
The hash and pad roles share slots zero and one.
The third slot serves only the hash role.
The tape type enforces this equality.
`Proof/SharedOracle.lean` proves the uniform public-oracle law for that tape type.

`Proof/SharedGarbling.lean` proves correctness for every input and every tape.
The proof covers equal points, identity results, and off-curve rejection.
The selected labels satisfy the Lamport interface.
The canonical public encoding contains 9,806,076 bytes.
`tests/Correctness.lean` checks these properties for the shared circuit.
`tests/Components.lean` checks the 92-digit count and the shared role mapping.

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
The challenge's `starter/PAPER_CORRECTIONS.md` records the coordinate counterexamples.

## Simulator proofs

`Proof/Privacy/Simulator/SharedSimulator.lean` uses one transcript for the three shared slots.
Lean proves its oracle-consistency rules and selected-gate equations.
The shared collision checks detect domain and range conflicts between the role names.
The shared assignment theorem gives the exact permutation probability for both branches.
`SharedOracleProgram.lean` proves the source program's online distribution law.
These results do not yet prove the complete shared-slot adaptive privacy bound.
The older source transport proofs still assume five independent permutation roles.

`Construction/Simulator/` contains fixed arithmetic machine components.
The corresponding proofs appear in `Proof/Privacy/Simulator/Arithmetic/`.
The word sampler produces a uniform 256-bit word in 1,798 instructions.
Its program table costs 13 additional units.
The bounded sampler has an exact retry law and a failure bound of `2^-256`.
The RAM caller preserves its saved address across the sampler call.
Its 256-attempt budget is at most 461,855 units, including its program table.
These component budgets do not establish the complete simulator budget.

The source simulator samples 91 free points and 92 nonzero scales.
Its existing resource bounds count higher-level operations.
Those bounds do not prove the revised arithmetic instruction budget.
The complete proof also needs RAM oracle tables, canonical serialization, and an implementation-error bound.

## Validation

The generated workspace uses these commands:

```sh
lake build Construction Proof
lake build Submission
```

The first command checks the exported construction and proof modules.
The second command remains a required acceptance test.
The current second command fails at the two open adaptive privacy goals.
The axiom checks permit only `propext`, `Classical.choice`, and `Quot.sound`.
No completed proof uses an assumed adaptive privacy theorem.
