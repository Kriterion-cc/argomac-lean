# argomac-lean

The ArgoMAC garbled circuit for BN254 scalar multiplication, in Lean 4.

This repository is the baseline submission for the Kriterion challenge
`scalar-multiplication`.

## Layout

| Path                                 | Content                                   |
| ------------------------------------ | ----------------------------------------- |
| `Construction.lean`, `Construction/` | The computable construction.              |
| `Proof.lean`, `Proof/`               | The proof.                                |
| `Submission.lean`                    | The entry point the verifier reads.       |
| `tests/`                             | Acceptance checks. Kriterion ignores them. |

The verifier copies `Submission.lean`, `Construction.lean`, `Proof.lean`,
`Construction/`, and `Proof/` into a workspace it generates. It ignores every other
root entry.

## Build

The construction and the proof import the challenge library. That library is
`examples/bn254-scalar-multiplication/formal` in the Kriterion repository, and
`challenge.yaml` pins its commit. To build this repository, place that library beside
these files and declare it as the Lean library `Kriterion`. Kriterion does this for
every submission it verifies.

## Status

`Submission.solution` supplies every field of `Kriterion.Solution`.
`Submission.adaptivePrivacy` proves the unchanged universal 100-bit privacy obligation.
The theorem applies to the entry variant described below.
The theorem uses ideal permutations and an ideal hash oracle.
The theorem covers one selected input encoding per garbling.
It does not prove security for concrete AES, concrete SHA256, repeated label releases, or the complete BaBe protocol.
The theorem fixes BN254 and 128-bit blocks.
It does not define an asymptotic family for every security parameter.

| Field | Where |
| --- | --- |
| `randomnessFromSeed` | `Construction/ArgoMAC/Seed.lean` derives the complete tape from the seed. It proves the clamped offset with plain `ZMod` arithmetic and a Bezout argument, without the field certificate. |
| `perfectCorrectness` | `Proof/RCBComplete.lean` with the termination instance in `Proof/Base7Termination.lean`. |
| `lamportCompatible` | `Proof/Lamport.lean`. |
| `adaptivePrivacy` | `Proof/ConcreteSmallSourceRatio.lean` proves the universal 100-bit bound. `Submission.adaptivePrivacy` supplies the challenge field. |

## Fixed-key schedule

The construction indexes each fixed-key permutation by an adaptor kind, a coordinate bit
position, and a slot (`Pipeline.FixedKeyIndex`). One bucket holds one label pair. The 91 output
digits share the bucket and differ by an injective tweak on the permutation input
(`Pipeline.FixedKeyLocation.tweak`). A bucket has three hash permutations and two pad
permutations. Each permutation therefore serves one branch of every gate in its bucket, and no
gate reads two labels through one permutation.

The schedule uses the bucketing method in `gc_rpm_proof.tex`.
The entry changes the concrete schedule and feed-forward formula.
A point permutation serves 91 gates.
A curve permutation serves one gate.

The field encoding biases the pad blocks.
The active collision proof includes this bias.

## Adaptive privacy

The Kriterion obligation uses two adaptive query phases and the original uniform random tape.
The proof covers valid and invalid inputs.

- `ValidEndpointRatio.lean` bounds the valid source by the real transcript.
- `InvalidGhostEndpoint.lean` bounds the invalid source by the real transcript.
- `ConcreteSmallSourceRatio.lean` combines both input cases for every small query budget.
- `AdaptiveSourceBound.lean` combines the source ratio with the ideal transcript bound.
- `AdaptiveLossAccounting.lean` places the full error below the 100-bit envelope.
- The large-budget case uses the bound of one on the decision advantage.

## Paper correspondence

The comparison uses BaBe.latex commit `e2dcf4d540b2708e13cd21090df759051119a116`.

| Item | Paper | Entry |
| --- | --- | --- |
| Digits | 92 | 91 |
| Point adaptor families in the count | 9 | 13 |
| Slots per bucket | 3 | 3 hash slots and 2 separate pad slots |
| Point permutations in the count | 6,858 | 16,510 |
| Curve permutations in the count | 3,810 | 6,350 |
| Block formula | `π(L XOR t) XOR (L XOR t)` | `π(L XOR t) XOR L` |

[PaperConstruction.lean](Proof/PaperConstruction.lean) proves the exact block and byte relations.
The field relation keeps the XOR inside the reduction modulo the field prime.
An output translation of a uniform permutation equates the block formulas for one fixed tweak.
One shared translation cannot equate the formulas for two different tweaks and every label.
The repository therefore proves this variant directly.
It does not claim that the two shared-bucket constructions have identical distributions.

| Paper component | Checked entry component |
| --- | --- |
| Point masks and output reconstruction | `PointDistribution.lean`, `OutputRowDistribution.lean` |
| Field-mask substitutions | `MaskRandomizerDistribution.lean`, `CircuitMaskDistribution.lean` |
| Bit-adaptor permutation programming | `Gate.lean`, `AdaptivePermutationRatio.lean` |
| Curve check and EncPRF link | `InvalidGhostEndpoint.lean`, `EncPRFTranscript.lean` |
| H-coefficient transcript comparison | `HCoefficient.lean`, `ConcreteSmallSourceRatio.lean` |
| Full concrete error | `AdaptiveArithmetic.lean`, `AdaptiveLossAccounting.lean` |
| Three oracle-query phases | `ThreePhasePrivacy.lean` |

[ThreePhasePrivacy.lean](Proof/ThreePhasePrivacy.lean) defines queries before the public table, between the table and labels, and after the labels.
Lean proves that the three-phase games have the distributions of the compiled two-phase games.
Lean proves the 100-bit bound with total work `q0 + q1 + q2 + 1`.
The circuit and auxiliary input are fixed independently of the oracle sample.
The theorem does not permit oracle-dependent circuit selection.
The ideal simulator can sample hidden coins early.
It keeps the table private during the first phase and retains all oracle state updates.

## Simulator

The simulator samples 90 free points and 91 nonzero homogeneous scales.
It samples all free gate targets.
It changes one low target in each coordinate to fix the required result.
The operation preserves the public table.

The proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
The proof does not assume adaptive privacy.

The paper also requires an efficient simulator.
The Kriterion simulator type contains probability distributions and no execution-cost field.
The computability of `Submission.solution` does not establish simulator efficiency.
[SimulatorPrivacy.lean](Proof/SimulatorPrivacy.lean) proves the exact sparse simulator's three-phase privacy.
[SimulatorFinitePrivacy.lean](Proof/SimulatorFinitePrivacy.lean) checks the aborting comparison experiment.
[SimulatorTotalImplementation.lean](Proof/SimulatorTotalImplementation.lean) proves privacy for the total finite implementation.
The finite sampler uses at most 256 attempts for each integer draw.
Its error relative to the exact ideal game is at most `(1813496 + q) / 2^256`.
[SimulatorFiniteArithmetic.lean](Proof/SimulatorFiniteArithmetic.lean) proves that this error preserves the 100-bit bound.

The executable oracle state stores sparse permutations, hash entries, and query records.
The conditional completion distributions appear only in the proof.
The executable simulator does not sample complete oracle functions.
[SimulatorSampling.lean](Proof/SimulatorSampling.lean) checks the private sampler and its random-draw count.
[SimulatorMachineCost.lean](Proof/SimulatorMachineCost.lean) checks sparse execution and storage bounds.
The executable implementation uses retained arrays and finite retry sampling.
[SimulatorTotalImplementation.lean](Proof/SimulatorTotalImplementation.lean) connects its exact game to the original ideal game.
Its finite game preserves the 100-bit privacy bound.
The cost theorem starts with empty sparse oracles.
It derives the state bounds after all three query phases.
It includes fallback private draws and fallback external queries.

The cost model counts source-level primitives.
Field operations and group operations each count as one primitive.
The local counters also count word, index, array, list, record, and comparison operations.
The rejection counter charges four control operations per sampled bit block.
The total encoder records its completed local work.
An integer draw selects zero if every attempt fails.
The simulator then continues execution.
The model excludes proof erasure, Lean compiler allocation, serialization, and the adversary's private computation.

For total adversary query budget `q`, define `n = q + 905765`, `D = 1813496 + q`, and `B = D * 257 * 256`.
The checked bounds have these forms:

| Resource | Bound |
| --- | --- |
| Private local work | 53,997,367 local operations |
| Sparse oracle work | `n * (10 * n + 16)` |
| Supplied fair bits | `B` |
| Rejection-control allowance | `4 * B` |
| Fallback selection allowance | `D` |

These bounds apply to the fixed BN254 instance.
They give a strict polynomial bound in the query budget under the stated primitive model.
They do not establish an asymptotic security family or a Lean instruction-count bound.
The verifier and benchmark use the computable `Submission.solution` entry.

## Source

The paper source is
<https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116>.
