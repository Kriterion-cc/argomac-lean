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

The construction and proof import the pinned Kriterion challenge library.
The library uses Lean 4.33.1, Mathlib 4.33.1, and VCV-io.
Kriterion includes this repository as a submodule.
You can run the full build from its challenge directory:

```sh
cd examples/bn254-scalar-multiplication
lake exe cache get
lake build
```

The verifier generates the same library and entry layout for each submission.

## Status

`Submission.solution` supplies every field of `Kriterion.Solution`.
`Submission.adaptivePrivacy` proves the unchanged universal 100-bit privacy obligation.

| Field | Where |
| --- | --- |
| `randomness` | `Construction/ArgoMAC/Seed.lean` derives the complete tape from the seed. It proves the clamped offset with plain `ZMod` arithmetic and a Bezout argument, without the field certificate. |
| `ciphertextSize` | `Construction/ArgoMAC/Encoding.lean` proves the complete public encoding has 9,699,931 bytes. |
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

The schedule follows `gc_rpm_proof.tex`.
A point permutation serves 91 gates.
A curve permutation serves one gate.

The field encoding biases the pad blocks.
The active collision proof includes this bias.

## Adaptive privacy

The proof keeps both adaptive query phases and the uniform random tape.
VCV-io supplies the uniform sampler and shared oracle interpreter.
The interpreter preserves arbitrary private samples and the indexed query budget.
The proof uses one interpreter for ordinary runs, traced runs, and paired states.
VCV-io state projections prove both coupling marginals.
Regression theorems preserve the execution distribution and query order.
The challenge library supplies the permutation counting and fresh programming lemmas.
The proof covers valid and invalid inputs.

- `ValidEndpointRatio.lean` bounds the valid source by the real transcript.
- `InvalidGhostEndpoint.lean` bounds the invalid source by the real transcript.
- `ConcreteSmallSourceRatio.lean` combines both input cases for every small query budget.
- `AdaptiveSourceBound.lean` combines the source ratio with the ideal transcript bound.
- `AdaptiveLossAccounting.lean` places the full error below the 100-bit envelope.
- The large-budget case uses the bound of one on the decision advantage.

## Simulator

The simulator samples 90 free points and 91 nonzero homogeneous scales.
It samples all free gate targets.
It changes one low target in each coordinate to fix the required result.
The operation preserves the public table.

The proof uses only `propext`, `Classical.choice`, and `Quot.sound`.
The proof does not assume adaptive privacy.
The verifier and byte metric use the computable `Submission.solution` entry.

## Source

The paper source is
<https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116>.
