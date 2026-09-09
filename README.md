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

`Submission.solutionOf` closes every field of `Kriterion.Solution` except `adaptivePrivacy`.
It takes that one proof as its argument. `Submission.AdaptivePrivacy` states it.

| Field | Where |
| --- | --- |
| `randomnessFromSeed` | `Construction/ArgoMAC/Seed.lean` derives the complete tape from the seed. It proves the clamped offset with plain `ZMod` arithmetic and a Bezout argument, without the field certificate. |
| `perfectCorrectness` | `Proof/RCBComplete.lean` with the termination instance in `Proof/Base7Termination.lean`. |
| `lamportCompatible` | `Proof/Lamport.lean`. |
| `adaptivePrivacy` | The full transcript bound remains open. Lean checks the circuit mask transport, point and scale laws, permutation counts, gate programming, and hash-query bounds. |

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
The active collision proof uses this bias.
`Security.adaptiveErrorEnvelope_has100Bits` checks a conservative integer envelope at 100 bits.
The final transcript proof must place the actual advantage below that envelope.
Lean checks the full shared hash source and adaptive output-row bound.
Lean checks the actual hidden-hash link bound `q/p + (508 + 4q)/2^128`.
The transcript factors retain both query phases and allow valid replay after encoding.
Lean checks the point birthday and adaptive prequery bounds.
Lean connects the full source to the actual ideal simulator transcript.
The invalid source keeps its curve request.
Lean checks the joint bad-source bound with the actual retained rows.
Lean checks the real-source density and weighted hidden-hash comparison.
Lean checks the complete hash-fiber transport and its invalid-source collision flag.
Lean checks the exact shared ghost-source expansion.
Lean checks the normalized invalid-source product comparison.
The source comparison retains every adaptive input choice.
Lean checks the valid-source product-density bound and its complete good-tag sum.
Lean bounds the invalid ghost source by the normalized missing-query source.
Lean factors that source into both adversary phases and its exact source event.
Every nonzero good transcript supplies compatible reference states and the query bound.
Lean checks the common prefix history for every retained source.
Lean checks the exact source reindex and the actual real transcript phase factors.
Lean bounds the full linked tag sum by the actual public source event.
The final valid-input and invalid-input mass comparisons remain open.

## Simulator

The simulator samples 90 free points and 91 nonzero homogeneous scales.
It samples all free gate targets.
It changes one low target in each coordinate to fix the required result.
The operation preserves the public table.

The new distribution lemmas use the standard Lean axioms.
They do not assume adaptive privacy.
`Submission.solution` remains absent until the full privacy theorem passes Lean.

## Source

The paper source is
<https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116>.
