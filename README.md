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
| `adaptivePrivacy` | Open. `Proof/Security.lean` reduces it to one trace transport and one change bound per adversary. The inherited simulator is not yet sound: `IdealEncoding.outputTargets` returns the output point and 90 points at infinity, and `ProgrammingBridge.coordinateLowTarget` returns 0 for every bit but one. The evaluator observes both, and the real world returns uniform values there. The simulator must sample 90 free rows and one uniform target per gate, and adjust one value per digit adaptor, as `gc_privacy_proofs.tex` does for `GC_1` and `GC_2`. |

## Fixed-key schedule

The construction indexes each fixed-key permutation by an adaptor kind, a coordinate bit
position, and a slot (`Pipeline.FixedKeyIndex`). One bucket holds one label pair. The 91 output
digits share the bucket and differ by an injective tweak on the permutation input
(`Pipeline.FixedKeyLocation.tweak`). A bucket has three hash permutations and two pad
permutations. Each permutation therefore serves one branch of every gate in its bucket, and no
gate reads two labels through one permutation.

This is the paper's bucketing from `gc_rpm_proof.tex`. The collision term per permutation is
`Q ^ 2 / 2 + 2 * Q * q`. Summed over `16,510` point permutations with `Q = 91` and `6,350` curve
permutations with `Q = 1`, the `q`-free part is `2 ^ 27.03`. `Security.bucketedCTPRFHas100Bits`
proves the work-per-advantage bound at 100 bits with about two bits of margin.

## Source

The paper source is
<https://github.com/babylonlabs-io/BaBe.latex/tree/e2dcf4d540b2708e13cd21090df759051119a116>.
