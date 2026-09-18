# Source record

This repository imports the ArgoMAC source, proofs, and tests from [Kriterion-cc/kriterion-challenge](https://github.com/Kriterion-cc/kriterion-challenge/tree/3322a36abd962aa5960e65d7f2d8b9f72478d1e3/bn254-scalar-multiplication/argomac-lean).
The imported commit is `3322a36abd962aa5960e65d7f2d8b9f72478d1e3`.
The source path is `bn254-scalar-multiplication/argomac-lean`.
The following record describes the source history in that repository.

The original source comes from https://github.com/SebastianElvis/argomac-lean.
The original baseline commit is `711689cd0253edece8d0c617ad5a7afaa937673e`.
The last source commit before this copy is `6544216f4c50bf846775fa27f1556bdf7e064bf7`.
This copy also includes the pending proof changes from that checkout.
The challenge repository records further changes in the same commits as the challenge.

The challenge's `baseline` field selects its `argomac-lean` directory.
The challenge's acceptance test uses that directory.
`Submission.solution` proves the complete adaptive privacy obligation.

The copy excludes Git metadata, dependency downloads, and build output.
The local Lake configuration pins the challenge library to the imported Git commit.
The source configuration used the challenge library in `..`.
The local test target lists every imported test module.

The source check covers all 956 source files from the previous checkout.
The local copy contains every file from that set.
The local copy also contains the later proof fixes.
The previous `BudgetAudit.lean` is now `tests/ProofAudit.lean`.
The memory layout proofs from `LayoutCheck.lean` already appear in `Proof/Privacy/Simulator/Arithmetic/MemoryLayout.lean`.
The protocol checks from `ProtocolCheck.lean` already appear in `Proof/Privacy/Simulator/Arithmetic/ParsedProgramSource.lean`.

The challenge's `argomac-lean/` directory is its only starter.
The challenge repository has no separate `starter/` directory.
The challenge repository contains one copy of the ArgoMAC source.
