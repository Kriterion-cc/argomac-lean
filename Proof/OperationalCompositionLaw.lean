/-
This file composes independent oracle completion kernels.
The composition preserves adaptive correlations within each component.
-/

import Proof.OperationalOracleLaw

namespace Kriterion.ArgoMAC.Security.OperationalOracle

open Cryptography

noncomputable section

/-- A sum request selects one of two oracle components. -/
abbrev sumSpec (left right : OracleSpec) : OracleSpec where
  Query := left.Query ⊕ right.Query
  Answer
    | .inl query => left.Answer query
    | .inr query => right.Answer query

/-- The eager handler updates only the component selected by the request. -/
def sumEager {left right : OracleSpec} {Left Right : Type}
    (leftHandler : OracleHandler left Left) (rightHandler : OracleHandler right Right) :
    OracleHandler (sumSpec left right) (Left × Right)
  | .inl query, state =>
      let answer := leftHandler query state.1
      (answer.1, answer.2, state.2)
  | .inr query, state =>
      let answer := rightHandler query state.2
      (answer.1, state.1, answer.2)

/-- The sampled handler also updates only the selected component. -/
def sumSampled {left right : OracleSpec} {Left Right : Type}
    (leftHandler : ∀ query, Left → PMF (left.Answer query × Left))
    (rightHandler : ∀ query, Right → PMF (right.Answer query × Right)) :
    ∀ query : (sumSpec left right).Query,
      (Left × Right) → PMF ((sumSpec left right).Answer query × (Left × Right))
  | .inl query, state =>
      (leftHandler query state.1).map (fun answer => (answer.1, answer.2, state.2))
  | .inr query, state =>
      (rightHandler query state.2).map (fun answer => (answer.1, state.1, answer.2))

/-- This kernel samples independent completions for the two stored states. -/
def productKernel {SparseLeft SparseRight EagerLeft EagerRight : Type}
    (leftKernel : SparseLeft → PMF EagerLeft) (rightKernel : SparseRight → PMF EagerRight)
    (state : SparseLeft × SparseRight) : PMF (EagerLeft × EagerRight) :=
  (leftKernel state.1).bind (fun left =>
    (rightKernel state.2).map (fun right => (left, right)))

/-- The two local step laws imply the complete sum-oracle step law. -/
theorem productKernel_step {left right : OracleSpec}
    {SparseLeft SparseRight EagerLeft EagerRight : Type}
    (leftEager : OracleHandler left EagerLeft) (rightEager : OracleHandler right EagerRight)
    (leftSampled : ∀ query, SparseLeft → PMF (left.Answer query × SparseLeft))
    (rightSampled : ∀ query, SparseRight → PMF (right.Answer query × SparseRight))
    (leftKernel : SparseLeft → PMF EagerLeft) (rightKernel : SparseRight → PMF EagerRight)
    (leftStep : ∀ query state,
      (leftKernel state).map (leftEager query) =
        (leftSampled query state).bind (fun answer =>
          (leftKernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    (rightStep : ∀ query state,
      (rightKernel state).map (rightEager query) =
        (rightSampled query state).bind (fun answer =>
          (rightKernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    (query : (sumSpec left right).Query) (state : SparseLeft × SparseRight) :
    (productKernel leftKernel rightKernel state).map (sumEager leftEager rightEager query) =
      (sumSampled leftSampled rightSampled query state).bind (fun answer =>
        (productKernel leftKernel rightKernel answer.2).map
          (fun eagerState => (answer.1, eagerState))) := by
  cases query with
  | inl query =>
      have law := congrArg
        (fun distribution : PMF (left.Answer query × EagerLeft) =>
          distribution.bind (fun answer => (rightKernel state.2).map
            (fun eagerRight => (answer.1, answer.2, eagerRight)))) (leftStep query state.1)
      simpa only [productKernel, sumEager, sumSampled, PMF.map_bind, PMF.map_comp,
        PMF.bind_map, PMF.bind_bind, Function.comp_def] using law
  | inr query =>
      have law := congrArg
        (fun distribution : PMF (right.Answer query × EagerRight) =>
          (leftKernel state.1).bind (fun eagerLeft => distribution.map
            (fun answer => (answer.1, eagerLeft, answer.2)))) (rightStep query state.2)
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at law
      simp only [productKernel, sumEager, sumSampled, PMF.map_bind, PMF.map_comp,
        PMF.bind_map, Function.comp_def]
      exact law.trans (PMF.bind_comm _ _ _)

/-- Adaptive programs can interleave both components without any additional premise. -/
theorem productKernel_adaptive_joint {left right : OracleSpec}
    {SparseLeft SparseRight EagerLeft EagerRight Result : Type}
    (leftEager : OracleHandler left EagerLeft) (rightEager : OracleHandler right EagerRight)
    (leftSampled : ∀ query, SparseLeft → PMF (left.Answer query × SparseLeft))
    (rightSampled : ∀ query, SparseRight → PMF (right.Answer query × SparseRight))
    (leftKernel : SparseLeft → PMF EagerLeft) (rightKernel : SparseRight → PMF EagerRight)
    (leftStep : ∀ query state,
      (leftKernel state).map (leftEager query) =
        (leftSampled query state).bind (fun answer =>
          (leftKernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    (rightStep : ∀ query state,
      (rightKernel state).map (rightEager query) =
        (rightSampled query state).bind (fun answer =>
          (rightKernel answer.2).map (fun eagerState => (answer.1, eagerState))))
    {budget : Nat} (program : OracleProgram (sumSpec left right) Result budget)
    (state : SparseLeft × SparseRight) :
    (productKernel leftKernel rightKernel state).bind
        (fun eagerState => program.run (sumEager leftEager rightEager) eagerState) =
      (runSampled (sumSampled leftSampled rightSampled) program state).bind (fun output =>
        (productKernel leftKernel rightKernel output.2).map
          (fun eagerState => (output.1, eagerState))) :=
  adaptive_joint_law (sumEager leftEager rightEager) (sumSampled leftSampled rightSampled)
    (productKernel leftKernel rightKernel)
    (productKernel_step leftEager rightEager leftSampled rightSampled
      leftKernel rightKernel leftStep rightStep) program state

end

end Kriterion.ArgoMAC.Security.OperationalOracle
