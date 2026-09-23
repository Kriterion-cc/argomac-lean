import Construction.Garbling
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Tactic.LinearCombination
import Security.Correctness
import Architect

namespace Kriterion.ArgoMAC.RCBComplete

open BN254

private theorem twoNe : (2 : BaseField) ≠ 0 := by decide

private theorem fourNe : (4 : BaseField) ≠ 0 := by decide

private theorem eightNe : (8 : BaseField) ≠ 0 := by decide

abbrev addX (a b u v : BaseField) : BaseField :=
  Coordinates.algorithmX { x := a, y := b } { x := u, y := v }

abbrev addY (a b u v : BaseField) : BaseField :=
  Coordinates.algorithmY { x := a, y := b } { x := u, y := v }

abbrev addZ (a b u v : BaseField) : BaseField :=
  Coordinates.algorithmZ { x := a, y := b } { x := u, y := v }

def output (a b u v : BaseField) : Fin 3 → BaseField :=
  ![addX a b u v, addY a b u v, addZ a b u v]

theorem outputOnCurve
    (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) :
    (addY a b u v) ^ 2 * addZ a b u v =
      (addX a b u v) ^ 3 + 3 * (addZ a b u v) ^ 3 := by
  simpa only [addX, addY, addZ, Coordinates.evaluateX, Coordinates.evaluateY,
    Coordinates.evaluateZ] using
    Coordinates.evaluatedOnCurve { x := a, y := b } { x := u, y := v }
      offsetOnCurve inputOnCurve

theorem outputEquation
    (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) :
    curve.toProjective.Equation (output a b u v) := by
  rw [WeierstrassCurve.Projective.equation_iff]
  simpa [output, curve, sub_eq_zero] using
    outputOnCurve a b u v offsetOnCurve inputOnCurve

theorem noAffineYZero [FieldCertificate] [GroupCertificate]
    (input : AffineInput) (inputOnCurve : OnCurve input) : input.y ≠ 0 := by
  intro yZero
  let valid : curve.toAffine.Nonsingular input.x input.y :=
    (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
      ((equation_iff_onCurve input).mpr inputOnCurve)
  let point : Point := .some _ _ valid
  have ySelfNeg : input.y = curve.toAffine.negY input.x input.y := by
    simp [WeierstrassCurve.Affine.negY, curve, yZero]
  have twoPoint : 2 • point = 0 := by
    simpa [two_nsmul] using WeierstrassCurve.Affine.Point.add_self_of_Y_eq ySelfNeg
  have groupOrder := GroupCertificate.groupOrder point
  have modulusOdd : scalarFieldModulus = 2 * (scalarFieldModulus / 2) + 1 := by
    decide
  rw [modulusOdd, add_nsmul, mul_nsmul, twoPoint, nsmul_zero, zero_add, one_nsmul]
    at groupOrder
  exact WeierstrassCurve.Affine.Point.some_ne_zero valid groupOrder

def differenceCoordinates [FieldCertificate] (a b u v : BaseField) : AffineInput :=
  let slope := curve.toAffine.slope a u b (-v)
  { x := curve.toAffine.addX a u slope
    y := curve.toAffine.addY a u b slope }

theorem differenceOnCurve [FieldCertificate] (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) (xDifferent : a ≠ u) :
    OnCurve (differenceCoordinates a b u v) := by
  have offsetEquation := (equation_iff_onCurve { x := a, y := b }).mpr offsetOnCurve
  have inputNegEquation : curve.toAffine.Equation u (-v) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [curve, zero_mul, add_zero, neg_sq]
    exact inputOnCurve
  apply (equation_iff_onCurve (differenceCoordinates a b u v)).mp
  exact WeierstrassCurve.Affine.equation_add offsetEquation inputNegEquation
    (fun exceptional => xDifferent exceptional.1)

theorem differenceYRelation [FieldCertificate] (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) (xDifferent : a ≠ u) :
    (differenceCoordinates a b u v).y * (a - u) ^ 3 = -addZ a b u v := by
  simp only [differenceCoordinates, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, curve, zero_mul, add_zero, sub_zero]
  rw [WeierstrassCurve.Affine.slope_of_X_ne xDifferent]
  field_simp [sub_ne_zero.mpr xDifferent]
  simp only [OnCurve] at offsetOnCurve inputOnCurve
  linear_combination (norm := (simp only [addZ, Coordinates.algorithmZ]; ring))
    (-2 * b - v) * inputOnCurve + (-b - 2 * v) * offsetOnCurve

theorem addZNeZeroOfXNe [FieldCertificate] [GroupCertificate] (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) (xDifferent : a ≠ u) :
    addZ a b u v ≠ 0 := by
  intro zZero
  have yProductZero :
      (differenceCoordinates a b u v).y * (a - u) ^ 3 = 0 := by
    rw [differenceYRelation a b u v offsetOnCurve inputOnCurve xDifferent, zZero, neg_zero]
  have differenceYZero : (differenceCoordinates a b u v).y = 0 :=
    (mul_eq_zero.mp yProductZero).resolve_right
      (pow_ne_zero 3 (sub_ne_zero.mpr xDifferent))
  exact noAffineYZero (differenceCoordinates a b u v)
    (differenceOnCurve a b u v offsetOnCurve inputOnCurve xDifferent) differenceYZero

def doubleCoordinates [FieldCertificate] (a b : BaseField) : AffineInput :=
  let slope := curve.toAffine.slope a a b b
  { x := curve.toAffine.addX a a slope
    y := curve.toAffine.addY a a b slope }

theorem doubleOnCurve [FieldCertificate] [GroupCertificate] (a b : BaseField)
    (pointOnCurve : OnCurve { x := a, y := b }) :
    OnCurve (doubleCoordinates a b) := by
  have bNonzero := noAffineYZero { x := a, y := b } pointOnCurve
  have bNotNeg : b ≠ -b := by
    intro equalNeg
    have twiceZero : 2 * b = 0 := by linear_combination equalNeg
    exact bNonzero ((mul_eq_zero.mp twiceZero).resolve_left twoNe)
  have pointEquation := (equation_iff_onCurve { x := a, y := b }).mpr pointOnCurve
  apply (equation_iff_onCurve (doubleCoordinates a b)).mp
  exact WeierstrassCurve.Affine.equation_add pointEquation pointEquation
    (by simpa [curve, WeierstrassCurve.Affine.negY] using bNotNeg)

theorem doubleYRelation [FieldCertificate] [GroupCertificate] (a b : BaseField)
    (pointOnCurve : OnCurve { x := a, y := b }) :
    (doubleCoordinates a b).y * (2 * b) ^ 3 = addY a b a (-b) := by
  have bNonzero := noAffineYZero { x := a, y := b } pointOnCurve
  have bNotNeg : b ≠ -b := by
    intro equalNeg
    have twiceZero : 2 * b = 0 := by linear_combination equalNeg
    exact bNonzero ((mul_eq_zero.mp twiceZero).resolve_left twoNe)
  have slopeDouble : curve.toAffine.slope a a b b = 3 * a ^ 2 / (2 * b) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl]
    · simp [curve, WeierstrassCurve.Affine.negY, two_mul]
    · simpa [curve, WeierstrassCurve.Affine.negY] using bNotNeg
  simp only [doubleCoordinates]
  rw [slopeDouble]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, curve, zero_mul, add_zero, sub_zero]
  field_simp [bNonzero, twoNe]
  simp only [OnCurve] at pointOnCurve
  linear_combination (norm := (simp only [addY, Coordinates.algorithmY]; ring))
    (27 * a ^ 3 - 9 * b ^ 2 - 27) * pointOnCurve

theorem doublingZ (a b : BaseField) (pointOnCurve : OnCurve { x := a, y := b }) :
    addZ a b a b = 8 * b ^ 3 := by
  simp only [OnCurve] at pointOnCurve
  linear_combination (norm := (simp only [addZ, Coordinates.algorithmZ]; ring))
    -6 * b * pointOnCurve

theorem outputNonzero [FieldCertificate] [GroupCertificate] (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) :
    output a b u v ≠ 0 := by
  intro outputZero
  have outputZZero : addZ a b u v = 0 := by
    have := congrFun outputZero 2
    simpa [output] using this
  by_cases xDifferent : a ≠ u
  · exact addZNeZeroOfXNe a b u v offsetOnCurve inputOnCurve xDifferent outputZZero
  · have xEqual : u = a := (Classical.not_not.mp xDifferent).symm
    subst u
    have squareEqual : v ^ 2 = b ^ 2 := by
      simp only [OnCurve] at offsetOnCurve inputOnCurve
      linear_combination inputOnCurve - offsetOnCurve
    have productZero : (v - b) * (v + b) = 0 := by
      linear_combination squareEqual
    rcases mul_eq_zero.mp productZero with sameY | oppositeY
    · have vEqual : v = b := sub_eq_zero.mp sameY
      subst v
      rw [doublingZ a b offsetOnCurve] at outputZZero
      have bNonzero := noAffineYZero { x := a, y := b } offsetOnCurve
      have bCubeZero : b ^ 3 = 0 := (mul_eq_zero.mp outputZZero).resolve_left eightNe
      exact bNonzero (eq_zero_of_pow_eq_zero bCubeZero)
    · have vEqual : v = -b := eq_neg_of_add_eq_zero_left oppositeY
      subst v
      have outputYZero : addY a b a (-b) = 0 := by
        have := congrFun outputZero 1
        simpa [output] using this
      have doubleYProductZero : (doubleCoordinates a b).y * (2 * b) ^ 3 = 0 := by
        rw [doubleYRelation a b offsetOnCurve, outputYZero]
      have bNonzero := noAffineYZero { x := a, y := b } offsetOnCurve
      have doubleYZero : (doubleCoordinates a b).y = 0 :=
        (mul_eq_zero.mp doubleYProductZero).resolve_right
          (pow_ne_zero 3 (mul_ne_zero twoNe bNonzero))
      exact noAffineYZero (doubleCoordinates a b) (doubleOnCurve a b offsetOnCurve) doubleYZero

@[blueprint "RCBComplete.outputNonsingular"
  (statement := /-- For two on-curve points $(a, b)$ and $(u, v)$, the output $(X, Y, Z)$ of the addition formula of
    Eqs.~29--31 is a nonsingular point of the projective BN254 curve. -/)
  (title := /-- BABE Eqs.~29--31 -/)]
theorem outputNonsingular [FieldCertificate] [GroupCertificate] (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) :
    curve.toProjective.Nonsingular (output a b u v) := by
  /-- The output satisfies the projective curve equation and is not the zero vector. If $Z = 0$, then
    $X = 0$ and $Y \neq 0$, so the point is the nonsingular point at infinity. If $Z \neq 0$, the
    affine point satisfies the curve equation, and the nonzero discriminant gives nonsingularity. -/
  have equation : curve.toProjective.Equation (output a b u v) :=
    outputEquation a b u v (by simpa [OnCurve] using offsetOnCurve)
      (by simpa [OnCurve] using inputOnCurve)
  have nonzero : output a b u v ≠ 0 :=
    outputNonzero a b u v offsetOnCurve inputOnCurve
  by_cases zZero : addZ a b u v = 0
  · have xZero : addX a b u v = 0 := by
      have := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero equation
        (by simpa [output] using zZero)
      simpa [output] using this
    have yNonzero : addY a b u v ≠ 0 := by
      intro yZero
      apply nonzero
      funext index
      fin_cases index <;> simp [output, xZero, yZero, zZero]
    apply (WeierstrassCurve.Projective.nonsingular_of_Z_eq_zero
      (by simpa [output] using zZero)).mpr
    refine ⟨equation, Or.inr ?_⟩
    simp [output, curve, xZero, yNonzero]
  · apply (WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero
      (by simpa [output] using zZero)).mpr
    apply (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
    exact (WeierstrassCurve.Projective.equation_of_Z_ne_zero
      (by simpa [output] using zZero)).mp equation

def affinePoint [FieldCertificate] (input : AffineInput) (inputOnCurve : OnCurve input) : Point :=
  .some input.x input.y <| (curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero discriminantNeZero).mp
    ((equation_iff_onCurve input).mpr inputOnCurve)

theorem recoveredXOfXNe [FieldCertificate] [GroupCertificate] (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) (xDifferent : a ≠ u) :
    addX a b u v / addZ a b u v =
      curve.toAffine.addX a u (curve.toAffine.slope a u b v) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne xDifferent]
  simp only [WeierstrassCurve.Affine.addX, curve, zero_mul, add_zero, sub_zero]
  field_simp [addZNeZeroOfXNe a b u v offsetOnCurve inputOnCurve xDifferent,
    sub_ne_zero.mpr xDifferent]
  simp only [OnCurve] at offsetOnCurve inputOnCurve
  linear_combination (norm := (simp only [addX, addZ, Coordinates.algorithmX, Coordinates.algorithmZ]; ring))
    (2 * a ^ 3 * b + 3 * a ^ 2 * b * u - 3 * a ^ 2 * u * v -
      3 * a * b * u ^ 2 + b ^ 3 + b ^ 2 * v - b * v ^ 2 + 6 * b - 9 * v) *
        inputOnCurve +
      (-3 * a ^ 2 * u * v - 3 * a * b * u ^ 2 + 3 * a * u ^ 2 * v -
        b ^ 2 * v + b * u ^ 3 - 6 * b + 3 * u ^ 3 * v + 9 * v) * offsetOnCurve

theorem recoveredYOfXNe [FieldCertificate] [GroupCertificate] (a b u v : BaseField)
    (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) (xDifferent : a ≠ u) :
    addY a b u v / addZ a b u v =
      curve.toAffine.addY a u b (curve.toAffine.slope a u b v) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne xDifferent]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, curve,
    zero_mul, add_zero, sub_zero]
  field_simp [addZNeZeroOfXNe a b u v offsetOnCurve inputOnCurve xDifferent,
    sub_ne_zero.mpr xDifferent]
  simp only [OnCurve] at offsetOnCurve inputOnCurve
  linear_combination (norm := (simp only [addY, addZ, Coordinates.algorithmY, Coordinates.algorithmZ]; ring))
    (6 * a ^ 5 * u - 9 * a ^ 4 * u ^ 2 + 2 * a ^ 3 * b ^ 2 +
      2 * a ^ 3 * b * v + 18 * a ^ 3 - 15 * a ^ 2 * b ^ 2 * u +
      6 * a ^ 2 * b * u * v - 3 * a ^ 2 * u * v ^ 2 - 36 * a ^ 2 * u +
      15 * a * b ^ 2 * u ^ 2 - 3 * a * b * u ^ 2 * v - 2 * b ^ 4 +
      2 * b ^ 2 * v ^ 2 + 6 * b ^ 2 - b * v ^ 3 + 15 * b * v -
      9 * v ^ 2 - 27) * inputOnCurve +
      (3 * a ^ 2 * b * u * v - 6 * a ^ 2 * u ^ 4 - 45 * a ^ 2 * u +
        3 * a * b ^ 2 * u ^ 2 - 6 * a * b * u ^ 2 * v + 9 * a * u ^ 5 +
        81 * a * u ^ 2 + b ^ 3 * v - 2 * b ^ 2 * u ^ 3 + 3 * b ^ 2 -
        2 * b * u ^ 3 * v - 15 * b * v - 18 * u ^ 3 + 27) * offsetOnCurve

theorem recoveredXDouble [FieldCertificate] [GroupCertificate] (a b : BaseField)
    (pointOnCurve : OnCurve { x := a, y := b }) :
    addX a b a b / addZ a b a b = (doubleCoordinates a b).x := by
  rw [doublingZ a b pointOnCurve]
  have bNonzero := noAffineYZero { x := a, y := b } pointOnCurve
  have bNotNeg : b ≠ -b := by
    intro equalNeg
    have twiceZero : 2 * b = 0 := by linear_combination equalNeg
    exact bNonzero ((mul_eq_zero.mp twiceZero).resolve_left twoNe)
  have slopeDouble : curve.toAffine.slope a a b b = 3 * a ^ 2 / (2 * b) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl]
    · simp [curve, WeierstrassCurve.Affine.negY, two_mul]
    · simpa [curve, WeierstrassCurve.Affine.negY] using bNotNeg
  simp only [doubleCoordinates]
  rw [slopeDouble]
  simp only [WeierstrassCurve.Affine.addX, curve, zero_mul, add_zero, sub_zero]
  field_simp [bNonzero, twoNe, eightNe]
  simp only [OnCurve] at pointOnCurve
  linear_combination (norm := (simp only [addX, Coordinates.algorithmX]; ring))
    72 * a * b * pointOnCurve

theorem recoveredYDouble [FieldCertificate] [GroupCertificate] (a b : BaseField)
    (pointOnCurve : OnCurve { x := a, y := b }) :
    addY a b a b / addZ a b a b = (doubleCoordinates a b).y := by
  rw [doublingZ a b pointOnCurve]
  have bNonzero := noAffineYZero { x := a, y := b } pointOnCurve
  have bNotNeg : b ≠ -b := by
    intro equalNeg
    have twiceZero : 2 * b = 0 := by linear_combination equalNeg
    exact bNonzero ((mul_eq_zero.mp twiceZero).resolve_left twoNe)
  have slopeDouble : curve.toAffine.slope a a b b = 3 * a ^ 2 / (2 * b) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl]
    · simp [curve, WeierstrassCurve.Affine.negY, two_mul]
    · simpa [curve, WeierstrassCurve.Affine.negY] using bNotNeg
  simp only [doubleCoordinates]
  rw [slopeDouble]
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY, curve,
    zero_mul, add_zero, sub_zero]
  field_simp [bNonzero, twoNe, eightNe]
  simp only [OnCurve] at pointOnCurve
  linear_combination (norm := (simp only [addY, Coordinates.algorithmY]; ring))
    (-216 * a ^ 3 + 72 * b ^ 2 + 216) * pointOnCurve

@[blueprint "RCBComplete.outputRepresentsSum"
  (statement := /-- For two on-curve points $(a, b)$ and $(u, v)$, the affine form of the output of the addition
    formula equals the group sum $(a, b) + (u, v)$ in $\mathbb{G}_1$. -/)
  (title := /-- BABE Eqs.~29--31 -/)]
theorem outputRepresentsSum [FieldCertificate] [GroupCertificate]
    (a b u v : BaseField) (offsetOnCurve : OnCurve { x := a, y := b })
    (inputOnCurve : OnCurve { x := u, y := v }) :
    WeierstrassCurve.Projective.Point.toAffine curve.toProjective (output a b u v) =
      affinePoint { x := a, y := b } offsetOnCurve +
        affinePoint { x := u, y := v } inputOnCurve := by
  /-- Split on whether $a \neq u$. If they differ, $Z \neq 0$, and the recovered coordinates match the
    affine addition formula. If $a = u$, the $y$ coordinates are equal or opposite. Equal $y$
    coordinates give the doubling formula with $Z \neq 0$. Opposite $y$ coordinates give $Z = 0$,
    the point at infinity, and the affine sum is also $0$. -/
  have outputValid := outputNonsingular a b u v offsetOnCurve inputOnCurve
  by_cases xDifferent : a ≠ u
  · rw [WeierstrassCurve.Projective.Point.toAffine_of_Z_ne_zero outputValid
      (by simpa [output] using
        addZNeZeroOfXNe a b u v offsetOnCurve inputOnCurve xDifferent)]
    simp only [affinePoint]
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne xDifferent]
    simp only [output, WeierstrassCurve.Projective.fin3_def_ext,
      WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨recoveredXOfXNe a b u v offsetOnCurve inputOnCurve xDifferent,
      recoveredYOfXNe a b u v offsetOnCurve inputOnCurve xDifferent⟩
  · have xEqual : u = a := (Classical.not_not.mp xDifferent).symm
    subst u
    have squareEqual : v ^ 2 = b ^ 2 := by
      simp only [OnCurve] at offsetOnCurve inputOnCurve
      linear_combination inputOnCurve - offsetOnCurve
    have productZero : (v - b) * (v + b) = 0 := by
      linear_combination squareEqual
    rcases mul_eq_zero.mp productZero with sameY | oppositeY
    · have vEqual : v = b := sub_eq_zero.mp sameY
      subst v
      have bNonzero := noAffineYZero { x := a, y := b } offsetOnCurve
      have bNotNeg : b ≠ curve.toAffine.negY a b := by
        simp only [curve, WeierstrassCurve.Affine.negY, zero_mul]
        intro equalNeg
        have twiceZero : 2 * b = 0 := by linear_combination equalNeg
        exact bNonzero ((mul_eq_zero.mp twiceZero).resolve_left twoNe)
      have zNonzero : addZ a b a b ≠ 0 := by
        rw [doublingZ a b offsetOnCurve]
        exact mul_ne_zero eightNe (pow_ne_zero 3 bNonzero)
      rw [WeierstrassCurve.Projective.Point.toAffine_of_Z_ne_zero outputValid
        (by simpa [output] using zNonzero)]
      simp only [affinePoint]
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne bNotNeg]
      simp only [output, WeierstrassCurve.Projective.fin3_def_ext,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨recoveredXDouble a b offsetOnCurve, recoveredYDouble a b offsetOnCurve⟩
    · have vEqual : v = -b := eq_neg_of_add_eq_zero_left oppositeY
      subst v
      have zZero : addZ a b a (-b) = 0 := by
        simp only [addZ, Coordinates.algorithmZ]
        ring
      rw [WeierstrassCurve.Projective.Point.toAffine_of_Z_eq_zero
        (by simpa [output] using zZero)]
      simp only [affinePoint]
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq rfl
        (by simp [curve, WeierstrassCurve.Affine.negY])]

def homogeneousVector (value : FieldMacToECMac.HomogeneousValue) :
    Fin 3 → BaseField :=
  ![value.x, value.y, value.z]

theorem decodePoint_eq_affinePoint [FieldCertificate]
    (input : AffineInput) (inputOnCurve : OnCurve input) :
    decodePoint input = some (affinePoint input inputOnCurve) := by
  simp [decodePoint, (validate_eq_true_iff input).mpr inputOnCurve, affinePoint]

theorem decodeHomogeneous_eq_toAffine [FieldCertificate]
    (value : FieldMacToECMac.HomogeneousValue)
    (valid : curve.toProjective.Nonsingular (homogeneousVector value)) :
    Garbling.decodeHomogeneous value =
      some (WeierstrassCurve.Projective.Point.toAffine curve.toProjective
        (homogeneousVector value)) := by
  by_cases zZero : value.z = 0
  · have vectorZZero : homogeneousVector value 2 = 0 := by
      simpa [homogeneousVector] using zZero
    have xZero : value.x = 0 := by
      have vectorXZero :=
        WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero valid.1 vectorZZero
      simpa [homogeneousVector] using vectorXZero
    have yNonzero : value.y ≠ 0 := by
      have vectorYUnit :=
        WeierstrassCurve.Projective.isUnit_Y_of_Z_eq_zero valid vectorZZero
      simpa [homogeneousVector] using vectorYUnit.ne_zero
    simp [Garbling.decodeHomogeneous, zZero, xZero, yNonzero,
      WeierstrassCurve.Projective.Point.toAffine_of_Z_eq_zero vectorZZero]
  · have vectorZNonzero : homogeneousVector value 2 ≠ 0 := by
      simpa [homogeneousVector] using zZero
    have affineValid :=
      (WeierstrassCurve.Projective.nonsingular_of_Z_ne_zero vectorZNonzero).mp valid
    have affineOnCurve : OnCurve { x := value.x / value.z, y := value.y / value.z } :=
      (equation_iff_onCurve _).mp
        ((curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
          discriminantNeZero).mpr affineValid)
    rw [Garbling.decodeHomogeneous, if_neg zZero,
      decodePoint_eq_affinePoint _ affineOnCurve,
      WeierstrassCurve.Projective.Point.toAffine_of_Z_ne_zero valid vectorZNonzero]
    rfl

theorem affineOffsetPoint_eq [FieldCertificate]
    (offset : FieldMacToECMac.AffineOffset) :
    FieldMacToECMac.AffineOffset.point offset =
      affinePoint offset.coordinates offset.onCurve := by
  simp [FieldMacToECMac.AffineOffset.point, decodePoint,
    (validate_eq_true_iff offset.coordinates).mpr offset.onCurve, affinePoint]

def scaledAlgorithmValue (randomizer : BaseField) (offset input : AffineInput) :
    FieldMacToECMac.HomogeneousValue := {
  x := randomizer * Coordinates.algorithmX offset input
  y := randomizer * Coordinates.algorithmY offset input
  z := randomizer * Coordinates.algorithmZ offset input
}

theorem homogeneousVector_scaledAlgorithmValue
    (randomizer : BaseField) (offset input : AffineInput) :
    homogeneousVector (scaledAlgorithmValue randomizer offset input) =
      randomizer • output offset.x offset.y input.x input.y := by
  funext index
  fin_cases index <;>
    simp [homogeneousVector, scaledAlgorithmValue, output, addX, addY, addZ]

@[blueprint "RCBComplete.decodeScaledAlgorithmValue"
  (statement := /-- Jacobian addition (Eqs.~29--31) decodes to the affine sum. For two on-curve points $K$ and $\pi$
    and a nonzero randomizer $a$: converting the scaled output $(a^2 X, a^3 Y, a Z)$ of the addition
    formula to affine coordinates returns $K + \pi$. -/)
  (title := /-- BABE Eqs.~29--31 -/)]
theorem decodeScaledAlgorithmValue [FieldCertificate] [GroupCertificate]
    (randomizer : BaseField) (offset input : AffineInput)
    (randomizerNonzero : randomizer ≠ 0)
    (offsetOnCurve : OnCurve offset) (inputOnCurve : OnCurve input) :
    Garbling.decodeHomogeneous (scaledAlgorithmValue randomizer offset input) =
      some (affinePoint offset offsetOnCurve + affinePoint input inputOnCurve) := by
  /-- By \cref{RCBComplete.outputNonsingular} the output of the addition formula is a nonsingular
    projective point. Scaling by $a$ keeps it nonsingular. The decoder returns the affine form of
    this point, and scaling does not change the affine form. By
    \cref{RCBComplete.outputRepresentsSum} the affine form is $K + \pi$. -/
  have baseValid :
      curve.toProjective.Nonsingular (output offset.x offset.y input.x input.y) :=
    outputNonsingular offset.x offset.y input.x input.y offsetOnCurve inputOnCurve
  have scaledValid :
      curve.toProjective.Nonsingular
        (homogeneousVector (scaledAlgorithmValue randomizer offset input)) := by
    rw [homogeneousVector_scaledAlgorithmValue]
    exact (WeierstrassCurve.Projective.nonsingular_smul _
      (Ne.isUnit randomizerNonzero)).mpr baseValid
  calc
    Garbling.decodeHomogeneous (scaledAlgorithmValue randomizer offset input) =
        some (WeierstrassCurve.Projective.Point.toAffine curve.toProjective
          (homogeneousVector (scaledAlgorithmValue randomizer offset input))) :=
      decodeHomogeneous_eq_toAffine _ scaledValid
    _ = some (WeierstrassCurve.Projective.Point.toAffine curve.toProjective
        (output offset.x offset.y input.x input.y)) := by
      rw [homogeneousVector_scaledAlgorithmValue,
        WeierstrassCurve.Projective.Point.toAffine_smul _
          (Ne.isUnit randomizerNonzero)]
    _ = some (affinePoint offset offsetOnCurve + affinePoint input inputOnCurve) := by
      rw [outputRepresentsSum offset.x offset.y input.x input.y
        offsetOnCurve inputOnCurve]

@[blueprint "RCBComplete.decodeEvaluateRowNone"
  (statement := /-- For the digit $r_j = 0$, an offset $K_j$, and a nonzero randomizer $a_j$: the row of $C_2$
    evaluates to a Jacobian representation of $K_j$ and decodes to $K_j$. -/)
  (title := /-- BABE Eqs.~29--31 -/)]
theorem decodeEvaluateRowNone [FieldCertificate]
    (offset : FieldMacToECMac.AffineOffset) (input : AffineInput)
    (randomizer : BaseField) (randomizerNonzero : randomizer ≠ 0) :
    Garbling.decodeHomogeneous
        (FieldMacToECMac.evaluateRow
          (Coordinates.rows offset.coordinates none randomizer) input) =
      some (FieldMacToECMac.AffineOffset.point offset) := by
  /-- Rewrite the row for the zero digit. The decoder divides by the nonzero randomizer and recovers
    $K_j$ in affine coordinates. -/
  rw [FieldMacToECMac.evaluateRowsNone]
  simp [Garbling.decodeHomogeneous, randomizerNonzero,
    decodePoint_eq_affinePoint offset.coordinates offset.onCurve,
    affineOffsetPoint_eq offset]

@[blueprint "RCBComplete.decodeEvaluateRowSome"
  (statement := /-- For a digit $r_j \neq 0$ with endomorphism base $\mu$, $\mu^6 = 1$, an offset $K_j$, a nonzero
    randomizer $a_j$, and an on-curve input $\pi$: the row of $C_2$ decodes to $K_j + \pi'$, where
    $\pi' = r_j \pi = (\mu^k x(\pi), \pm y(\pi))$ is the transformed input. -/)
  (title := /-- BABE Eqs.~29--31 -/)]
theorem decodeEvaluateRowSome [FieldCertificate] [GroupCertificate]
    (offset : FieldMacToECMac.AffineOffset) (input : AffineInput)
    (phi : NonZeroBase) (randomizer : BaseField)
    (randomizerNonzero : randomizer ≠ 0) (phiSix : phi.value ^ 6 = 1)
    (inputOnCurve : OnCurve input) :
    Garbling.decodeHomogeneous
        (FieldMacToECMac.evaluateRow
          (Coordinates.rows offset.coordinates (some phi.value) randomizer) input) =
      some (FieldMacToECMac.AffineOffset.point offset +
        affinePoint (FieldMacToECMac.transformedInput phi.value input)
          (by
            simpa [FieldMacToECMac.transformedInput] using
              Coordinates.transformedOnCurve phi.value phiSix input inputOnCurve)) := by
  /-- The transformed input $\pi'$ stays on the curve because $\mu^6 = 1$. Rewrite the row as the
    Jacobian addition of $K_j$ and $\pi'$ scaled by $a_j$. Conclude with
    \cref{RCBComplete.decodeScaledAlgorithmValue}. -/
  have transformedOnCurve :
      OnCurve (FieldMacToECMac.transformedInput phi.value input) := by
    simpa [FieldMacToECMac.transformedInput] using
      Coordinates.transformedOnCurve phi.value phiSix input inputOnCurve
  rw [FieldMacToECMac.evaluateRowsSome]
  change Garbling.decodeHomogeneous
      (scaledAlgorithmValue randomizer offset.coordinates
        (FieldMacToECMac.transformedInput phi.value input)) = _
  rw [decodeScaledAlgorithmValue randomizer offset.coordinates
      (FieldMacToECMac.transformedInput phi.value input) randomizerNonzero
      offset.onCurve transformedOnCurve,
    affineOffsetPoint_eq offset]

theorem affinePoint_eq_of_decode [FieldCertificate]
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point)
    (inputOnCurve : OnCurve input) :
    affinePoint input inputOnCurve = point := by
  have canonical := decodePoint_eq_affinePoint input inputOnCurve
  exact Option.some.inj (canonical.symm.trans decoded)

theorem transformedInputPoint_eq_digitEndomorphism
    [FieldCertificate] (digit : Digit) (phi : BaseField)
    (selected : digitEndomorphismBase digit = some phi)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point)
    (transformedOnCurve : OnCurve (FieldMacToECMac.transformedInput phi input)) :
    affinePoint (FieldMacToECMac.transformedInput phi input) transformedOnCurve =
      digitEndomorphism digit point := by
  have inputOnCurve : OnCurve input :=
    (decodePoint_defined input).mp (by simp [decoded])
  have pointEq := affinePoint_eq_of_decode input point decoded inputOnCurve
  have generatorSquared : endomorphismGenerator ^ 2 = BN254.endomorphismBase := by
    calc
      endomorphismGenerator ^ 2 =
          BN254.endomorphismBase ^ 3 * BN254.endomorphismBase := by
        simp only [endomorphismGenerator]
        ring
      _ = BN254.endomorphismBase := by rw [BN254.endomorphismBaseCube]; simp
  have generatorCube : endomorphismGenerator ^ 3 = (-1 : BaseField) := by
    calc
      endomorphismGenerator ^ 3 = -(BN254.endomorphismBase ^ 3) ^ 2 := by
        simp only [endomorphismGenerator]
        ring
      _ = -1 := by rw [BN254.endomorphismBaseCube]; simp
  have generatorFourth :
      endomorphismGenerator ^ 4 = BN254.endomorphismBase ^ 2 := by
    calc
      endomorphismGenerator ^ 4 =
          endomorphismGenerator ^ 3 * endomorphismGenerator := by ring
      _ = BN254.endomorphismBase ^ 2 := by
        rw [generatorCube]
        simp [endomorphismGenerator]
  have generatorSixth : endomorphismGenerator ^ 6 = (1 : BaseField) := by
    calc
      endomorphismGenerator ^ 6 = (endomorphismGenerator ^ 3) ^ 2 := by ring
      _ = 1 := by rw [generatorCube]; ring
  subst point
  cases digit with
  | zero => simp [digitEndomorphismBase] at selected
  | one =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism]
  | negOne =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism, curve,
        show (endomorphismGenerator ^ 3) ^ 4 = (1 : BaseField) by
          rw [generatorCube]
          ring,
        show (endomorphismGenerator ^ 3) ^ 3 = (-1 : BaseField) by
          rw [generatorCube]
          ring]
      change _ = WeierstrassCurve.Affine.Point.neg _
      simp [WeierstrassCurve.Affine.Point.neg, WeierstrassCurve.Affine.negY, curve, pow_two, mul_assoc]
  | omega =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism,
        show (endomorphismGenerator ^ 2) ^ 4 =
          (BN254.endomorphismBase : BaseField) by
            calc
              (endomorphismGenerator ^ 2) ^ 4 =
                  endomorphismGenerator ^ 6 * endomorphismGenerator ^ 2 := by ring
              _ = BN254.endomorphismBase := by rw [generatorSixth, generatorSquared]; simp,
        show (endomorphismGenerator ^ 2) ^ 3 = (1 : BaseField) by
          rw [show (endomorphismGenerator ^ 2) ^ 3 =
            endomorphismGenerator ^ 6 by ring, generatorSixth]]
  | negOmega =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism, curve,
        show (endomorphismGenerator ^ 5) ^ 4 =
          (BN254.endomorphismBase : BaseField) by
            calc
              (endomorphismGenerator ^ 5) ^ 4 =
                  (endomorphismGenerator ^ 6) ^ 3 *
                    endomorphismGenerator ^ 2 := by ring
              _ = BN254.endomorphismBase := by rw [generatorSixth, generatorSquared]; simp,
        show (endomorphismGenerator ^ 5) ^ 3 = (-1 : BaseField) by
          calc
            (endomorphismGenerator ^ 5) ^ 3 =
                (endomorphismGenerator ^ 6) ^ 2 * endomorphismGenerator ^ 3 := by ring
            _ = -1 := by rw [generatorSixth, generatorCube]; simp]
      change _ = WeierstrassCurve.Affine.Point.neg _
      simp [WeierstrassCurve.Affine.Point.neg, WeierstrassCurve.Affine.negY, curve, pow_two, mul_assoc]
  | omegaSquared =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism,
        show (endomorphismGenerator ^ 4) ^ 4 =
          (BN254.endomorphismBase ^ 2 : BaseField) by
            calc
              (endomorphismGenerator ^ 4) ^ 4 =
                  (endomorphismGenerator ^ 6) ^ 2 *
                    endomorphismGenerator ^ 4 := by ring
              _ = BN254.endomorphismBase ^ 2 := by
                rw [generatorSixth, generatorFourth]
                simp,
        show (endomorphismGenerator ^ 4) ^ 3 = (1 : BaseField) by
          rw [show (endomorphismGenerator ^ 4) ^ 3 =
            (endomorphismGenerator ^ 6) ^ 2 by ring, generatorSixth]
          simp] <;> ring
  | negOmegaSquared =>
      simp [digitEndomorphismBase] at selected
      subst phi
      simp [FieldMacToECMac.transformedInput, affinePoint, digitEndomorphism,
        BN254.endomorphism, curve,
        show endomorphismGenerator ^ 4 =
          (BN254.endomorphismBase ^ 2 : BaseField) from generatorFourth,
        show endomorphismGenerator ^ 3 = (-1 : BaseField) from generatorCube]
      change _ = WeierstrassCurve.Affine.Point.neg _
      simp [WeierstrassCurve.Affine.Point.neg, WeierstrassCurve.Affine.negY, curve, pow_two, mul_assoc]


@[blueprint "RCBComplete.decodeEvaluateOutputKeyRow"
  (statement := /-- One row of $C_2$ decodes to $r_j P + K_j$. For an output key $(r_j, K_j)$ with digit $r_j \in D
    = \{0, \pm 1, \pm\omega, \pm(1+\omega)\}$, a nonzero randomizer $a_j$, and an input $\pi$ that
    decodes to $P$: converting the evaluated row $(X, Y, Z)$ to affine coordinates returns $r_j P +
    K_j$. -/)
  (title := /-- BABE Fig.~9 -/)]
theorem decodeEvaluateOutputKeyRow [FieldCertificate] [GroupCertificate]
    (key : FieldMacToECMac.OutputKey)
    (randomness : FieldMacToECMac.RowRandomness)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    Garbling.decodeHomogeneous
        (FieldMacToECMac.evaluateRow
          (Coordinates.rows key.offset.coordinates
            (digitEndomorphismBase key.digit) randomness.rho.value) input) =
      some (digitScalar key.digit • point +
        FieldMacToECMac.AffineOffset.point key.offset) := by
  /-- Since $\pi$ decodes to a point, $\pi$ is on the curve. Split on the endomorphism base of the
    digit $r_j$. If $r_j = 0$, \cref{RCBComplete.decodeEvaluateRowNone} returns $K_j$. Otherwise the
    base is a sixth root of unity $\mu$ with $r_j \pi = (\mu^k x(\pi), \pm y(\pi))$, and
    \cref{RCBComplete.decodeEvaluateRowSome} returns $K_j + r_j P$. -/
  have inputOnCurve : OnCurve input :=
    (decodePoint_defined input).mp (by simp [decoded])
  cases selected : digitEndomorphismBase key.digit with
  | none =>
      have digitZero : key.digit = .zero := by
        cases digitCase : key.digit
        case zero => rfl
        all_goals simp [digitCase, digitEndomorphismBase] at selected
      rw [digitZero]
      rw [decodeEvaluateRowNone key.offset input randomness.rho.value
        randomness.rho.nonzero]
      simp [digitScalar]
      exact Module.zero_smul point
  | some phi =>
      have phiSix : phi ^ 6 = 1 :=
        digitEndomorphismBasePowSix key.digit phi selected
      have phiNonzero : phi ≠ 0 := by
        intro phiZero
        rw [phiZero] at phiSix
        norm_num at phiSix
      let nonzeroPhi : NonZeroBase := { value := phi, nonzero := phiNonzero }
      have rowDecoded :=
        decodeEvaluateRowSome key.offset input nonzeroPhi randomness.rho.value
          randomness.rho.nonzero phiSix inputOnCurve
      change Garbling.decodeHomogeneous
          (FieldMacToECMac.evaluateRow
            (Coordinates.rows key.offset.coordinates (some phi) randomness.rho.value) input) =
        _ at rowDecoded
      rw [rowDecoded]
      rw [transformedInputPoint_eq_digitEndomorphism key.digit phi selected
        input point decoded]
      rw [digitEndomorphismAction]
      abel

private theorem optionMapMOfFn {n : Nat} {α β : Type}
    (f : Fin n → α) (g : Fin n → β) (decode : α → Option β)
    (decoded : ∀ index, decode (f index) = some (g index)) :
    (List.ofFn f).mapM decode = some (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n inductionHypothesis =>
      rw [List.ofFn_succ, List.ofFn_succ, List.mapM_cons, decoded]
      rw [inductionHypothesis (fun index => f index.succ)
        (fun index => g index.succ) (fun index => decoded index.succ)]
      rfl

@[blueprint "RCBComplete.decodeRowsForOutputKeys"
  (statement := /-- For output keys $(r_j, K_j)_j$, randomizers $a_j$, and an input $\pi$ that decodes to $P$:
    converting every evaluated row of $C_2$ from Jacobian to affine coordinates returns the list of
    points $r_j P + K_j$ (Fig.~9). -/)
  (title := /-- BABE Fig.~9 -/)]
theorem decodeRowsForOutputKeys [FieldCertificate] [GroupCertificate]
    (keys : FieldMacToECMac.OutputKeys)
    (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    Garbling.decodePointMacs
        (FieldMacToECMac.evaluateRows
          (FieldMacToECMac.rowsForOutputKeys keys randomness) input) =
      some ((Vector.ofFn fun index =>
        digitScalar (keys.get index).digit • point +
          FieldMacToECMac.AffineOffset.point (keys.get index).offset).toList) := by
  /-- Unfold the point decoder and the rows. Decode each row with
    \cref{RCBComplete.decodeEvaluateOutputKeyRow}. The vector of successful decodings is the
    expected list. -/
  simp only [Garbling.decodePointMacs, FieldMacToECMac.evaluateRows,
    FieldMacToECMac.rowsForOutputKeys, Vector.toList_ofFn, Vector.get_ofFn]
  apply optionMapMOfFn
  intro index
  rw [decodeEvaluateOutputKeyRow
    (key := keys.get index) (randomness := randomness.get index)
    (input := input) (point := point) decoded]

def successfulOffsetRandomness [FieldCertificate]
    (offsets : FieldMacToECMac.SuccessfulOffsets) : OffsetRandomness := {
  freeOffsets := FieldMacToECMac.freeOffsetPoints offsets.free
  freeOffsetCount := by simp [FieldMacToECMac.freeOffsetPoints]
}

theorem successfulOffsetPoints [FieldCertificate] [GroupCertificate]
    (offsets : FieldMacToECMac.SuccessfulOffsets)
    (clamped : offsets.IsClamped) :
    (offsets.values.map FieldMacToECMac.AffineOffset.point).toList =
      construction.offsets (successfulOffsetRandomness offsets) := by
  simp only [FieldMacToECMac.SuccessfulOffsets.values, Vector.toList_map,
    Construction.offsets, clampOffsets, successfulOffsetRandomness]
  change FieldMacToECMac.AffineOffset.point offsets.first ::
      FieldMacToECMac.freeOffsetPoints offsets.free =
    -(radix • pointHorner radix (FieldMacToECMac.freeOffsetPoints offsets.free)) ::
      FieldMacToECMac.freeOffsetPoints offsets.free
  rw [clamped]
  rfl

private theorem encodeDigits_eq_zipWith [FieldCertificate] [GroupCertificate]
    (point : Point) (digits : List ScalarField) (offsets : List Point) :
    encodeDigits point digits offsets =
      List.zipWith (fun digit offset => digit • point + offset) digits offsets := by
  induction digits generalizing offsets with
  | nil => simp [encodeDigits]
  | cons digit digits inductionHypothesis =>
      cases offsets <;> simp [encodeDigits, inductionHypothesis]

private theorem vectorZipWithToList {n : Nat} {α β γ : Type}
    (f : α → β → γ) (left : Vector α n) (right : Vector β n) :
    (Vector.ofFn fun index => f (left.get index) (right.get index)).toList =
      List.zipWith f left.toList right.toList := by
  apply List.ext_getElem
  · simp
  · intro index leftBound rightBound
    simp only [Vector.toList_ofFn] at leftBound ⊢
    rw [List.getElem_ofFn, List.getElem_zipWith,
      Vector.getElem_toList, Vector.getElem_toList, Vector.get_eq_getElem,
      Vector.get_eq_getElem]

@[blueprint "RCBComplete.outputKeyPoints"
  (statement := /-- The list of points $r_j P + K_j$ over all output keys equals $L_1 =
    \mathsf{Encode}_1(\mathsf{ek}_1, P)$ of Fig.~7, where the offsets are clamped by $K_0 = -\sum_{j
    \geq 1} (2-\omega)^j K_j$. -/)
  (title := /-- BABE Fig.~7 -/)]
theorem outputKeyPoints [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (offsets : FieldMacToECMac.SuccessfulOffsets)
    (clamped : offsets.IsClamped) (point : Point) :
    (Vector.ofFn fun index =>
      digitScalar
          ((FieldMacToECMac.outputKeys construction scalar offsets).get index).digit • point +
        FieldMacToECMac.AffineOffset.point
          ((FieldMacToECMac.outputKeys construction scalar offsets).get index).offset).toList =
      construction.outputs scalar (successfulOffsetRandomness offsets) point := by
  /-- Read the output keys as the digit vector $(r_0, \ldots, r_{\ell-1})$ paired with the offsets.
    Rewrite the vector as a zip of the digit multiples with the offset points. The clamped
    successful offsets are $(K_0, \ldots, K_{\ell-1})$. The zip is the definition of
    $\mathsf{Encode}_1$. -/
  let digits : Vector Digit FieldMacToECMac.outputMacCount :=
    ⟨(construction.digits scalar).toArray,
      by simpa [FieldMacToECMac.outputMacCount] using construction.digitCount scalar⟩
  calc
    (Vector.ofFn fun index =>
        digitScalar
            ((FieldMacToECMac.outputKeys construction scalar offsets).get index).digit • point +
          FieldMacToECMac.AffineOffset.point
            ((FieldMacToECMac.outputKeys construction scalar offsets).get index).offset).toList =
      (Vector.ofFn fun index =>
        digitScalar (digits.get index) • point +
          FieldMacToECMac.AffineOffset.point (offsets.values.get index)).toList := by
        simp [FieldMacToECMac.outputKeys, digits]
    _ = List.zipWith (fun digit offset => digit • point + offset)
        (digits.map digitScalar).toList
        (offsets.values.map FieldMacToECMac.AffineOffset.point).toList := by
      simpa only [Vector.get_map] using
        vectorZipWithToList (fun digit offset => digit • point + offset)
          (digits.map digitScalar)
          (offsets.values.map FieldMacToECMac.AffineOffset.point)
    _ = List.zipWith (fun digit offset => digit • point + offset)
        ((construction.digits scalar).map digitScalar)
        (construction.offsets (successfulOffsetRandomness offsets)) := by
      rw [successfulOffsetPoints offsets clamped]
      simp [digits]
    _ = construction.outputs scalar (successfulOffsetRandomness offsets) point := by
      rw [Construction.outputs, encodeDigits_eq_zipWith]

@[blueprint "RCBComplete.decodeExpectedResult"
  (statement := /-- Decoding the output of $\mathsf{Eval}_2$ gives $rP$. For clamped offsets $K_j$, randomizers
    $a_j$, and an input $\pi$ that decodes to $P$: converting the Jacobian coordinates $(X, Y,
    Z)(r_j \pi + K_j)$ to affine coordinates and running $\mathsf{Eval}_1$ (Fig.~21) returns $rP$. -/)
  (title := /-- BABE Fig.~21 -/)]
theorem decodeExpectedResult [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : ScalarField)
    (offsets : FieldMacToECMac.SuccessfulOffsets) (clamped : offsets.IsClamped)
    (randomness : FieldMacToECMac.Randomness)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    Garbling.decodeResult
        (FieldMacToECMac.expectedResult
          (FieldMacToECMac.rowsForOutputKeys
            (FieldMacToECMac.outputKeys construction scalar offsets) randomness) input) =
      some (scalarMultiplication scalar point) := by
  /-- Unfold the decoder and the expected result. By \cref{RCBComplete.decodeRowsForOutputKeys} the
    rows decode to the points $r_j P + K_j$. By \cref{RCBComplete.outputKeyPoints} this list equals
    $L_1 = (L_{1,0}, \ldots, L_{1,\ell-1})$ of $\mathsf{Encode}_1$. By \cref{Construction.correct}
    $\mathsf{Eval}_1(\bot, L_1) = rP$. -/
  unfold Garbling.decodeResult FieldMacToECMac.expectedResult
  rw [decodeRowsForOutputKeys
    (FieldMacToECMac.outputKeys construction scalar offsets)
    randomness input point decoded]
  simp only [Option.map_some]
  rw [outputKeyPoints scalar offsets clamped point]
  exact congrArg some
    (construction.correct scalar (successfulOffsetRandomness offsets) point)

@[blueprint "RCBComplete.pipelineEvaluateInvalid"
  (statement := /-- When $\pi$ is not a point of $\mathbb{G}_1$, the evaluation chain $\mathsf{Eval}_5 \to
    \mathsf{Eval}_4 \to \mathsf{Dec}_{\hat t} \to \mathsf{Eval}_3 \to \mathsf{Eval}_2$ of Fig.~21
    returns $\bot$ for every $\mathsf{ct}_{\mathsf{gc}}$ and every label vector $L$. -/)
  (title := /-- BABE Eq.~27 -/)]
theorem pipelineEvaluateInvalid [FieldCertificate]
    (fixedKeyOracle : Cryptography.PermutationOracle Pipeline.FixedKeyIndex
      Cryptography.Block)
    (encPRFOracle : Cryptography.PermutationOracle EncPRF.PermutationIndex
      Cryptography.Block)
    (hashOracle : EncPRF.HashOracle) (table : Pipeline.Table)
    (input : AffineInput) (inputMac : InputMac)
    (invalid : decodePoint input = none) :
    Pipeline.evaluate fixedKeyOracle encPRFOracle hashOracle table
      (BitInput.ofAffine input) inputMac = none := by
  /-- Unfold the chain. The first step decodes $\pi$ as a curve point and fails, so the chain returns
    $\bot$. -/
  simp [Pipeline.evaluate, BitInput.toAffineOfAffine, invalid]

private theorem optionBindSome {α β : Type} (result : Option α)
    (value : α) (output : β) (decode : α → Option β)
    (evaluated : result = some value) (decoded : decode value = some output) :
    result.bind decode = some output := by
  rw [evaluated]
  exact decoded

@[blueprint "RCBComplete.evaluateCorrectInvalid"
  (statement := /-- When $\pi$ is not a point of $\mathbb{G}_1$, $\mathsf{Eval}$ returns $f[r](\pi) = 0$ (Eq.~27).
    The curve membership check $C_4[t, w]$ (Fig.~17) does not release $t$, so the labels $L_3$ stay
    encrypted. -/)
  (title := /-- BABE Eq.~27 -/)]
theorem evaluateCorrectInvalid [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) (input : AffineInput)
    (invalid : decodePoint input = none) :
    Garbling.evaluate
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
        (Garbling.garble construction scalar randomness).1
        (Garbling.encode (Garbling.garble construction scalar randomness).2
          (BitInput.ofAffine input)) =
      checkedScalarMultiplication scalar.value input := by
  /-- Unfold $\mathsf{Eval}$. By \cref{RCBComplete.pipelineEvaluateInvalid} the evaluation chain
    returns $\bot$. The function $f[r]$ also returns $0$ for an off-curve input. -/
  change Garbling.evaluate
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
    (Garbling.garble construction scalar randomness).1
    { input := BitInput.ofAffine input
      inputMac := randomness.inputMacKey.encode (BitInput.ofAffine input) } =
      checkedScalarMultiplication scalar.value input
  unfold Garbling.evaluate
  rw [pipelineEvaluateInvalid randomness.fixedKeyOracle
    randomness.encPRFOracle randomness.hashOracle
    (Garbling.garble construction scalar randomness).1 input
    (randomness.inputMacKey.encode (BitInput.ofAffine input)) invalid]
  simp [checkedScalarMultiplication, invalid]

@[blueprint "RCBComplete.evaluateCorrectValid"
  (statement := /-- When $\pi$ decodes to a point $P \in \mathbb{G}_1$: $\mathsf{Eval}(\mathsf{ct}_{\mathsf{gc}},
    \mathsf{Encode}(\mathsf{ek}, \pi), \pi) = f[r](\pi) = rP$. -/)
  (title := /-- BABE Fig.~21 -/)]
theorem evaluateCorrectValid [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) :
    Garbling.evaluate
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
        (Garbling.garble construction scalar randomness).1
        (Garbling.encode (Garbling.garble construction scalar randomness).2
          (BitInput.ofAffine input)) =
      checkedScalarMultiplication scalar.value input := by
  /-- Unfold $\mathsf{Eval}$ into the evaluation chain followed by the decoder. By
    \cref{Garbling.evaluateEncodeRows} the chain returns the Jacobian coordinates of $r_j \pi + K_j$
    for all $j$. The offsets $K_j$ are clamped, so \cref{RCBComplete.decodeExpectedResult} decodes
    these coordinates to $rP$. -/
  change Garbling.evaluate
    (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
    (Garbling.garble construction scalar randomness).1
    { input := BitInput.ofAffine input
      inputMac := randomness.inputMacKey.encode (BitInput.ofAffine input) } =
      checkedScalarMultiplication scalar.value input
  unfold Garbling.evaluate
  change (Pipeline.evaluate randomness.fixedKeyOracle randomness.encPRFOracle
    randomness.hashOracle (Garbling.garble construction scalar randomness).1
    (BitInput.ofAffine input)
    (randomness.inputMacKey.encode (BitInput.ofAffine input))).bind
      Garbling.decodeResult = checkedScalarMultiplication scalar.value input
  have evaluated := Garbling.evaluateEncodeRows construction
    ({ scalar, randomness } : Garbling.EncodingKey) input point decoded
  simp only [Garbling.encode] at evaluated
  have offsetsClamped : randomness.offsets.IsClamped :=
    randomness.offsetsClamped
  have decodedRows := decodeExpectedResult scalar.value randomness.offsets
    offsetsClamped randomness.pointRandomness input point decoded
  have bound := optionBindSome
    (Pipeline.evaluate randomness.fixedKeyOracle randomness.encPRFOracle
      randomness.hashOracle (Garbling.garble construction scalar randomness).1
      (BitInput.ofAffine input)
      (randomness.inputMacKey.encode (BitInput.ofAffine input)))
    (FieldMacToECMac.expectedResult
      (FieldMacToECMac.rowsForOutputKeys
        (FieldMacToECMac.outputKeys construction scalar.value randomness.offsets)
        randomness.pointRandomness) input)
    (scalarMultiplication scalar.value point) Garbling.decodeResult evaluated decodedRows
  exact bound.trans (by simp [checkedScalarMultiplication, decoded])

@[blueprint "RCBComplete.evaluateCorrect"
  (statement := /-- For every nonzero scalar $r$, every randomness, and every input $\pi$:
    $\mathsf{Eval}(\mathsf{ct}_{\mathsf{gc}}, \mathsf{Encode}(\mathsf{ek}, \pi), \pi) = f[r](\pi)$,
    where $(\mathsf{ct}_{\mathsf{gc}}, \mathsf{ek}) = \mathsf{Garble}(C[r])$ (Fig.~21). -/)
  (title := /-- BABE Fig.~21 -/)]
theorem evaluateCorrect [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) (input : AffineInput) :
    Garbling.evaluate
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)
        (Garbling.garble construction scalar randomness).1
        (Garbling.encode (Garbling.garble construction scalar randomness).2
          (BitInput.ofAffine input)) =
      checkedScalarMultiplication scalar.value input := by
  /-- Split on whether $\pi$ decodes to a point of $\mathbb{G}_1$. The off-curve case is
    \cref{RCBComplete.evaluateCorrectInvalid}. The on-curve case is
    \cref{RCBComplete.evaluateCorrectValid}. -/
  cases decoded : decodePoint input with
  | none => exact evaluateCorrectInvalid scalar randomness input decoded
  | some point => exact evaluateCorrectValid scalar randomness input point decoded

@[blueprint "RCBComplete.perfectCorrectness"
  (statement := /-- Perfect correctness of the garbled circuit of Fig.~21 for the fixed base-$(2-\omega)$
    construction with $\ell = 92$ digits. The random tape supplies the fixed-key permutations of
    $\mathsf{CTPRF}$, the permutations of $\mathsf{EncPRF}$, and the hash oracle. -/)
  (title := /-- BABE Fig.~21 -/)]
theorem perfectCorrectness [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] :
    GarbledCircuit.PerfectCorrectness (Garbling.garbledCircuit construction)
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) := by
  /-- Fix $r$, the randomness, and $\pi$. The claim is \cref{RCBComplete.evaluateCorrect} wrapped in
    \texttt{some}. -/
  intro securityParameter scalar randomness input
  exact congrArg some (evaluateCorrect scalar randomness input)

end Kriterion.ArgoMAC.RCBComplete
