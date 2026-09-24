/-
Blueprint nodes for the perfect correctness proof.
-/
import Architect
import Batteries.Tactic.OpenPrivate
import Construction.ArgoMAC.Base7
import Construction.ArgoMAC.CurveMembership
import Construction.ArgoMAC.EncPRF
import Construction.ArgoMAC.FieldMacToECMac
import Construction.ArgoMAC.Offsets
import Construction.ArgoMAC.Pipeline
import Construction.ArgoMAC.RandomizedEncoding
import Construction.Garbling
import Proof.Correctness.Base7Termination
import Proof.Correctness.RCBComplete
import Proof.LamportCompatibility.Labels
import Proof.SharedGarbling

attribute [blueprint "Shared.programPerfectCorrectness"
  (statement := /-- Perfect correctness of the garbling scheme $(\mathsf{Garble}, \mathsf{Encode}, \mathsf{Eval})$
    of Fig.~21 for $f[r]$ (Eq.~27). For every secret scalar $r$, every random tape, and every input
    $\pi = (x(\pi), y(\pi))$: $\mathsf{Eval}(\mathsf{ct}_{\mathsf{gc}}, \mathsf{Encode}(\mathsf{ek},
    \pi), \pi) = f[r](\pi)$, where $(\mathsf{ct}_{\mathsf{gc}}, \mathsf{ek}) =
    \mathsf{Garble}(C[r])$. The tape supplies the private coins and the public oracles
    $\mathsf{CTPRF}$, $\mathsf{EncPRF}$, and the hash. -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- Fix $r$, the tape, and $\pi$. Apply \cref{Shared.perfectCorrectness} to the tape whose public
    oracle is replaced by the oracle component of the tape. Unfold the program circuit, the wire
    circuit, and the label map. The two sides agree. -/)] Kriterion.ArgoMAC.Shared.programPerfectCorrectness

attribute [blueprint "Shared.perfectCorrectness"
  (statement := /-- Perfect correctness of the wire circuit, the garbling scheme of Fig.~21 whose input labels are
    the Lamport signatures of the bits of $\pi$ (Eqs.~15--16). For every coherent tape and every
    input $\pi$, evaluation under the evaluation oracle returns $f[r](\pi)$. -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- Fix $r$, a coherent tape, and $\pi$. Unfold the wire circuit and rewrite the evaluation oracle
    with the tape property. By \cref{Lamport.restore_selected} the Lamport signature restores the
    bit labels $L$. Conclude with \cref{RCBComplete.perfectCorrectness}. -/)] Kriterion.ArgoMAC.Shared.perfectCorrectness

attribute [blueprint "Lamport.restore_selected"
  (statement := /-- The wire adapter inverts the Lamport encoding. For every input $\pi$ and every label vector $L =
    \{L^{x_i(\pi)}_{x,i}, L^{y_i(\pi)}_{y,i}\}_{i < 254}$, restoring $L$ from its $508$ Lamport
    signature slots returns the bits of $\pi$ together with $L$. -/)
  (title := /-- BABE Eqs.~15--16 -/)
  (proof := /-- Compare the $x$ and $y$ label vectors index by index. For $i < 254$ slot $i$ holds
    $L^{x_i(\pi)}_{x,i}$. For $i \geq 254$ slot $i$ holds $L^{y_{i-254}(\pi)}_{y,i-254}$. -/)] Kriterion.ArgoMAC.Lamport.restore_selected

attribute [blueprint "RCBComplete.perfectCorrectness"
  (statement := /-- Perfect correctness of the garbled circuit of Fig.~21 for the fixed base-$(2-\omega)$
    construction with $\ell = 92$ digits. The random tape supplies the fixed-key permutations of
    $\mathsf{CTPRF}$, the permutations of $\mathsf{EncPRF}$, and the hash oracle. -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- Fix $r$, the randomness, and $\pi$. The claim is \cref{RCBComplete.evaluateCorrect} wrapped in
    \texttt{some}. -/)] Kriterion.ArgoMAC.RCBComplete.perfectCorrectness

attribute [blueprint "RCBComplete.evaluateCorrect"
  (statement := /-- For every nonzero scalar $r$, every randomness, and every input $\pi$:
    $\mathsf{Eval}(\mathsf{ct}_{\mathsf{gc}}, \mathsf{Encode}(\mathsf{ek}, \pi), \pi) = f[r](\pi)$,
    where $(\mathsf{ct}_{\mathsf{gc}}, \mathsf{ek}) = \mathsf{Garble}(C[r])$ (Fig.~21). -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- Split on whether $\pi$ decodes to a point of $\mathbb{G}_1$. The off-curve case is
    \cref{RCBComplete.evaluateCorrectInvalid}. The on-curve case is
    \cref{RCBComplete.evaluateCorrectValid}. -/)] Kriterion.ArgoMAC.RCBComplete.evaluateCorrect

attribute [blueprint "RCBComplete.evaluateCorrectInvalid"
  (statement := /-- When $\pi$ is not a point of $\mathbb{G}_1$, $\mathsf{Eval}$ returns $f[r](\pi) = 0$ (Eq.~27).
    The curve membership check $C_4[t, w]$ (Fig.~17) does not release $t$, so the labels $L_3$ stay
    encrypted. -/)
  (title := /-- BABE Eq.~27 -/)
  (proof := /-- Unfold $\mathsf{Eval}$. By \cref{RCBComplete.pipelineEvaluateInvalid} the evaluation chain
    returns $\bot$. The function $f[r]$ also returns $0$ for an off-curve input. -/)] Kriterion.ArgoMAC.RCBComplete.evaluateCorrectInvalid

attribute [blueprint "RCBComplete.pipelineEvaluateInvalid"
  (statement := /-- When $\pi$ is not a point of $\mathbb{G}_1$, the evaluation chain $\mathsf{Eval}_5 \to
    \mathsf{Eval}_4 \to \mathsf{Dec}_{\hat t} \to \mathsf{Eval}_3 \to \mathsf{Eval}_2$ of Fig.~21
    returns $\bot$ for every $\mathsf{ct}_{\mathsf{gc}}$ and every label vector $L$. -/)
  (title := /-- BABE Eq.~27 -/)
  (proof := /-- Unfold the chain. The first step decodes $\pi$ as a curve point and fails, so the chain returns
    $\bot$. -/)] Kriterion.ArgoMAC.RCBComplete.pipelineEvaluateInvalid

attribute [blueprint "RCBComplete.evaluateCorrectValid"
  (statement := /-- When $\pi$ decodes to a point $P \in \mathbb{G}_1$: $\mathsf{Eval}(\mathsf{ct}_{\mathsf{gc}},
    \mathsf{Encode}(\mathsf{ek}, \pi), \pi) = f[r](\pi) = rP$. -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- Unfold $\mathsf{Eval}$ into the evaluation chain followed by the decoder. By
    \cref{Garbling.evaluateEncodeRows} the chain returns the Jacobian coordinates of $r_j \pi + K_j$
    for all $j$. The offsets $K_j$ are clamped, so \cref{RCBComplete.decodeExpectedResult} decodes
    these coordinates to $rP$. -/)] Kriterion.ArgoMAC.RCBComplete.evaluateCorrectValid

attribute [blueprint "Garbling.evaluateEncodeRows"
  (statement := /-- For an on-curve input $\pi$ and the encoding key $\mathsf{ek}$ of $\mathsf{Garble}$, the
    evaluation chain of Fig.~21 applied to $\mathsf{ct}_{\mathsf{gc}}$ and
    $\mathsf{Encode}(\mathsf{ek}, \pi)$ returns the Jacobian coordinates $(X, Y, Z)(r_j \pi + K_j)$
    of $\mathsf{Eval}_2$ for all $j \in \{0, \ldots, \ell-1\}$. -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- This is \cref{Pipeline.evaluateEncoded} applied to the output keys $(r_j, K_j)$, the randomizers
    $a_j$, and the oracles of $\mathsf{ek}$. -/)] Kriterion.ArgoMAC.Garbling.evaluateEncodeRows

attribute [blueprint "Pipeline.evaluateEncoded"
  (statement := /-- Correctness of the evaluation chain. For an on-curve input $\pi$, evaluating the garbled table
    on the bit labels $L = \mathsf{Encode}(\mathsf{ek}, \pi)$ returns
    $\mathsf{Eval}_2(\mathsf{ct}_{\mathsf{gc}, 2}, L_2, x(\pi), y(\pi))$, the Jacobian coordinates
    of $r_j \pi + K_j$ for all $j$ (Fig.~10). -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- Since $\pi$ decodes to a point, $\pi$ is on the curve. Unfold $\mathsf{Eval}$ and
    $\mathsf{Garble}$. By \cref{CurveMembership.evaluateEncodedOnCurve} the garbled $C_4[t, w]$
    releases $\hat t = t$. By \cref{EncPRF.transformEncode} decrypting the encrypted labels
    $\mathsf{Enc}_t(L_3)$ with $t$ gives the labels $L_3$ of $\pi$. By
    \cref{FieldMacToECMac.evaluateEncoded} the garbled $C_2$ evaluates to the expected coordinates,
    because its rows are sparse. -/)] Kriterion.ArgoMAC.Pipeline.evaluateEncoded

attribute [blueprint "CurveMembership.evaluateEncodedOnCurve"
  (statement := /-- Correctness of the garbled $C_4[t, w]$ (Fig.~18). For all $t, w, r_1, r_2 \in \mathbb{F}_p$,
    every input $\pi$ on the curve $y^2 = x^3 + 3$, and the labels of $\pi$: $\mathsf{Eval}_4$
    returns $t + w\,(x(\pi)^3 + 3 - y(\pi)^2) = t$. -/)
  (title := /-- BABE Fig.~18 -/)
  (proof := /-- Rewrite the evaluation on the labels of $\pi$. The curve equation gives $x(\pi)^3 + 3 - y(\pi)^2
    = 0$, which removes the masked term. The remaining terms cancel by ring arithmetic. -/)] Kriterion.ArgoMAC.CurveMembership.evaluateEncodedOnCurve

attribute [blueprint "EncPRF.transformEncode"
  (statement := /-- Encrypting labels commutes with selecting labels. For the permutation oracle of
    $\mathsf{EncPRF}$, whitening keys, an encoding key $\mathsf{ek}_3$, and input bits $\mathbf{b}$:
    $\mathsf{Enc}_t(\mathsf{Encode}_3(\mathsf{ek}_3, \mathbf{b})) =
    \mathsf{Encode}_3(\mathsf{Enc}_t(\mathsf{ek}_3), \mathbf{b})$, where
    $\mathsf{Enc}_t(\mathsf{ek}_3)$ encrypts every label as in Eq.~33 and Claim~7. -/)
  (title := /-- BABE Claim~7 -/)
  (proof := /-- Compare the $x$ and $y$ label vectors. Each coordinate follows from the transformation of one
    coordinate encoding. -/)] Kriterion.ArgoMAC.EncPRF.transformEncode

attribute [blueprint "FieldMacToECMac.evaluateEncoded"
  (statement := /-- Correctness of the garbled $C_2$ (Fig.~10). For garbled rows $\{c'^{(j, W)}_k\}$, randomizers
    $a_j$, oracles, an encoding key, and an input $\pi$: if every row is sparse, then
    $\mathsf{Eval}_2$ on the labels of $\pi$ returns the expected result $\{W(r_j \pi + K_j)\}_{j,
    W}$ of the rows. -/)
  (title := /-- BABE Fig.~10 -/)
  (proof := /-- Unfold $\mathsf{Eval}_2$. The evaluation of the homogeneous labels equals the expected result,
    because every row is sparse. -/)] Kriterion.ArgoMAC.FieldMacToECMac.evaluateEncoded

attribute [blueprint "RCBComplete.decodeExpectedResult"
  (statement := /-- Decoding the output of $\mathsf{Eval}_2$ gives $rP$. For clamped offsets $K_j$, randomizers
    $a_j$, and an input $\pi$ that decodes to $P$: converting the Jacobian coordinates $(X, Y,
    Z)(r_j \pi + K_j)$ to affine coordinates and running $\mathsf{Eval}_1$ (Fig.~21) returns $rP$. -/)
  (title := /-- BABE Fig.~21 -/)
  (proof := /-- Unfold the decoder and the expected result. By \cref{RCBComplete.decodeRowsForOutputKeys} the
    rows decode to the points $r_j P + K_j$. By \cref{RCBComplete.outputKeyPoints} this list equals
    $L_1 = (L_{1,0}, \ldots, L_{1,\ell-1})$ of $\mathsf{Encode}_1$. By \cref{Construction.correct}
    $\mathsf{Eval}_1(\bot, L_1) = rP$. -/)] Kriterion.ArgoMAC.RCBComplete.decodeExpectedResult

attribute [blueprint "RCBComplete.decodeRowsForOutputKeys"
  (statement := /-- For output keys $(r_j, K_j)_j$, randomizers $a_j$, and an input $\pi$ that decodes to $P$:
    converting every evaluated row of $C_2$ from Jacobian to affine coordinates returns the list of
    points $r_j P + K_j$ (Fig.~9). -/)
  (title := /-- BABE Fig.~9 -/)
  (proof := /-- Unfold the point decoder and the rows. Decode each row with
    \cref{RCBComplete.decodeEvaluateOutputKeyRow}. The vector of successful decodings is the
    expected list. -/)] Kriterion.ArgoMAC.RCBComplete.decodeRowsForOutputKeys

attribute [blueprint "RCBComplete.decodeEvaluateOutputKeyRow"
  (statement := /-- One row of $C_2$ decodes to $r_j P + K_j$. For an output key $(r_j, K_j)$ with digit $r_j \in D
    = \{0, \pm 1, \pm\omega, \pm(1+\omega)\}$, a nonzero randomizer $a_j$, and an input $\pi$ that
    decodes to $P$: converting the evaluated row $(X, Y, Z)$ to affine coordinates returns $r_j P +
    K_j$. -/)
  (title := /-- BABE Fig.~9 -/)
  (proof := /-- Since $\pi$ decodes to a point, $\pi$ is on the curve. Split on the endomorphism base of the
    digit $r_j$. If $r_j = 0$, \cref{RCBComplete.decodeEvaluateRowNone} returns $K_j$. Otherwise the
    base is a sixth root of unity $\mu$ with $r_j \pi = (\mu^k x(\pi), \pm y(\pi))$, and
    \cref{RCBComplete.decodeEvaluateRowSome} returns $K_j + r_j P$. -/)] Kriterion.ArgoMAC.RCBComplete.decodeEvaluateOutputKeyRow

attribute [blueprint "RCBComplete.decodeEvaluateRowNone"
  (statement := /-- For the digit $r_j = 0$, an offset $K_j$, and a nonzero randomizer $a_j$: the row of $C_2$
    evaluates to a Jacobian representation of $K_j$ and decodes to $K_j$. -/)
  (title := /-- BABE Eqs.~29--31 -/)
  (proof := /-- Rewrite the row for the zero digit. The decoder divides by the nonzero randomizer and recovers
    $K_j$ in affine coordinates. -/)] Kriterion.ArgoMAC.RCBComplete.decodeEvaluateRowNone

attribute [blueprint "RCBComplete.decodeEvaluateRowSome"
  (statement := /-- For a digit $r_j \neq 0$ with endomorphism base $\mu$, $\mu^6 = 1$, an offset $K_j$, a nonzero
    randomizer $a_j$, and an on-curve input $\pi$: the row of $C_2$ decodes to $K_j + \pi'$, where
    $\pi' = r_j \pi = (\mu^k x(\pi), \pm y(\pi))$ is the transformed input. -/)
  (title := /-- BABE Eqs.~29--31 -/)
  (proof := /-- The transformed input $\pi'$ stays on the curve because $\mu^6 = 1$. Rewrite the row as the
    Jacobian addition of $K_j$ and $\pi'$ scaled by $a_j$. Conclude with
    \cref{RCBComplete.decodeScaledAlgorithmValue}. -/)] Kriterion.ArgoMAC.RCBComplete.decodeEvaluateRowSome

attribute [blueprint "RCBComplete.decodeScaledAlgorithmValue"
  (statement := /-- Jacobian addition (Eqs.~29--31) decodes to the affine sum. For two on-curve points $K$ and $\pi$
    and a nonzero randomizer $a$: converting the scaled output $(a^2 X, a^3 Y, a Z)$ of the addition
    formula to affine coordinates returns $K + \pi$. -/)
  (title := /-- BABE Eqs.~29--31 -/)
  (proof := /-- By \cref{RCBComplete.outputNonsingular} the output of the addition formula is a nonsingular
    projective point. Scaling by $a$ keeps it nonsingular. The decoder returns the affine form of
    this point, and scaling does not change the affine form. By
    \cref{RCBComplete.outputRepresentsSum} the affine form is $K + \pi$. -/)] Kriterion.ArgoMAC.RCBComplete.decodeScaledAlgorithmValue

attribute [blueprint "RCBComplete.outputNonsingular"
  (statement := /-- For two on-curve points $(a, b)$ and $(u, v)$, the output $(X, Y, Z)$ of the addition formula of
    Eqs.~29--31 is a nonsingular point of the projective BN254 curve. -/)
  (title := /-- BABE Eqs.~29--31 -/)
  (proof := /-- The output satisfies the projective curve equation and is not the zero vector. If $Z = 0$, then
    $X = 0$ and $Y \neq 0$, so the point is the nonsingular point at infinity. If $Z \neq 0$, the
    affine point satisfies the curve equation, and the nonzero discriminant gives nonsingularity. -/)] Kriterion.ArgoMAC.RCBComplete.outputNonsingular

attribute [blueprint "RCBComplete.outputRepresentsSum"
  (statement := /-- For two on-curve points $(a, b)$ and $(u, v)$, the affine form of the output of the addition
    formula equals the group sum $(a, b) + (u, v)$ in $\mathbb{G}_1$. -/)
  (title := /-- BABE Eqs.~29--31 -/)
  (proof := /-- Split on whether $a \neq u$. If they differ, $Z \neq 0$, and the recovered coordinates match the
    affine addition formula. If $a = u$, the $y$ coordinates are equal or opposite. Equal $y$
    coordinates give the doubling formula with $Z \neq 0$. Opposite $y$ coordinates give $Z = 0$,
    the point at infinity, and the affine sum is also $0$. -/)] Kriterion.ArgoMAC.RCBComplete.outputRepresentsSum

attribute [blueprint "RCBComplete.outputKeyPoints"
  (statement := /-- The list of points $r_j P + K_j$ over all output keys equals $L_1 =
    \mathsf{Encode}_1(\mathsf{ek}_1, P)$ of Fig.~7, where the offsets are clamped by $K_0 = -\sum_{j
    \geq 1} (2-\omega)^j K_j$. -/)
  (title := /-- BABE Fig.~7 -/)
  (proof := /-- Read the output keys as the digit vector $(r_0, \ldots, r_{\ell-1})$ paired with the offsets.
    Rewrite the vector as a zip of the digit multiples with the offset points. The clamped
    successful offsets are $(K_0, \ldots, K_{\ell-1})$. The zip is the definition of
    $\mathsf{Encode}_1$. -/)] Kriterion.ArgoMAC.RCBComplete.outputKeyPoints

attribute [blueprint "Construction.correct"
  (statement := /-- Correctness of $C_1$ (Fig.~6): $\mathsf{Eval}_1(\bot, L_1) = \sum_{j=0}^{\ell-1} (2-\omega)^j
    (r_j P + K_j) = rP$ for every scalar $r$, every offset randomness, and every point $P$. -/)
  (title := /-- BABE Fig.~6 -/)
  (proof := /-- Unfold $\mathsf{Encode}_1$. The Horner sum splits into $\big(\sum_j r_j (2-\omega)^j\big) P$
    plus $\sum_j (2-\omega)^j K_j$. By \cref{Construction.scalarReconstruction} the first factor is
    $r$. By \cref{Construction.offsetsCancel} the second sum is $0$. -/)] Kriterion.ArgoMAC.Construction.correct

attribute [blueprint "Construction.scalarReconstruction"
  (statement := /-- Reconstruction of Alg.~8: $\sum_{j=0}^{\ell-1} r_j (2-\omega)^j \equiv r \pmod{\mathbb{r}}$ for
    the base-$(2-\omega)$ digits $r_j \in D$ of every scalar $r$, with $\ell = 92$. The termination
    certificate uses \cref{GLV91.glvInitialTerminates92}. -/)
  (title := /-- BABE Alg.~8 -/)
  (proof := /-- The reconstruction invariant holds for $92$ iterations of Alg.~8 with the remaining pair $(A,
    B)$ as a tail. By the termination certificate $(A, B) = (0, 0)$ after $92$ iterations, so the
    tail vanishes. The initial pair $(a, b)$ satisfies $a + \omega b \equiv r$ by the GLV
    decomposition. -/)
  (proofUses := ["GLV91.glvInitialTerminates92"])] Kriterion.ArgoMAC.Construction.scalarReconstruction

attribute [blueprint "GLV91.glvInitialTerminates92"
  (statement := /-- Alg.~8 terminates. For every scalar $r$, the GLV pair $(a, b)$ with $r \equiv a + \omega b
    \pmod{\mathbb{r}}$ reaches $(A, B) = (0, 0)$ after $92$ iterations of the digit loop
    (Appendix~C). -/)
  (title := /-- BABE Appendix~C -/)
  (proof := /-- It is enough that the norm of $(a, b)$ is at most the bound for $91$ iterations. The GLV
    coefficients satisfy the bounds of the decomposition. Bound $a^2$, $b^2$, and $-ab$ by the basis
    constants. A numeric check compares the constants with the norm bound. -/)] Kriterion.ArgoMAC.GLV91.glvInitialTerminates92

attribute [blueprint "Construction.offsetsCancel"
  (statement := /-- The clamped offsets of $\mathsf{Garble}_1$ (Fig.~7) cancel: $\sum_{j=0}^{\ell-1} (2-\omega)^j
    K_j = 0$ for every offset randomness, because $K_0 = -\sum_{j \geq 1} (2-\omega)^j K_j$. -/)
  (title := /-- BABE Fig.~7 -/)
  (proof := /-- The clamp lemma cancels the Horner sum of the free offsets $K_1, \ldots, K_{\ell-1}$. -/)] Kriterion.ArgoMAC.Construction.offsetsCancel
