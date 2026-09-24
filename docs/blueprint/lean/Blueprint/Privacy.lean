/-
Blueprint nodes for the adaptive privacy proof.
-/
import Architect
import Batteries.Tactic.OpenPrivate
import Blueprint.Correctness
import Blueprint.Lamport
import Proof.Privacy.Bounds.SharedAdaptiveArithmetic
import Proof.Privacy.Bounds.SharedMachineArithmetic
import Proof.Privacy.Bounds.SharedSourceEventBound
import Proof.Privacy.Collision.SharedMaskSourceBad
import Proof.Privacy.Collision.SharedPipelinePrefixBadMass
import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptiveGame
import Proof.Privacy.Simulator.Arithmetic.CompiledMachine
import Proof.Privacy.Simulator.Arithmetic.CompiledOnlineProtocol
import Proof.Privacy.Simulator.Arithmetic.CompiledSetupJoint
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyDecision
import Proof.Privacy.Simulator.Arithmetic.OnlineLazyExecution
import Proof.Privacy.Source.Invalid.SharedCurveSupportedRatio
import Proof.Privacy.Source.SharedCombinedRatio
import Proof.Privacy.Source.StrictGateSource
import Proof.Privacy.Source.StrictSourceSampling
import Proof.Privacy.Source.StrictWirePrivacy
import Proof.Privacy.Source.Valid.SharedPipelineSupportedRatio
import Proof.Shared.SourceHCoefficient
import Proof.SharedOracle

open private phaseBudget from Proof.Privacy.Simulator.Arithmetic.CompiledMachine

attribute [blueprint "ArithmeticSimulator.lazyCompiledAdaptivePrivacy"
  (statement := /-- Adaptive privacy of the optimized garbling scheme (Theorem~8) at the concrete level of Lemma~14.
    The compiled simulator $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ proves the public privacy obligation
    for the program circuit, the Lamport wire encoding, the ciphertext size $9806076$ bytes, and the
    uniform private tape: every adversary with work $T$ has advantage $\delta$ with $T / \delta \geq
    2^{100}$. The proof uses no hardness assumption beyond the programmable random permutation
    model. -/)
  (title := /-- BABE Theorem~8 -/)
  (proof := /-- Apply \cref{Security.sharedStrictOraclePrivacy} to the compiled machine.
    \Cref{ArithmeticSimulator.lazyCompiledIdealGame_eqStrict} shows that the machine implements the
    strict simulator. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyCompiledAdaptivePrivacy

attribute [blueprint "Security.sharedStrictOraclePrivacy"
  (statement := /-- A closed implementation of the strict simulator meets the privacy rule of Definition~3. If a
    bounded machine implements the ideal world of $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ with $256$
    sampling attempts per draw, then the program circuit satisfies oracle adaptive privacy with $T /
    \delta \geq 2^{100}$. -/)
  (title := /-- BABE Theorem~8 -/)
  (proof := /-- Use the given machine as the simulator. Rewrite the real world with
    \cref{Security.OperationalOracle.shared_lazy_real} and the ideal world with the implementation
    premise. Apply \cref{Security.sharedStrictWirePrivacy} to the machine adversary. The machine
    step count $T$ dominates the query budget. -/)] Kriterion.ArgoMAC.Security.sharedStrictOraclePrivacy

attribute [blueprint "Security.OperationalOracle.shared_lazy_real"
  (statement := /-- The real world $\mathcal{O}_{\mathrm{real}}$ splits into private coins and the public
    permutation (hybrid $\mathsf{Hyb}_0$ in the proof of Theorem~7). The lazy real game, which
    samples the public permutation on demand, equals the real game of the wire circuit with a
    uniformly sampled tape. -/)
  (title := /-- BABE Theorem~7 -/)
  (proof := /-- Rewrite the lazy real game with the uniform tape. Split the uniform randomness into the private
    coins and the public permutation. Both games run the adversary under a public handler. The
    permutation state does not change during the choose phase, so both games evaluate the same
    experiment. -/)] Kriterion.ArgoMAC.Security.OperationalOracle.shared_lazy_real

attribute [blueprint "Security.sharedStrictWirePrivacy"
  (statement := /-- Concrete adaptive privacy (Lemma~14). For every adversary with query budget $q$, the advantage
    $\delta$ between the real world of the wire circuit and the strict simulator with $256$ attempts
    per draw satisfies $(q + 1) / \delta \geq 2^{100}$. -/)
  (title := /-- BABE Lemma~14 -/)
  (proof := /-- Let $q$ be the total query budget. Transfer the advantage through the exact strict simulator. If
    $q < 2^{101}$, apply \cref{Security.sharedErrors_has100Bits} with
    \cref{Security.sharedStrictWireAdvantage_envelope} and
    \cref{Security.sharedStrictSourceDecision_allowance}. Otherwise apply
    \cref{Security.sharedLargeBudget_has100Bits}. -/)] Kriterion.ArgoMAC.Security.sharedStrictWirePrivacy

attribute [blueprint "Security.sharedStrictWireAdvantage_envelope"
  (statement := /-- For $q \leq 2^{101}$, the advantage between the real world of the wire circuit and the exact
    strict simulator is at most $\varepsilon_3(q) = (251850146 + 833\,q) / 2^{128}$, the Lean
    counterpart of the bucketed bound of Lemma~14. -/)
  (title := /-- BABE Lemma~14 -/)
  (proof := /-- Rewrite the exact strict simulator. Apply \cref{Security.sharedStrictAdaptiveAdvantage_envelope}
    to the wire adversary. The wire circuit is the internal circuit with Lamport-mapped labels, so
    the two real worlds agree. -/)] Kriterion.ArgoMAC.Security.sharedStrictWireAdvantage_envelope

attribute [blueprint "Security.sharedStrictAdaptiveAdvantage_envelope"
  (statement := /-- For $q \leq 2^{101}$, the advantage between the real world of the internal circuit and the ideal
    world of the strict simulator $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ is at most $\varepsilon_3(q)$. -/)
  (title := /-- BABE Lemma~14 -/)
  (proof := /-- Apply \cref{Security.sharedStrictAdaptive_event_bound} to the event $\{\mathrm{true}\}$ with the
    bad-transcript mass of \cref{Security.sharedFullPipelinePrefixBad_mass_le}. The real decision is
    the projection of the real transcript.
    \Cref{Security.sharedAdaptiveThreeRoundingLossSum_le_envelope} collects $\varepsilon_1$,
    $\varepsilon_2$, and the sampling losses into $\varepsilon_3(q)$. -/)] Kriterion.ArgoMAC.Security.sharedStrictAdaptiveAdvantage_envelope

attribute [blueprint "Security.sharedStrictAdaptive_event_bound"
  (statement := /-- H-coefficient bound for the strict simulator (Lemma~13). For every event on the decision bit,
    the real-world transcript and the ideal-world transcript differ by at most the bad-transcript
    mass $\varepsilon_1$, which is the given offline bound plus $(60199524 + 372\,q) / 2^{128}$ plus
    $(q + 1) / p$, plus two hash-rounding losses plus $2^{-240}$. -/)
  (title := /-- BABE Lemma~13 -/)
  (proof := /-- Bound the bad-transcript mass with \cref{Security.sharedCombinedBad_real_mass_le}. Apply
    \cref{Security.hCoefficient_event_of_sourceGoodMass_congr} to the real transcript and the ideal
    sample space. The ratio premise $1 - \varepsilon_2$ is
    \cref{Security.sharedCombinedGood_real_le}. The agreement premise on good transcripts is
    \cref{Security.sharedStrictTranscript_good}. The strict decision is the projection of the strict
    transcript. Add the sampling loss of \cref{Security.sharedStrictGateSource_entrance} by the
    triangle inequality. -/)] Kriterion.ArgoMAC.Security.sharedStrictAdaptive_event_bound

attribute [blueprint "Security.hCoefficient_event_of_sourceGoodMass_congr"
  (statement := /-- The H-coefficient technique (Lemma~13) in event form. Let $\mathrm{real}$ be a distribution on
    transcripts, let the ideal sample space have a bad set $\mathcal{T}_{\mathrm{bad}}$ of mass at
    most $\varepsilon_1$, and let a kernel map samples to transcripts. If $\Pr_{\mathrm{real}}[\tau]
    \geq (1 - \varepsilon_2) \cdot \Pr[\text{good sample} \mapsto \tau]$ for every $\tau$, and a
    replacement kernel agrees with the kernel on good samples, then every event differs between
    $\mathrm{real}$ and the replacement by at most $\varepsilon_1 + \varepsilon_2$. -/)
  (title := /-- BABE Lemma~13 -/)
  (proof := /-- Apply the H-coefficient event bound to the replacement kernel. The good mass of the replacement
    equals the good mass of the kernel, because both agree on every supported sample outside
    $\mathcal{T}_{\mathrm{bad}}$. The ratio premise transfers. -/)] Kriterion.ArgoMAC.Security.hCoefficient_event_of_sourceGoodMass_congr

attribute [blueprint "Security.sharedCombinedBad_real_mass_le"
  (statement := /-- Bad-transcript mass $\varepsilon_1$ (Claim~11). The mass of the bad event of the ideal sample
    space is at most the given offline bound (collisions among the programmed points, events bad1,
    bad2, bad4) plus the hash-rounding loss plus $(q + 1) / p$ (the adversary hits a programmed
    point, event bad3). -/)
  (title := /-- BABE Claim~11 -/)
  (proof := /-- The combined bad mass is at most the offline bad mass plus the mass of a hit on a programmed
    point. The first term is the offline bound. The second term is the exact bound for a hit. -/)] Kriterion.ArgoMAC.Security.sharedCombinedBad_real_mass_le

attribute [blueprint "Security.sharedCombinedGood_real_le"
  (statement := /-- Good-transcript ratio (Claim~12). For $q \leq 2^{101}$ and every transcript $\tau$: $(1 -
    \varepsilon_2) \cdot \Pr_{\mathrm{ideal}}[\text{good sample} \mapsto \tau] \leq
    \Pr_{\mathrm{real}}[\tau]$ with $\varepsilon_2 = (60199524 + 372\,q) / 2^{128}$, for an on-curve
    and for an off-curve chosen input. -/)
  (title := /-- BABE Claim~12 -/)
  (proof := /-- Split on whether the chosen input is on the curve. For an on-curve input, the good mass is at
    most the offline good mass. If that mass is zero the claim is trivial. Otherwise
    \cref{Security.sharedFullPipelinePrefix_real_le_supported} applies with the query length of a
    supported transcript. For an off-curve input, the good mass is at most the curve good mass, and
    \cref{Security.sharedFullCurveGood_real_le_budget} applies. -/)] Kriterion.ArgoMAC.Security.sharedCombinedGood_real_le

attribute [blueprint "Security.sharedFullPipelinePrefix_real_le_supported"
  (statement := /-- Good-transcript ratio for an on-curve input. For every transcript $\tau$ whose chosen input is
    on the curve and whose permutation queries number at most $q \leq 2^{101}$: $(1 - (60199016 +
    368\,q) / 2^{128}) \cdot \Pr_{\mathrm{ideal}}[\text{good offline sample} \mapsto \tau] \leq
    \Pr_{\mathrm{real}}[\tau]$. -/)
  (title := /-- BABE Claim~12 -/)
  (proof := /-- If the good mass is zero the claim is trivial. Otherwise expand the good mass as a weighted sum
    and pick a nonzero term. The term supplies compatible active labels, input bits, and a label
    vector. The supported-ratio lemma for the on-curve branch gives the bound. -/)] Kriterion.ArgoMAC.Security.sharedFullPipelinePrefix_real_le_supported

attribute [blueprint "Security.sharedFullCurveGood_real_le_budget"
  (statement := /-- Good-transcript ratio for an off-curve input. For every transcript $\tau$ whose chosen input is
    off the curve and $q \leq 2^{101}$: $(1 - \varepsilon_2) \cdot \Pr_{\mathrm{ideal}}[\text{good
    sample} \mapsto \tau] \leq \Pr_{\mathrm{real}}[\tau]$. Only the curve membership layer $C_4,
    C_5$ is compared, because the labels $L_3$ stay encrypted. -/)
  (title := /-- BABE Claim~12 -/)
  (proof := /-- If the good mass is zero the claim is trivial. Otherwise expand the good mass as a weighted sum
    and pick a nonzero term. The term bounds the query length by $q$. The supported-ratio lemma for
    the off-curve branch gives the bound. -/)] Kriterion.ArgoMAC.Security.sharedFullCurveGood_real_le_budget

attribute [blueprint "Security.sharedStrictTranscript_good"
  (statement := /-- On a good sample, the strict simulator does not abort. For every sample of the ideal space
    outside $\mathcal{T}_{\mathrm{bad}}$ (Definition~20), the strict transcript equals the sampled
    transcript. -/)
  (title := /-- BABE Definition~20 -/)
  (proof := /-- Unfold the ideal sample space to find the prior draw of the sample. The offline phase does not
    abort on a good sample. Without an abort the strict transcript equals the sampled transcript.
    The abort lemmas reduce to \cref{Security.sharedStrictSelectedView_good}. -/)
  (proofUses := ["Security.sharedStrictSelectedView_good"])] Kriterion.ArgoMAC.Security.sharedStrictTranscript_good

attribute [blueprint "Security.sharedStrictSelectedView_good"
  (statement := /-- The programming of $\mathsf{Sim}_2$ succeeds on a good tag. When the garbled $C_2, C_3$ tag is
    good and the permutation state starts without a conflict, programming the active labels of the
    chosen input (Construction~3, Step~3) does not raise the bad flag, on the on-curve and on the
    off-curve branch. -/)
  (title := /-- BABE Definition~20 -/)
  (proof := /-- Split on whether the input is on the curve. In both branches, rewrite the program view as the
    source view. The programming commands of a good tag stay fresh, so the bad flag stays false. -/)] Kriterion.ArgoMAC.Security.sharedStrictSelectedView_good

attribute [blueprint "Security.sharedStrictGateSource_entrance"
  (statement := /-- Sampling loss of the real oracle. The real gate source, which samples $\mathbb{F}_p$ elements by
    reducing $384$-bit hash outputs, and the ideal gate source differ on every event by at most the
    hash-rounding loss $305054 \cdot (2^{384} \bmod p) / 2^{384}$ plus $2^{-240}$. -/)
  (title := /-- BABE Lemma~14 -/)
  (proof := /-- This is the gate source observation bound applied to the strict observer. -/)] Kriterion.ArgoMAC.Security.sharedStrictGateSource_entrance

attribute [blueprint "Security.sharedFullPipelinePrefixBad_mass_le"
  (statement := /-- Bad-transcript mass of the offline phase (Claim~11, events bad1, bad2, bad4). The probability
    that the programmed points of $\mathsf{Sim}_2$ collide is at most $188023005.716 / 2^{128} +
    368\,q_1 / 2^{128}$ plus the hash-rounding loss, where $q_1$ is the number of queries before the
    chosen input. -/)
  (title := /-- BABE Claim~11 -/)
  (proof := /-- The bad offline event is the image of the retained bad source under the offline law. By
    \cref{Security.sharedGoodMaskSourceBad_mass_le} the retained bad source has the joint collision
    bound. Add the hash-rounding loss. -/)
  (proofUses := ["Security.sharedGoodMaskSourceBad_mass_le"])] Kriterion.ArgoMAC.Security.sharedFullPipelinePrefixBad_mass_le

attribute [blueprint "Security.sharedGoodMaskSourceBad_mass_le"
  (statement := /-- Joint collision bound (Claim~11). For the independent mask source of the ideal world, the
    collision flag has mass at most $188023005.716 / 2^{128} + 368\,q_1 / 2^{128}$. -/)
  (title := /-- BABE Claim~11 -/)
  (proof := /-- Bound the mass by the concrete retained flags. Unfold both sources into a product of uniform
    draws. For each retained tape, the observer flags have the checked collision mass. -/)] Kriterion.ArgoMAC.Security.sharedGoodMaskSourceBad_mass_le

attribute [blueprint "Security.sharedAdaptiveThreeRoundingLossSum_le_envelope"
  (statement := /-- Arithmetic of Lemma~14. The sum $\varepsilon_1 + \varepsilon_2$ plus three hash-rounding losses
    plus $2^{-240}$ is at most $\varepsilon_3(q) = (251850146 + 833\,q) / 2^{128}$ when $q_1 \leq
    q$. -/)
  (title := /-- BABE Lemma~14 -/)
  (proof := /-- The field mask loss is at most the block loss, so $(q + 1) / p \leq (q + 1) / 2^{128}$. The term
    $2^{-240}$ is at most $2^{-128}$. Sum all terms and compare with the constant of $\varepsilon_3$
    by linear arithmetic. -/)] Kriterion.ArgoMAC.Security.sharedAdaptiveThreeRoundingLossSum_le_envelope

attribute [blueprint "Security.sharedStrictSourceDecision_allowance"
  (statement := /-- Bounded rejection sampling. The advantage between the exact strict simulator and the strict
    simulator with $256$ attempts per draw is at most the machine cutoff allowance of $q$. The
    simulator of Construction~3 samples with unbounded rejection; the Lean simulator bounds each
    draw. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- The total law of \cref{Security.sharedStrictSourceDecision_law} with $256$ attempts bounds the
    advantage. Unfold the cutoff allowance and compare the coefficients. -/)] Kriterion.ArgoMAC.Security.sharedStrictSourceDecision_allowance

attribute [blueprint "Security.sharedStrictSourceDecision_law"
  (statement := /-- The strict simulator draws $917653$ field elements by rejection sampling. With $k$ attempts per
    draw, the simulator with bounded draws is a total law of the exact simulator: it agrees with the
    exact simulator unless some draw fails $k$ times. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Unfold the strict simulator. The offline sampler $\mathsf{Sim}_1$ has a total law with $917470$
    draws. The online sampler $\mathsf{Sim}_2$ adds $183$ draws. The remaining steps are exact. -/)] Kriterion.ArgoMAC.Security.sharedStrictSourceDecision_law

attribute [blueprint "Security.sharedErrors_has100Bits"
  (statement := /-- Security level (Lemma~14). If the privacy error is at most $\varepsilon_3(q)$ and the
    implementation error is at most the cutoff allowance of $q$, then $(q + 1) / (\text{privacy
    error} + \text{implementation error}) \geq 2^{100}$. -/)
  (title := /-- BABE Lemma~14 -/)
  (proof := /-- Add the two bounds. Multiply by $2^{100}$. The envelope $\varepsilon_3$ plus the cutoff
    allowance has $100$ bits of work. -/)] Kriterion.ArgoMAC.Security.sharedErrors_has100Bits

attribute [blueprint "Security.sharedLargeBudget_has100Bits"
  (statement := /-- Large budgets. When $q \geq 2^{101}$, the sum of two advantages, each at most $1$, satisfies $(q
    + 1) / (\delta + \delta') \geq 2^{100}$. -/)
  (title := /-- BABE Lemma~14 -/)
  (proof := /-- Each advantage is at most one, so the sum is at most two. Multiply by $2^{100}$. The budget plus
    one is at least $2^{101}$, which dominates. -/)] Kriterion.ArgoMAC.Security.sharedLargeBudget_has100Bits

attribute [blueprint "ArithmeticSimulator.lazyCompiledIdealGame_eqStrict"
  (statement := /-- The compiled machine implements the strict simulator. The ideal world of the compiled machine
    equals the ideal world of $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ (Construction~3) with $256$
    attempts per draw. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Apply \cref{ArithmeticSimulator.lazyCompiledIdealGame_finiteSource}. For each setup in the
    support, apply \cref{ArithmeticSimulator.lazyChosenDecision_completion}. The online premise is
    \cref{ArithmeticSimulator.lazyCompiledOnline_decision} with the offline coin stored in memory. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyCompiledIdealGame_eqStrict

attribute [blueprint "ArithmeticSimulator.lazyCompiledIdealGame_finiteSource"
  (statement := /-- If the online phase of the compiled machine equals, for every setup in the support of
    $\mathsf{Sim}_1$, the strict frame decision of $\mathsf{Sim}_2$ after the public completion of
    the permutation, then the ideal world of the machine equals the strict simulator. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Split the parsed game into the setup and online phases and rewrite the setup with
    \cref{ArithmeticSimulator.lazySetupJoint_parsed}. Replace the online decision on the support of
    the setup by the premise. The result is the strict simulator over the joint setup law. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyCompiledIdealGame_finiteSource

attribute [blueprint "ArithmeticSimulator.lazySetupJoint_parsed"
  (statement := /-- The setup phase of the compiled machine is $\mathsf{Sim}_1$. Parsing the memory after the setup
    run returns the public table $\mathsf{ct}_{\mathsf{gc}}$, the memory, and the empty lazy
    permutation, distributed as the joint offline source. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Parse the result of the setup machine run. The setup machine law gives the joint offline source.
    On the support of the joint source, the public value in memory parses to
    $\mathsf{ct}_{\mathsf{gc}}$. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazySetupJoint_parsed

attribute [blueprint "ArithmeticSimulator.lazyChosenDecision_completion"
  (statement := /-- The choose phase keeps only the permutation fields that affect the strict decision. If the
    parsed online phase has the completed strict law for every chosen input, then the chosen
    decision of the machine equals the strict frame decision of $\mathsf{Sim}_2$ after the public
    completion. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Complete the choose phase with the online premise. The chosen decision unfolds to the same bind
    on the support. The strict frame decision agrees with the completed run because the public run
    keeps the bad flag false. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyChosenDecision_completion

attribute [blueprint "ArithmeticSimulator.lazyCompiledOnline_decision"
  (statement := /-- The online phase of the compiled machine is $\mathsf{Sim}_2$. When the offline coin is stored in
    memory and the lazy permutation matches the transcript, the parsed online decision equals the
    strict decision: sample the online randomness with $256$ attempts, program the active labels of
    the chosen input, abort on a conflict, and otherwise run the adversary's decision on the
    programmed permutation. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Rewrite the parsed online phase with
    \cref{ArithmeticSimulator.lazyCompiledMachine_onlineParsed}. The lazy online result decision
    lemma gives the completed strict law. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyCompiledOnline_decision

attribute [blueprint "ArithmeticSimulator.lazyCompiledMachine_onlineParsed"
  (statement := /-- The online parser returns the active labels $L_3$ and the programmed permutation. The parsed
    online phase of the compiled machine equals the lazy online result mapped to the $508$ labels of
    $128$ bits. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Prepare the input memory with the phase dispatch. Run the compiled machine for the online phase.
    By \cref{ArithmeticSimulator.lazyOnlineMachine_run} the online machine returns the lazy online
    result. Parse the labels from memory word $3$. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyCompiledMachine_onlineParsed

attribute [blueprint "ArithmeticSimulator.lazyOnlineMachine_run"
  (statement := /-- Every online request fits the fuel $2^{46}$. Running the online machine on a memory that holds
    the chosen input and the optional output point returns the lazy online result at program counter
    $317804843$. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Bound the prefix cost and the sampling budget. Split on the output. Without an output the null
    run fits the fuel. With an output the valid run fits the fuel bound. -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyOnlineMachine_run

attribute [blueprint "ArithmeticSimulator.lazyCompiledMachine"
  (statement := /-- The compiled simulator $(\mathsf{Sim}_1, \mathsf{Sim}_2)$ as one bounded machine. The phase
    simulator combines the offline machine with $256$ attempts per draw and the lazy online machine
    under the shared instruction allowance. -/)
  (title := /-- BABE Construction~3 -/)] Kriterion.ArgoMAC.ArithmeticSimulator.lazyCompiledMachine

attribute [blueprint "ArithmeticSimulator.phaseBudget"
  (statement := /-- The size of the phase simulator plus both fuel allowances is at most $2^{60}$, when the setup
    size plus fuel is at most $605084290688$, the online code has at most $317804844$ instructions,
    and the online fuel is at most $2^{46}$. -/)
  (title := /-- BABE Construction~3 -/)
  (proof := /-- Unfold the phase simulator size and use linear arithmetic. -/)] phaseBudget
