/-
This file defines the concrete online ArgoMAC simulator.
-/

import Proof.ProjectiveDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

/-- This state keeps the hidden public sample and its programmable oracles. -/
structure CircuitSimulatorState where
  oracle : SimulatorState
  curve : CurveGateRequest
  points : PointGateRequests
  inputKey : InputMacKey
  bridgeKey : BaseField

def CircuitSimulatorState.table (state : CircuitSimulatorState) : Pipeline.Table := {
  curve := state.curve.table
  pointMAC := pointGateTable state.points
}

def CircuitSimulatorState.labels (state : CircuitSimulatorState)
    (input : AffineInput) : Garbling.Labels := {
  input := BitInput.ofAffine input
  inputMac := state.inputKey.encodeAffine input
}

def CircuitSimulatorState.selectedCurve (state : CircuitSimulatorState)
    (input : AffineInput) : CurveGateRequest :=
  state.curve.retarget input state.bridgeKey

def CircuitSimulatorState.selectedPoints [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    PointGateRequests :=
  retargetPointGateRequests state.points input (outputTargets output free scales)

def CircuitSimulatorState.selectedSchedule [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    List GateDirective :=
  linkedPipelineGateSchedule state.oracle (state.selectedCurve input)
    (state.selectedPoints input output free scales) input (state.labels input).inputMac

/-- This operation programs the selected rows for one requested output. -/
def CircuitSimulatorState.programForOutput [FieldCertificate] [GroupCertificate]
    (state : CircuitSimulatorState) (input : AffineInput) (output : Point)
    (free : Vector Point 90) (scales : Fin FieldMacToECMac.outputMacCount → NonZeroBase) :
    CircuitSimulatorState :=
  { state with oracle := programGateSchedule state.oracle (state.selectedSchedule input output free scales) }

/-- The ideal handler updates only the programmable oracle state. -/
def circuitSimulatorOracleHandler :
    OracleHandler Garbling.oracleSpec CircuitSimulatorState
  | query, state =>
      let answered := idealOracleHandler query state.oracle
      (answered.1, { state with oracle := answered.2 })

/-- This simulator samples a public state and programs the online selected path. -/
noncomputable def circuitSimulator [FieldCertificate] [GroupCertificate]
    (stateTape : Nat → Garbling.Topology → PMF CircuitSimulatorState) :
    GarbledCircuit.Simulator AffineInput (Option Point) Pipeline.Table Garbling.Labels
      Garbling.Topology CircuitSimulatorState := by
  classical
  exact {
    simulateGarble := fun parameter topology =>
      (stateTape parameter topology).map fun state => (state.table, state)
    simulateEncode := fun state input output => match output with
      | none =>
          let schedule := (state.selectedCurve input).schedule input (state.labels input).inputMac
          PMF.pure (state.labels input,
            { state with oracle := programGateSchedule state.oracle schedule })
      | some point =>
          (PMF.uniformOfFintype ((Fin 90 → Point) ×
            (Fin FieldMacToECMac.outputMacCount → NonZeroBase))).map fun sample =>
              (state.labels input,
                state.programForOutput input point (Vector.ofFn sample.1) sample.2)
  }

end Kriterion.ArgoMAC.Security
