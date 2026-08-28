import Wikipedia.NoExoticSixSphere.JamesSphereConeStageCompression
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Contractibility of every actual auxiliary James cone stage

The first stage is homeomorphic to the reduced cone. Each next stage
strongly retracts to the actual embedded predecessor. Induction gives
contractibility and vanishing of positive-degree integral singular
homology for the original quotient spaces. The word-space homology
splitting still requires the cone cover and its actual inclusion maps.
-/

noncomputable section

open Set Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.ConeStage

theorem exists_step_equiv (n k : ℕ) :
    ∃ e : ContinuousMap.HomotopyEquiv (Space n k) (Space n (k + 1)), e.toFun = step n k := by
  obtain ⟨R, hR, ⟨H⟩⟩ := exists_stage_deformation n k
  let j : C(preceding n k, Space n (k + 1)) := ⟨Subtype.val, continuous_subtype_val⟩
  have hRj : R.comp j = ContinuousMap.id (preceding n k) := ContinuousMap.ext hR
  let E : ContinuousMap.HomotopyEquiv (preceding n k) (Space n (k + 1)) :=
    ⟨j, R, by rw [hRj], ⟨H.toHomotopy.symm⟩⟩
  exact ⟨(stepHomeomorph n k).toHomotopyEquiv.trans E, rfl⟩

theorem contractibleSpace (n k : ℕ) : ContractibleSpace (Space n k) := by
  induction k with
  | zero => infer_instance
  | succ k ih =>
      let : ContractibleSpace (Space n k) := ih
      obtain ⟨e, _⟩ := exists_step_equiv n k
      exact e.symm.contractibleSpace

instance contractibleSpaceInst (n k : ℕ) : ContractibleSpace (Space n k) := contractibleSpace n k

theorem positive_homology_subsingleton (n k d : ℕ) (hd : d ≠ 0) :
    Subsingleton (SingularHomology (Space n k) d) :=
  contractible_homology_subsingleton (Space n k) d hd

end NoExoticSixSphere.JamesSphere.ConeStage
