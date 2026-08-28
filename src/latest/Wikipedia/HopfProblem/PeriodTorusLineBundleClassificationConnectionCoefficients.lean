import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnectionDlog
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnectionPartition

/-!
# Smooth rank-one connection forms from the actual scalar cocycle

Write `gᵢⱼ` for the scalar coordinate change from chart `i` to chart `j`.
With the constructed subordinate smooth partition `ρ`, set
`Aᵢ = ∑ₖ ρₖ dlog(gᵢₖ)`. The logarithmic derivative is the actual real
Fréchet derivative divided by the nonzero scalar, not a chosen branch of log.
The exact transformation law is `Aⱼ = Aᵢ - dlog(gᵢⱼ)`.
-/

noncomputable section

open Function Filter Set Topology
open scoped ContDiff BigOperators

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection

open HolomorphicCharacterBundle

local notation "Iℝ" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι)

/-- The local connection form built from the actual native scalar transitions
and the constructed smooth partition of unity. -/
def connectionForm (i : ι) (x : ComplexPlane₂) : ComplexPlane₂ →L[ℝ] ℂ :=
  HolomorphicCousin.partitionCochain (subordinatePartition A) (logDerivative A) i x

theorem connectionForm_eq_finsum (i : ι) (x : ComplexPlane₂) :
    connectionForm A i x =
      ∑ᶠ k, subordinatePartition A k x • logDerivative A i k x := rfl

theorem connectionForm_eq_sum (i : ι) (x : ComplexPlane₂) :
    connectionForm A i x =
      ∑ k ∈ (subordinatePartition A).finsupport x,
        subordinatePartition A k x • logDerivative A i k x :=
  ((subordinatePartition A).sum_finsupport_smul_eq_finsum x (logDerivative A i)).symm

/-- Only locally finitely many summands can contribute; values of a scalar
transition outside its overlap do not create a regularity assumption. -/
theorem connectionForm_summands_locallyFinite (i : ι) :
    LocallyFinite (fun k => support
      (fun x => subordinatePartition A k x • logDerivative A i k x)) :=
  (subordinatePartition A).locallyFinite.smul_left _

variable [A.IsHolomorphic Iℂ]

theorem connectionForm_contMDiffOn (i : ι) :
    ContMDiffOn Iℝ (modelWithCornersSelf ℝ (ComplexPlane₂ →L[ℝ] ℂ)) ∞
      (connectionForm A i) (A.baseSet i) :=
  HolomorphicCousin.partitionCochain_contMDiffOn A.isOpen_baseSet
    (subordinatePartition_isSubordinate A)
    (fun i j => (logDerivative_contDiffOn A i j).contMDiffOn) i

/-- Every local connection coefficient is genuinely real-smooth on its chart. -/
theorem connectionForm_contDiffOn (i : ι) :
    ContDiffOn ℝ ∞ (connectionForm A i) (A.baseSet i) :=
  (connectionForm_contMDiffOn A i).contDiffOn

theorem connectionForm_sub (i j : ι) {x : ComplexPlane₂}
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) :
    connectionForm A i x - connectionForm A j x = logDerivative A i j x :=
  HolomorphicCousin.partitionCochain_sub_eq (subordinatePartition_isSubordinate A)
    (fun i j k x hi hj hk => logDerivative_add A i j k x ⟨⟨hi, hj⟩, hk⟩) i j hi hj

/-- The sign agrees with coordinates transforming as `cⱼ = gᵢⱼ cᵢ`:
the connection forms transform as `Aⱼ = Aᵢ - dlog(gᵢⱼ)`. -/
theorem connectionForm_change (i j : ι) {x : ComplexPlane₂}
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) :
    connectionForm A j x = connectionForm A i x - logDerivative A i j x := by
  rw [← connectionForm_sub A i j hi hj]
  exact (sub_sub_cancel _ _).symm

/-- The transformation is valid on a whole neighborhood of each overlap point. -/
theorem connectionForm_change_eventuallyEq (i j : ι) {x : ComplexPlane₂}
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) :
    connectionForm A j =ᶠ[𝓝 x]
      (fun y => connectionForm A i y - logDerivative A i j y) := by
  filter_upwards [((A.isOpen_baseSet i).inter (A.isOpen_baseSet j)).mem_nhds ⟨hi, hj⟩]
    with y hy
  exact connectionForm_change A i j hy.1 hy.2

/-- The transformation law evaluated on an actual real tangent vector. -/
theorem connectionForm_change_apply (i j : ι) {x : ComplexPlane₂}
    (hi : x ∈ A.baseSet i) (hj : x ∈ A.baseSet j) (v : ComplexPlane₂) :
    connectionForm A j x v = connectionForm A i x v -
      (A.transition i j x : ℂ)⁻¹ *
        fderiv ℝ (fun y => (A.transition i j y : ℂ)) x v := by
  have h := congrArg (fun L : ComplexPlane₂ →L[ℝ] ℂ => L v)
    (connectionForm_change A i j hi hj)
  simpa [logDerivative] using h

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationConnection
