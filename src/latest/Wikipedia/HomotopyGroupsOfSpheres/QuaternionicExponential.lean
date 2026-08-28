import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicLieGroup
import Wikipedia.NoExoticSixSphere.OrthogonalExponential

/-! # The actual exponential in the quaternionic operator group -/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential

open NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ}

local instance : NormedAlgebra ℚ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))

theorem exp_mem_commutant (K : SkewSpace n) : NormedSpace.exp K.val ∈ commutant n := by
  apply (mem_commutant_iff n _).mpr
  intro q
  have h : Commute K.val (rightAction n q) :=
    (mem_commutant_iff n K.val).mp K.property.2 q
  exact h.exp_left.eq

/-- Exponentiation of the actual skew operator, retained in the quaternionic subgroup. -/
def exp (K : SkewSpace n) : symplecticSubgroup n :=
  ⟨NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n K),
    (mem_symplecticSubgroup_iff n _).mpr (exp_mem_commutant K)⟩

theorem exp_operator (K : SkewSpace n) : (exp K).val.val.val = NormedSpace.exp K.val := rfl

theorem exp_zero : exp (0 : SkewSpace n) = 1 := by
  apply Subtype.ext
  change NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n 0) = 1
  rw [map_zero, NoExoticSixSphere.OrthogonalExponential.exp_zero]

theorem exp_add_of_commute (K L : SkewSpace n) (h : Commute K.val L.val) :
    exp (K + L) = exp K * exp L := by
  apply Subtype.ext
  change NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n (K + L)) = _
  rw [map_add]
  exact NoExoticSixSphere.OrthogonalExponential.exp_add_of_commute _ _ h

theorem exp_add_smul (K : SkewSpace n) (s t : ℝ) :
    exp ((s + t) • K) = exp (s • K) * exp (t • K) := by
  apply Subtype.ext
  change NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n ((s + t) • K)) =
    NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n (s • K)) *
      NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n (t • K))
  simp only [map_smul]
  exact NoExoticSixSphere.OrthogonalExponential.exp_add_smul (toOrthogonalSkew n K) s t

theorem exp_neg (K : SkewSpace n) : exp (-K) = (exp K)⁻¹ := by
  apply Subtype.ext
  change NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n (-K)) =
    (NoExoticSixSphere.OrthogonalExponential.exp (toOrthogonalSkew n K))⁻¹
  have h : toOrthogonalSkew n (-K) = -(toOrthogonalSkew n K) := Subtype.ext rfl
  rw [h, NoExoticSixSphere.OrthogonalExponential.exp_neg]

theorem contDiff_exp_operator :
    ContDiff ℝ ∞ (fun K : SkewSpace n => (exp K).val.val.val) := by
  have h : ContDiff ℝ ∞ (toOrthogonalSkew n) :=
    finiteLinearMap_contDiff (E := SkewSpace n)
      (F := NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4)) (toOrthogonalSkew n)
  exact (NoExoticSixSphere.OrthogonalExponential.contDiff_exp_operator
    (n := 4 * n + 4)).comp h

theorem contMDiff_exp : ContMDiff 𝓘(ℝ, SkewSpace n) 𝓘(ℝ, SkewSpace n) ∞ (exp (n := n)) :=
  Smoothness.contMDiff_iff_operator.mpr contDiff_exp_operator.contMDiff

theorem contMDiff_exp_smul (K : SkewSpace n) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, SkewSpace n) ∞ (fun t : ℝ => exp (t • K)) :=
  contMDiff_exp.comp (contMDiff_id.smul contMDiff_const)

def path (K : SkewSpace n) : Path (1 : symplecticSubgroup n) (exp K) where
  toFun t := exp ((t : ℝ) • K)
  continuous_toFun := (contMDiff_exp_smul K).continuous.comp continuous_subtype_val
  source' := by change exp ((0 : ℝ) • K) = 1; rw [zero_smul, exp_zero]
  target' := by change exp ((1 : ℝ) • K) = exp K; rw [one_smul]

theorem hasDerivAt_exp_smul_operator (K : SkewSpace n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (exp (s • K)).val.val.val)
      ((exp (t • K)).val.val.val.comp K.val) t :=
  hasDerivAt_exp_smul_const K.val t

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential
