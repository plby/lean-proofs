import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPaths

/-!
# Continuous parameters for families of smooth minimum paths

The parameter is the entrywise imaginary part of the path's midpoint.
This explicit formula is continuous in any parameter space. It recovers
the original balanced rotation family without choosing eigenbases.
-/

noncomputable section

open scoped Matrix.Norms.Operator ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions

theorem parameter_eq_midpoint {n : ℕ} (J : Space n)
    (γ : ℝ → QuaternionicSymmetricMatrices.SpecialSpace (Index n))
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = rotation J (t * Real.pi)) :
    (γ (1 / 2)).val.val.val.map Complex.im = J.val := by
  have hm := hγ (1 / 2) (by norm_num)
  rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring] at hm
  rw [hm, rotation_midpoint_recover]

theorem midpoint_mem_locus_of_energy_eq_min {n : ℕ}
    {γ : ℝ → QuaternionicSymmetricMatrices.SpecialSpace (Index n)}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val))
    (hzero : γ 0 = QuaternionicSymmetricMatrices.specialIdentity)
    (hone : γ 1 = antipode n)
    (henergy : QuaternionicSymmetricMatrices.energy γ = (4 * n : ℝ) * Real.pi ^ 2) :
    (γ (1 / 2)).val.val.val.map Complex.im ∈ locus n := by
  obtain ⟨J, hJ⟩ := eq_rotation_of_energy_eq_min hγ hzero hone henergy
  rw [parameter_eq_midpoint J γ hJ]
  exact J.property

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

def midpointMatrix (F : C(ℝ × X, QuaternionicSymmetricMatrices.SpecialSpace (Index n))) :
    C(X, Matrix (Index n) (Index n) ℝ) where
  toFun x := (F (1 / 2, x)).val.val.val.map Complex.im
  continuous_toFun := by
    have hF : Continuous (fun x : X ↦ F (1 / 2, x)) :=
      F.continuous.comp (continuous_const.prodMk continuous_id)
    have hM : Continuous (fun x : X ↦ (F (1 / 2, x)).val.val.val) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp hF))
    exact hM.matrix_map Complex.continuous_im

def minimumParameter (F : C(ℝ × X, QuaternionicSymmetricMatrices.SpecialSpace (Index n)))
    (hF : ∀ x, ContDiff ℝ ∞ (fun t ↦ (F (t, x)).val.val.val))
    (hzero : ∀ x, F (0, x) = QuaternionicSymmetricMatrices.specialIdentity)
    (hone : ∀ x, F (1, x) = antipode n)
    (henergy : ∀ x, QuaternionicSymmetricMatrices.energy (fun t ↦ F (t, x)) =
      (4 * n : ℝ) * Real.pi ^ 2) : C(X, Space n) where
  toFun x := ⟨midpointMatrix F x,
    midpoint_mem_locus_of_energy_eq_min (hF x) (hzero x) (hone x) (henergy x)⟩
  continuous_toFun := (midpointMatrix F).continuous.subtype_mk _

theorem minimumParameter_formula
    (F : C(ℝ × X, QuaternionicSymmetricMatrices.SpecialSpace (Index n)))
    (hF : ∀ x, ContDiff ℝ ∞ (fun t ↦ (F (t, x)).val.val.val))
    (hzero : ∀ x, F (0, x) = QuaternionicSymmetricMatrices.specialIdentity)
    (hone : ∀ x, F (1, x) = antipode n)
    (henergy : ∀ x, QuaternionicSymmetricMatrices.energy (fun t ↦ F (t, x)) =
      (4 * n : ℝ) * Real.pi ^ 2) (x : X) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    F (t, x) = rotation (minimumParameter F hF hzero hone henergy x) (t * Real.pi) := by
  obtain ⟨J, hJ⟩ := eq_rotation_of_energy_eq_min (hF x) (hzero x) (hone x) (henergy x)
  have hp : minimumParameter F hF hzero hone henergy x = J := by
    apply Subtype.ext
    exact parameter_eq_midpoint J (fun t ↦ F (t, x)) hJ
  rw [hp]
  exact hJ t ht

theorem minimumParameter_unique
    (F : C(ℝ × X, QuaternionicSymmetricMatrices.SpecialSpace (Index n)))
    (hF : ∀ x, ContDiff ℝ ∞ (fun t ↦ (F (t, x)).val.val.val))
    (hzero : ∀ x, F (0, x) = QuaternionicSymmetricMatrices.specialIdentity)
    (hone : ∀ x, F (1, x) = antipode n)
    (henergy : ∀ x, QuaternionicSymmetricMatrices.energy (fun t ↦ F (t, x)) =
      (4 * n : ℝ) * Real.pi ^ 2)
    (G : C(X, Space n))
    (hG : ∀ x t, t ∈ Set.Icc (0 : ℝ) 1 → F (t, x) = rotation (G x) (t * Real.pi)) :
    minimumParameter F hF hzero hone henergy = G := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact parameter_eq_midpoint (G x) (fun t ↦ F (t, x)) (hG x)

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions
