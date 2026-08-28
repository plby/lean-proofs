import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructures
import Wikipedia.NoExoticSixSphere.OrthogonalMinimumPaths

/-!
# Classification of minimum-energy symplectic antipodal paths

The real orthogonal energy bound applies to every smooth symplectic path.
In its equality case, the recovered complex structure is quaternionic-linear:
it is the midpoint of the path after left translation by its initial point.
Thus restriction of the minimum-energy classification is justified directly,
without restricting an unproved homotopy comparison.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.MinimumPaths

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.OrthogonalPathEnergy
open ComplexStructures

variable {n : ℕ}

theorem antipodal_energy_ge {γ : ℝ → symplecticSubgroup n}
    (hγ : ContDiff ℝ ∞ (fun t => (γ t).val.val.val))
    (hend : (γ 1).val.val.val = -(γ 0).val.val.val) :
    (4 * n + 4 : ℕ) * Real.pi ^ 2 ≤ energy (fun t => (γ t).val.val.val) 0 1 :=
  NoExoticSixSphere.OrthogonalPathEnergy.antipodal_energy_ge
    (γ := fun t => (γ t).val) hγ hend

theorem energy_complexStructure (b : symplecticSubgroup n) (J : Space n) :
    energy (fun t => (b * Exponential.exp (t • (Real.pi • J.val))).val.val.val) 0 1 =
      (4 * n + 4 : ℕ) * Real.pi ^ 2 :=
  NoExoticSixSphere.OrthogonalMinimumPaths.energy_complexStructure b.val (toOrthogonal J)

theorem eq_complexStructure_of_energy_eq_min {γ : ℝ → symplecticSubgroup n}
    (hγ : ContDiff ℝ ∞ (fun t => (γ t).val.val.val))
    (hend : (γ 1).val.val.val = -(γ 0).val.val.val)
    (he : energy (fun t => (γ t).val.val.val) 0 1 = (4 * n + 4 : ℕ) * Real.pi ^ 2) :
    ∃ J : Space n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ t = γ 0 * Exponential.exp (t • (Real.pi • J.val)) := by
  obtain ⟨J, hJ⟩ :=
    NoExoticSixSphere.OrthogonalMinimumPaths.eq_complexStructure_of_energy_eq_min
      (γ := fun t => (γ t).val) hγ hend he
  have hmid : (γ (1 / 2)).val = (γ 0).val *
      NoExoticSixSphere.OrthogonalComplexStructures.toOrthogonal J := by
    rw [hJ (1 / 2) (by norm_num)]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    rw [smul_smul, show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
      NoExoticSixSphere.OrthogonalComplexStructures.exp_smul,
      Real.cos_pi_div_two, Real.sin_pi_div_two,
      zero_smul ℝ (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)), zero_add]
    exact one_smul ℝ _
  have hrelative : ((γ 0)⁻¹ * γ (1 / 2)).val =
      NoExoticSixSphere.OrthogonalComplexStructures.toOrthogonal J := by
    change (γ 0).val⁻¹ * (γ (1 / 2)).val = _
    rw [hmid, inv_mul_cancel_left]
  have hcomm : J.val.val ∈ commutant n := by
    have hmem := (mem_symplecticSubgroup_iff n ((γ 0)⁻¹ * γ (1 / 2)).val).mp
      ((γ 0)⁻¹ * γ (1 / 2)).property
    rw [hrelative] at hmem
    exact hmem
  let Q : Space n := ⟨⟨J.val.val, ⟨J.val.property, hcomm⟩⟩, J.property⟩
  refine ⟨Q, fun t ht => ?_⟩
  apply Subtype.ext
  exact hJ t ht

theorem energy_eq_min_iff {γ : ℝ → symplecticSubgroup n}
    (hγ : ContDiff ℝ ∞ (fun t => (γ t).val.val.val))
    (hend : (γ 1).val.val.val = -(γ 0).val.val.val) :
    energy (fun t => (γ t).val.val.val) 0 1 = (4 * n + 4 : ℕ) * Real.pi ^ 2 ↔
      ∃ J : Space n, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ t = γ 0 * Exponential.exp (t • (Real.pi • J.val)) := by
  constructor
  · exact eq_complexStructure_of_energy_eq_min hγ hend
  · rintro ⟨J, hJ⟩
    rw [energy_congr_Icc zero_le_one
      (fun t ht => congrArg (fun a : symplecticSubgroup n => a.val.val.val) (hJ t ht))]
    exact energy_complexStructure (γ 0) J

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.MinimumPaths
