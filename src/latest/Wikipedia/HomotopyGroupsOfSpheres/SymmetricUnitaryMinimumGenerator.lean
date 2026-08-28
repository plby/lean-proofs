import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryTraceRigidity
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryMidpointRecovery
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryNegativeVariation
import Wikipedia.NoExoticSixSphere.OrthogonalMinimumPaths

/-!
# Recovering the generator of a minimum-energy symmetric unitary path

The orthogonal energy bound applies through the faithful real action.
In the equality case, the midpoint recovers a real symmetric involution.
Determinant one along the entire path then forces its trace to vanish.
-/

noncomputable section

open scoped Matrix.Norms.Operator ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open ImaginarySymmetricMatrices ComplexMatrixRealRepresentation
open NoExoticSixSphere.GLOrthonormalization

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem specialOrthogonal_identity :
    specialOrthogonal (specialIdentity : SpecialSpace N) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact action_one

theorem contDiff_real_path {γ : ℝ → SpecialSpace N}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val)) :
    ContDiff ℝ ∞ (fun t ↦ (specialOrthogonal (γ t)).val.val) := by
  let L : Matrix N N ℂ →L[ℝ] (RealSpace N →L[ℝ] RealSpace N) :=
    (representation (N := N)).toLinearMap.toContinuousLinearMap
  exact L.contDiff.comp hγ

theorem antipodal_energy_ge {γ : ℝ → SpecialSpace N}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val))
    (hend : (γ 1).val.val.val = -(γ 0).val.val.val) :
    (2 * Fintype.card N : ℕ) * Real.pi ^ 2 ≤ energy γ := by
  apply NoExoticSixSphere.OrthogonalPathEnergy.antipodal_energy_ge
    (γ := fun t ↦ specialOrthogonal (γ t)) (contDiff_real_path hγ)
  change action (γ 1).val.val.val = -action (γ 0).val.val.val
  rw [hend]
  change representation (-(γ 0).val.val.val) = -representation (γ 0).val.val.val
  rw [map_neg]

theorem exists_minimum_generator {γ : ℝ → SpecialSpace N}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).val.val.val))
    (hzero : γ 0 = specialIdentity) (hone : (γ 1).val.val.val = -1)
    (henergy : energy γ = (2 * Fintype.card N : ℕ) * Real.pi ^ 2) :
    ∃ A : Matrix N N ℝ, A.transpose = A ∧ A * A = 1 ∧ A.trace = 0 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (γ t).val.val.val = NormedSpace.exp (imaginary ((t * Real.pi) • A)) := by
  let g : ℝ → OrthogonalOperators (2 * Fintype.card N) := fun t ↦ specialOrthogonal (γ t)
  have hgzero : g 0 = 1 := by
    change specialOrthogonal (γ 0) = 1
    rw [hzero, specialOrthogonal_identity]
  have hgend : (g 1).val.val = -(g 0).val.val := by
    change action (γ 1).val.val.val = -action (γ 0).val.val.val
    rw [hone, hzero]
    change representation (-1 : Matrix N N ℂ) = -representation 1
    rw [map_neg]
  obtain ⟨J, hJ⟩ := NoExoticSixSphere.OrthogonalMinimumPaths.eq_complexStructure_of_energy_eq_min
    (γ := g) (contDiff_real_path hγ) hgend henergy
  have hmid : g (1 / 2) = NoExoticSixSphere.OrthogonalComplexStructures.toOrthogonal J := by
    rw [hJ (1 / 2) (by norm_num), hgzero, one_mul]
    apply Subtype.ext
    apply Subtype.ext
    rw [smul_smul, show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
      NoExoticSixSphere.OrthogonalComplexStructures.exp_smul,
      Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, zero_add, one_smul]
    rfl
  have hm : action (γ (1 / 2)).val.val.val = J.val.val :=
    congrArg (fun B : OrthogonalOperators (2 * Fintype.card N) ↦ B.val.val) hmid
  obtain ⟨A, hsym, hsq, hA⟩ := recover_midpoint (γ (1 / 2)).val J hm
  have hraw (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      (γ t).val.val.val = NormedSpace.exp (imaginary ((t * Real.pi) • A)) := by
    apply action_injective
    rw [action_exp, map_smul, action_smul, hA, hm]
    have hj := hJ t ht
    rw [hgzero, one_mul] at hj
    have hp := congrArg (fun B : OrthogonalOperators (2 * Fintype.card N) ↦ B.val.val) hj
    change action (γ t).val.val.val = NormedSpace.exp (t • (Real.pi • J.val.val)) at hp
    simpa only [smul_smul] using hp
  have htrace : A.trace = 0 := by
    apply trace_eq_zero_of_det_pi_exp_interval A hsym
    intro t ht
    rw [← hraw t ht]
    exact congrArg (fun z : Circle ↦ (z : ℂ)) (γ t).property
  exact ⟨A, hsym, hsq, htrace, hraw⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
