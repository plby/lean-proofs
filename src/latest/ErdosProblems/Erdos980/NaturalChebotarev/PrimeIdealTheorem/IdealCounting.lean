import CebotarevDensity.NumberFieldEulerProduct

/-!
# Summatory ideal-norm multiplicities

This file records the exact bridge between the Dirichlet-series coefficients of the Dedekind
zeta function and Mathlib's geometry-of-numbers ideal-counting theorem.  It is the non-prime
counting input used in elementary proofs of the prime ideal theorem.
-/

noncomputable section

open Filter NumberField
open scoped Topology nonZeroDivisors

namespace Chebotarev

section IdealCounting

variable (K : Type*) [Field K] [NumberField K]

/-- Summing `idealNormMultiplicity` through `N` counts exactly the nonzero integral ideals of
absolute norm at most `N`. -/
theorem sum_idealNormMultiplicity_eq_card_norm_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, idealNormMultiplicity K k =
      Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ N} := by
  classical
  have h_finite : ∀ b : ℕ, {I : NonzeroIdeal K | Ideal.absNorm I.1 = b}.Finite := fun b ↦
    Set.Finite.preimage (f := fun I : NonzeroIdeal K ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) b)
  have key := Finset.card_preimage_eq_sum_card_image_eq
    (f := fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) (s := Finset.Icc 1 N)
    (fun b _ ↦ h_finite b)
  rw [show ((fun I : NonzeroIdeal K ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 N)) =
      {I : NonzeroIdeal K | Ideal.absNorm I.1 ≤ N} by
    ext ⟨I, hI⟩
    simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨fun h ↦ h.2, fun h ↦
      ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
  exact key.symm

/-- The subtype of nonzero ideals used by the Euler-product development and Mathlib's
`nonZeroDivisors` subtype have the same bounded-norm cardinality. -/
theorem card_nonzeroIdeal_norm_le_eq_card_nonZeroDivisor_norm_le (N : ℕ) :
    Nat.card {I : NonzeroIdeal K // Ideal.absNorm I.1 ≤ N} =
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm I.1 ≤ N} := by
  exact Nat.card_congr
    { toFun := fun ⟨⟨I, hI⟩, hN⟩ ↦
        ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, hN⟩
      invFun := fun ⟨⟨I, hI⟩, hN⟩ ↦
        ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, hN⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- The cumulative Dedekind-zeta coefficient count is asymptotic to the residue of `ζ_K` times
`N`.  This is a direct restatement of Mathlib's geometry-of-numbers ideal-counting theorem. -/
theorem tendsto_sum_idealNormMultiplicity_div :
    Tendsto
      (fun N : ℕ ↦
        (∑ k ∈ Finset.Icc 1 N, (idealNormMultiplicity K k : ℝ)) / (N : ℝ))
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  have h := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop
  rw [NumberField.dedekindZeta_residue_def]
  apply h.congr'
  filter_upwards with N
  change (Nat.card {I : (Ideal (𝓞 K))⁰ //
      ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (N : ℝ)} : ℝ) / (N : ℝ) = _
  rw [← Nat.cast_sum, sum_idealNormMultiplicity_eq_card_norm_le K N,
    card_nonzeroIdeal_norm_le_eq_card_nonZeroDivisor_norm_le K N]
  rw [show Nat.card {I : (Ideal (𝓞 K))⁰ //
        ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (N : ℝ)} =
      Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm I.1 ≤ N} from
    Nat.card_congr
      { toFun := fun ⟨I, hI⟩ ↦ ⟨I, by exact_mod_cast hI⟩
        invFun := fun ⟨I, hI⟩ ↦ ⟨I, by exact_mod_cast hI⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }]

end IdealCounting

end Chebotarev
