import ErdosProblems.Erdos980.External.CebotarevDensity.ForMathlib.IdealCongruenceCount
import ErdosProblems.Erdos980.External.CebotarevDensity.NumberFieldEulerProduct
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# Checked interfaces for a Landau-style prime-ideal theorem

This file records two elementary bridges that are already supported by the repository:

* the effective norm-residue count at modulus `1` is the effective count of all nonzero
  integral ideals;
* the leading constant is the positive Dedekind-zeta residue.

The analytic prime-ideal theorem itself requires further work described in `README.md`.
-/

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace Erdos980.NaturalChebotarev.PrimeIdealTheorem.Landau

/-- The effective ideal-congruence theorem at modulus `1` gives the standard effective count
of all nonzero integral ideals. -/
theorem exists_effective_nonzeroIdeal_count
    (K : Type*) [Field K] [NumberField K] :
    ∃ κ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} : ℝ)
          - κ * N|
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨κ, C, h⟩ :=
    Chebotarev.exists_card_norm_le_norm_residue_eq_sub_mul_rpow_le K 1 (0 : ZMod 1)
  refine ⟨κ, C, fun N hN ↦ ?_⟩
  let e :
      {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} ≃
        {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N ∧
          ((Ideal.absNorm (I : Ideal (𝓞 K)) : ZMod 1)) = 0} :=
    Equiv.subtypeEquivRight fun I ↦
      ⟨fun hI ↦ ⟨hI, Subsingleton.elim _ _⟩, fun hI ↦ hI.1⟩
  rw [Nat.card_congr e]
  exact h N hN

/-- A power-saving estimate `f N = κ N + O(N^(1-1/d))` determines `κ` as the limit of
`f N / N`.  The helper is public here because the corresponding proof internal to the
ideal-congruence development is intentionally private. -/
theorem tendsto_div_atTop_of_effective_count {f : ℕ → ℝ} {κ C : ℝ} {d : ℕ}
    (hd : 0 < d)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      |f N - κ * N| ≤ C * (N : ℝ) ^ (1 - (d : ℝ)⁻¹)) :
    Filter.Tendsto (fun N : ℕ ↦ f N / (N : ℝ)) Filter.atTop (nhds κ) := by
  have hdpos : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
  have hzero : Filter.Tendsto
      (fun N : ℕ ↦ |C| * (N : ℝ) ^ (-(d : ℝ)⁻¹))
      Filter.atTop (nhds 0) := by
    have hreal : Filter.Tendsto (fun x : ℝ ↦ x ^ (-(d : ℝ)⁻¹))
        Filter.atTop (nhds 0) := tendsto_rpow_neg_atTop hdpos
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    simpa using hnat.const_mul |C|
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N ↦ norm_nonneg _) ?_ hzero
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.zero_lt_one.trans_le hN
  rw [Real.norm_eq_abs, div_sub' hNpos.ne', abs_div, abs_of_pos hNpos,
    div_le_iff₀ hNpos, mul_comm (N : ℝ) κ]
  refine (hbound N hN).trans ?_
  have hsplit : (N : ℝ) ^ (1 - (d : ℝ)⁻¹) =
      (N : ℝ) ^ (-(d : ℝ)⁻¹) * (N : ℝ) := by
    rw [show (1 : ℝ) - (d : ℝ)⁻¹ = -(d : ℝ)⁻¹ + 1 by ring,
      Real.rpow_add hNpos, Real.rpow_one]
  rw [hsplit, ← mul_assoc]
  gcongr
  exact le_abs_self C

/-- Effective all-ideal counting with its canonical, positive leading constant. -/
theorem exists_effective_nonzeroIdeal_count_residue
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |(Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} : ℝ)
          - NumberField.dedekindZeta_residue K * N|
        ≤ C * (N : ℝ) ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨κ, C, hbound⟩ := exists_effective_nonzeroIdeal_count K
  have hκ := tendsto_div_atTop_of_effective_count Module.finrank_pos hbound
  have hres : Filter.Tendsto
      (fun N : ℕ ↦
        (Nat.card {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} : ℝ) /
          (N : ℝ))
      Filter.atTop (nhds (NumberField.dedekindZeta_residue K)) := by
    have h := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop
    rw [NumberField.dedekindZeta_residue_def]
    refine h.congr' ?_
    filter_upwards with N
    let e :
        {I : (Ideal (𝓞 K))⁰ //
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ (N : ℝ)} ≃
        {I : (Ideal (𝓞 K))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N} :=
      Equiv.subtypeEquivRight fun I ↦ by simp only [Nat.cast_le]
    simp only [Function.comp_apply]
    rw [Nat.card_congr e]
  have hκeq : κ = NumberField.dedekindZeta_residue K :=
    tendsto_nhds_unique hκ hres
  exact ⟨C, by simpa [hκeq] using hbound⟩

end Erdos980.NaturalChebotarev.PrimeIdealTheorem.Landau
