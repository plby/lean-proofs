/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Single-degree local root tails from exact circular second moments.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CircleMoments
import ErdosProblems.Erdos521.LocalRootBounds

namespace Erdos521

open MeasureTheory Filter Metric

theorem localRootCount_single_pow_le (n : ℕ) (c : ℝ) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (ε : ℕ → ℝ)
    (hcenter : δ ≤ |powerSum ε (n + 1) c|) :
    δ ^ 2 * (4 : ℝ) ^ localRootCount ε n c r ≤
      2 * (1 + circularMeanSquare n (c : ℂ) (4 * r) ε) := by
  classical
  let T := (realRoots ε n).filter fun x ↦ |x - c| ≤ r
  let S := T.image (fun x : ℝ ↦ (x : ℂ))
  have hcard : S.card = localRootCount ε n c r :=
    Finset.card_image_of_injective T Complex.ofReal_injective
  have hS : ∀ z ∈ S, z ∈ closedBall (c : ℂ) r ∧
      ((polynomial ε n).map Complex.ofRealHom).eval z = 0 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hxroot, hxdist⟩ := Finset.mem_filter.mp hx
    have hxzero : (polynomial ε n).eval x = 0 :=
      Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp hxroot)
    constructor
    · simpa only [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hxdist
    · rw [complex_polynomial_eval, complexPowerSum_ofReal, ← polynomial_eval, hxzero]
      simp
  have hB := circularMeanSquare_nonneg n (c : ℂ) (4 * r) ε
  have h := polynomial_zeros_pow_le ((polynomial ε n).map Complex.ofRealHom) (c : ℂ)
    hδ (by simpa only [complex_polynomial_eval, complexPowerSum_ofReal,
      Complex.norm_real, Real.norm_eq_abs] using hcenter) hr
    (by linarith : 1 ≤ 1 + circularMeanSquare n (c : ℂ) (4 * r) ε)
    (by simp only [complex_polynomial_eval]; exact le_add_of_nonneg_left zero_le_one) S hS
  rwa [hcard] at h

theorem localRootCount_single_large_center_probability (n k : ℕ) (c : ℝ) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) :
    sequenceLaw.real {ε | δ ≤ |powerSum ε (n + 1) c| ∧ k ≤ localRootCount ε n c r} ≤
      2 * (1 + geometricVariance (|c| + 4 * r) (n + 1)) / (δ ^ 2 * (4 : ℝ) ^ k) := by
  let f := fun ε ↦ 1 + circularMeanSquare n (c : ℂ) (4 * r) ε
  have hf : Integrable f sequenceLaw := (integrable_const 1).add (circularMeanSquare_integrable n _ _)
  have hf₀ : 0 ≤ᵐ[sequenceLaw] f := Eventually.of_forall fun ε ↦ by
    have h := circularMeanSquare_nonneg n (c : ℂ) (4 * r) ε
    dsimp [f]
    linarith
  have h := measureReal_le_integral_div_of_ae sequenceLaw hf hf₀
    (by positivity : 0 < δ ^ 2 * (4 : ℝ) ^ k / 2) (E := {ε |
      δ ≤ |powerSum ε (n + 1) c| ∧ k ≤ localRootCount ε n c r}) ?_
  · have hint : (∫ ε, f ε ∂sequenceLaw) ≤ 1 + geometricVariance (|c| + 4 * r) (n + 1) := by
      dsimp [f]
      rw [integral_add (integrable_const 1) (circularMeanSquare_integrable n _ _)]
      have hbound := integral_circularMeanSquare_le n (c : ℂ) (4 * r)
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 4 * r)] at hbound
      simpa using add_le_add (le_refl (1 : ℝ)) hbound
    apply h.trans
    calc
      (∫ ε, f ε ∂sequenceLaw) / (δ ^ 2 * (4 : ℝ) ^ k / 2) ≤
          (1 + geometricVariance (|c| + 4 * r) (n + 1)) / (δ ^ 2 * (4 : ℝ) ^ k / 2) :=
        div_le_div_of_nonneg_right hint (by positivity)
      _ = _ := by ring
  · filter_upwards [] with ε hε
    have hpow : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ localRootCount ε n c r :=
      pow_le_pow_right₀ (by norm_num) hε.2
    have hmul := mul_le_mul_of_nonneg_left hpow (sq_nonneg δ)
    have hroot := localRootCount_single_pow_le n c hr hδ ε hε.1
    dsimp [f]
    linarith

theorem localRootCount_single_probability_split (n k : ℕ) (c : ℝ) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) :
    sequenceLaw.real {ε | k ≤ localRootCount ε n c r} ≤
      sequenceLaw.real {ε | |powerSum ε (n + 1) c| ≤ δ} +
        2 * (1 + geometricVariance (|c| + 4 * r) (n + 1)) / (δ ^ 2 * (4 : ℝ) ^ k) := by
  have hsub : {ε | k ≤ localRootCount ε n c r} ⊆
      {ε | |powerSum ε (n + 1) c| ≤ δ} ∪
        {ε | δ ≤ |powerSum ε (n + 1) c| ∧ k ≤ localRootCount ε n c r} := by
    intro ε hε
    rcases le_total |powerSum ε (n + 1) c| δ with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hε⟩
  apply ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
  exact add_le_add le_rfl (localRootCount_single_large_center_probability n k c hr hδ)

end Erdos521
