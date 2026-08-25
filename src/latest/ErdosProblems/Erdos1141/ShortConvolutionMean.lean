import ErdosProblems.Erdos1141.ConvolutionMean
import ErdosProblems.Erdos1141.LinearPrefixAbel
import ErdosProblems.Erdos1141.ShortMeanParameters

/-!
# A convolution mean below the square-root threshold
-/

open scoped BigOperators

namespace Erdos1141

open BoundedGaps.Maynard

lemma sum_Icc_add_sum_Ioc_eq {R : Type*} [AddCommMonoid R] (f : ℕ → R)
    {D M : ℕ} (hDM : D ≤ M) :
    (∑ n ∈ Finset.Icc 1 D, f n) + (∑ n ∈ Finset.Ioc D M, f n) =
      ∑ n ∈ Finset.Icc 1 M, f n := by
  have hd : Disjoint (Finset.Icc 1 D) (Finset.Ioc D M) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    omega
  rw [← Finset.sum_union hd]
  congr 1
  ext n
  simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
  omega

theorem norm_LFunction_one_sub_prefix_le_of_linear_prefix {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (K : ℝ) (hK : 0 ≤ K) (D M : ℕ) (hD : 0 < D) (hDM : D ≤ M)
    (hprefix : ∀ N : ℕ, D ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)‖ ≤ (N : ℝ) * K) :
    ‖χ.LFunction 1 - ∑ n ∈ Finset.Icc 1 D, χ (n : ZMod q) / n‖ ≤
      K * (3 + Real.log (M : ℝ)) + 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / M := by
  have hf0 : χ ((0 : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_zero] using χ.map_zero' (Nat.ne_of_gt hq)
  have hfinite := norm_reciprocal_interval_le_of_linear_prefix
    (fun n ↦ χ (n : ZMod q)) hf0 K hK D M hD hDM hprefix
  have hinfinite := norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    hq χ hχ M (hD.trans_le hDM)
  have hsum := sum_Icc_add_sum_Ioc_eq (fun n ↦ χ (n : ZMod q) / (n : ℂ)) hDM
  have hid : χ.LFunction 1 - ∑ n ∈ Finset.Icc 1 D, χ (n : ZMod q) / n =
      (∑ n ∈ Finset.Ioc D M, χ (n : ZMod q) / n) +
        (χ.LFunction 1 - ∑ n ∈ Finset.Icc 1 M, χ (n : ZMod q) / n) := by
    linear_combination -hsum
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hfinite hinfinite)

theorem norm_zetaMul_prefix_sub_main_le_of_linear_prefix {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (K : ℝ) (hK : 0 ≤ K) (X D M : ℕ) (hD : 0 < D) (hDX : D ≤ X) (hDM : D ≤ M)
    (hprefix : ∀ N : ℕ, D ≤ N →
      ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)‖ ≤ (N : ℝ) * K) :
    ‖(∑ n ∈ Finset.Icc 1 X, χ.zetaMul n) - (X : ℂ) * χ.LFunction 1‖ ≤
      (D : ℝ) + X * K * (5 + Real.log (X : ℝ) + Real.log (M : ℝ)) +
        (4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * X / M := by
  rw [zetaMul_prefix_eq_sum_mul_div]
  apply (norm_sum_mul_div_sub_main_le_of_linear_prefix (fun n ↦ χ (n : ZMod q))
    (fun n ↦ χ.norm_le_one n) K _ hK (χ.LFunction 1) X D hD hDX hprefix
    (norm_LFunction_one_sub_prefix_le_of_linear_prefix hq χ hχ K hK D M hD hDM hprefix)).trans
  apply le_of_eq
  ring

/-- A power saving in the convolution mean at a cutoff strictly below `sqrt M`. -/
theorem exists_short_convolution_mean_cutoff :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M →
      ∀ q : ℕ, [NeZero q] → 1 < q → q ≤ M →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      (∀ N : ℕ, (M : ℝ) ^ (15 / 32 : ℝ) ≤ (N : ℝ) →
        ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)‖ ≤
          (N : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ)) →
      let X := ⌊(M : ℝ) ^ (31 / 64 : ℝ)⌋₊
      0 < X ∧ X ≤ M ∧
        ‖(∑ n ∈ Finset.Icc 1 X, χ.zetaMul n) - (X : ℂ) * χ.LFunction 1‖ ≤
          3 * (X : ℝ) * (M : ℝ) ^ (-1 / 1024 : ℝ) := by
  obtain ⟨M0, hcut⟩ := exists_short_mean_parameter_cutoff
  refine ⟨M0, ?_⟩
  intro M hM q _ hq hqM χ hχ hprefix
  let X := ⌊(M : ℝ) ^ (31 / 64 : ℝ)⌋₊
  let D := ⌈(M : ℝ) ^ (15 / 32 : ℝ)⌉₊
  obtain ⟨hX, hD, hDX, hXM, herror⟩ := hcut M hM
  refine ⟨hX, hXM, ?_⟩
  have hprefix' : ∀ N : ℕ, D ≤ N → ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)‖ ≤
      (N : ℝ) * (M : ℝ) ^ (-1 / 512 : ℝ) := by
    intro N hN
    apply hprefix N
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN)
  exact (norm_zetaMul_prefix_sub_main_le_of_linear_prefix hq χ hχ _ (by positivity)
    X D M hD hDX (hDX.trans hXM) hprefix').trans (herror q hq hqM)

end Erdos1141
