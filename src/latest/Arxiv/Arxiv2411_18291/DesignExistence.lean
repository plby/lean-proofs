import Arxiv.Arxiv2411_18291.GlobalDivisibility
import Arxiv.Arxiv2411_18291.HigherRankDesignExistence
import Arxiv.Arxiv2411_18291.RankOneDesign
import Arxiv.Arxiv2411_18291.FinitePaperFlattening

/-!
# Theorem 1.1: existence of designs

For every `q > r ≥ 1`, all sufficiently large divisible complete
`r`-graphs have an actual `K_q^r`-decomposition. The proof constructs the
reserve, absorber, regular clique family, approximate packing, and cover;
none of those constructions is assumed. Rank one is handled by a partition.

The qualitative theorem now follows from a uniform explicit corrected
threshold. This bound includes the larger flattening cost and is not the
numerical value proposed in the paper; it is strictly larger for triangles.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

/-- A uniform sufficient bound, including all palette, assembly, and
flattening costs. Rank one needs no size restriction. -/
def correctedDesignThreshold (q r : ℕ) : ℕ :=
  if r = 1 then 0 else boundedIntegralGeneratorThreshold q (r - 1)

theorem design_existence_explicit {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : correctedDesignThreshold q r ≤ n) :
    Divisible q (complete (Fin n) r) →
      HasDecomposition q (complete (Fin n) r) := by
  cases r with
  | zero => omega
  | succ r =>
    by_cases hr0 : r = 0
    · subst r
      exact hasDecomposition_complete_one_of_divisible
    · have hn' : boundedIntegralGeneratorThreshold q r ≤ n := by
        simpa only [correctedDesignThreshold, show r + 1 ≠ 1 by omega,
          if_false, Nat.add_sub_cancel] using hn
      exact hasDecomposition_complete_succ_explicit (by omega) hqr hn'

theorem flatteningThreshold_le_correctedDesignThreshold (q r : ℕ) (hr : 2 ≤ r) :
    finiteFlatteningThreshold q (r - 1) ≤ correctedDesignThreshold q r := by
  rw [correctedDesignThreshold, if_neg (by omega), boundedIntegralGeneratorThreshold]
  exact le_max_right _ _

theorem correctedDesignThreshold_triangle_gt_printed :
    paperSizeThreshold 3 2 < correctedDesignThreshold 3 2 :=
  triangle_threshold_lt_finiteFlatteningThreshold.trans_le
    (flatteningThreshold_le_correctedDesignThreshold 3 2 (by decide))

theorem eventually_hasDecomposition_complete (q r : ℕ) (hr : 1 ≤ r) (hqr : r < q) :
    ∀ᶠ n : ℕ in atTop, Divisible q (complete (Fin n) r) →
      HasDecomposition q (complete (Fin n) r) := by
  filter_upwards [eventually_ge_atTop (correctedDesignThreshold q r)] with n hn
  exact design_existence_explicit hr hqr hn

/-- Theorem 1.1 of *A short proof of the existence of designs*. -/
theorem design_existence (q r : ℕ) (hr : 1 ≤ r) (hqr : r < q) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → Divisible q (complete (Fin n) r) →
      HasDecomposition q (complete (Fin n) r) :=
  ⟨correctedDesignThreshold q r, fun _ hn => design_existence_explicit hr hqr hn⟩

theorem hasDecomposition_iff_binomial_divisibility_explicit {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r < q)
    (hn : max (correctedDesignThreshold q r) (q + r) ≤ n) :
    HasDecomposition q (complete (Fin n) r) ↔
      ∀ i ≤ r, (q - i).choose (r - i) ∣ (n - i).choose (r - i) := by
  have hqn : q + r ≤ n := (le_max_right _ _).trans hn
  have hcriterion := complete_divisible_iff (V := Fin n) hqr.le
    (by simpa only [Fintype.card_fin] using hqn)
  simp only [Fintype.card_fin] at hcriterion
  exact ⟨fun h => hcriterion.mp h.divisible,
    fun h => design_existence_explicit hr hqr ((le_max_left _ _).trans hn) (hcriterion.mpr h)⟩

/-- The standard numerical divisibility conditions are necessary and,
for every sufficiently large vertex set, sufficient. -/
theorem eventually_hasDecomposition_iff_binomial_divisibility
    (q r : ℕ) (hr : 1 ≤ r) (hqr : r < q) :
    ∀ᶠ n : ℕ in atTop,
      HasDecomposition q (complete (Fin n) r) ↔
        ∀ i ≤ r, (q - i).choose (r - i) ∣ (n - i).choose (r - i) := by
  filter_upwards [eventually_ge_atTop (max (correctedDesignThreshold q r) (q + r))] with n hn
  exact hasDecomposition_iff_binomial_divisibility_explicit hr hqr hn

theorem design_existence_iff_binomial_divisibility (q r : ℕ) (hr : 1 ≤ r) (hqr : r < q) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (HasDecomposition q (complete (Fin n) r) ↔
        ∀ i ≤ r, (q - i).choose (r - i) ∣ (n - i).choose (r - i)) :=
  ⟨max (correctedDesignThreshold q r) (q + r),
    fun _ hn => hasDecomposition_iff_binomial_divisibility_explicit hr hqr hn⟩

end Arxiv2411_18291
