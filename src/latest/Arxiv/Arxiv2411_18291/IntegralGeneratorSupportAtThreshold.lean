import Arxiv.Arxiv2411_18291.PaperIntegralGeneratorsAtThreshold
import Arxiv.Arxiv2411_18291.AbsorberFromGenerators

/-! # Integral generators together with their support at n0

The source graph and the generator support each use at most half the
`n^(-3*alpha/5)` budget. Their union is therefore a valid input graph for
the weighted decoder and variable-capacity splitting construction.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem paper_source_half_generator_density {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (n : ℝ) ^ (-paperRho q (r + 1)) ≤
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hsource : (n : ℝ) ^ (-paperRho q (r + 1)) ≤
      (n : ℝ) ^ (-paperAlpha q (r + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg (paperAlpha_le_rho hqr))
  have hg := paper_threshold_alpha_rpow_lower (s := 1) hqr hn
    (by norm_num : (0 : ℝ) ≤ 2 / 5) (by linarith only [hq])
  have htwo : (2 : ℝ) ≤ (n : ℝ) ^ (paperAlpha q (r + 1) * (2 / 5)) :=
    (by simp only [pow_one]; linarith only [hq] : (2 : ℝ) ≤ (4 * q : ℝ) ^ 1).trans hg
  have hscale := mul_le_mul_of_nonneg_right htwo
    (Real.rpow_nonneg hn0.le (-paperAlpha q (r + 1)))
  have heq : (n : ℝ) ^ (paperAlpha q (r + 1) * (2 / 5)) *
      (n : ℝ) ^ (-paperAlpha q (r + 1)) =
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [heq] at hscale
  linarith only [hsource, hscale]

theorem exists_paper_integral_generators_with_support {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      IsGraphBounded (B ∪ cliqueSupport (r + 1) D)
        ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J → GeneratedBy D J := by
  obtain ⟨D, hD, hgen⟩ := exists_paper_integral_generators_paper_threshold hqr hn B hB
  have hθ : 0 ≤ (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨D, hD.mono (by linarith only [hθ]), ?_, hgen⟩
  have hh := (hB.mono (paper_source_half_generator_density hqr hn)).union hD.support_graphBounded
  simpa only [add_halves] using hh

end Arxiv2411_18291
