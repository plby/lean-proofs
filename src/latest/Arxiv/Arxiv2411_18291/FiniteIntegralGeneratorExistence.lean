import Arxiv.Arxiv2411_18291.PaperIntegralGeneratorsAtThreshold

/-! # Unconditional integral generators above a uniform explicit threshold -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_paper_integral_generators_explicit {q r n : ℕ} (hqr : r + 1 < q)
    (hn : integralGeneratorThreshold q r ≤ n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J → GeneratedBy D J := by
  have hn0 : paperSizeThreshold q (r + 1) ≤ n := (le_max_left _ _).trans hn
  obtain ⟨D, hD, hgen⟩ := exists_paper_integral_generators_paper_threshold hqr hn0 B hB
  have hθ : 0 ≤ (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact ⟨D, hD.mono (by linarith only [hθ]), hgen⟩

end Arxiv2411_18291
