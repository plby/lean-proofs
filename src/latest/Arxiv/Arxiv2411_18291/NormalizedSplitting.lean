import Arxiv.Arxiv2411_18291.AbsorberWorkingParameters
import Arxiv.Arxiv2411_18291.ExplicitSplittingFamily
import Arxiv.Arxiv2411_18291.SparseSignedAbsorber

/-! # Finite splitting at the multiplicity-16 absorber parameters -/

noncomputable section

namespace Arxiv2411_18291

theorem exists_normalized_splitting_family_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (8 * q))
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hB : IsGraphBounded B (absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1),
      (D.filter fun P => e.val ⊆ P.val).card ≤ absorberGeneratorMultiplicity q (r + 1)) :
    Nonempty (SplittingFamily S D B (absorberCoefficientCap q (r + 1))
      (splittingFactor S (absorberCoefficientCap q (r + 1))
        (absorberNormalizationFactor q (r + 1)) *
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) := by
  have hSb : S.graph.card ≤ (4 * q) ^ (8 * q) :=
    (hS.trans (paper_exchange_graph_bound (by omega) hqr)).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  rw [splittingFactor_mul]
  exact exists_splitting_family_paper_threshold S hqr hn hw hSb
    (absorberCoefficientCap q (r + 1)) (absorberGeneratorMultiplicity q (r + 1))
    (absorberCoefficientCap_pos _ _) (absorber_splitting_conflict_constant (by omega) hqr)
    (by exact_mod_cast absorberNormalizationFactor_pos q (r + 1))
    (by exact_mod_cast absorber_splitting_density_constant (by omega) hqr) D B hD hB hDB hmult

end Arxiv2411_18291
