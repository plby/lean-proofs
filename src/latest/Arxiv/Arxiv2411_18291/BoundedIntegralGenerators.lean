import Arxiv.Arxiv2411_18291.IntegralGeneratorParameters
import Arxiv.Arxiv2411_18291.SparseFlattening
import Arxiv.Arxiv2411_18291.FiniteSparseFlattening
import Arxiv.Arxiv2411_18291.FiniteIntegralGeneratorExistence

/-!
# A sparse integral generating family with fixed edge multiplicity

At the paper's density scales, flatten the `n^(-3α/5)` generating family
to an `n^(-α/2)` family with edge multiplicities at most 16. It generates
every integral vector supported on the reserve. The generalized absorber
accepts this fixed bound; multiplicity two is not needed there. Flattening
and assembly now use explicit valid thresholds. The typical and modular host
and all rainbow colour experiments are constructed at n0. The assembly
coefficient is bounded uniformly in q and r, so the final threshold has
no dependence on an unspecified exchange or palette.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

def boundedIntegralGeneratorThreshold (q r : ℕ) : ℕ :=
  max (integralGeneratorThreshold q r) (finiteFlatteningThreshold q r)

theorem exists_bounded_integral_generators_explicit {q r n : ℕ} (hqr : r + 1 < q)
    (hn : boundedIntegralGeneratorThreshold q r ≤ n) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) ∧
      (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ 16) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J → GeneratedBy D J := by
  obtain ⟨D, hD, hspan⟩ := exists_paper_integral_generators_explicit hqr
    ((le_max_left _ _).trans hn) B hB
  obtain ⟨F, hF, hDF, hm⟩ := exists_sparse_flattening_explicit hqr
    ((le_max_right _ _).trans hn) D hD
  exact ⟨F, hF, hm, fun J hs hJ => hDF J (hspan J hs hJ)⟩

theorem eventually_exists_bounded_integral_generators_paper_parameters
    (q r : ℕ) (hqr : r + 1 < q) :
    let k := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
    let α : ℝ := ρ / (2 * q : ℝ) ^ (r + 1)
    ∀ᶠ n : ℕ in atTop, ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ D : Finset (Block (Fin n) q), IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(α / 2))) ∧
        (∀ e : Block (Fin n) (r + 1), (D.filter fun Q => e.val ⊆ Q.val).card ≤ 16) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J → GeneratedBy D J := by
  dsimp only
  filter_upwards [eventually_ge_atTop (boundedIntegralGeneratorThreshold q r)] with n hn
  exact exists_bounded_integral_generators_explicit hqr hn

end Arxiv2411_18291
