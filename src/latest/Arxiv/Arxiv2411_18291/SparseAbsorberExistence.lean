import Arxiv.Arxiv2411_18291.BoundedIntegralGenerators
import Arxiv.Arxiv2411_18291.FiniteAbsorberFromGenerators

/-!
# Unconditional sparse absorbers at the paper's density parameters

The integral generating family has multiplicity at most 16. All subsequent
decoders, splitting, cancellation, and density estimates hold at the printed
threshold. The generating family uses finite colour experiments and explicit
assembly and flattening thresholds, which are not all certified below n0.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_absorber_explicit {q r n : ℕ} (hqr : r + 1 < q)
    (hn : boundedIntegralGeneratorThreshold q r ≤ n) (R : Hypergraph (Fin n) (r + 1))
    (hR : IsGraphBounded R ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ H : Hypergraph (Fin n) (r + 1), IsAbsorber q H R ∧
      IsGraphBounded H ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) := by
  have hnI : integralGeneratorThreshold q r ≤ n := (le_max_left _ _).trans hn
  have hn0 : paperSizeThreshold q (r + 1) ≤ n := (le_max_left _ _).trans hnI
  obtain ⟨D, hD, hmult, hspan⟩ := exists_bounded_integral_generators_explicit hqr hn R hR
  exact exists_sparse_absorber_paper_threshold_of_generators hqr hn0 R hR D hD hmult hspan

theorem eventually_exists_sparse_absorber_paper_parameters (q r : ℕ) (hqr : r + 1 < q) :
    let k := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * k : ℝ) ^ 2
    let α : ℝ := ρ / (2 * q : ℝ) ^ (r + 1)
    ∀ᶠ n : ℕ in atTop, ∀ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) →
      ∃ H : Hypergraph (Fin n) (r + 1), IsAbsorber q H R ∧
        IsGraphBounded H ((n : ℝ) ^ (-(α / 4))) := by
  dsimp only
  filter_upwards [eventually_ge_atTop (boundedIntegralGeneratorThreshold q r)] with n hn
  exact exists_sparse_absorber_explicit hqr hn

end Arxiv2411_18291
