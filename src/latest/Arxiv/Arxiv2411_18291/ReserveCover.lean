import Arxiv.Arxiv2411_18291.ExplicitReserveCover

/-!
# The paper's reserve and cover parameters

The Cover lemma holds at the printed threshold with `a = choose(q,r)*ρ`,
where `ρ = (6*choose(q,r))^(-2)`. Combining it with the reserve construction
produces an actual sparse reserve that covers every sufficiently sparse
disjoint leave. Each resulting partial decomposition has exactly one
clique per leave edge and uses only leave and reserve edges. The eventual
interfaces below are corollaries of the finite constructions.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

theorem paper_cover_exponent {K : ℕ} (hK : 1 ≤ K) :
    0 < (K : ℝ) * (1 / (6 * K : ℝ) ^ 2) ∧
      (K : ℝ) * (1 / (6 * K : ℝ) ^ 2) < 1 / 2 := by
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  refine ⟨by positivity, ?_⟩
  rw [mul_one_div]
  apply (div_lt_iff₀ (by positivity)).mpr
  have hsq := mul_le_mul_of_nonneg_left hKreal hKpos.le
  nlinarith

theorem eventually_exists_clique_cover_paper_parameters (q r : ℕ) (hqr : r + 1 < q) :
    let K := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * K : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∀ R L : Hypergraph (Fin n) (r + 1),
      Disjoint L R → IsGraphBounded L ((n : ℝ) ^ (-(3 * K * ρ))) →
      (∀ e ∉ R, (n : ℝ) ^ (-((K : ℝ) * ρ)) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques R e q).card) →
      ∃ Q : L → Block (Fin n) q, IsCliqueCover R (fun e : L => e.val) Q := by
  dsimp only
  filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
  intro R L hLR hL hcount
  exact exists_clique_cover_paper_threshold hqr hn R L hLR hL
    (fun e he => hcount e (fun heR => disjoint_left.mp hLR he heR))

theorem eventually_exists_coverable_reserve (q r : ℕ) (hqr : r + 1 < q) :
    let K := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * K : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∃ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), Disjoint L R →
        IsGraphBounded L ((n : ℝ) ^ (-(3 * K * ρ))) →
        ∃ Q : L → Block (Fin n) q, IsCliqueCover R (fun e : L => e.val) Q := by
  dsimp only
  filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
  exact exists_coverable_reserve_paper_threshold q r n hqr hn

theorem eventually_exists_reserve_cover_decompositions (q r : ℕ) (hqr : r + 1 < q) :
    let K := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * K : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∃ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) ∧
      ∀ L : Hypergraph (Fin n) (r + 1), Disjoint L R →
        IsGraphBounded L ((n : ℝ) ^ (-(3 * K * ρ))) →
        ∃ G : Hypergraph (Fin n) (r + 1), ∃ D : Finset (Block (Fin n) q),
          L ⊆ G ∧ G ⊆ L ∪ R ∧ IsDecomposition G D ∧ D.card = L.card := by
  dsimp only
  filter_upwards [eventually_ge_atTop (paperSizeThreshold q (r + 1))] with n hn
  exact exists_reserve_cover_decompositions_paper_threshold q r n hqr hn

end Arxiv2411_18291
