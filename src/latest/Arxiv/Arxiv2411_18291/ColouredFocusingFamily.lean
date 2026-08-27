import Arxiv.Arxiv2411_18291.ColouredFocusingCounts
import Arxiv.Arxiv2411_18291.SparseFocusingFamily

/-!
# Sparse focusing into the union of the colour graphs

The proved rainbow punctured-clique count discharges the candidate-size
condition for sparse focusing. The resulting fixed family works for every
integrally decomposable signed vector supported on the input graph.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {I : Type*} [Fintype I]

theorem eventually_exists_coloured_focusing_family (q r : ℕ) (hq : r + 1 ≤ q)
    {b α a ρ : ℝ} (hb : 0 < b) (ha : 0 ≤ a)
    (hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < a)
    (hρ : 2 * a < ρ) (hρ1 : ρ - a < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      b * (n : ℝ) ^ (-α) ≤ density G → ∀ σ : I → Equiv.Perm (Fin n),
      (∀ e : Block (Fin n) (r + 1),
        ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
          (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
            (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card) →
      ∀ B : Hypergraph (Fin n) (r + 1), IsGraphBounded B ((n : ℝ) ^ (-ρ)) →
      ∃ F : Finset (Block (Fin n) q),
        IsCliqueFamilyBounded r F ((n : ℝ) ^ (-ρ) + q.choose (r + 1) *
          (4 * (r + 1).factorial * (n : ℝ) ^ (-(ρ - a)))) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J →
          ∃ K : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - K) ∧
            (∀ e, e ∉ permutedUnion σ G → K e = 0) ∧ IntegrallyDecomposable q K := by
  filter_upwards [eventually_coloured_punctured_clique_count (I := I) q r hb hgap,
    eventually_exists_sparse_focusing_family q r hq ha hρ hρ1] with n hcount hfocus
  intro G hd σ hG B hB
  exact hfocus B (permutedUnion σ G) hB (fun e _ => hcount G hd σ hG e)

end Arxiv2411_18291
