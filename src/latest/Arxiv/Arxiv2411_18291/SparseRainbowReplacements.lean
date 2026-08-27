import Arxiv.Arxiv2411_18291.RainbowExchangeReplacements
import Arxiv.Arxiv2411_18291.ExchangeCliqueCounts

/-!
# Rainbow replacements at the sparse-host parameters

The exchange clique counts put the combined near-frame and collision
exponent below `5 * α * |H|`. Thus `α*h ≤ 1/12` leaves room for a
polynomial failure bound and finitely many trials, uniformly over every
initial colour family.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {J W : Type*} [Fintype J] [Fintype W] [DecidableEq W] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

theorem eventually_sparse_host_rainbow_replacements (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (h : ℕ) (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 12) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h →
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K →
      ∀ D : Finset (Block (Fin n) q), D ⊆ cliqueFamily K q →
      (((cliqueFamily K q) \ D).card : ℝ) ≤
        (n : ℝ) ^ (-(α / 10)) * (cliqueFamily K q).card →
      ∀ G : Hypergraph (Fin n) (r + 1),
      (∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(α / 10)) * cliqueMainTerm n (density K) q (r + 1) (r + 1)) →
      ∀ σ : J → Equiv.Perm (Fin n),
      ∃ τ : Fin L × S.farCliques → Equiv.Perm (Fin n), ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding G) (cliqueEdges (r + 1) Q) →
        ∃ f : W ↪ Fin n, mapBlock f S.base = Q ∧
          ∀ P ∈ S.replacementCliques,
            mapBlock f P ∈ permutedUnion σ D ∪ permutedUnion τ D := by
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr.le)).trans hqh
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hα1 : α ≤ 1 / 12 := by nlinarith only [hhR, hαh, hα]
  have hk : α * q.choose (r + 1) ≤ 1 / 12 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hqh) hα.le).trans hαh
  have hpred : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) ≤ 1 / 12 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le (q.choose (r + 1)) 1)
      hα.le).trans hk
  have hS : α * S.graph.card ≤ 1 / 12 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hSh) hα.le).trans hαh
  have he := hA.colour_exponent_le (Nat.succ_pos r) hα.le
  obtain ⟨L, hL⟩ := exists_trial_number q (by positivity : (0 : ℝ) < α / 100)
  refine ⟨L, eventually_rainbow_exchange_replacements hA hqr h L hqh
    (b := 1 / 2) (α := α) (δ := 1 / 10) (τ := α / 10) (γ := α / 50)
    (χ := α / 25) (κ := α / 100) (by norm_num) hα.le (by positivity)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith only [hpred]) (by linarith only [hk])
    (by linarith only [he, hS, hα1]) hL⟩

end Arxiv2411_18291
