import Arxiv.Arxiv2411_18291.Decomposition

/-!
# Nonnegative boundary forces a unique available partner

If at most one possible positive clique covers an edge, the presence of
a negative clique there forces that positive clique to occur. The same
count shows that no second negative clique can cover that edge.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem signed_edge_partner_forced (P N : Finset (Block V q)) (e : Block V r)
    (Q R : Block V q) (hR : R ∈ N) (heR : e ∈ cliqueEdges r R)
    (hnonneg : 0 ≤ boundary r (indicator P - indicator N) e)
    (hpos : ∀ T ∈ P, e ∈ cliqueEdges r T → T = Q) :
    Q ∈ P ∧ ∀ T ∈ N, e ∈ cliqueEdges r T → T = R := by
  have hcount : (N.filter fun T => e.val ⊆ T.val).card ≤
      (P.filter fun T => e.val ⊆ T.val).card := by
    rw [boundary_sub, Pi.sub_apply, boundary_indicator, boundary_indicator] at hnonneg
    exact_mod_cast sub_nonneg.mp hnonneg
  have hp : P.filter (fun T => e.val ⊆ T.val) ⊆ {Q} := by
    intro T hT
    exact mem_singleton.mpr (hpos T (mem_filter.mp hT).1
      ((mem_cliqueEdges _ _).mpr (mem_filter.mp hT).2))
  have hcard : (N.filter fun T => e.val ⊆ T.val).card ≤ 1 :=
    hcount.trans ((card_le_card hp).trans_eq (card_singleton Q))
  have hRfilter : R ∈ N.filter (fun T => e.val ⊆ T.val) :=
    mem_filter.mpr ⟨hR, (mem_cliqueEdges _ _).mp heR⟩
  have hposcard : 0 < (P.filter fun T => e.val ⊆ T.val).card :=
    (card_pos.mpr ⟨R, hRfilter⟩).trans_le hcount
  obtain ⟨T, hT⟩ := card_pos.mp hposcard
  have hTQ := mem_singleton.mp (hp hT)
  refine ⟨hTQ ▸ (mem_filter.mp hT).1, ?_⟩
  intro T hT heT
  exact card_le_one.mp hcard T (mem_filter.mpr ⟨hT, (mem_cliqueEdges _ _).mp heT⟩) R hRfilter

end Arxiv2411_18291
