import ErdosProblems.Erdos19.PairCompletion

/-! # Charging large edges to missing pairs of the graph part -/

namespace Erdos19.SetHypergraph

open Finset

variable {X : Type*} [Fintype X]

noncomputable def missingOrderedPairs (H : SetHypergraph X) : Finset (X × X) := by
  classical
  exact univ.filter fun p ↦ p.1 ≠ p.2 ∧ ¬H.twoGraph.Adj p.1 p.2

theorem not_twoGraph_adj_of_large_edge (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) (he : 3 ≤ e.1.ncard)
    {x y : X} (hx : x ∈ e.1) (hy : y ∈ e.1) : ¬H.twoGraph.Adj x y := by
  intro hxy
  have hne : e.1 ≠ {x, y} := by
    intro heq
    rw [heq, Set.ncard_pair hxy.1] at he
    omega
  have hsub := hlinear e.2 hxy.2 hne
  exact hxy.1 (hsub ⟨hx, by simp⟩ ⟨hy, by simp⟩)

theorem sum_pair_weight_le_missingOrderedPairs (H J : SetHypergraph X)
    (hlinear : H.IsLinear) (hJH : J ⊆ H) (hmin : ∀ e : J, 3 ≤ e.1.ncard) :
    (∑ e : J, e.1.ncard * (e.1.ncard - 1)) ≤ H.missingOrderedPairs.card := by
  classical
  let code (p : Σ e : J, OrderedPairsInSet e.1) : H.missingOrderedPairs :=
    ⟨p.2.1, mem_filter.mpr ⟨mem_univ _, p.2.2.2.2,
      H.not_twoGraph_adj_of_large_edge hlinear ⟨p.1.1, hJH p.1.2⟩
        (hmin p.1) p.2.2.1 p.2.2.2.1⟩⟩
  have hinj : Function.Injective code := by
    intro p q hpq
    have hpairs : p.2.1 = q.2.1 := congrArg Subtype.val hpq
    have hedge : p.1 = q.1 := by
      apply Subtype.ext
      by_contra heq
      have hsub := hlinear (hJH p.1.2) (hJH q.1.2) heq
      have hfirst : p.2.1.1 ∈ p.1.1 ∩ q.1.1 := by
        refine ⟨p.2.2.1, ?_⟩
        rw [congrArg Prod.fst hpairs]
        exact q.2.2.1
      have hsecond : p.2.1.2 ∈ p.1.1 ∩ q.1.1 := by
        refine ⟨p.2.2.2.1, ?_⟩
        rw [congrArg Prod.snd hpairs]
        exact q.2.2.2.1
      exact p.2.2.2.2 (hsub hfirst hsecond)
    apply Sigma.ext hedge
    exact (Subtype.heq_iff_coe_eq (fun z ↦ by rw [hedge])).2 hpairs
  have hcard := Fintype.card_le_of_injective code hinj
  calc
    (∑ e : J, e.1.ncard * (e.1.ncard - 1)) =
        ∑ e : J, Fintype.card (OrderedPairsInSet e.1) := by
      apply sum_congr rfl
      intro e _
      exact (card_orderedPairsInSet e.1).symm
    _ = Fintype.card (Σ e : J, OrderedPairsInSet e.1) := Fintype.card_sigma.symm
    _ ≤ Fintype.card H.missingOrderedPairs := hcard
    _ = H.missingOrderedPairs.card := Fintype.card_coe _

#print axioms sum_pair_weight_le_missingOrderedPairs

end Erdos19.SetHypergraph
