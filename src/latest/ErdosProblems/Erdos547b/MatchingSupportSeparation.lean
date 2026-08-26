/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma611Full

/-! Literal support separation for disjoint subfamilies of a matching. -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoMatchingSupportSeparation

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoLemma611Full

variable {K : Type*} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]

theorem mem_selectedSupport_iff (M : R.Subgraph) (L : Finset K)
    (E : Finset (MatchingEdge M)) (x : K) :
    x ∈ matchingSupport (edgeFinsetSubgraph M L E) ↔
      ∃ e ∈ E, ∃ c : Fin 2, orientedEndpoint M L e c = x := by
  rw [mem_matchingSupport]
  constructor
  · rintro ⟨e, he, h | h⟩
    · exact ⟨e, he, 0, h.symm⟩
    · exact ⟨e, he, 1, h.symm⟩
  · rintro ⟨e, he, c, h⟩
    refine ⟨e, he, ?_⟩
    fin_cases c
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem selectedSupport_disjoint (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (E F : Finset (MatchingEdge M)) (hEF : Disjoint E F) :
    Disjoint (matchingSupport (edgeFinsetSubgraph M L E))
      (matchingSupport (edgeFinsetSubgraph M L F)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨e, he, c, hc⟩ := (mem_selectedSupport_iff M L E x).mp hx
  obtain ⟨f, hf, d, hd⟩ := (mem_selectedSupport_iff M L F x).mp hy
  have hpair : (e, c) = (f, d) := orientedEndpoint_injective M hM L (hc.trans hd.symm)
  have hef : e = f := congrArg Prod.fst hpair
  exact Finset.disjoint_left.mp hEF he (hef.symm ▸ hf)

theorem sum_selectedSupport (M : R.Subgraph) (hM : M.IsMatching) (L : Finset K)
    (E : Finset (MatchingEdge M)) (w : K → ℝ) :
    (∑ x ∈ matchingSupport (edgeFinsetSubgraph M L E), w x) =
      ∑ e ∈ E, (w (orientedEndpoint M L e 0) + w (orientedEndpoint M L e 1)) := by
  rw [matchingSupport_edgeFinsetSubgraph, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_pair (orientedEndpoint_ne M L e)]
  · intro e _ f _ hef
    have h := selectedSupport_disjoint M hM L {e} {f} (by simpa using hef)
    simpa only [matchingSupport_edgeFinsetSubgraph, Finset.singleton_biUnion] using h

end Erdos547b.ZhaoMatchingSupportSeparation

#print axioms Erdos547b.ZhaoMatchingSupportSeparation.selectedSupport_disjoint
#print axioms Erdos547b.ZhaoMatchingSupportSeparation.sum_selectedSupport
