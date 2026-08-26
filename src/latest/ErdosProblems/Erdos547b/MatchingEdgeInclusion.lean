/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma611Full

/-! # Faithful edge indices under reduced-subgraph inclusions -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoMatchingEdgeInclusion

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoLemma611Full

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : SimpleGraph V} [DecidableRel R.Adj]
variable {M N P : R.Subgraph}

def edgeInclusion (h : M ≤ N) (e : MatchingEdge M) : MatchingEdge N :=
  ⟨e.val, Subgraph.edgeSet_mono h e.property⟩

omit [Fintype V] [DecidableEq V] [DecidableRel R.Adj] in
theorem edgeInclusion_injective (h : M ≤ N) : Function.Injective (edgeInclusion h) := by
  intro e f hef
  exact Subtype.ext (congrArg (fun x : MatchingEdge N => x.val) hef)

omit [Fintype V] [DecidableRel R.Adj] in
theorem orientedEndpoint_edgeInclusion (h : M ≤ N) (L : Finset V)
    (e : MatchingEdge M) (c : Fin 2) :
    orientedEndpoint N L (edgeInclusion h e) c = orientedEndpoint M L e c := rfl

def liftedEdges (h : M ≤ N) (E : Finset (MatchingEdge M)) : Finset (MatchingEdge N) :=
  E.image (edgeInclusion h)

omit [Fintype V] [DecidableRel R.Adj] in
theorem liftedEdges_card (h : M ≤ N) (E : Finset (MatchingEdge M)) :
    (liftedEdges h E).card = E.card := Finset.card_image_of_injective _ (edgeInclusion_injective h)

omit [Fintype V] [DecidableRel R.Adj] in
theorem sum_liftedEdges (h : M ≤ N) (E : Finset (MatchingEdge M)) (w : MatchingEdge N → ℝ) :
    (∑ e ∈ liftedEdges h E, w e) = ∑ e ∈ E, w (edgeInclusion h e) :=
  Finset.sum_image (fun _ _ _ _ hef => edgeInclusion_injective h hef)

theorem liftedEdges_disjoint_of_support (hM : M ≤ P) (hN : N ≤ P)
    (hdis : Disjoint (matchingSupport M) (matchingSupport N))
    (E : Finset (MatchingEdge M)) (F : Finset (MatchingEdge N)) :
    Disjoint (liftedEdges hM E) (liftedEdges hN F) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp he
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hf
  have heq : orientedEndpoint M ∅ a 0 = orientedEndpoint N ∅ b 0 :=
    congrArg (fun z : MatchingEdge P => orientedEndpoint P ∅ z 0) (ha.trans hb.symm)
  have hMa := (mem_matchingSupport M _).mpr (orientedEndpoint_adj M ∅ a).fst_mem
  have hNb := (mem_matchingSupport N _).mpr (orientedEndpoint_adj N ∅ b).fst_mem
  exact Finset.disjoint_left.mp hdis hMa (heq.symm ▸ hNb)

end Erdos547b.ZhaoMatchingEdgeInclusion

#print axioms Erdos547b.ZhaoMatchingEdgeInclusion.orientedEndpoint_edgeInclusion
#print axioms Erdos547b.ZhaoMatchingEdgeInclusion.sum_liftedEdges
#print axioms Erdos547b.ZhaoMatchingEdgeInclusion.liftedEdges_disjoint_of_support
