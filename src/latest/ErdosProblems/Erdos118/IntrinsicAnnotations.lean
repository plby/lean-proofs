import ErdosProblems.Erdos118.RedFamily
import ErdosProblems.Erdos118.EdgeRefinement

/-!
Completed exact annotations are determined by ordinary vertices. Therefore
tests of completed clear pairs lift to symmetric edge properties, to which
the proved blue edge-refinement theorem applies without a history premise.
-/

namespace Erdos118.IntrinsicAnnotations

open Negative Negative.Exact LabelledExtensions LabelCoarsening CutIndices
open DecisionStates ClearPairs

theorem completed_eq (S U : Completed) (T V : Stem)
    (hS : S.stem.ordinary = U.stem.ordinary) (hT : T.ordinary = V.ordinary)
    (hST : ExactAnnotations S.stem T) (hUV : ExactAnnotations U.stem V) : S = U := by
  have hroot : S.stem.rootLabel = U.stem.rootLabel := by
    apply S.stem.label_pairwise.eq_of_mem_iff U.stem.label_pairwise
    intro x
    rw [hST.root, hUV.root]
    constructor
    · rintro ⟨i, j, hij, hx⟩
      exact ⟨i, j, (cut_congr hS hT i j).mp hij, hx⟩
    · rintro ⟨i, j, hij, hx⟩
      exact ⟨i, j, (cut_congr hS hT i j).mpr hij, hx⟩
  have hlen : S.stem.bodyLabels.length = U.stem.bodyLabels.length := by
    simp only [Stem.bodyLabels, List.length_map, S.full, U.full]
    exact (List.cons.inj hS).1
  have hbody : S.stem.bodyLabels = U.stem.bodyLabels := by
    apply List.ext_getElem hlen
    intro i hi hi'
    apply (ProjectionBounds.body_label_pairwise S.stem i hi).eq_of_mem_iff
      (ProjectionBounds.body_label_pairwise U.stem i hi')
    intro j
    rw [hST.body, hUV.body]
    exact cut_congr hS hT i j
  have he := NextBodyCuts.stem_eq_of_ordinary_labels S.stem U.stem hS hroot hbody
  cases S
  cases U
  cases he
  rfl

theorem clear_pair_unique (S T U V : Completed)
    (hST : ClearPair S.stem T.stem) (hUV : ClearPair U.stem V.stem)
    (hs : GraphPayoff.vertex S = GraphPayoff.vertex U)
    (ht : GraphPayoff.vertex T = GraphPayoff.vertex V) : S = U ∧ T = V := by
  have hS : S.stem.ordinary = U.stem.ordinary :=
    (S.stem.toGood_word S.full).symm.trans
      ((congrArg (fun s : G ↦ word s.1) hs).trans (U.stem.toGood_word U.full))
  have hT : T.stem.ordinary = V.stem.ordinary :=
    (T.stem.toGood_word T.full).symm.trans
      ((congrArg (fun s : G ↦ word s.1) ht).trans (V.stem.toGood_word V.full))
  exact ⟨completed_eq S U T.stem V.stem hS hT hST.exactLeft hUV.exactLeft,
    completed_eq T V S.stem U.stem hT hS hST.exactRight hUV.exactRight⟩

def OnVertices (test : Completed → Completed → Prop) (s t : G) : Prop :=
  ∃ S T : Completed, GraphPayoff.vertex S = s ∧ GraphPayoff.vertex T = t ∧
    ClearPair S.stem T.stem ∧ test S T

theorem onVertices_iff (test : Completed → Completed → Prop) (S T : Completed)
    (hclear : ClearPair S.stem T.stem) :
    OnVertices test (GraphPayoff.vertex S) (GraphPayoff.vertex T) ↔ test S T := by
  constructor
  · rintro ⟨U, V, hu, hv, hUV, htest⟩
    obtain ⟨rfl, rfl⟩ := clear_pair_unique U V S T hUV hclear hu hv
    exact htest
  · intro htest
    exact ⟨S, T, rfl, rfl, hclear, htest⟩

noncomputable def color (test : Completed → Completed → Prop) (s t : G) : Bool := by
  classical
  exact if s.1.length < t.1.length then decide (OnVertices test s t)
    else if t.1.length < s.1.length then decide (OnVertices test t s) else false

theorem color_symm (test : Completed → Completed → Prop) (s t : G) :
    color test s t = color test t s := by
  classical
  by_cases hst : s.1.length < t.1.length
  · have hts : ¬ t.1.length < s.1.length := by omega
    simp [color, hst, hts]
  · by_cases hts : t.1.length < s.1.length <;> simp [color, hst, hts]

theorem color_at_clear (test : Completed → Completed → Prop) (S T : Completed)
    (hclear : ClearPair S.stem T.stem) (hroot : S.stem.root < T.stem.root) :
    color test (GraphPayoff.vertex S) (GraphPayoff.vertex T) =
      @decide (test S T) (Classical.propDecidable _) := by
  classical
  have hrootV : (GraphPayoff.vertex S).1.length < (GraphPayoff.vertex T).1.length := by
    simpa only [RedFamily.vertex_root] using hroot
  simp only [color, hrootV, ↓reduceIte, onVertices_iff test S T hclear]

theorem class_test (test : Completed → Completed → Prop) (B : SimpleGraph G)
    (value : Bool) (o : GraphPayoff.Orientation) (S T : Completed)
    (hpay : GraphPayoff.payoff
      (EdgeRefinement.edgeClass B (color test) (color_symm test) value) o S T = true) :
    @decide (test S T) (Classical.propDecidable _) = value := by
  classical
  obtain ⟨hroot, hclear, _, hedge⟩ := (GraphPayoff.payoff_true_iff _ o S T).mp hpay
  exact (color_at_clear test S T hclear hroot).symm.trans hedge.2

theorem refine_test {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true)
    (test : Completed → Completed → Prop) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C o (.initial, .initial)) true ∧
      ∃ value : Bool, ∀ S T : Completed, GraphPayoff.payoff C o S T = true →
        @decide (test S T) (Classical.propDecidable _) = value := by
  classical
  obtain ⟨K, hKH, hK, value, hblueK⟩ := EdgeRefinement.blue_edgeClass hH B (color test)
    (color_symm test) o (.initial, .initial) hblue
  refine ⟨K, hKH, hK, EdgeRefinement.edgeClass B (color test) (color_symm test) value,
    ?_, EdgeRefinement.edgeClass_cliqueFree B _ _ value 3 hB, hblueK, value, ?_⟩
  · intro s t h
    exact h.1
  · exact class_test test B value o

end Erdos118.IntrinsicAnnotations
