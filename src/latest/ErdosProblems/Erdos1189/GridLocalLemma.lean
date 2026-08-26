/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The finite local lemma for boxes, with the dependency hypotheses proved.
Informal source: the dependency construction in BBMST Lemma 3.5.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridIndependence

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

/-- Including the event itself only strengthens the local-lemma condition. -/
noncomputable def boxNeighbours (H : α → Box q) (A : Finset α) (a : α) : Finset α := by
  classical
  exact A.filter fun b => ¬ Disjoint (fixed (H a)) (fixed (H b))

lemma boxNeighbours_subset (H : α → Box q) (A : Finset α) (a : α) :
    boxNeighbours H A a ⊆ A := filter_subset _ _

lemma box_neighbour_independence (H : α → Box q) {A T : Finset α} {a : α}
    (hTA : T ⊆ A) (hdisj : Disjoint T (boxNeighbours H A a)) :
    (boxEvent (H a) ∩ avoidingEvents (fun b => boxEvent (H b)) T).card *
      Fintype.card (Point q) =
        (boxEvent (H a)).card * (avoidingEvents (fun b => boxEvent (H b)) T).card := by
  classical
  apply (boxEvent_depends (H a)).card_independent (avoidingBoxes_depends H T)
  apply disjoint_left.mpr
  intro i hi hiT
  obtain ⟨b, hb, hib⟩ := mem_familyFixed.mp hiT
  have hbad : ¬ Disjoint (fixed (H a)) (fixed (H b)) :=
    fun h => disjoint_left.mp h hi hib
  exact disjoint_left.mp hdisj hb (mem_filter.mpr ⟨hTA hb, hbad⟩)

/-- The local lemma conclusion for a box family on a nonempty finite grid. -/
theorem box_local_lemma (H : α → Box q) (A : Finset α) (x : α → ℝ)
    (hq : ∀ i, 0 < q i) (hx : ∀ a ∈ A, 0 ≤ x a ∧ x a < 1)
    (hprob : ∀ a ∈ A, finiteProbability (boxEvent (H a)) ≤
      x a * ∏ b ∈ boxNeighbours H A a, (1 - x b)) : ¬ CoversOn H A Set.univ := by
  classical
  let : Nonempty (Point q) := ⟨fun i => ⟨0, hq i⟩⟩
  obtain ⟨u, hu⟩ := finite_local_lemma A (boxNeighbours H A) (fun a => boxEvent (H a)) x
    (fun a _ => boxNeighbours_subset H A a) hx
    (fun a _ T hTA _ hdisj => box_neighbour_independence H hTA hdisj) hprob
  intro hcover
  obtain ⟨a, ha, hua⟩ := hcover u (Set.mem_univ _)
  exact hu a ha (mem_boxEvent.mpr hua)

end Erdos1189.Grid
