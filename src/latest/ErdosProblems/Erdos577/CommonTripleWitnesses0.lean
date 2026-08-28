import ErdosProblems.Erdos577.CommonTripleMasks0

/-! Explicit common-neighbor replacements and matching gains for Wang 3.3. -/

namespace Erdos577.CommonTriple.D0

open Finset

private theorem witness_0 : Positive 0 816 := by
  right
  let p : TwoEdges (graph 0 816) := {
    vertices := ⟨![0, 1, 6, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, by decide +kernel, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_1 : Positive 0 1632 := by
  right
  let p : TwoEdges (graph 0 1632) := {
    vertices := ⟨![0, 1, 4, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, by decide +kernel, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_2 : Positive 0 2448 := by
  right
  let p : TwoEdges (graph 0 2448) := {
    vertices := ⟨![0, 1, 5, 6], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, by decide +kernel, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_3 : Positive 0 3264 := by
  right
  let p : TwoEdges (graph 0 3264) := {
    vertices := ⟨![0, 1, 4, 5], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, by decide +kernel, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_4 : Positive 0 21024 := by
  left
  refine ⟨5, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_5 : Positive 0 22656 := by
  left
  refine ⟨7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_6 : Positive 0 41232 := by
  left
  refine ⟨4, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_7 : Positive 0 42048 := by
  left
  refine ⟨6, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 0 m := by
  simp only [masks, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_0
  · exact witness_1
  · exact witness_2
  · exact witness_3
  · exact witness_4
  · exact witness_5
  · exact witness_6
  · exact witness_7

theorem finite_classification (m : Fin 65536) (hh : Hypotheses m.val) :
    Positive 0 m.val ∨ Conclusion m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hh) with hp | hc
  · obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hp
    exact Or.inl ((masks_sound hw).mono (beq_iff_eq.mp hsub))
  · exact Or.inr (of_decide_eq_true hc)

end Erdos577.CommonTriple.D0
