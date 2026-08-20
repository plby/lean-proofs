import ErdosProblems.Erdos733.ST.PolygonalArcVertexAvoidsNonincidentSegment
import ErdosProblems.Erdos733.ST.PositiveSeparation
import Mathlib.Analysis.Normed.Module.Convex

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcVertexNonincidentSegmentSeparation]
lemma PolygonalArcVertexNonincidentSegmentSeparation (γ : PolygonalArc)
    {i j : ℕ} (hi : i < γ.vertices.length)
    (hj : j + 1 < γ.vertices.length) (hij : i ≠ j) (hijs : i ≠ j + 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q, q ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] →
        δ ≤ dist γ.vertices[i] q := by
-- BODY
  let E := EuclideanSpace ℝ (Fin 2)
  let A : Set E := {γ.vertices[i]}
  let B : Set E := segment ℝ γ.vertices[j] γ.vertices[j + 1]
  have hA_nonempty : A.Nonempty := by
    exact ⟨γ.vertices[i], by simp [A]⟩
  have hB_nonempty : B.Nonempty := by
    exact ⟨γ.vertices[j], by simp [B, left_mem_segment]⟩
  have hA_compact : IsCompact A := by
    simp [A]
  have hB_compact : IsCompact B := by
    dsimp [B]
    rw [segment_eq_image' ℝ γ.vertices[j] γ.vertices[j + 1]]
    exact isCompact_Icc.image
      (by fun_prop :
        Continuous (fun θ : ℝ =>
          γ.vertices[j] + θ • (γ.vertices[j + 1] - γ.vertices[j])))
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    have hx : x = γ.vertices[i] := by
      simpa [A] using hxA
    subst x
    exact PolygonalArcVertexAvoidsNonincidentSegment γ hi hj hij hijs
      (by simpa [B] using hxB)
  obtain ⟨δ, hδpos, hδ⟩ :=
    PositiveSeparation hA_nonempty hB_nonempty hA_compact hB_compact hdisj
  exact ⟨δ, hδpos, by
    intro q hq
    exact hδ γ.vertices[i] (by simp [A]) q (by simpa [B] using hq)⟩
