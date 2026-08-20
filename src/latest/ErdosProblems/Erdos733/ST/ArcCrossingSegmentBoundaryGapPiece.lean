import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalPathOriginalSegmentGap
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingSegmentBoundaryGapPiece]
lemma ArcCrossingSegmentBoundaryGapPiece
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length) (s t : ℝ) :
    α.carrier ⊆ Kᶜ →
      0 ≤ s →
        s ≤ t →
          t ≤ 1 →
            α.vertices[i] ∉ γ.carrier →
              α.vertices[i + 1] ∉ γ.carrier →
                (∀ u : ℝ, 0 < u → u < 1 →
                  (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) u ∈ γ.carrier →
                    ¬ (s ≤ u ∧ u ≤ t)) →
                  ∃ η : PolygonalPath,
                    η.source =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) s ∧
                      η.target =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) t ∧
                        η.carrier ⊆ (K ∪ γ.carrier)ᶜ := by
-- BODY
  intro hαK hs0 hst ht1 hA_notγ hB_notγ hno
  let A := α.vertices[i]
  let B := α.vertices[i + 1]
  let P := (AffineMap.lineMap A B) s
  let Q := (AffineMap.lineMap A B) t
  have hline_line :
      ∀ θ : ℝ,
        (AffineMap.lineMap ((AffineMap.lineMap A B) s) ((AffineMap.lineMap A B) t)) θ =
          (AffineMap.lineMap A B) ((AffineMap.lineMap s t) θ) := by
    intro θ
    simp [AffineMap.lineMap_apply_module, smul_add, add_smul, smul_smul]
    module
  have hPseg : P ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨hs0, le_trans hst ht1⟩, rfl⟩
  have hQseg : Q ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨le_trans hs0 hst, ht1⟩, rfl⟩
  have hPQ_subset : segment ℝ P Q ⊆ segment ℝ A B :=
    (convex_segment A B).segment_subset hPseg hQseg
  have hPQ_disjoint : Disjoint (segment ℝ P Q) γ.carrier := by
    rw [Set.disjoint_left]
    intro y hyseg hyγ
    have hyseg' : y ∈ segment ℝ ((AffineMap.lineMap A B) s)
        ((AffineMap.lineMap A B) t) := by
      simpa [P, Q] using hyseg
    rw [segment_eq_image_lineMap] at hyseg'
    rcases hyseg' with ⟨θ, hθ, hθy⟩
    let u : ℝ := (AffineMap.lineMap s t) θ
    have hyu : y = (AffineMap.lineMap A B) u := by
      rw [← hθy]
      exact hline_line θ
    have hu_seg : u ∈ segment ℝ s t := by
      rw [segment_eq_image_lineMap]
      exact ⟨θ, hθ, rfl⟩
    have hu_bounds : s ≤ u ∧ u ≤ t := by
      simpa [segment_eq_Icc hst] using hu_seg
    have hu0le : 0 ≤ u := le_trans hs0 hu_bounds.1
    have hu1le : u ≤ 1 := le_trans hu_bounds.2 ht1
    by_cases hu0eq : u = 0
    · have hγA : A ∈ γ.carrier := by
        simpa [A, B, hyu, hu0eq] using hyγ
      exact hA_notγ hγA
    · by_cases hu1eq : u = 1
      · have hγB : B ∈ γ.carrier := by
          simpa [A, B, hyu, hu1eq] using hyγ
        exact hB_notγ hγB
      · have hu0 : 0 < u := lt_of_le_of_ne hu0le (Ne.symm hu0eq)
        have hu1 : u < 1 := lt_of_le_of_ne hu1le hu1eq
        exact hno u hu0 hu1 (by simpa [A, B, hyu] using hyγ) hu_bounds
  simpa [A, B, P, Q] using
    PolygonalPathOriginalSegmentGap K γ.carrier α i hi P Q hαK hPQ_subset hPQ_disjoint
