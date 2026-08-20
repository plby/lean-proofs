import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalPathOriginalSegmentGap
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingSegmentParameterGapPiece]
lemma ArcCrossingSegmentParameterGapPiece
    (K : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalArc) (α : PolygonalPath)
    (i : ℕ) (hi : i + 1 < α.vertices.length) (left right s t : ℝ) :
    α.carrier ⊆ Kᶜ →
      left < s →
        s ≤ t →
          t < right →
            0 < left →
              right < 1 →
                (∀ u : ℝ, 0 < u → u < 1 →
                  (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) u ∈ γ.carrier →
                    ¬ (left < u ∧ u < right)) →
                  ∃ η : PolygonalPath,
                    η.source =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) s ∧
                      η.target =
                        (AffineMap.lineMap α.vertices[i] α.vertices[i + 1]) t ∧
                        η.carrier ⊆ (K ∪ γ.carrier)ᶜ := by
-- BODY
  intro hαK hleft_s hst ht_right hleft_pos hright_lt_one hno
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
  have hs0 : 0 < s := lt_trans hleft_pos hleft_s
  have hs1 : s < 1 := lt_trans (lt_of_le_of_lt hst ht_right) hright_lt_one
  have ht0 : 0 < t := lt_of_lt_of_le hs0 hst
  have ht1 : t < 1 := lt_trans ht_right hright_lt_one
  have hPseg : P ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨le_of_lt hs0, le_of_lt hs1⟩, rfl⟩
  have hQseg : Q ∈ segment ℝ A B := by
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨le_of_lt ht0, le_of_lt ht1⟩, rfl⟩
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
    have hu0 : 0 < u := lt_of_lt_of_le hs0 hu_bounds.1
    have hu1 : u < 1 := lt_of_le_of_lt hu_bounds.2 ht1
    exact hno u hu0 hu1 (by simpa [A, B, hyu] using hyγ)
      ⟨lt_of_lt_of_le hleft_s hu_bounds.1, lt_of_le_of_lt hu_bounds.2 ht_right⟩
  simpa [A, B, P, Q] using
    PolygonalPathOriginalSegmentGap K γ.carrier α i hi P Q hαK hPQ_subset hPQ_disjoint
