import Wikipedia.SmoothSixDPoincare.TubularBigonSheetFrames
import Wikipedia.SmoothSixDPoincare.ComplementFrameGermJoin

/-!
# An actual upper-edge complement retaining both lower-edge corner germs

The sign condition is now on the two original full normal frames, not on
an auxiliary chosen complement or a postulated coefficient extension.
Construct the upper complement, pass to its quotient coefficients, join
them and correct the frame. Both complete lower-frame endpoint germs remain.
The relation to opposite native six-dimensional intersection signs remains.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

/-- One fixed identification of the two normal two-planes with the tubular normal four-space. -/
def normalPairCoordinates :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 4) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin])

/-- The genuine determinant of two normal frames, computed in one fixed model at both corners. -/
def normalPairDet (A B : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (normalPairCoordinates.symm.toContinuousLinearMap.comp (A.coprod B)).toLinearMap.det

end Wikipedia.SmoothSixDPoincare.FrameField

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}

/-- Construct the boundary complement from the sign of the actual endpoint normal frames. -/
theorem exists_boundary_complement_of_normal_sign
    {k : CleanStripPatch (E := E) S T a k₀ k₁}
    {l : CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) S k.map)
    (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3))
      (E := E) T l.map)
    (hsign : 0 < normalPairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      normalPairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)) :
    ∃ U : Set ℝ, IsOpen U ∧ Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U ∧
      ∃ H : ℝ → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)),
        ContDiffOn ℝ ∞ H U ∧
        (∀ t ∈ U, Bijective ((e.normalFrame tube.chart t).coprod (H t))) ∧
        (H =ᶠ[𝓝 (0 : ℝ)] d.normalFrame tube.chart) ∧
        (H =ᶠ[𝓝 (1 : ℝ)] d.normalFrame tube.chart) := by
  obtain ⟨⟨V, hV, hIV, hL⟩, _⟩ := tube.lower_sheetFrame d
  obtain ⟨W, hW, hIW, hR, C, hC, _, hRC⟩ := tube.upper_sheetFrame_complement e
  let U := V ∩ W
  have hU : IsOpen U := hV.inter hW
  have hIU : Icc (0 : ℝ) 1 ⊆ U := fun _ ht => ⟨hIV ht, hIW ht⟩
  have hLU := hL.mono (show U ⊆ V from inter_subset_left)
  have hRU := hR.mono (show U ⊆ W from inter_subset_right)
  have hCU := hC.mono (show U ⊆ W from inter_subset_right)
  have hsplit : ∀ t ∈ U, Bijective ((e.normalFrame tube.chart t).coprod (C t)) :=
    fun t ht => hRC t ht.2
  obtain ⟨H, hH, hiH, hleft, hright⟩ :=
    exists_smooth_complement_with_germs_of_frame_sign finrank_euclideanSpace_fin
      normalPairCoordinates hU hIU hRU hCU hLU hsplit hsign
  exact ⟨U, hU, hIU, hLU, H, hH, hiH, hleft, hright⟩

end Wikipedia.SmoothSixDPoincare.TubularBigon
