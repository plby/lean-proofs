import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerFacetsCoordinates
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerPieces

/-!
# The exceptional upper-last whisker facet as an actual native loop

The two arms are the first-coordinate facets with their leading parameter
rotated to the end; the final arm is reversed. The middle is the original
upper-last facet. Their native concatenation agrees pointwise with the
uncurried whiskered facet, using exactly the native clamped times.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

open NativeSubdivision

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- The first-coordinate native concatenation uses the original clamped times. -/
theorem whiskerFacet_transAt_zero_apply (p q : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → I) :
    GenLoop.transAt 0 p q u =
      if (u 0 : ℝ) ≤ 1 / 2 then
        p (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))))
      else
        q (Function.update u 0 (Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1))) := rfl

/-- The exceptional upper-last facet is literally the concatenation of its
three original oriented faces, before taking native homotopy classes. -/
theorem whiskeredCell_face_last_upper (F : BasedCubicalCell (n + 2) x) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) =
      GenLoop.transAt 0
        (permuteCubeLoop (cubicalLowerFace F 0) (finRotate (n + 1)))
        (GenLoop.transAt 0 (cubicalUpperFace F (Fin.last (n + 1)))
          (GenLoop.symmAt 0
            (permuteCubeLoop (cubicalUpperFace F 0) (finRotate (n + 1))))) := by
  apply GenLoop.ext
  intro u
  rw [whiskerFacet_last_upper_uncurry_apply, whiskerTrack_concat,
    whiskerFacet_transAt_zero_apply]
  by_cases h₀ : (u 0 : ℝ) ≤ 1 / 2
  · simp only [if_pos h₀, whiskerFacet_rotated_face_apply,
      Fin.tail_update_zero, Function.update_self]
  · simp only [if_neg h₀]
    rw [whiskerFacet_transAt_zero_apply]
    simp only [Function.update_self]
    split_ifs
    · rw [whiskerFacet_last_upper_apply]
      simp only [Fin.tail_update_zero, Function.update_self]
    · rw [whiskerFacet_reflected_rotated_face_apply]
      simp only [Fin.tail_update_zero, Function.update_self]

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
