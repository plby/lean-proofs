import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexWhiskerCell
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexUncurryBasic

/-!
# Exact coordinate identities for the exceptional whisker facet

The first-coordinate rotation moves that coordinate to the last position.
The formulas below retain the original ordered facet maps and native
generalized loops, before passing to any homotopy class.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

open NativeSubdivision

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- Rotating the cube coordinates puts the original first coordinate last. -/
theorem whiskerFacet_rotate_coordinates (u : Fin (n + 1) → I) :
    (fun i => u (finRotate (n + 1) i)) = Fin.snoc (Fin.tail u) (u 0) := by
  simpa only [Fin.cons_self_tail] using
    (Fin.snoc_eq_cons_rotate (Fin.tail u) (u 0)).symm

theorem whiskerFacet_zero_coordinates (ε : I) (u : Fin (n + 1) → I) :
    cubeFacet (n + 1) 0 ε u = Fin.cons ε u :=
  Fin.insertNth_zero' ε u

theorem whiskerFacet_last_coordinates (ε : I) (u : Fin n → I) :
    cubeFacet n (Fin.last n) ε u = Fin.snoc u ε :=
  Fin.insertNth_last' ε u

/-- The first original facet, with the leading loop parameter moved to its end. -/
theorem whiskerFacet_rotated_face_apply (F : BasedCubicalCell (n + 2) x)
    (ε : I) (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → I) :
    permuteCubeLoop (cubicalFace F 0 ε hε) (finRotate (n + 1)) u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) (u 0))) := by
  rw [permuteCubeLoop_apply, cubicalFace_apply, whiskerFacet_zero_coordinates,
    whiskerFacet_rotate_coordinates]

/-- The last original upper facet, split into its first and remaining coordinates. -/
theorem whiskerFacet_last_upper_apply (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) :
    cubicalUpperFace F (Fin.last (n + 1)) u =
      F.val (Fin.cons (u 0) (Fin.snoc (Fin.tail u) 1)) := by
  rw [cubicalFace_apply, whiskerFacet_last_coordinates,
    Fin.cons_snoc_eq_snoc_cons, Fin.cons_self_tail]

/-- Reversal of the first coordinate uses the same literal coordinate update
as native concatenation. -/
theorem whiskerFacet_symmAt_zero_apply (p : GenLoop (Fin (n + 1)) X x)
    (u : Fin (n + 1) → I) :
    GenLoop.symmAt 0 p u = p (Function.update u 0 (σ (u 0))) := by
  change p (fun j => if j = 0 then σ (u 0) else u j) = _
  congr 1
  funext j
  simp only [Function.update_apply]

/-- The reversed final arm retains the upper first facet's original orientation. -/
theorem whiskerFacet_reflected_rotated_face_apply (F : BasedCubicalCell (n + 2) x)
    (ε : I) (hε : ε = 0 ∨ ε = 1) (u : Fin (n + 1) → I) :
    GenLoop.symmAt 0 (permuteCubeLoop (cubicalFace F 0 ε hε)
      (finRotate (n + 1))) u =
      F.val (Fin.cons ε (Fin.snoc (Fin.tail u) (σ (u 0)))) := by
  rw [whiskerFacet_symmAt_zero_apply, whiskerFacet_rotated_face_apply]
  simp only [Fin.tail_update_zero, Function.update_self]

/-- The exceptional upper facet is the original cell on the rectangle track. -/
theorem whiskerFacet_last_upper_uncurry_apply (F : BasedCubicalCell (n + 2) x)
    (u : Fin (n + 1) → I) :
    uncurryLoop (cubicalUpperFace (whiskeredCell F) (Fin.last n)) u =
      F.val (Fin.cons (whiskerTrack (u 0)).1
        (Fin.snoc (Fin.tail u) (whiskerTrack (u 0)).2)) := by
  rw [uncurryLoop_apply, cubicalFace_apply, whiskeredCell_apply,
    whiskerFacet_last_coordinates, whiskerMap_apply]
  simp only [Fin.init_snoc, Fin.snoc_last, mul_one]
  rfl

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
