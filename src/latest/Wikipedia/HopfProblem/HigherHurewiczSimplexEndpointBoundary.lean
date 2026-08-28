import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceCover
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedPrismOperators

/-!
# Whole-boundary control from coherent terminal face maps

A coherent simplex homotopy whose lower-dimensional terminal maps are
constant produces an actual whole-boundary-based simplex. This uses the
proved surjectivity of the original geometric face maps and works in
every positive dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {n : ℕ}
  (H : SingularSimplex X n → C(I × Simplex n, X))
  (H' : SingularSimplex X (n + 1) → C(I × Simplex (n + 1), X))
  (hface : FaceCompatibleHomotopies n H H') (x : X)
  (hone : ∀ smp, timeSlice (H smp) 1 = ContinuousMap.const (Simplex n) x)

include hface hone

/-- Every actual face of the terminal simplex is literally the constant map. -/
theorem simplexEndpoint_face_constant (smp : SingularSimplex X (n + 1))
    (i : Fin (n + 2)) :
    (timeSlice (H' smp) 1).comp (simplexFace n i) =
      ContinuousMap.const (Simplex n) x :=
  (timeSlice_face hface smp i 1).trans (hone _)

/-- The terminal simplex is constant on its entire original geometric boundary. -/
theorem simplexEndpoint_boundary (smp : SingularSimplex X (n + 1))
    (s : Simplex (n + 1)) (hs : s ∈ simplexBoundary (n + 1)) :
    timeSlice (H' smp) 1 s = x := by
  obtain ⟨i, t, ht⟩ := simplexBoundary_exists_face n (⟨s, hs⟩ : SimplexBoundary (n + 1))
  have he : simplexFace n i t = s := congrArg Subtype.val ht
  rw [← he]
  exact congrArg (fun f : C(Simplex n, X) => f t)
    (simplexEndpoint_face_constant H H' hface x hone smp i)

end Wikipedia.HopfProblem.HigherHurewicz
