import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeBasic
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexGenericBasic
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationBoundaryImage

/-!
# Actual based permutation simplices of an internally based cube

The simplex here is literally the original cube composed with its affine
permutation cell. Its native loop is obtained with the explicit simplex
quotient, not by replacing the original homotopy group with a presentation.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

open FirstHurewicz SimplexGeometry CubeTriangulation

/-- The actual permutation cell composed with the native simplex quotient. -/
def nativeCubeSimplexQuotient {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (cubeSimplex e).comp (simplexQuotient n)

theorem nativeCubeSimplexQuotient_apply {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) :
    nativeCubeSimplexQuotient e u = cubeSimplex e (simplexQuotient n u) := rfl

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Every geometric face of every actual cell is based. -/
theorem nativeCubeSimplex_based {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (s : Simplex n) (hs : s ∈ SecondHurewicz.SimplyConnected.simplexBoundary n) :
    p (cubeSimplex e s) = x := by
  cases n with
  | zero =>
      obtain ⟨i, hi⟩ := hs
      have hi0 : i = 0 := Fin.ext (by omega)
      subst i
      have hsum : s 0 = 1 := by
        simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] using
          stdSimplex.sum_eq_one s
      exact False.elim (by linarith)
  | succ n =>
      rcases cubeSimplex_simplexBoundary e s hs with h | ⟨i, j, hij, h⟩
      · exact p.property _ h
      · exact hp _ i j hij h

/-- The literal restriction to the original affine permutation simplex. -/
def nativeBasedCubeSimplex {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) : BasedSimplex n x :=
  ⟨p.val.comp (cubeSimplex e), nativeCubeSimplex_based p hp e⟩

@[simp] theorem nativeBasedCubeSimplex_val {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    (nativeBasedCubeSimplex p hp e).val = p.val.comp (cubeSimplex e) := rfl

@[simp] theorem nativeBasedCubeSimplex_loop_apply {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) :
    basedSimplexLoop (nativeBasedCubeSimplex p hp e) u =
      p (nativeCubeSimplexQuotient e u) := rfl

theorem nativeCubeSimplexQuotient_based {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) : p (nativeCubeSimplexQuotient e u) = x :=
  nativeCubeSimplex_based p hp e _ (simplexQuotient_boundary u hu)

theorem nativeCubeSimplexQuotientLoop_eq_basedSimplexLoop {n : ℕ}
    (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    nativeCubePullbackLoop p (nativeCubeSimplexQuotient e)
        (nativeCubeSimplexQuotient_based p hp e) =
      basedSimplexLoop (nativeBasedCubeSimplex p hp e) := rfl

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
