import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeDuffy
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecoverySimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientCellsBasic

/-!
# Native recovery of actual simplex classes from Duffy maps

The product parametrization and the actual simplex quotient have a common
affine boundary plane on every parameter face. Their pointwise linear
interpolation therefore gives a genuine homotopy relative to the whole
cube boundary, in every dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

open SimplexGeometry

@[simp] theorem nativeCubeSimplexQuotient_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeCubeSimplexQuotient e u (e i) = prefixMinimum u (i.val + 1) :=
  Subtype.ext (cubeSimplex_quotient_coordinate e u i)

theorem nativeCubeSimplexQuotient_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (i j : Fin n) (hij : i ≤ j) (hi : u i = 0) :
    nativeCubeSimplexQuotient e u (e j) = 0 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  exact le_antisymm (hi ▸ prefixMinimum_le_coordinate u _ i (by omega)) bot_le

theorem nativeCubeSimplexQuotient_coordinate_zero_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1)))
    (hu : u 0 = 1) : nativeCubeSimplexQuotient e u (e 0) = 1 := by
  rw [nativeCubeSimplexQuotient_coordinate]
  change prefixMinimum u (0 + 1) = 1
  rw [prefixMinimum_succ u 0 (Nat.zero_lt_succ n), prefixMinimum_zero]
  simp [hu]

theorem nativeCubeSimplexQuotient_adjacent_of_one {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (u : NativeCube (Fin (n + 1)))
    (i : Fin n) (hi : u i.succ = 1) :
    nativeCubeSimplexQuotient e u (e i.castSucc) =
      nativeCubeSimplexQuotient e u (e i.succ) := by
  rw [nativeCubeSimplexQuotient_coordinate, nativeCubeSimplexQuotient_coordinate,
    prefixMinimum_succ u i.succ.val i.succ.isLt]
  change prefixMinimum u (i.val + 1) = min (prefixMinimum u (i.val + 1)) (u i.succ)
  rw [hi, min_eq_left (show prefixMinimum u (i.val + 1) ≤ 1 from
    (prefixMinimum u (i.val + 1)).property.2)]

/-- Each corresponding pair of boundary values lies in one common based affine plane. -/
theorem nativeDuffyCube_simplex_sameFlat {n : ℕ} (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (nativeDuffyCube e u) (nativeCubeSimplexQuotient e u) := by
  obtain ⟨i, hi | hi⟩ := hu
  · exact .zero (e i) (nativeDuffyCube_coordinate_eq_zero e u i i le_rfl hi)
      (nativeCubeSimplexQuotient_coordinate_eq_zero e u i i le_rfl hi)
  · cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      cases i using Fin.cases with
      | zero =>
          exact .one (e 0) (nativeDuffyCube_coordinate_zero_of_one e u hi)
            (nativeCubeSimplexQuotient_coordinate_zero_of_one e u hi)
      | succ i =>
          exact .equal (e i.castSucc) (e i.succ)
            (e.injective.ne (by intro h; have := congrArg Fin.val h; simp at this))
            (nativeDuffyCube_adjacent_of_one e u i hi)
            (nativeCubeSimplexQuotient_adjacent_of_one e u i hi)

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The actual relative affine homotopy to the native loop of the original simplex. -/
def nativeDuffyCubeSimplexHomotopy {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    (nativeDuffyCubeLoop p hp e).val.HomotopyRel
      (basedSimplexLoop (nativeBasedCubeSimplex p hp e)).val (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp (nativeDuffyCube e) (nativeCubeSimplexQuotient e)
    (nativeDuffyCube_based p hp e) (nativeCubeSimplexQuotient_based p hp e)
    (nativeDuffyCube_simplex_sameFlat e)

theorem nativeDuffyCube_homotopic_basedSimplexLoop {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    GenLoop.Homotopic (nativeDuffyCubeLoop p hp e)
      (basedSimplexLoop (nativeBasedCubeSimplex p hp e)) :=
  ⟨nativeDuffyCubeSimplexHomotopy p hp e⟩

/-- Equality in the original native homotopy group with the literal affine simplex class. -/
theorem nativeDuffyCubeClass_eq_basedSimplexClass {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n)) :
    nativeClass (nativeDuffyCubeLoop p hp e) =
      basedSimplexClass (nativeBasedCubeSimplex p hp e) :=
  nativeClass_homotopic (nativeDuffyCube_homotopic_basedSimplexLoop p hp e)

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
