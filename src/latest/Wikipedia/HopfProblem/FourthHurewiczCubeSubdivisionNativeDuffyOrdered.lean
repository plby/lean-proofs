import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeDuffy
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeSymmetries

/-!
# Duffy maps with ordered physical input coordinates

Permuting both the physical output coordinates and the corresponding input
coordinates gives the face-compatible Duffy chart used for native cubical
subdivision. The input permutation contributes its actual native parity.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

/-- The ordered Duffy chart uses parameter `u (e i)` at rank `i`. -/
def nativeOrderedDuffyMap {n : ℕ} (e : Equiv.Perm (Fin n)) :
    C(NativeCube (Fin n), NativeCube (Fin n)) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

@[simp] theorem nativeOrderedDuffyMap_coordinate {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n) :
    nativeOrderedDuffyMap e u (e i) =
      prefixProduct (fun k => u (e k)) (i.val + 1) := by
  exact nativeDuffyCube_coordinate e (permuteCubeCoordinates e u) i

theorem nativeOrderedDuffyMap_coordinate_eq_zero {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n))
    (i j : Fin n) (hij : i ≤ j) (hi : u (e i) = 0) :
    nativeOrderedDuffyMap e u (e j) = 0 :=
  nativeDuffyCube_coordinate_eq_zero e (permuteCubeCoordinates e u) i j hij hi

theorem nativeOrderedDuffyMap_zero_last {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n)
    (_hi : i.val + 1 = n) (hu : u (e i) = 0) :
    nativeOrderedDuffyMap e u (e i) = 0 :=
  nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu

theorem nativeOrderedDuffyMap_zero_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n)
    (hij : i.val + 1 = j.val) (hu : u (e i) = 0) :
    nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate_eq_zero e u i i le_rfl hu,
    nativeOrderedDuffyMap_coordinate_eq_zero e u i j (by omega) hu]

theorem nativeOrderedDuffyMap_one_first {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i : Fin n)
    (hi : i.val = 0) (hu : u (e i) = 1) :
    nativeOrderedDuffyMap e u (e i) = 1 := by
  rw [nativeOrderedDuffyMap_coordinate,
    prefixProduct_succ_of_one (fun k => u (e k)) i hu, hi, prefixProduct_zero]

theorem nativeOrderedDuffyMap_one_adjacent {n : ℕ}
    (e : Equiv.Perm (Fin n)) (u : NativeCube (Fin n)) (i j : Fin n)
    (hji : j.val + 1 = i.val) (hu : u (e i) = 1) :
    nativeOrderedDuffyMap e u (e i) = nativeOrderedDuffyMap e u (e j) := by
  rw [nativeOrderedDuffyMap_coordinate, nativeOrderedDuffyMap_coordinate,
    prefixProduct_succ_of_one (fun k => u (e k)) i hu, hji]

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem nativeOrderedDuffyMap_based {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (u : NativeCube (Fin n)) (hu : u ∈ Cube.boundary (Fin n)) :
    p (nativeOrderedDuffyMap e u) = x :=
  nativeDuffyCube_based p hp e _ (permuteCubeCoordinates_boundary e u hu)

/-- The literal affine interpolation from a compatible chart to its ordered Duffy map. -/
def nativeCubeOrderedDuffyHomotopy {n : ℕ} (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin n))
    (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    (nativeCubePullbackLoop p f hf).val.HomotopyRel
      (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e).val (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp f (nativeOrderedDuffyMap e) hf
    (nativeOrderedDuffyMap_based p hp e) hfg

/-- The ordered-input chart contributes precisely the permutation's native sign. -/
theorem nativeClass_commonOrderedDuffy {n : ℕ} [Nontrivial (Fin n)]
    (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (e : Equiv.Perm (Fin n)) (f : C(NativeCube (Fin n), NativeCube (Fin n)))
    (hf : ∀ u ∈ Cube.boundary (Fin n), p (f u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin n), NativeCubeSameFlat (f u) (nativeOrderedDuffyMap e u)) :
    nativeClass (nativeCubePullbackLoop p f hf) =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • nativeClass (nativeDuffyCubeLoop p hp e) := by
  calc
    nativeClass (nativeCubePullbackLoop p f hf) =
        nativeClass (permuteCubeLoop (nativeDuffyCubeLoop p hp e) e) :=
      nativeClass_homotopic ⟨nativeCubeOrderedDuffyHomotopy p hp e f hf hfg⟩
    _ = _ := permuteCubeLoop_additiveClass _ e

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
