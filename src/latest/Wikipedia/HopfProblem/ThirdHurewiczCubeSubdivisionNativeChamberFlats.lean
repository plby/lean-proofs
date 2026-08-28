import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeChamberMaps

/-!
# Common faces for product and ordered tetrahedron parametrizations

Each of the six parameter faces lies on one common cube boundary plane or
one common coordinate-equality plane for the two actual maps. Affine
interpolation is therefore based throughout, without any degree argument.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

theorem nativeMiddleChamber_flats (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeMiddleChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 1 2) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .zero 1 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 1 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .one 0 (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeMiddleChamberMap, hi]) (by simp [hi])

theorem nativeHighChamber_flats (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeHighChamberMap u) (nativeOrderedDuffyMap (nativeCubeCycle201) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .zero 1 (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 0 2 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .one 2 (by simp [nativeHighChamberMap, hi]) (by simp [hi])

theorem nativeUpperLowChamber_flats (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperLowChamberMap u) (nativeOrderedDuffyMap (Equiv.swap 0 1) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .zero 2 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .one 1 (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperLowChamberMap, hi]) (by simp [hi])

theorem nativeUpperMiddleChamber_flats (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperMiddleChamberMap u)
      (nativeOrderedDuffyMap nativeCubeCycle120 u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .one 1 (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperMiddleChamberMap, hi]) (by simp [hi])

theorem nativeUpperHighChamber_flats (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    NativeCubeSameFlat (nativeUpperHighChamberMap u)
      (nativeOrderedDuffyMap (Equiv.swap 0 2) u) := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact .zero 0 (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 0 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 0 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
  · fin_cases i
    · change u 0 = 1 at hi
      exact .equal 0 1 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 1 = 1 at hi
      exact .equal 1 2 (by decide) (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])
    · change u 2 = 1 at hi
      exact .one 2 (by simp [nativeUpperHighChamberMap, hi]) (by simp [hi])

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem nativeCubeMap_based_of_commonLeft (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) {f g : C(NativeCube, NativeCube)}
    (h : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) : p (f u) = x := by
  simpa only [nativeCubeBlend_zero] using nativeCubeBlend_based p hp (h u hu) 0

theorem nativeCubeMap_based_of_commonRight (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) {f g : C(NativeCube, NativeCube)}
    (h : ∀ u ∈ Cube.boundary (Fin 3), NativeCubeSameFlat (f u) (g u))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) : p (g u) = x := by
  simpa only [nativeCubeBlend_one] using nativeCubeBlend_based p hp (h u hu) 1

end Wikipedia.HopfProblem.ThirdHurewicz
