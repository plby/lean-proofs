import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeChamberFlats

/-!
# The actual native prism and chamber loops

The two original prism maps are based on every parameter boundary face.
For the five remaining chambers the common-face comparisons give the same
boundary statement directly, before any equality of homotopy classes.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem nativeLowerPrismMap_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeLowerPrismMap u) = x := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact p.property _ ⟨0, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
    · change u 1 = 0 at hi
      exact p.property _ ⟨1, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
    · change u 2 = 0 at hi
      exact p.property _ ⟨2, Or.inl (by simp [nativeLowerPrismMap, hi])⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact p.property _ ⟨0, Or.inr (by simp [nativeLowerPrismMap, hi])⟩
    · change u 1 = 1 at hi
      exact hp _ 0 1 (by decide) (by simp [nativeLowerPrismMap, hi])
    · change u 2 = 1 at hi
      exact p.property _ ⟨2, Or.inr (by simp [nativeLowerPrismMap, hi])⟩

theorem nativeUpperPrismMap_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) : p (nativeUpperPrismMap u) = x := by
  rcases hu with ⟨i, hi | hi⟩
  · fin_cases i
    · change u 0 = 0 at hi
      exact p.property _ ⟨0, Or.inl (by simp [nativeUpperPrismMap, hi])⟩
    · change u 1 = 0 at hi
      exact hp _ 0 1 (by decide) (by simp [nativeUpperPrismMap, hi])
    · change u 2 = 0 at hi
      exact p.property _ ⟨2, Or.inl (by simp [nativeUpperPrismMap, hi])⟩
  · fin_cases i
    · change u 0 = 1 at hi
      exact p.property _ ⟨0, Or.inr (by simp [nativeUpperPrismMap, hi])⟩
    · change u 1 = 1 at hi
      exact p.property _ ⟨1, Or.inr (by simp [nativeUpperPrismMap, hi])⟩
    · change u 2 = 1 at hi
      exact p.property _ ⟨2, Or.inr (by simp [nativeUpperPrismMap, hi])⟩

def nativeLowerPrismLoop (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeLowerPrismMap (nativeLowerPrismMap_based p hp)

def nativeUpperPrismLoop (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperPrismMap (nativeUpperPrismMap_based p hp)

def nativeMiddleChamberLoop (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeMiddleChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeMiddleChamber_flats)

def nativeHighChamberLoop (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeHighChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeHighChamber_flats)

def nativeUpperLowChamberLoop (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperLowChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperLowChamber_flats)

def nativeUpperMiddleChamberLoop (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperMiddleChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperMiddleChamber_flats)

def nativeUpperHighChamberLoop (p : GenLoop (Fin 3) X x) (hp : NativeCubeInternalBased p) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p nativeUpperHighChamberMap
    (nativeCubeMap_based_of_commonLeft p hp nativeUpperHighChamber_flats)

@[simp] theorem nativeLowerPrismLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube) :
    nativeLowerPrismLoop p hp u = p (nativeLowerPrismMap u) := rfl

@[simp] theorem nativeUpperPrismLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube) :
    nativeUpperPrismLoop p hp u = p (nativeUpperPrismMap u) := rfl

@[simp] theorem nativeMiddleChamberLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube) :
    nativeMiddleChamberLoop p hp u = p (nativeMiddleChamberMap u) := rfl

@[simp] theorem nativeHighChamberLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube) :
    nativeHighChamberLoop p hp u = p (nativeHighChamberMap u) := rfl

@[simp] theorem nativeUpperLowChamberLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube) :
    nativeUpperLowChamberLoop p hp u = p (nativeUpperLowChamberMap u) := rfl

@[simp] theorem nativeUpperMiddleChamberLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube) :
    nativeUpperMiddleChamberLoop p hp u = p (nativeUpperMiddleChamberMap u) := rfl

@[simp] theorem nativeUpperHighChamberLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (u : NativeCube) :
    nativeUpperHighChamberLoop p hp u = p (nativeUpperHighChamberMap u) := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
