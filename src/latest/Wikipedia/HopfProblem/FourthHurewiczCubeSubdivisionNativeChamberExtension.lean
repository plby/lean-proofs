import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeExtension
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeChamberChartsBasic

/-!
# Based native loops from partially inserted chamber charts

Matching chamber charts send each input boundary face to a common affine
face. Extending a chart by unchanged coordinates preserves this property.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {m n : ℕ}

theorem NativeChamberChart.sameFlat {e : Equiv.Perm (Fin m)}
    (chart other : NativeChamberChart e) (u : NativeCube (Fin m))
    (hu : u ∈ Cube.boundary (Fin m)) :
    NativeCubeSameFlat (chart.toContinuousMap u) (other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  let i := e.symm j
  have hei : e i = j := e.apply_symm_apply j
  rcases hj with hj | hj
  · have hi : u (e i) = 0 := hei ▸ hj
    by_cases hilast : i.val + 1 = m
    · exact .zero (e i) (chart.zero_last u i hilast hi) (other.zero_last u i hilast hi)
    · let k : Fin m := ⟨i.val + 1, by have := i.isLt; omega⟩
      have hik : i.val + 1 = k.val := rfl
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact .equal (e i) (e k) hne (chart.zero_adjacent u i k hik hi)
        (other.zero_adjacent u i k hik hi)
  · have hi : u (e i) = 1 := hei ▸ hj
    by_cases hifirst : i.val = 0
    · exact .one (e i) (chart.one_first u i hifirst hi) (other.one_first u i hifirst hi)
    · let k : Fin m := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hki : k.val + 1 = i.val := by dsimp [k]; omega
      have hne : e i ≠ e k := by
        intro h
        have hv := congrArg Fin.val (e.injective h)
        dsimp [k] at hv
        omega
      exact .equal (e i) (e k) hne (chart.one_adjacent u i k hki hi)
        (other.one_adjacent u i k hki hi)

theorem extendedChamberMap_sameFlat (h : m ≤ n) {e : Equiv.Perm (Fin m)}
    (chart other : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) :
    NativeCubeSameFlat (extendCubeMap h chart.toContinuousMap u)
      (extendCubeMap h other.toContinuousMap u) := by
  obtain ⟨j, hj⟩ := hu
  by_cases hjm : j.val < m
  · let k : Fin m := ⟨j.val, hjm⟩
    have hk : Fin.castLE h k = j := Fin.ext rfl
    apply extendCubeMap_sameFlat
    apply chart.sameFlat other
    refine ⟨k, ?_⟩
    simpa only [cubeRestriction_apply, hk] using hj
  · rcases hj with hj | hj
    · exact .zero j
        ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
        ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
    · exact .one j
        ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)
        ((extendCubeMap_outside h _ u j (Nat.le_of_not_gt hjm)).trans hj)

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem extendedChamberMap_based (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m ≤ n) {e : Equiv.Perm (Fin m)}
    (chart : NativeChamberChart e) (u : NativeCube (Fin n))
    (hu : u ∈ Cube.boundary (Fin n)) :
    p (extendCubeMap h chart.toContinuousMap u) = x := by
  simpa only [nativeCubeBlend_zero] using nativeCubeBlend_based p hp
    (extendedChamberMap_sameFlat h chart chart u hu) 0

/-- The actual native loop represented by a chart on the first coordinates. -/
def extendedChamberLoop (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart : NativeChamberChart e) :
    GenLoop (Fin n) X x :=
  nativeCubePullbackLoop p (extendCubeMap h chart.toContinuousMap)
    (extendedChamberMap_based p hp h chart)

@[simp] theorem extendedChamberLoop_apply (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m ≤ n) {e : Equiv.Perm (Fin m)}
    (chart : NativeChamberChart e) (u : NativeCube (Fin n)) :
    extendedChamberLoop p hp h chart u = p (extendCubeMap h chart.toContinuousMap u) := rfl

@[simp] theorem extendedChamberLoop_zero (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : 0 ≤ n) {e : Equiv.Perm (Fin 0)}
    (chart : NativeChamberChart e) : extendedChamberLoop p hp h chart = p := by
  apply GenLoop.ext
  intro u
  simp

/-- Chart changes satisfying the same face conditions are actual relative homotopies. -/
def extendedChamberHomotopy (p : GenLoop (Fin n) X x) (hp : NativeCubeInternalBased p)
    (h : m ≤ n) {e : Equiv.Perm (Fin m)} (chart other : NativeChamberChart e) :
    (extendedChamberLoop p hp h chart).val.HomotopyRel
      (extendedChamberLoop p hp h other).val (Cube.boundary (Fin n)) :=
  nativeCubeLinearHomotopy p hp
    (extendCubeMap h chart.toContinuousMap) (extendCubeMap h other.toContinuousMap)
    (extendedChamberMap_based p hp h chart) (extendedChamberMap_based p hp h other)
    (extendedChamberMap_sameFlat h chart other)

theorem nativeClass_extendedChamber_eq (p : GenLoop (Fin n) X x)
    (hp : NativeCubeInternalBased p) (h : m ≤ n) {e : Equiv.Perm (Fin m)}
    (chart other : NativeChamberChart e) :
    nativeClass (extendedChamberLoop p hp h chart) =
      nativeClass (extendedChamberLoop p hp h other) :=
  nativeClass_homotopic ⟨extendedChamberHomotopy p hp h chart other⟩

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
