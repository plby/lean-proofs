import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeCutSpecializationLoops
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeCutThree

/-!
# Native two-prism and three-chamber cutting identities

The original cube is first cut along the equality of its first two
coordinates. Each resulting original prism is then cut along the two
remaining equality graphs. The parametrizations and their native classes
are the literal maps used in the chamber comparisons.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

def nativePrismFirstCut : C(NativeCube, I) := ⟨fun u => u 0, continuous_apply 0⟩

def nativeLowerPrismCut : C(NativeCube, I) where
  toFun u := u 0 * u 1
  continuous_toFun := by fun_prop

def nativeUpperPrismCut : C(NativeCube, I) where
  toFun u := Set.Icc.convexComb (u 0) 1 (u 1)
  continuous_toFun := by fun_prop

theorem nativePrismFirstCut_independent (i : Fin 3) (hi : i ≠ 0) :
    NativeCubeCutIndependent i nativePrismFirstCut := by
  intro u v
  simp [nativePrismFirstCut, hi.symm]

theorem nativeLowerPrismCut_independent : NativeCubeCutIndependent 2 nativeLowerPrismCut := by
  intro u v
  simp [nativeLowerPrismCut]

theorem nativeUpperPrismCut_independent : NativeCubeCutIndependent 2 nativeUpperPrismCut := by
  intro u v
  simp [nativeUpperPrismCut]

theorem nativeInterval_convexComb_mul (a b t : I) :
    Set.Icc.convexComb (a * b) a t = a * Set.Icc.convexComb b 1 t := by
  apply Subtype.ext
  change (1 - (t : ℝ)) * ((a : ℝ) * (b : ℝ)) + (t : ℝ) * (a : ℝ) =
    (a : ℝ) * ((1 - (t : ℝ)) * (b : ℝ) + (t : ℝ) * 1)
  ring

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem nativePrismFirstCut_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) : NativeCubeCutBased p 1 nativePrismFirstCut := by
  intro u
  exact hp _ 0 1 (by decide) (by simp [nativePrismFirstCut])

theorem nativeLowerPrismCut_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut := by
  intro u
  change p (nativeLowerPrismMap (Function.update u 2 (u 0 * u 1))) = x
  exact hp _ 1 2 (by decide) (by simp [nativeLowerPrismMap])

theorem nativeLowerPrismFirstCut_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeLowerPrismLoop p hp) 2 nativePrismFirstCut := by
  intro u
  change p (nativeLowerPrismMap (Function.update u 2 (u 0))) = x
  exact hp _ 0 2 (by decide) (by simp [nativeLowerPrismMap])

theorem nativeUpperPrismFirstCut_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut := by
  intro u
  change p (nativeUpperPrismMap (Function.update u 2 (u 0))) = x
  exact hp _ 0 2 (by decide) (by simp [nativeUpperPrismMap])

theorem nativeUpperPrismCut_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    NativeCubeCutBased (nativeUpperPrismLoop p hp) 2 nativeUpperPrismCut := by
  intro u
  change p (nativeUpperPrismMap
    (Function.update u 2 (Set.Icc.convexComb (u 0) 1 (u 1)))) = x
  exact hp _ 1 2 (by decide) (by simp [nativeUpperPrismMap])

theorem nativeCubeCutLowerLoop_eq_lowerPrism (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp) =
      nativeLowerPrismLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem nativeCubeCutUpperLoop_eq_upperPrism (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp) =
      nativeUpperPrismLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

/-- The two original prisms recover the native class of the original cube. -/
theorem nativeCubeClass_prisms (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass p = nativeCubeClass (nativeLowerPrismLoop p hp) +
      nativeCubeClass (nativeUpperPrismLoop p hp) := by
  simpa only [nativeCubeCutLowerLoop_eq_lowerPrism p hp,
    nativeCubeCutUpperLoop_eq_upperPrism p hp] using
    nativeCubeCutTwo_class p 1 nativePrismFirstCut (nativePrismFirstCut_based p hp)
      (nativePrismFirstCut_independent 1 (by decide))

theorem nativeLowerPrismCutLowerLoop_eq_duffy (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut
      (nativeLowerPrismCut_based p hp) = nativeDuffyCubeLoop p hp 1 := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem nativeLowerPrismCutMiddleLoop_eq_middle (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutMiddleLoop (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut nativePrismFirstCut
      (nativeLowerPrismCut_based p hp) (nativeLowerPrismFirstCut_based p hp) =
      nativeMiddleChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  change p ![u 0, u 0 * u 1, Set.Icc.convexComb (u 0 * u 1) (u 0) (u 2)] =
    p ![u 0, u 0 * u 1, u 0 * Set.Icc.convexComb (u 1) 1 (u 2)]
  rw [nativeInterval_convexComb_mul]

theorem nativeLowerPrismCutUpperLoop_eq_high (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop (nativeLowerPrismLoop p hp) 2 nativePrismFirstCut
      (nativeLowerPrismFirstCut_based p hp) = nativeHighChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

/-- Three coordinate slices of the original lower prism, with the canonical Duffy piece first. -/
theorem nativeLowerPrismClass_eq (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeLowerPrismLoop p hp) = nativeCubeClass (nativeDuffyCubeLoop p hp 1) +
      nativeCubeClass (nativeMiddleChamberLoop p hp) +
      nativeCubeClass (nativeHighChamberLoop p hp) := by
  simpa only [nativeLowerPrismCutLowerLoop_eq_duffy, nativeLowerPrismCutMiddleLoop_eq_middle,
    nativeLowerPrismCutUpperLoop_eq_high] using
    nativeCubeCutThree_class (nativeLowerPrismLoop p hp) 2 nativeLowerPrismCut nativePrismFirstCut
      (nativeLowerPrismCut_based p hp) (nativeLowerPrismFirstCut_based p hp)
      nativeLowerPrismCut_independent (nativePrismFirstCut_independent 2 (by decide))

theorem nativeUpperPrismCutLowerLoop_eq_lower (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutLowerLoop (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut
      (nativeUpperPrismFirstCut_based p hp) = nativeUpperLowChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem nativeUpperPrismCutMiddleLoop_eq_middle (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutMiddleLoop (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut nativeUpperPrismCut
      (nativeUpperPrismFirstCut_based p hp) (nativeUpperPrismCut_based p hp) =
      nativeUpperMiddleChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

theorem nativeUpperPrismCutUpperLoop_eq_upper (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeCutUpperLoop (nativeUpperPrismLoop p hp) 2 nativeUpperPrismCut
      (nativeUpperPrismCut_based p hp) = nativeUpperHighChamberLoop p hp := by
  apply GenLoop.ext
  intro u
  apply congrArg p
  funext j
  fin_cases j <;> rfl

/-- Three coordinate slices of the original upper prism, in their original parametrizations. -/
theorem nativeUpperPrismClass_eq (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) :
    nativeCubeClass (nativeUpperPrismLoop p hp) = nativeCubeClass (nativeUpperLowChamberLoop p hp) +
      nativeCubeClass (nativeUpperMiddleChamberLoop p hp) +
      nativeCubeClass (nativeUpperHighChamberLoop p hp) := by
  simpa only [nativeUpperPrismCutLowerLoop_eq_lower, nativeUpperPrismCutMiddleLoop_eq_middle,
    nativeUpperPrismCutUpperLoop_eq_upper] using
    nativeCubeCutThree_class (nativeUpperPrismLoop p hp) 2 nativePrismFirstCut nativeUpperPrismCut
      (nativeUpperPrismFirstCut_based p hp) (nativeUpperPrismCut_based p hp)
      (nativePrismFirstCut_independent 2 (by decide)) nativeUpperPrismCut_independent

end Wikipedia.HopfProblem.ThirdHurewicz
