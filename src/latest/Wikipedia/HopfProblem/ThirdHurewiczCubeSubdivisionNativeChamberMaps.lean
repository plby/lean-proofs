import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeBasic
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeDuffy
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeSymmetries

/-!
# The actual product parametrizations of the ordered cube chambers

These maps are used in the explicit slice cuts. Their boundary faces agree
with faces of the correspondingly input-permuted, oriented Duffy maps.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

@[fun_prop] theorem nativeInterval_continuous_mul {Y : Type*} [TopologicalSpace Y]
    {f g : Y → I} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => f y * g y := by
  apply Continuous.subtype_mk
  exact hf.subtype_val.mul hg.subtype_val

@[fun_prop] theorem nativeInterval_continuous_convexComb {Y : Type*} [TopologicalSpace Y]
    {f g t : Y → I} (hf : Continuous f) (hg : Continuous g) (ht : Continuous t) :
    Continuous fun y => Set.Icc.convexComb (f y) (g y) (t y) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub ht.subtype_val).mul hf.subtype_val).add
    (ht.subtype_val.mul hg.subtype_val)

def nativeLowerPrismMap : C(NativeCube, NativeCube) where
  toFun u := ![u 0, u 0 * u 1, u 2]
  continuous_toFun := by fun_prop

def nativeUpperPrismMap : C(NativeCube, NativeCube) where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1), u 2]
  continuous_toFun := by fun_prop

def nativeMiddleChamberMap : C(NativeCube, NativeCube) where
  toFun u := ![u 0, u 0 * u 1, u 0 * Set.Icc.convexComb (u 1) 1 (u 2)]
  continuous_toFun := by fun_prop

def nativeHighChamberMap : C(NativeCube, NativeCube) where
  toFun u := ![u 0, u 0 * u 1, Set.Icc.convexComb (u 0) 1 (u 2)]
  continuous_toFun := by fun_prop

def nativeUpperLowChamberMap : C(NativeCube, NativeCube) where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1), u 0 * u 2]
  continuous_toFun := by fun_prop

def nativeUpperMiddleChamberMap : C(NativeCube, NativeCube) where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1),
    Set.Icc.convexComb (u 0) (Set.Icc.convexComb (u 0) 1 (u 1)) (u 2)]
  continuous_toFun := by fun_prop

def nativeUpperHighChamberMap : C(NativeCube, NativeCube) where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1),
    Set.Icc.convexComb (Set.Icc.convexComb (u 0) 1 (u 1)) 1 (u 2)]
  continuous_toFun := by fun_prop

/-- The ordered Duffy parametrization with the same permutation on the input coordinates. -/
def nativeOrderedDuffyMap (e : Equiv.Perm (Fin 3)) : C(NativeCube, NativeCube) :=
  (nativeDuffyCube e).comp (permuteCubeCoordinates e)

@[simp] theorem nativeOrderedDuffyMap_identity (u : NativeCube) :
    nativeOrderedDuffyMap 1 u = ![u 0, u 0 * u 1, u 0 * u 1 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem nativeOrderedDuffyMap_swap12 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 1 2) u =
      ![u 0, u 0 * u 2 * u 1, u 0 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem nativeOrderedDuffyMap_cycle201 (u : NativeCube) :
    nativeOrderedDuffyMap nativeCubeCycle201 u =
      ![u 2 * u 0, u 2 * u 0 * u 1, u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem nativeOrderedDuffyMap_swap01 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 0 1) u =
      ![u 1 * u 0, u 1, u 1 * u 0 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem nativeOrderedDuffyMap_cycle120 (u : NativeCube) :
    nativeOrderedDuffyMap nativeCubeCycle120 u =
      ![u 1 * u 2 * u 0, u 1, u 1 * u 2] := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem nativeOrderedDuffyMap_swap02 (u : NativeCube) :
    nativeOrderedDuffyMap (Equiv.swap 0 2) u =
      ![u 2 * u 1 * u 0, u 2 * u 1, u 2] := by
  funext i
  fin_cases i <;> rfl

end Wikipedia.HopfProblem.ThirdHurewicz
