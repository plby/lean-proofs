import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeBasic

/-!
# Extending a cubical reparametrization by untouched coordinates

The first coordinates carry the lower-dimensional chart. All remaining
coordinates are unchanged, and updates in those directions commute with
the extended chart.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {m n : ℕ}

def cubeRestriction (h : m ≤ n) :
    C(NativeCube (Fin n), NativeCube (Fin m)) where
  toFun u i := u (Fin.castLE h i)
  continuous_toFun := continuous_pi fun i => continuous_apply (Fin.castLE h i)

@[simp] theorem cubeRestriction_apply (h : m ≤ n)
    (u : NativeCube (Fin n)) (i : Fin m) :
    cubeRestriction h u i = u (Fin.castLE h i) := rfl

def extendCubeMap (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m))) :
    C(NativeCube (Fin n), NativeCube (Fin n)) where
  toFun u i := if hi : i.val < m then f (cubeRestriction h u) ⟨i.val, hi⟩ else u i
  continuous_toFun := by
    apply continuous_pi
    intro i
    by_cases hi : i.val < m
    · simp only [dif_pos hi]
      exact (continuous_apply ⟨i.val, hi⟩).comp (f.continuous.comp (cubeRestriction h).continuous)
    · simpa only [dif_neg hi] using
        (continuous_apply i : Continuous fun u : NativeCube (Fin n) => u i)

@[simp] theorem extendCubeMap_castLE (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m)))
    (u : NativeCube (Fin n)) (i : Fin m) :
    extendCubeMap h f u (Fin.castLE h i) = f (cubeRestriction h u) i := by
  simp [extendCubeMap]

theorem extendCubeMap_outside (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m)))
    (u : NativeCube (Fin n)) (i : Fin n) (hi : m ≤ i.val) :
    extendCubeMap h f u i = u i := by
  simp [extendCubeMap, Nat.not_lt.mpr hi]

theorem cubeRestriction_update_outside (h : m ≤ n) (u : NativeCube (Fin n))
    (i : Fin n) (hi : m ≤ i.val) (v : I) :
    cubeRestriction h (Function.update u i v) = cubeRestriction h u := by
  funext j
  apply Function.update_of_ne
  intro heq
  have hv := congrArg Fin.val heq
  exact (Nat.not_lt.mpr hi) (hv ▸ j.isLt)

theorem extendCubeMap_update_outside (h : m ≤ n)
    (f : C(NativeCube (Fin m), NativeCube (Fin m)))
    (u : NativeCube (Fin n)) (i : Fin n) (hi : m ≤ i.val) (v : I) :
    extendCubeMap h f (Function.update u i v) =
      Function.update (extendCubeMap h f u) i v := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [extendCubeMap_outside h f _ i hi]
  · rw [Function.update_of_ne hj]
    by_cases hjm : j.val < m
    · simp only [extendCubeMap, ContinuousMap.coe_mk, dif_pos hjm]
      rw [cubeRestriction_update_outside h u i hi v]
    · rw [extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm),
        extendCubeMap_outside h f _ j (Nat.le_of_not_gt hjm),
        Function.update_of_ne hj]

@[simp] theorem cubeRestriction_refl (u : NativeCube (Fin n)) :
    cubeRestriction (le_refl n) u = u := rfl

@[simp] theorem extendCubeMap_refl
    (f : C(NativeCube (Fin n), NativeCube (Fin n))) :
    extendCubeMap (le_refl n) f = f := by
  ext u i
  simp [extendCubeMap]

@[simp] theorem extendCubeMap_zero (h : 0 ≤ n)
    (f : C(NativeCube (Fin 0), NativeCube (Fin 0))) :
    extendCubeMap h f = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro u
  funext i
  exact extendCubeMap_outside h f u i (Nat.zero_le _)

theorem extendCubeMap_sameFlat (h : m ≤ n)
    (f g : C(NativeCube (Fin m), NativeCube (Fin m)))
    (u : NativeCube (Fin n))
    (hfg : NativeCubeSameFlat (f (cubeRestriction h u)) (g (cubeRestriction h u))) :
    NativeCubeSameFlat (extendCubeMap h f u) (extendCubeMap h g u) := by
  cases hfg with
  | zero i hf hg =>
      exact .zero (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | one i hf hg =>
      exact .one (Fin.castLE h i) (by simpa using hf) (by simpa using hg)
  | equal i j hij hf hg =>
      exact .equal (Fin.castLE h i) (Fin.castLE h j)
        (fun heq => hij (Fin.ext (congrArg (fun k : Fin n => k.val) heq)))
        (by simpa using hf) (by simpa using hg)

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
