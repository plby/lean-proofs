import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeBasic

/-!
# Native cube slices along based coordinate graphs

The three coordinate maps preserve every coordinate except the selected one.
Their boundary conditions use the actual graph of the cut, not a homotopy
class of that graph. An endpoint-preserving coordinate warp is joined to the
identity by a literal homotopy relative to the original cube boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

def NativeCubeCutIndependent (i : Fin 3) (a : C(NativeCube, I)) : Prop :=
  ∀ u v, a (Function.update u i v) = a u

def NativeCubeCutBased (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

def nativeCubeCutLowerMap (i : Fin 3) (a : C(NativeCube, I)) :
    C(NativeCube, NativeCube) where
  toFun u := Function.update u i (a u * u i)
  continuous_toFun := continuous_id.update i
    (((continuous_subtype_val.comp a.continuous).mul
      (continuous_subtype_val.comp (continuous_apply i))).subtype_mk _)

def nativeCubeCutMiddleMap (i : Fin 3) (a b : C(NativeCube, I)) :
    C(NativeCube, NativeCube) where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun := continuous_id.update i
    (Set.Icc.continuous_convexComb_prod.comp
      (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

def nativeCubeCutUpperMap (i : Fin 3) (b : C(NativeCube, I)) :
    C(NativeCube, NativeCube) where
  toFun u := Function.update u i (Set.Icc.convexComb (b u) 1 (u i))
  continuous_toFun := continuous_id.update i
    (Set.Icc.continuous_convexComb_prod.comp
      (b.continuous.prodMk (continuous_const.prodMk (continuous_apply i))))

theorem nativeCubeCutLowerMap_based (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeCutLowerMap i a u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · exact p.property _ ⟨i, Or.inl (by simp [nativeCubeCutLowerMap, hj])⟩
    · simpa [nativeCubeCutLowerMap, hj] using ha u
  · exact p.property _ ⟨j, by simpa [nativeCubeCutLowerMap, hji] using hj⟩

theorem nativeCubeCutMiddleMap_based (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a b : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (hb : NativeCubeCutBased p i b)
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeCutMiddleMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [nativeCubeCutMiddleMap, hj] using ha u
    · simpa [nativeCubeCutMiddleMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [nativeCubeCutMiddleMap, hji] using hj⟩

theorem nativeCubeCutUpperMap_based (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (b : C(NativeCube, I)) (hb : NativeCubeCutBased p i b)
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeCubeCutUpperMap i b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [nativeCubeCutUpperMap, hj] using hb u
    · exact p.property _ ⟨i, Or.inr (by simp [nativeCubeCutUpperMap, hj])⟩
  · exact p.property _ ⟨j, by simpa [nativeCubeCutUpperMap, hji] using hj⟩

def nativeCubeCutLowerLoop (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) (ha : NativeCubeCutBased p i a) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutLowerMap i a)
    (nativeCubeCutLowerMap_based p i a ha)

def nativeCubeCutMiddleLoop (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a b : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (hb : NativeCubeCutBased p i b) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutMiddleMap i a b)
    (nativeCubeCutMiddleMap_based p i a b ha hb)

def nativeCubeCutUpperLoop (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (b : C(NativeCube, I)) (hb : NativeCubeCutBased p i b) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutUpperMap i b)
    (nativeCubeCutUpperMap_based p i b hb)

@[simp] theorem nativeCubeCutLowerLoop_apply (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) (ha : NativeCubeCutBased p i a) (u : NativeCube) :
    nativeCubeCutLowerLoop p i a ha u = p (Function.update u i (a u * u i)) := rfl

@[simp] theorem nativeCubeCutMiddleLoop_apply (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a b : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (hb : NativeCubeCutBased p i b) (u : NativeCube) :
    nativeCubeCutMiddleLoop p i a b ha hb u =
      p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) := rfl

@[simp] theorem nativeCubeCutUpperLoop_apply (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (b : C(NativeCube, I)) (hb : NativeCubeCutBased p i b) (u : NativeCube) :
    nativeCubeCutUpperLoop p i b hb u =
      p (Function.update u i (Set.Icc.convexComb (b u) 1 (u i))) := rfl

def nativeCubeCutCoordinateMap (i : Fin 3) (w : C(NativeCube, I)) :
    C(NativeCube, NativeCube) where
  toFun u := Function.update u i (w u)
  continuous_toFun := continuous_id.update i w.continuous

theorem nativeCubeCutCoordinateMap_boundary (i : Fin 3) (w : C(NativeCube, I))
    (hzero : ∀ u, u i = 0 → w u = 0) (hone : ∀ u, u i = 1 → w u = 1)
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeCubeCutCoordinateMap i w u ∈ Cube.boundary (Fin 3) := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · exact ⟨i, Or.inl (by simp [nativeCubeCutCoordinateMap, hzero u hj])⟩
    · exact ⟨i, Or.inr (by simp [nativeCubeCutCoordinateMap, hone u hj])⟩
  · exact ⟨j, by simpa [nativeCubeCutCoordinateMap, hji] using hj⟩

def nativeCubeCutCoordinateLoop (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (w : C(NativeCube, I)) (hzero : ∀ u, u i = 0 → w u = 0)
    (hone : ∀ u, u i = 1 → w u = 1) : GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeCubeCutCoordinateMap i w)
    (fun u hu => p.property _ (nativeCubeCutCoordinateMap_boundary i w hzero hone u hu))

/-- Coordinate interpolation fixes every boundary face throughout the homotopy. -/
def nativeCubeCutCoordinateHomotopy (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (w : C(NativeCube, I)) (hzero : ∀ u, u i = 0 → w u = 0)
    (hone : ∀ u, u i = 1 → w u = 1) :
    p.val.HomotopyRel (nativeCubeCutCoordinateLoop p i w hzero hone).val
      (Cube.boundary (Fin 3)) where
  toFun v := p (Function.update v.2 i (Set.Icc.convexComb (v.2 i) (w v.2) v.1))
  continuous_toFun := p.val.continuous.comp
    (continuous_snd.update i (Set.Icc.continuous_convexComb_prod.comp
      (((continuous_apply i).comp continuous_snd).prodMk
        ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left u := by simp
  map_one_left u := by
    change p (Function.update u i (Set.Icc.convexComb (u i) (w u) 1)) =
      p (Function.update u i (w u))
    rw [Set.Icc.convexComb_one]
  prop' t u hu := by
    rw [p.property u hu]
    apply p.property
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · exact ⟨i, Or.inl (by simp [hj, hzero u hj])⟩
      · exact ⟨i, Or.inr (by simp [hj, hone u hj])⟩
    · exact ⟨j, by simpa [hji] using hj⟩

end Wikipedia.HopfProblem.ThirdHurewicz
