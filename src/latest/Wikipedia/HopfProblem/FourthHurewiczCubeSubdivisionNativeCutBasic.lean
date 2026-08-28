import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeBasic

/-!
# Coordinate slices of native cubes in arbitrary dimension

A slice is bounded by two actual based coordinate graphs. Its relative
homotopies use coordinate interpolation, so neither ordered cuts nor any
replacement for the original generalized loops is needed.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {N : Type*} [DecidableEq N]
variable {X : Type*} [TopologicalSpace X] {x : X}

def CutIndependent (i : N) (a : C(NativeCube N, I)) : Prop :=
  ∀ u v, a (Function.update u i v) = a u

def CutBased (p : GenLoop N X x) (i : N) (a : C(NativeCube N, I)) : Prop :=
  ∀ u, p (Function.update u i (a u)) = x

def sliceMap (i : N) (a b : C(NativeCube N, I)) : C(NativeCube N, NativeCube N) where
  toFun u := Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))
  continuous_toFun := continuous_id.update i
    (Set.Icc.continuous_convexComb_prod.comp
      (a.continuous.prodMk (b.continuous.prodMk (continuous_apply i))))

theorem sliceMap_based (p : GenLoop N X x) (i : N) (a b : C(NativeCube N, I))
    (ha : CutBased p i a) (hb : CutBased p i b)
    (u : NativeCube N) (hu : u ∈ Cube.boundary N) : p (sliceMap i a b u) = x := by
  rcases hu with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    rcases hj with hj | hj
    · simpa [sliceMap, hj] using ha u
    · simpa [sliceMap, hj] using hb u
  · exact p.property _ ⟨j, by simpa [sliceMap, hji] using hj⟩

/-- The original generalized loop pulled back along an actual coordinate slice. -/
def sliceLoop (p : GenLoop N X x) (i : N) (a b : C(NativeCube N, I))
    (ha : CutBased p i a) (hb : CutBased p i b) : GenLoop N X x :=
  ⟨p.val.comp (sliceMap i a b), sliceMap_based p i a b ha hb⟩

@[simp] theorem sliceLoop_apply (p : GenLoop N X x) (i : N) (a b : C(NativeCube N, I))
    (ha : CutBased p i a) (hb : CutBased p i b) (u : NativeCube N) :
    sliceLoop p i a b ha hb u =
      p (Function.update u i (Set.Icc.convexComb (a u) (b u) (u i))) := rfl

theorem sliceLoop_self (p : GenLoop N X x) (i : N) (a : C(NativeCube N, I))
    (ha : CutBased p i a) : sliceLoop p i a a ha ha = GenLoop.const := by
  apply GenLoop.ext
  intro u
  simpa only [sliceLoop_apply, Set.Icc.convexComb_eq, GenLoop.const_apply] using ha u

theorem sliceLoop_full (p : GenLoop N X x) (i : N) (a b : C(NativeCube N, I))
    (ha : CutBased p i a) (hb : CutBased p i b)
    (ha0 : ∀ u, a u = 0) (hb1 : ∀ u, b u = 1) : sliceLoop p i a b ha hb = p := by
  apply GenLoop.ext
  intro u
  simp [ha0 u, hb1 u]

/-- Interpolation to any actual coordinate presentation with the same two endpoint graphs. -/
def sliceHomotopyOfCoordinate (p : GenLoop N X x) (i : N) (a b : C(NativeCube N, I))
    (ha : CutBased p i a) (hb : CutBased p i b) (q : GenLoop N X x)
    (w : C(NativeCube N, I)) (hq : ∀ u, q u = p (Function.update u i (w u)))
    (hw0 : ∀ u, u i = 0 → w u = a u) (hw1 : ∀ u, u i = 1 → w u = b u) :
    (sliceLoop p i a b ha hb).val.HomotopyRel q.val (Cube.boundary N) where
  toFun v := p (Function.update v.2 i
    (Set.Icc.convexComb (Set.Icc.convexComb (a v.2) (b v.2) (v.2 i)) (w v.2) v.1))
  continuous_toFun := p.val.continuous.comp
    (continuous_snd.update i (Set.Icc.continuous_convexComb_prod.comp
      ((Set.Icc.continuous_convexComb_prod.comp
        ((a.continuous.comp continuous_snd).prodMk
          ((b.continuous.comp continuous_snd).prodMk
            ((continuous_apply i).comp continuous_snd)))).prodMk
        ((w.continuous.comp continuous_snd).prodMk continuous_fst))))
  map_zero_left u := by
    change p (Function.update u i
      (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 0)) = _
    rw [Set.Icc.convexComb_zero]
    rfl
  map_one_left u := by
    change p (Function.update u i
      (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) 1)) = q u
    rw [Set.Icc.convexComb_one]
    exact (hq u).symm
  prop' t u hu := by
    change p (Function.update u i
      (Set.Icc.convexComb (Set.Icc.convexComb (a u) (b u) (u i)) (w u) t)) =
      sliceLoop p i a b ha hb u
    have hs : sliceLoop p i a b ha hb u = x := (sliceLoop p i a b ha hb).property u hu
    rw [hs]
    rcases hu with ⟨j, hj⟩
    by_cases hji : j = i
    · subst j
      rcases hj with hj | hj
      · simpa [hj, hw0 u hj] using ha u
      · simpa [hj, hw1 u hj] using hb u
    · exact p.property _ ⟨j, by simpa [hji] using hj⟩

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
