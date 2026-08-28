import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeCutTwo
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeWarpThree

/-!
# Native three-piece subdivision along two based coordinate graphs

Two coordinate-independent based graphs cut a cube into lower, middle and
upper parametrized pieces. No order condition on the graphs is needed:
the explicit warp also handles a reversed middle interval. The concatenation
is the original native operation, with the lower two pieces nested first.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

def nativeCubeCutThreeWarpCoordinate (i : Fin 3) (a b : C(NativeCube, I)) :
    C(NativeCube, I) where
  toFun u := subdivisionWarpThreeCoordinate ((a u, b u), u i)
  continuous_toFun := subdivisionWarpThreeCoordinate.continuous.comp
    ((a.continuous.prodMk b.continuous).prodMk (continuous_apply i))

theorem nativeCubeCutThreeWarpCoordinate_zero (i : Fin 3) (a b : C(NativeCube, I))
    (u : NativeCube) (hu : u i = 0) : nativeCubeCutThreeWarpCoordinate i a b u = 0 := by
  simp [nativeCubeCutThreeWarpCoordinate, hu]

theorem nativeCubeCutThreeWarpCoordinate_one (i : Fin 3) (a b : C(NativeCube, I))
    (u : NativeCube) (hu : u i = 1) : nativeCubeCutThreeWarpCoordinate i a b u = 1 := by
  simp [nativeCubeCutThreeWarpCoordinate, hu]

variable {X : Type*} [TopologicalSpace X] {x : X}

def nativeCubeCutThreeWarpLoop (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a b : C(NativeCube, I)) : GenLoop (Fin 3) X x :=
  nativeCubeCutCoordinateLoop p i (nativeCubeCutThreeWarpCoordinate i a b)
    (nativeCubeCutThreeWarpCoordinate_zero i a b) (nativeCubeCutThreeWarpCoordinate_one i a b)

theorem nativeCubeCutThreeWarpLoop_eq_transAt (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a b : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (hb : NativeCubeCutBased p i b) (haInd : NativeCubeCutIndependent i a)
    (hbInd : NativeCubeCutIndependent i b) :
    nativeCubeCutThreeWarpLoop p i a b = GenLoop.transAt i
      (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutMiddleLoop p i a b ha hb))
      (nativeCubeCutUpperLoop p i b hb) := by
  apply GenLoop.ext
  intro u
  change p (Function.update u i (subdivisionWarpThreeCoordinate ((a u, b u), u i))) =
    if (u i : ℝ) ≤ 1 / 2 then
      (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha)
        (nativeCubeCutMiddleLoop p i a b ha hb))
          (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
    else
      nativeCubeCutUpperLoop p i b hb
        (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))
  split_ifs with h
  · change p (Function.update u i (subdivisionWarpThreeCoordinate ((a u, b u), u i))) =
      if ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ) ≤ 1 / 2 then
        nativeCubeCutLowerLoop p i a ha
          (Function.update
            (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i
            (Set.projIcc 0 1 zero_le_one
              (2 * ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ))))
      else
        nativeCubeCutMiddleLoop p i a b ha hb
          (Function.update
            (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i
            (Set.projIcc 0 1 zero_le_one
              (2 *
                ((Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ)))) i : ℝ) - 1)))
    simp only [Function.update_self]
    split_ifs with hi
    · simp only [nativeCubeCutLowerLoop_apply, Function.update_self,
        Function.update_idem]
      rw [haInd u _]
      exact congrArg (fun v => p (Function.update u i v))
        (subdivisionWarpThreeCoordinate_nested_lower (a u) (b u) (u i) h hi)
    · simp only [nativeCubeCutMiddleLoop_apply, Function.update_self,
        Function.update_idem]
      rw [haInd u _, hbInd u _]
      exact congrArg (fun v => p (Function.update u i v))
        (subdivisionWarpThreeCoordinate_nested_middle (a u) (b u) (u i) h (lt_of_not_ge hi))
  · rw [nativeCubeCutUpperLoop_apply, hbInd u _, Function.update_self,
      Function.update_idem]
    exact congrArg (fun v => p (Function.update u i v))
      (subdivisionWarpThreeCoordinate_nested_upper (a u) (b u) (u i) (lt_of_not_ge h))

/-- An explicit relative homotopy realizes all three slices with native concatenation. -/
theorem nativeCubeCutThree_homotopic (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a b : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (hb : NativeCubeCutBased p i b) (haInd : NativeCubeCutIndependent i a)
    (hbInd : NativeCubeCutIndependent i b) :
    GenLoop.Homotopic p (GenLoop.transAt i
      (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutMiddleLoop p i a b ha hb))
      (nativeCubeCutUpperLoop p i b hb)) := by
  have h : GenLoop.Homotopic p (nativeCubeCutThreeWarpLoop p i a b) :=
    ⟨nativeCubeCutCoordinateHomotopy p i (nativeCubeCutThreeWarpCoordinate i a b)
      (nativeCubeCutThreeWarpCoordinate_zero i a b) (nativeCubeCutThreeWarpCoordinate_one i a b)⟩
  rwa [nativeCubeCutThreeWarpLoop_eq_transAt p i a b ha hb haInd hbInd] at h

theorem nativeCubeCutThree_class (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a b : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (hb : NativeCubeCutBased p i b) (haInd : NativeCubeCutIndependent i a)
    (hbInd : NativeCubeCutIndependent i b) :
    nativeCubeClass p = nativeCubeClass (nativeCubeCutLowerLoop p i a ha) +
      nativeCubeClass (nativeCubeCutMiddleLoop p i a b ha hb) +
      nativeCubeClass (nativeCubeCutUpperLoop p i b hb) := by
  rw [nativeCubeClass_homotopic (nativeCubeCutThree_homotopic p i a b ha hb haInd hbInd),
    nativeCubeClass_transAt, nativeCubeClass_transAt]

end Wikipedia.HopfProblem.ThirdHurewicz
