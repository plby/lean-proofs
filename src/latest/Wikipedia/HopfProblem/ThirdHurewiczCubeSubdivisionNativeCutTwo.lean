import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeCutBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionWarp

/-!
# Native two-piece subdivision along a based coordinate graph

The coordinate warp is exactly the clamped formula of native concatenation.
Its interpolation from the identity gives an actual boundary-relative
homotopy, so the result concerns Mathlib's original third homotopy group.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open SecondHurewicz.SimplyConnected

def nativeCubeCutTwoWarpCoordinate (i : Fin 3) (a : C(NativeCube, I)) :
    C(NativeCube, I) where
  toFun u := subdivisionWarpCoordinate (a u, u i)
  continuous_toFun := subdivisionWarpCoordinate.continuous.comp
    (a.continuous.prodMk (continuous_apply i))

theorem nativeCubeCutTwoWarpCoordinate_zero (i : Fin 3) (a : C(NativeCube, I))
    (u : NativeCube) (hu : u i = 0) : nativeCubeCutTwoWarpCoordinate i a u = 0 := by
  simp [nativeCubeCutTwoWarpCoordinate, hu]

theorem nativeCubeCutTwoWarpCoordinate_one (i : Fin 3) (a : C(NativeCube, I))
    (u : NativeCube) (hu : u i = 1) : nativeCubeCutTwoWarpCoordinate i a u = 1 := by
  simp [nativeCubeCutTwoWarpCoordinate, hu]

variable {X : Type*} [TopologicalSpace X] {x : X}

def nativeCubeCutTwoWarpLoop (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) : GenLoop (Fin 3) X x :=
  nativeCubeCutCoordinateLoop p i (nativeCubeCutTwoWarpCoordinate i a)
    (nativeCubeCutTwoWarpCoordinate_zero i a) (nativeCubeCutTwoWarpCoordinate_one i a)

theorem nativeCubeCutTwoWarpLoop_eq_transAt (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (haInd : NativeCubeCutIndependent i a) :
    nativeCubeCutTwoWarpLoop p i a =
      GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutUpperLoop p i a ha) := by
  apply GenLoop.ext
  intro u
  change p (Function.update u i (subdivisionWarpCoordinate (a u, u i))) =
    if (u i : ℝ) ≤ 1 / 2 then
      nativeCubeCutLowerLoop p i a ha
        (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
    else
      nativeCubeCutUpperLoop p i a ha
        (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))
  split_ifs with h
  · rw [nativeCubeCutLowerLoop_apply, haInd u _, Function.update_self,
      Function.update_idem]
    exact congrArg (fun v => p (Function.update u i v))
      (subdivisionWarpCoordinate_of_le_half (a u) (u i) h)
  · rw [nativeCubeCutUpperLoop_apply, haInd u _, Function.update_self,
      Function.update_idem]
    exact congrArg (fun v => p (Function.update u i v))
      (subdivisionWarpCoordinate_of_half_lt (a u) (u i) (lt_of_not_ge h))

/-- The literal relative homotopy cutting the cube into its two coordinate slices. -/
theorem nativeCubeCutTwo_homotopic (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (haInd : NativeCubeCutIndependent i a) :
    GenLoop.Homotopic p
      (GenLoop.transAt i (nativeCubeCutLowerLoop p i a ha) (nativeCubeCutUpperLoop p i a ha)) := by
  have h : GenLoop.Homotopic p (nativeCubeCutTwoWarpLoop p i a) :=
    ⟨nativeCubeCutCoordinateHomotopy p i (nativeCubeCutTwoWarpCoordinate i a)
      (nativeCubeCutTwoWarpCoordinate_zero i a) (nativeCubeCutTwoWarpCoordinate_one i a)⟩
  rwa [nativeCubeCutTwoWarpLoop_eq_transAt p i a ha haInd] at h

theorem nativeCubeCutTwo_class (p : GenLoop (Fin 3) X x) (i : Fin 3)
    (a : C(NativeCube, I)) (ha : NativeCubeCutBased p i a)
    (haInd : NativeCubeCutIndependent i a) :
    nativeCubeClass p = nativeCubeClass (nativeCubeCutLowerLoop p i a ha) +
      nativeCubeClass (nativeCubeCutUpperLoop p i a ha) :=
  (nativeCubeClass_homotopic (nativeCubeCutTwo_homotopic p i a ha haInd)).trans
    (nativeCubeClass_transAt i _ _)

end Wikipedia.HopfProblem.ThirdHurewicz
