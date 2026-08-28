import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticRetraction
import Wikipedia.HopfProblem.EllipticFirstHomologySingular
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Actual first homology of the small elliptic pieces and their global patches

The genuine special central surface retracts both its chosen positive-radius
elliptic piece and the full lifted elliptic patch in the constructed threefold.
Naturality of the first Hurewicz isomorphism identifies the resulting integral
singular first-homology isomorphisms with the actual inclusion-induced maps.

The rank-two computations below concern the small native pieces and their
actual global lifted patches. They do not assert an isomorphism with the
homology of the whole threefold.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic EllipticFilling FirstHurewicz

/-- Radial paths in the actual positive-radius piece join every point to
its path-connected special central surface. -/
instance piecePathConnected (j : Kind) : PathConnectedSpace (LocalSpace j) where
  nonempty := ⟨centralSurfaceIntoPiece j
    (Classical.choice (PathConnectedSpace.nonempty (X := SpecialCentralSurface j)))⟩
  joined x y := by
    let H := (pieceStrongDeformationRetraction j).toHomotopy
    have hx : Joined x (centralSurfaceIntoPiece j (pieceSurfaceRetraction j x)) :=
      ⟨H.evalAt x⟩
    have hy : Joined y (centralSurfaceIntoPiece j (pieceSurfaceRetraction j y)) :=
      ⟨H.evalAt y⟩
    have hxy := (PathConnectedSpace.joined
      (pieceSurfaceRetraction j x) (pieceSurfaceRetraction j y)).map
        (centralSurfaceIntoPiece j).continuous
    exact hx.trans (hxy.trans hy.symm)

/-- The corresponding radial paths lie in the entire actual global
lifted elliptic patch. -/
instance liftedPatchPathConnected (j : Kind) :
    PathConnectedSpace (Threefold.liftedPatch (some (some j))) where
  nonempty := ⟨centralSurfaceIntoLiftedPatch j
    (Classical.choice (PathConnectedSpace.nonempty (X := SpecialCentralSurface j)))⟩
  joined x y := by
    let H := (liftedPatchStrongDeformationRetraction j).toHomotopy
    have hx : Joined x
        (centralSurfaceIntoLiftedPatch j (liftedPatchSurfaceRetraction j x)) :=
      ⟨H.evalAt x⟩
    have hy : Joined y
        (centralSurfaceIntoLiftedPatch j (liftedPatchSurfaceRetraction j y)) :=
      ⟨H.evalAt y⟩
    have hxy := (PathConnectedSpace.joined
      (liftedPatchSurfaceRetraction j x) (liftedPatchSurfaceRetraction j y)).map
        (centralSurfaceIntoLiftedPatch j).continuous
    exact hx.trans (hxy.trans hy.symm)

/-- Abelianization of the actual small-piece inclusion on fundamental groups. -/
def pieceCentralSurfaceAbelianizationEquiv (j : Kind) (a : SpecialCentralSurface j) :
    AbelianPi1 (SpecialCentralSurface j) a ≃ₗ[ℤ]
      AbelianPi1 (LocalSpace j) (centralSurfaceIntoPiece j a) :=
  abelianizationLinearCongr (pieceSurfaceFundamentalGroupEquiv j a)

@[simp] theorem pieceCentralSurfaceAbelianizationEquiv_toLinearMap
    (j : Kind) (a : SpecialCentralSurface j) :
    (pieceCentralSurfaceAbelianizationEquiv j a).toLinearMap =
      inducedAbelianPi1 (centralSurfaceIntoPiece j) a := by
  change (Abelianization.map
    (pieceSurfaceFundamentalGroupEquiv j a).toMonoidHom).toAdditive.toIntLinearMap = _
  rw [pieceSurfaceFundamentalGroupEquiv_toMonoidHom]
  rfl

/-- The actual central-surface inclusion into the positive-radius native
piece induces this first singular homology isomorphism. -/
def pieceCentralSurfaceSingularH1Equiv (j : Kind) (a : SpecialCentralSurface j) :
    SingularH1 (SpecialCentralSurface j) ≃ₗ[ℤ] SingularH1 (LocalSpace j) :=
  (firstHurewiczEquiv a).symm.trans
    ((pieceCentralSurfaceAbelianizationEquiv j a).trans
      (firstHurewiczEquiv (centralSurfaceIntoPiece j a)))

@[simp] theorem pieceCentralSurfaceSingularH1Equiv_hurewicz
    (j : Kind) (a : SpecialCentralSurface j) (c : AbelianPi1 (SpecialCentralSurface j) a) :
    pieceCentralSurfaceSingularH1Equiv j a (firstHurewiczEquiv a c) =
      firstHurewiczEquiv (centralSurfaceIntoPiece j a)
        (pieceCentralSurfaceAbelianizationEquiv j a c) := by
  change firstHurewiczEquiv (centralSurfaceIntoPiece j a)
    (pieceCentralSurfaceAbelianizationEquiv j a
      ((firstHurewiczEquiv a).symm (firstHurewiczEquiv a c))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Equality with Mathlib's actual induced singular homology map of the
unchanged small-piece inclusion. -/
theorem pieceCentralSurfaceSingularH1Equiv_toLinearMap
    (j : Kind) (a : SpecialCentralSurface j) :
    (pieceCentralSurfaceSingularH1Equiv j a).toLinearMap =
      inducedHomology (centralSurfaceIntoPiece j) := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := (firstHurewiczEquiv a).surjective c
  change pieceCentralSurfaceSingularH1Equiv j a (firstHurewiczEquiv a b) = _
  rw [pieceCentralSurfaceSingularH1Equiv_hurewicz]
  have hb : pieceCentralSurfaceAbelianizationEquiv j a b =
      inducedAbelianPi1 (centralSurfaceIntoPiece j) a b :=
    LinearMap.congr_fun (pieceCentralSurfaceAbelianizationEquiv_toLinearMap j a) b
  rw [hb]
  exact (firstHurewiczEquiv_natural (centralSurfaceIntoPiece j) a b).symm

theorem pieceCentralSurface_singularH1_bijective (j : Kind) :
    Function.Bijective (inducedHomology (centralSurfaceIntoPiece j)) := by
  rw [← pieceCentralSurfaceSingularH1Equiv_toLinearMap j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 0)]
  exact (pieceCentralSurfaceSingularH1Equiv j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 0)).bijective

/-- Abelianization of the actual central inclusion into the entire
global lifted elliptic patch. -/
def liftedPatchCentralSurfaceAbelianizationEquiv (j : Kind) (a : SpecialCentralSurface j) :
    AbelianPi1 (SpecialCentralSurface j) a ≃ₗ[ℤ]
      AbelianPi1 (Threefold.liftedPatch (some (some j)))
        (centralSurfaceIntoLiftedPatch j a) :=
  abelianizationLinearCongr (liftedPatchSurfaceFundamentalGroupEquiv j a)

@[simp] theorem liftedPatchCentralSurfaceAbelianizationEquiv_toLinearMap
    (j : Kind) (a : SpecialCentralSurface j) :
    (liftedPatchCentralSurfaceAbelianizationEquiv j a).toLinearMap =
      inducedAbelianPi1 (centralSurfaceIntoLiftedPatch j) a := by
  change (Abelianization.map
    (liftedPatchSurfaceFundamentalGroupEquiv j a).toMonoidHom).toAdditive.toIntLinearMap = _
  rw [liftedPatchSurfaceFundamentalGroupEquiv_toMonoidHom]
  rfl

/-- The actual central inclusion into the entire global lifted patch
induces this first singular homology isomorphism. -/
def liftedPatchCentralSurfaceSingularH1Equiv (j : Kind) (a : SpecialCentralSurface j) :
    SingularH1 (SpecialCentralSurface j) ≃ₗ[ℤ]
      SingularH1 (Threefold.liftedPatch (some (some j))) :=
  (firstHurewiczEquiv a).symm.trans
    ((liftedPatchCentralSurfaceAbelianizationEquiv j a).trans
      (firstHurewiczEquiv (centralSurfaceIntoLiftedPatch j a)))

@[simp] theorem liftedPatchCentralSurfaceSingularH1Equiv_hurewicz
    (j : Kind) (a : SpecialCentralSurface j) (c : AbelianPi1 (SpecialCentralSurface j) a) :
    liftedPatchCentralSurfaceSingularH1Equiv j a (firstHurewiczEquiv a c) =
      firstHurewiczEquiv (centralSurfaceIntoLiftedPatch j a)
        (liftedPatchCentralSurfaceAbelianizationEquiv j a c) := by
  change firstHurewiczEquiv (centralSurfaceIntoLiftedPatch j a)
    (liftedPatchCentralSurfaceAbelianizationEquiv j a
      ((firstHurewiczEquiv a).symm (firstHurewiczEquiv a c))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Equality with the actual map on integral singular homology of the
global lifted-patch inclusion. -/
theorem liftedPatchCentralSurfaceSingularH1Equiv_toLinearMap
    (j : Kind) (a : SpecialCentralSurface j) :
    (liftedPatchCentralSurfaceSingularH1Equiv j a).toLinearMap =
      inducedHomology (centralSurfaceIntoLiftedPatch j) := by
  apply LinearMap.ext
  intro c
  obtain ⟨b, rfl⟩ := (firstHurewiczEquiv a).surjective c
  change liftedPatchCentralSurfaceSingularH1Equiv j a (firstHurewiczEquiv a b) = _
  rw [liftedPatchCentralSurfaceSingularH1Equiv_hurewicz]
  have hb : liftedPatchCentralSurfaceAbelianizationEquiv j a b =
      inducedAbelianPi1 (centralSurfaceIntoLiftedPatch j) a b :=
    LinearMap.congr_fun (liftedPatchCentralSurfaceAbelianizationEquiv_toLinearMap j a) b
  rw [hb]
  exact (firstHurewiczEquiv_natural (centralSurfaceIntoLiftedPatch j) a b).symm

theorem liftedPatchCentralSurface_singularH1_bijective (j : Kind) :
    Function.Bijective (inducedHomology (centralSurfaceIntoLiftedPatch j)) := by
  rw [← liftedPatchCentralSurfaceSingularH1Equiv_toLinearMap j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 0)]
  exact (liftedPatchCentralSurfaceSingularH1Equiv j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) 0)).bijective

/-- Integral rank-two coordinates on the actual small native piece. -/
def pieceSingularH1RankTwoEquiv (j : Kind) (y : RealCoordinates) :
    SingularH1 (LocalSpace j) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (pieceCentralSurfaceSingularH1Equiv j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) y)).symm.trans
        (surfaceSingularH1RankTwoEquiv j (specialLocalData j).centralPeriod
          j.twist (mainTwist_admissible j) y)

@[simp] theorem pieceSingularH1RankTwoEquiv_inclusion (j : Kind) (y : RealCoordinates)
    (c : SingularH1 (SpecialCentralSurface j)) :
    pieceSingularH1RankTwoEquiv j y (inducedHomology (centralSurfaceIntoPiece j) c) =
      surfaceSingularH1RankTwoEquiv j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j) y c := by
  rw [← pieceCentralSurfaceSingularH1Equiv_toLinearMap j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) y)]
  change surfaceSingularH1RankTwoEquiv j (specialLocalData j).centralPeriod
    j.twist (mainTwist_admissible j) y
      ((pieceCentralSurfaceSingularH1Equiv j
        (affineCoverProjection j (specialLocalData j).centralPeriod
          j.twist (mainTwist_admissible j) y)).symm
        (pieceCentralSurfaceSingularH1Equiv j
          (affineCoverProjection j (specialLocalData j).centralPeriod
            j.twist (mainTwist_admissible j) y) c)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Integral rank-two coordinates on the entire actual global lifted
elliptic patch, not on the whole threefold. -/
def liftedPatchSingularH1RankTwoEquiv (j : Kind) (y : RealCoordinates) :
    SingularH1 (Threefold.liftedPatch (some (some j))) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (liftedPatchCentralSurfaceSingularH1Equiv j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) y)).symm.trans
        (surfaceSingularH1RankTwoEquiv j (specialLocalData j).centralPeriod
          j.twist (mainTwist_admissible j) y)

@[simp] theorem liftedPatchSingularH1RankTwoEquiv_inclusion
    (j : Kind) (y : RealCoordinates) (c : SingularH1 (SpecialCentralSurface j)) :
    liftedPatchSingularH1RankTwoEquiv j y
        (inducedHomology (centralSurfaceIntoLiftedPatch j) c) =
      surfaceSingularH1RankTwoEquiv j (specialLocalData j).centralPeriod
        j.twist (mainTwist_admissible j) y c := by
  rw [← liftedPatchCentralSurfaceSingularH1Equiv_toLinearMap j
    (affineCoverProjection j (specialLocalData j).centralPeriod
      j.twist (mainTwist_admissible j) y)]
  change surfaceSingularH1RankTwoEquiv j (specialLocalData j).centralPeriod
    j.twist (mainTwist_admissible j) y
      ((liftedPatchCentralSurfaceSingularH1Equiv j
        (affineCoverProjection j (specialLocalData j).centralPeriod
          j.twist (mainTwist_admissible j) y)).symm
        (liftedPatchCentralSurfaceSingularH1Equiv j
          (affineCoverProjection j (specialLocalData j).centralPeriod
            j.twist (mainTwist_admissible j) y) c)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem pieceSingularH1_free (j : Kind) : Module.Free ℤ (SingularH1 (LocalSpace j)) :=
  Module.Free.of_equiv (pieceSingularH1RankTwoEquiv j 0).symm

theorem pieceSingularH1_finite (j : Kind) : Module.Finite ℤ (SingularH1 (LocalSpace j)) :=
  Module.Finite.of_surjective (pieceSingularH1RankTwoEquiv j 0).symm.toLinearMap
    (pieceSingularH1RankTwoEquiv j 0).symm.surjective

theorem pieceSingularH1_finrank (j : Kind) : Module.finrank ℤ (SingularH1 (LocalSpace j)) = 2 := by
  rw [(pieceSingularH1RankTwoEquiv j 0).finrank_eq]
  simp

theorem pieceSingularH1_torsionFree (j : Kind) :
    Module.IsTorsionFree ℤ (SingularH1 (LocalSpace j)) := by
  let := pieceSingularH1_free j
  infer_instance

theorem liftedPatchSingularH1_free (j : Kind) :
    Module.Free ℤ (SingularH1 (Threefold.liftedPatch (some (some j)))) :=
  Module.Free.of_equiv (liftedPatchSingularH1RankTwoEquiv j 0).symm

theorem liftedPatchSingularH1_finite (j : Kind) :
    Module.Finite ℤ (SingularH1 (Threefold.liftedPatch (some (some j)))) :=
  Module.Finite.of_surjective (liftedPatchSingularH1RankTwoEquiv j 0).symm.toLinearMap
    (liftedPatchSingularH1RankTwoEquiv j 0).symm.surjective

theorem liftedPatchSingularH1_finrank (j : Kind) :
    Module.finrank ℤ (SingularH1 (Threefold.liftedPatch (some (some j)))) = 2 := by
  rw [(liftedPatchSingularH1RankTwoEquiv j 0).finrank_eq]
  simp

theorem liftedPatchSingularH1_torsionFree (j : Kind) :
    Module.IsTorsionFree ℤ (SingularH1 (Threefold.liftedPatch (some (some j)))) := by
  let := liftedPatchSingularH1_free j
  infer_instance

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
