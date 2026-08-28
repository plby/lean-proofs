import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticRetraction
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The actual elliptic retraction on fundamental groups at every basepoint

The actual radial retraction induces a fundamental-group isomorphism at
every point of the chosen small elliptic piece, including noncentral
points.  Its forward map is exactly the continuous retraction's induced
map.  The corresponding result also holds on the full lifted elliptic
patch.  This does not identify attaching meridians or assert anything
about the fundamental group of the entire global threefold.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.EllipticRetractionTopology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homotopy equivalence induces a bijection on the actual loop classes
at every basepoint, since its fundamental-groupoid functor is fully faithful. -/
theorem fundamentalGroup_map_bijective (e : X ≃ₕ Y) (x : X) :
    Function.Bijective (FundamentalGroup.map e.toFun x) := by
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact E.fullyFaithfulFunctor.map_bijective
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x)

/-- The induced group isomorphism retains exactly the original continuous
map, not a separately chosen basepoint-change map. -/
def fundamentalGroupEquivAt (e : X ≃ₕ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  MulEquiv.ofBijective (FundamentalGroup.map e.toFun x) (fundamentalGroup_map_bijective e x)

@[simp] theorem fundamentalGroupEquivAt_toMonoidHom (e : X ≃ₕ Y) (x : X) :
    (fundamentalGroupEquivAt e x).toMonoidHom = FundamentalGroup.map e.toFun x := rfl

end Wikipedia.HopfProblem.EllipticRetractionTopology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling

/-- The actual small-piece retraction induces an isomorphism at every
basepoint, with no centrality condition. -/
def pieceSurfaceRetractionFundamentalGroupEquiv (j : Elliptic.Kind) (x : LocalSpace j) :
    FundamentalGroup (LocalSpace j) x ≃*
      FundamentalGroup (SpecialCentralSurface j) (pieceSurfaceRetraction j x) :=
  EllipticRetractionTopology.fundamentalGroupEquivAt (pieceSurfaceHomotopyEquiv j).symm x

@[simp] theorem pieceSurfaceRetractionFundamentalGroupEquiv_toMonoidHom
    (j : Elliptic.Kind) (x : LocalSpace j) :
    (pieceSurfaceRetractionFundamentalGroupEquiv j x).toMonoidHom =
      FundamentalGroup.map (pieceSurfaceRetraction j) x := rfl

theorem pieceSurfaceRetraction_fundamentalGroup_map_bijective
    (j : Elliptic.Kind) (x : LocalSpace j) :
    Function.Bijective (FundamentalGroup.map (pieceSurfaceRetraction j) x) :=
  (pieceSurfaceRetractionFundamentalGroupEquiv j x).bijective

@[simp] theorem pieceSurfaceRetractionFundamentalGroupEquiv_apply
    (j : Elliptic.Kind) (x : LocalSpace j) (γ : FundamentalGroup (LocalSpace j) x) :
    pieceSurfaceRetractionFundamentalGroupEquiv j x γ =
      FundamentalGroup.map (pieceSurfaceRetraction j) x γ := rfl

/-- On a represented loop, the isomorphism is literally pointwise retraction. -/
@[simp] theorem pieceSurfaceRetractionFundamentalGroupEquiv_fromPath
    (j : Elliptic.Kind) (x : LocalSpace j) (γ : Path x x) :
    pieceSurfaceRetractionFundamentalGroupEquiv j x (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.map (pieceSurfaceRetraction j).continuous⟧ := rfl

/-- The same actual retraction map gives an isomorphism at every point
of the full lifted elliptic patch in the global threefold. -/
def liftedPatchSurfaceRetractionFundamentalGroupEquiv (j : Elliptic.Kind)
    (x : Threefold.liftedPatch (some (some j))) :
    FundamentalGroup (Threefold.liftedPatch (some (some j))) x ≃*
      FundamentalGroup (SpecialCentralSurface j) (liftedPatchSurfaceRetraction j x) :=
  EllipticRetractionTopology.fundamentalGroupEquivAt
    (liftedPatchSurfaceHomotopyEquiv j).symm x

@[simp] theorem liftedPatchSurfaceRetractionFundamentalGroupEquiv_toMonoidHom
    (j : Elliptic.Kind) (x : Threefold.liftedPatch (some (some j))) :
    (liftedPatchSurfaceRetractionFundamentalGroupEquiv j x).toMonoidHom =
      FundamentalGroup.map (liftedPatchSurfaceRetraction j) x := rfl

theorem liftedPatchSurfaceRetraction_fundamentalGroup_map_bijective
    (j : Elliptic.Kind) (x : Threefold.liftedPatch (some (some j))) :
    Function.Bijective (FundamentalGroup.map (liftedPatchSurfaceRetraction j) x) :=
  (liftedPatchSurfaceRetractionFundamentalGroupEquiv j x).bijective

@[simp] theorem liftedPatchSurfaceRetractionFundamentalGroupEquiv_apply
    (j : Elliptic.Kind) (x : Threefold.liftedPatch (some (some j)))
    (γ : FundamentalGroup (Threefold.liftedPatch (some (some j))) x) :
    liftedPatchSurfaceRetractionFundamentalGroupEquiv j x γ =
      FundamentalGroup.map (liftedPatchSurfaceRetraction j) x γ := rfl

@[simp] theorem liftedPatchSurfaceRetractionFundamentalGroupEquiv_fromPath
    (j : Elliptic.Kind) (x : Threefold.liftedPatch (some (some j))) (γ : Path x x) :
    liftedPatchSurfaceRetractionFundamentalGroupEquiv j x (FundamentalGroup.fromPath ⟦γ⟧) =
      FundamentalGroup.fromPath ⟦γ.map (liftedPatchSurfaceRetraction j).continuous⟧ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
