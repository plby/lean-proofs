import Wikipedia.HopfProblem.EllipticFillingTopology
import Wikipedia.HopfProblem.EllipticCentralFibre

/-!
# Retraction of an elliptic filling onto its actual central surface

The central-fibre homeomorphism identifies the target of the radial
retraction with the compact quotient surface constructed in §5. The
resulting inclusion and retraction are actual continuous maps, and the
homotopy fixes the central surface pointwise, as required in Lemma 7.3(i).
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic

/-- The existing central surface embedding, packaged as a continuous map. -/
def surfaceIntoFilling (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (Surface j (centralPeriod j) v hv) (Filling j v hv) :=
  ⟨centralFibreInclusion j v hv, centralFibreInclusion_continuous j v hv⟩

/-- Retract radially, then identify the actual central fibre with its
already constructed compact complex surface. -/
def fillingSurfaceRetraction (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (Filling j v hv) (Surface j (centralPeriod j) v hv) :=
  ContinuousMap.comp
    ⟨(centralFibreHomeomorph j v hv).symm, (centralFibreHomeomorph j v hv).symm.continuous⟩
    (fillingCentralRetraction j v hv)

@[simp] theorem fillingSurfaceRetraction_comp_inclusion (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (fillingSurfaceRetraction j v hv).comp (surfaceIntoFilling j v hv) =
      ContinuousMap.id _ := by
  ext x
  have he : fillingCentralRetraction j v hv (centralFibreInclusion j v hv x) =
      centralFibreHomeomorph j v hv x := by
    apply Subtype.ext
    exact fillingRadial_fixed j v hv 1 _ (fillingProjection_centralFibreInclusion j v hv x)
  change (centralFibreHomeomorph j v hv).symm
    (fillingCentralRetraction j v hv (centralFibreInclusion j v hv x)) = x
  rw [he, Homeomorph.symm_apply_apply]

theorem surfaceIntoFilling_comp_retraction (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (surfaceIntoFilling j v hv).comp (fillingSurfaceRetraction j v hv) =
      (fillingCentralSubtypeInclusion j v hv).comp (fillingCentralRetraction j v hv) := by
  ext x
  exact congrArg Subtype.val
    ((centralFibreHomeomorph j v hv).apply_symm_apply (fillingCentralRetraction j v hv x))

/-- The actual radial strong deformation onto the central quotient surface. -/
def fillingSurfaceStrongDeformationRetraction (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (ContinuousMap.id (Filling j v hv)).HomotopyRel
      ((surfaceIntoFilling j v hv).comp (fillingSurfaceRetraction j v hv))
      (range (surfaceIntoFilling j v hv)) where
  toFun p := fillingRadial j v hv p.1 p.2
  continuous_toFun := fillingRadial_continuous j v hv
  map_zero_left := fillingRadial_zero j v hv
  map_one_left x := congrArg (fun f : ContinuousMap (Filling j v hv) (Filling j v hv) => f x)
    (surfaceIntoFilling_comp_retraction j v hv).symm
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact fillingRadial_fixed j v hv t _ (fillingProjection_centralFibreInclusion j v hv y)

/-- The genuine central surface embedding is a homotopy equivalence. -/
def fillingSurfaceHomotopyEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Surface j (centralPeriod j) v hv ≃ₕ Filling j v hv :=
  retractionHomotopyEquiv (surfaceIntoFilling j v hv) (fillingSurfaceRetraction j v hv)
    (fillingSurfaceRetraction_comp_inclusion j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv)

/-- The central surface inclusion induces the pointed fundamental-group
isomorphism, with inverse induced by the displayed retraction. -/
def fillingSurfaceFundamentalGroupEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : Surface j (centralPeriod j) v hv) :
    FundamentalGroup (Surface j (centralPeriod j) v hv) a ≃*
      FundamentalGroup (Filling j v hv) (centralFibreInclusion j v hv a) :=
  retractionFundamentalGroupEquiv (surfaceIntoFilling j v hv) (fillingSurfaceRetraction j v hv)
    (fillingSurfaceRetraction_comp_inclusion j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv) a

@[simp] theorem fillingSurfaceFundamentalGroupEquiv_toMonoidHom (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : Surface j (centralPeriod j) v hv) :
    (fillingSurfaceFundamentalGroupEquiv j v hv a).toMonoidHom =
      FundamentalGroup.map (surfaceIntoFilling j v hv) a := rfl

/-- Both twists selected in the source give these actual homotopy
equivalences with no remaining admissibility hypothesis. -/
def mainFillingSurfaceHomotopyEquiv (j : Kind) :
    MainSurface j (centralPeriod j) ≃ₕ MainFilling j :=
  fillingSurfaceHomotopyEquiv j j.twist (mainTwist_admissible j)

def mainFillingSurfaceFundamentalGroupEquiv (j : Kind)
    (a : MainSurface j (centralPeriod j)) :
    FundamentalGroup (MainSurface j (centralPeriod j)) a ≃*
      FundamentalGroup (MainFilling j)
        (centralFibreInclusion j j.twist (mainTwist_admissible j) a) :=
  fillingSurfaceFundamentalGroupEquiv j j.twist (mainTwist_admissible j) a

end Wikipedia.HopfProblem.Elliptic
