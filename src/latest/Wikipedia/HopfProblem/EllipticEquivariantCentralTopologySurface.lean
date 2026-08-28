import Wikipedia.HopfProblem.EllipticEquivariantCentralTopology
import Wikipedia.HopfProblem.EllipticEquivariantCentralFibre
import Wikipedia.HopfProblem.EllipticFillingTopologySurface

/-!
# The actual central surface as a deformation retract for arbitrary periods

The genuine central surface of the supplied period family is identified
with its literal central fibre.  The radial deformation therefore retracts
the actual generic filling onto that surface, through its specified
embedding.  A separate topological homeomorphism with the concrete central
surface commutes with both actual embeddings; it makes no comparison of
their complex structures.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

variable {j : Kind} (D : Equivariant.Data j)

/-- The generic and concrete central surfaces have the same underlying
topology through their actual central-fibre identifications. -/
def centralSurfaceConcreteHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    Surface j D.centralPeriod v hv ≃ₜ Surface j (Elliptic.centralPeriod j) v hv :=
  (D.centralFibreHomeomorph v hv).trans
    ((D.fillingCentralSubtypeHomeomorph v hv).trans
      (Elliptic.centralFibreHomeomorph j v hv).symm)

@[simp] theorem centralSurfaceConcreteHomeomorph_inclusion (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) :
    Elliptic.centralFibreInclusion j v hv (D.centralSurfaceConcreteHomeomorph v hv x) =
      D.fillingHomeomorph v hv (D.centralFibreInclusion v hv x) :=
  congrArg Subtype.val ((Elliptic.centralFibreHomeomorph j v hv).apply_symm_apply
    (D.fillingCentralSubtypeHomeomorph v hv (D.centralFibreHomeomorph v hv x)))

/-- The actual central-surface embedding, packaged as a continuous map. -/
def surfaceIntoFilling (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (Surface j D.centralPeriod v hv) (D.Space v hv) :=
  ⟨D.centralFibreInclusion v hv, D.centralFibreInclusion_continuous v hv⟩

/-- Radial retraction followed by the inverse of the genuine central-fibre
homeomorphism. -/
def fillingSurfaceRetraction (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (D.Space v hv) (Surface j D.centralPeriod v hv) :=
  ContinuousMap.comp
    ⟨(D.centralFibreHomeomorph v hv).symm, (D.centralFibreHomeomorph v hv).symm.continuous⟩
    (D.fillingCentralRetraction v hv)

@[simp] theorem fillingSurfaceRetraction_comp_inclusion (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (D.fillingSurfaceRetraction v hv).comp (D.surfaceIntoFilling v hv) =
      ContinuousMap.id _ := by
  ext x
  have he : D.fillingCentralRetraction v hv (D.centralFibreInclusion v hv x) =
      D.centralFibreHomeomorph v hv x := by
    apply Subtype.ext
    exact D.fillingRadial_fixed v hv 1 _ (D.projection_centralFibreInclusion v hv x)
  change (D.centralFibreHomeomorph v hv).symm
    (D.fillingCentralRetraction v hv (D.centralFibreInclusion v hv x)) = x
  rw [he, Homeomorph.symm_apply_apply]

theorem surfaceIntoFilling_comp_retraction (v : Lattice) (hv : AdmissibleTwist j v) :
    (D.surfaceIntoFilling v hv).comp (D.fillingSurfaceRetraction v hv) =
      (D.fillingCentralSubtypeInclusion v hv).comp (D.fillingCentralRetraction v hv) := by
  ext x
  exact congrArg Subtype.val
    ((D.centralFibreHomeomorph v hv).apply_symm_apply (D.fillingCentralRetraction v hv x))

/-- The radial homotopy is a strong deformation retraction through the
actual central-surface inclusion. -/
def fillingSurfaceStrongDeformationRetraction (v : Lattice) (hv : AdmissibleTwist j v) :
    (ContinuousMap.id (D.Space v hv)).HomotopyRel
      ((D.surfaceIntoFilling v hv).comp (D.fillingSurfaceRetraction v hv))
      (range (D.surfaceIntoFilling v hv)) where
  toFun p := D.fillingRadial v hv p.1 p.2
  continuous_toFun := D.fillingRadial_continuous v hv
  map_zero_left := D.fillingRadial_zero v hv
  map_one_left x := congrArg (fun f : ContinuousMap (D.Space v hv) (D.Space v hv) => f x)
    (D.surfaceIntoFilling_comp_retraction v hv).symm
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact D.fillingRadial_fixed v hv t _ (D.projection_centralFibreInclusion v hv y)

/-- The actual surface inclusion is a homotopy equivalence. -/
def fillingSurfaceHomotopyEquiv (v : Lattice) (hv : AdmissibleTwist j v) :
    Surface j D.centralPeriod v hv ≃ₕ D.Space v hv :=
  retractionHomotopyEquiv (D.surfaceIntoFilling v hv) (D.fillingSurfaceRetraction v hv)
    (D.fillingSurfaceRetraction_comp_inclusion v hv)
    (D.fillingSurfaceStrongDeformationRetraction v hv)

@[simp] theorem fillingSurfaceHomotopyEquiv_apply (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Surface j D.centralPeriod v hv) :
    D.fillingSurfaceHomotopyEquiv v hv x = D.centralFibreInclusion v hv x := rfl

/-- The isomorphism of pointed fundamental groups induced by the actual
surface inclusion; its inverse comes from the displayed retraction. -/
def fillingSurfaceFundamentalGroupEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (a : Surface j D.centralPeriod v hv) :
    FundamentalGroup (Surface j D.centralPeriod v hv) a ≃*
      FundamentalGroup (D.Space v hv) (D.centralFibreInclusion v hv a) :=
  retractionFundamentalGroupEquiv (D.surfaceIntoFilling v hv) (D.fillingSurfaceRetraction v hv)
    (D.fillingSurfaceRetraction_comp_inclusion v hv)
    (D.fillingSurfaceStrongDeformationRetraction v hv) a

@[simp] theorem fillingSurfaceFundamentalGroupEquiv_toMonoidHom (v : Lattice)
    (hv : AdmissibleTwist j v) (a : Surface j D.centralPeriod v hv) :
    (D.fillingSurfaceFundamentalGroupEquiv v hv a).toMonoidHom =
      FundamentalGroup.map (D.surfaceIntoFilling v hv) a := rfl

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
