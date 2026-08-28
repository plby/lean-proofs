import Wikipedia.HopfProblem.EllipticEquivariantFillings
import Wikipedia.HopfProblem.EllipticFillingTopology
import Wikipedia.HopfProblem.EllipticNonzeroFibres

/-!
# The central-fibre retraction for arbitrary equivariant periods

The underlying real family, affine deck action, and orbit-quotient topology
do not depend on the supplied period map.  We identify these topological
spaces explicitly and transfer the actual radial deformation to the literal
central fibre of the supplied family's projection.

These are topological identifications only: no equality of complex atlases
or holomorphicity of the identifications is asserted.
-/

noncomputable section

open Set Topology
open scoped Matrix ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

/-- The underlying real torus family has the original product topology. -/
def totalSpaceHomeomorph : D.TotalSpace ≃ₜ Family j := Homeomorph.refl _

@[simp] theorem totalSpaceHomeomorph_apply (x : D.TotalSpace) :
    D.totalSpaceHomeomorph x = x := rfl

/-- The deck action itself, not merely its orbit relation, is unchanged. -/
@[simp] theorem action_eq_familyAction (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    D.action v hv = familyAction j v hv := rfl

theorem totalSpaceHomeomorph_smul (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    D.totalSpaceHomeomorph (@SMul.smul _ _ (D.action v hv).toSMul g x) =
      @SMul.smul _ _ (familyAction j v hv).toSMul g (D.totalSpaceHomeomorph x) := rfl

/-- The actual generic quotient carries exactly the original orbit topology. -/
def fillingHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    D.Space v hv ≃ₜ Filling j v hv := Homeomorph.refl _

@[simp] theorem fillingHomeomorph_quotient (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.TotalSpace) :
    D.fillingHomeomorph v hv (D.quotient v hv x) =
      fillingQuotient j v hv (D.totalSpaceHomeomorph x) := rfl

@[simp] theorem fillingHomeomorph_projection (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.Space v hv) :
    fillingProjection j v hv (D.fillingHomeomorph v hv x) = D.projection v hv x := rfl

@[simp] theorem fillingHomeomorph_symm_projection (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Filling j v hv) :
    D.projection v hv ((D.fillingHomeomorph v hv).symm x) =
      fillingProjection j v hv x := rfl

/-- Every fibre of the supplied family's projection is connected in its
actual subspace topology, including the central fibre. -/
theorem projection_fibre_isConnected (v : Lattice) (hv : AdmissibleTwist j v) (b : Disc) :
    IsConnected (D.projection v hv ⁻¹' {b}) :=
  Elliptic.fillingProjection_fibre_connected j v hv b

/-- The same identification restricts to the literal central-fibre subtypes. -/
def fillingCentralSubtypeHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    (D.projection v hv ⁻¹' {Elliptic.discZero}) ≃ₜ
      (fillingProjection j v hv ⁻¹' {Elliptic.discZero}) := Homeomorph.refl _

@[simp] theorem fillingCentralSubtypeHomeomorph_coe (v : Lattice)
    (hv : AdmissibleTwist j v) (x : D.projection v hv ⁻¹' {Elliptic.discZero}) :
    (D.fillingCentralSubtypeHomeomorph v hv x : Filling j v hv) =
      D.fillingHomeomorph v hv x := rfl

/-- The radial contraction descended through the actual generic quotient. -/
def fillingRadial (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) : D.Space v hv → D.Space v hv :=
  Elliptic.fillingRadial j v hv t

@[simp] theorem fillingRadial_quotient (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) (x : D.TotalSpace) :
    D.fillingRadial v hv t (D.quotient v hv x) =
      D.quotient v hv (discRadial t x.1, x.2) := rfl

theorem fillingRadial_continuous (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (fun p : unitInterval × D.Space v hv => D.fillingRadial v hv p.1 p.2) :=
  Elliptic.fillingRadial_continuous j v hv

@[simp] theorem fillingRadial_zero (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.Space v hv) : D.fillingRadial v hv 0 x = x :=
  Elliptic.fillingRadial_zero j v hv x

theorem fillingRadial_one_mem_central (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.Space v hv) :
    D.fillingRadial v hv 1 x ∈ D.projection v hv ⁻¹' {Elliptic.discZero} :=
  Elliptic.fillingRadial_one_mem_central j v hv x

theorem fillingRadial_fixed (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) (x : D.Space v hv) (hx : D.projection v hv x = Elliptic.discZero) :
    D.fillingRadial v hv t x = x :=
  Elliptic.fillingRadial_fixed j v hv t x hx

/-- The literal inclusion of the actual central fibre into the generic filling. -/
def fillingCentralSubtypeInclusion (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (D.projection v hv ⁻¹' {Elliptic.discZero}) (D.Space v hv) :=
  Elliptic.fillingCentralSubtypeInclusion j v hv

@[simp] theorem fillingCentralSubtypeInclusion_apply (v : Lattice)
    (hv : AdmissibleTwist j v) (x : D.projection v hv ⁻¹' {Elliptic.discZero}) :
    D.fillingCentralSubtypeInclusion v hv x = x := rfl

/-- Time one of the radial deformation lands in the actual central fibre. -/
def fillingCentralRetraction (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (D.Space v hv) (D.projection v hv ⁻¹' {Elliptic.discZero}) :=
  Elliptic.fillingCentralRetraction j v hv

@[simp] theorem fillingCentralRetraction_coe (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.Space v hv) :
    (D.fillingCentralRetraction v hv x : D.Space v hv) = D.fillingRadial v hv 1 x := rfl

@[simp] theorem fillingCentralRetraction_comp_inclusion (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (D.fillingCentralRetraction v hv).comp (D.fillingCentralSubtypeInclusion v hv) =
      ContinuousMap.id _ :=
  Elliptic.fillingCentralRetraction_comp_inclusion j v hv

/-- The actual strong deformation fixes the literal central fibre at all times. -/
def fillingStrongDeformationRetraction (v : Lattice) (hv : AdmissibleTwist j v) :
    (ContinuousMap.id (D.Space v hv)).HomotopyRel
      ((D.fillingCentralSubtypeInclusion v hv).comp (D.fillingCentralRetraction v hv))
      (range (D.fillingCentralSubtypeInclusion v hv)) :=
  Elliptic.fillingStrongDeformationRetraction j v hv

@[simp] theorem fillingStrongDeformationRetraction_apply (v : Lattice)
    (hv : AdmissibleTwist j v) (p : unitInterval × D.Space v hv) :
    D.fillingStrongDeformationRetraction v hv p = D.fillingRadial v hv p.1 p.2 := rfl

/-- The actual central-fibre inclusion is a homotopy equivalence. -/
def fillingCentralHomotopyEquiv (v : Lattice) (hv : AdmissibleTwist j v) :
    (D.projection v hv ⁻¹' {Elliptic.discZero}) ≃ₕ D.Space v hv :=
  Elliptic.fillingCentralHomotopyEquiv j v hv

/-- The literal inclusion induces an isomorphism of pointed fundamental groups. -/
def fillingCentralFundamentalGroupEquiv (v : Lattice) (hv : AdmissibleTwist j v)
    (a : D.projection v hv ⁻¹' {Elliptic.discZero}) :
    FundamentalGroup (D.projection v hv ⁻¹' {Elliptic.discZero}) a ≃*
      FundamentalGroup (D.Space v hv) (a : D.Space v hv) :=
  Elliptic.fillingCentralFundamentalGroupEquiv j v hv a

@[simp] theorem fillingCentralFundamentalGroupEquiv_toMonoidHom (v : Lattice)
    (hv : AdmissibleTwist j v) (a : D.projection v hv ⁻¹' {Elliptic.discZero}) :
    (D.fillingCentralFundamentalGroupEquiv v hv a).toMonoidHom =
      FundamentalGroup.map (D.fillingCentralSubtypeInclusion v hv) a := rfl

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
