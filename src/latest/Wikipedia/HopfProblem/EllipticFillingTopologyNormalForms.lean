import Wikipedia.HopfProblem.EllipticFillingTopologyUniversalCover
import Wikipedia.HopfProblem.EllipticFillingTopologyCoverFibres
import Wikipedia.HopfProblem.EllipticFillingTopologySurface

/-!
# Affine normal forms for actual elliptic fundamental-group elements

Lifted endpoints in the actual universal affine cover give a bijection
between loop classes and a finite affine residue together with an integer
translation. We also exhibit the straight paths representing every such
class. These are set equivalences with geometric markings; no abstract
presentation or multiplication law on the normal-form set is asserted.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.Elliptic

variable (j : Kind) (p : FixedPeriod j) (v : Lattice) (hv : AdmissibleTwist j v)

@[simp] theorem affineCoverFibreEquiv_symm_coe (y : RealCoordinates)
    (a : Fin j.order × Lattice) :
    ((affineCoverFibreEquiv j p v hv y).symm a : RealCoordinates) =
      realCast a.2 + (flatAffine j v)^[a.1.val] y := rfl

/-- Each actual loop class is uniquely specified by its lifted endpoint's
affine residue and integer translation coordinates. -/
def surfaceFundamentalGroupNormalFormEquiv (y : RealCoordinates) :
    FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y) ≃
      Fin j.order × Lattice :=
  (fundamentalGroupCoverFibreEquiv (affineCoverProjection_isCoveringMap j p v hv) y).trans
    (affineCoverFibreEquiv j p v hv y)

/-- The normal form describes the endpoint of the actual lifted loop. -/
theorem surfaceFundamentalGroupNormalForm_endpoint (y : RealCoordinates)
    (γ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    realCast (surfaceFundamentalGroupNormalFormEquiv j p v hv y γ).2 +
        (flatAffine j v)^[(surfaceFundamentalGroupNormalFormEquiv j p v hv y γ).1.val] y =
      ((affineCoverProjection_isCoveringMap j p v hv).monodromy γ
        ⟨y, rfl⟩ : RealCoordinates) :=
  congrArg Subtype.val ((affineCoverFibreEquiv j p v hv y).symm_apply_apply _)

/-- A representative of a normal form is the projection of the straight
segment to the corresponding affine translate of the selected basepoint. -/
def affinePeriodLoop (y : RealCoordinates) (a : Fin j.order × Lattice) :
    Path (affineCoverProjection j p v hv y) (affineCoverProjection j p v hv y) :=
  ((Path.segment y (realCast a.2 + (flatAffine j v)^[a.1.val] y)).map
    (affineCoverProjection_continuous j p v hv)).cast rfl
      ((affineCoverProjection_eq_iff_translate j p v hv _ _).mpr
        ⟨a.1.val, a.1.isLt, a.2, rfl⟩).symm

theorem affinePeriodLoop_monodromy (y : RealCoordinates) (a : Fin j.order × Lattice) :
    (affineCoverProjection_isCoveringMap j p v hv).monodromy
      (FundamentalGroup.fromPath ⟦affinePeriodLoop j p v hv y a⟧) ⟨y, rfl⟩ =
        (affineCoverFibreEquiv j p v hv y).symm a := by
  apply (affineCoverProjection_isCoveringMap j p v hv).monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk
      (Path.segment y (realCast a.2 + (flatAffine j v)^[a.1.val] y)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

@[simp] theorem surfaceFundamentalGroupNormalForm_affinePeriodLoop (y : RealCoordinates)
    (a : Fin j.order × Lattice) :
    surfaceFundamentalGroupNormalFormEquiv j p v hv y
      (FundamentalGroup.fromPath ⟦affinePeriodLoop j p v hv y a⟧) = a := by
  change affineCoverFibreEquiv j p v hv y
    ((affineCoverProjection_isCoveringMap j p v hv).monodromy
      (FundamentalGroup.fromPath ⟦affinePeriodLoop j p v hv y a⟧) ⟨y, rfl⟩) = a
  exact (congrArg (affineCoverFibreEquiv j p v hv y)
    (affinePeriodLoop_monodromy j p v hv y a)).trans
      ((affineCoverFibreEquiv j p v hv y).apply_symm_apply a)

theorem surfaceFundamentalGroupNormalForm_symm_apply (y : RealCoordinates)
    (a : Fin j.order × Lattice) :
    (surfaceFundamentalGroupNormalFormEquiv j p v hv y).symm a =
      FundamentalGroup.fromPath ⟦affinePeriodLoop j p v hv y a⟧ := by
  apply (surfaceFundamentalGroupNormalFormEquiv j p v hv y).injective
  rw [Equiv.apply_symm_apply, surfaceFundamentalGroupNormalForm_affinePeriodLoop]

/-- The same geometric normal forms apply to the actual logarithmic
filling, using the proved central-surface retraction. -/
def fillingFundamentalGroupNormalFormEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Filling j v hv)
        (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y)) ≃
      Fin j.order × Lattice :=
  (fillingSurfaceFundamentalGroupEquiv j v hv
    (affineCoverProjection j (centralPeriod j) v hv y)).symm.toEquiv.trans
      (surfaceFundamentalGroupNormalFormEquiv j (centralPeriod j) v hv y)

end Wikipedia.HopfProblem.Elliptic
