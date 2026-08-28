import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusElliptic

/-!
# An actual base-circle section of the affine elliptic boundary

The torus coordinate of the section is the image of `-(t / m) v`.
Invariance of the actual integral twist vector proves that applying the
affine monodromy at time `t + 1` gives the torus coordinate at time `t`.
The resulting periodic continuous cylinder map descends to `AddCircle 1`.
Its composition with the boundary inclusion gives an explicit section
curve in the original punctured filling, including the affine translation.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods CuspUniformization Wikipedia.HopfProblem.Elliptic

/-- The actual translation in the rank-four real-period torus along the section. -/
def sectionFlatPath (j : Kind) (v : Lattice) : C(ℝ, RealTorus₄) where
  toFun t := standardLattice.mkQ (-(t / (j.order : ℝ)) • realCast v)
  continuous_toFun := standardLattice.continuous_mkQ.comp
    ((continuous_id.div_const (j.order : ℝ)).neg.smul continuous_const)

@[simp] theorem sectionFlatPath_apply (j : Kind) (v : Lattice) (t : ℝ) :
    sectionFlatPath j v t =
      standardLattice.mkQ (-(t / (j.order : ℝ)) • realCast v) := rfl

@[simp] theorem sectionFlatPath_zero (j : Kind) (v : Lattice) :
    sectionFlatPath j v 0 = 0 := by
  simp only [sectionFlatPath_apply, zero_div, neg_zero, zero_smul, map_zero]

/-- The true real affine map carries the next endpoint back to the current one. -/
theorem sectionFlatLift_endpoint (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (t : ℝ) :
    flatAffine j v (-((t + 1) / (j.order : ℝ)) • realCast v) =
      -(t / (j.order : ℝ)) • realCast v := by
  rw [flatAffine, map_smul, flatLinear_fixes_realCast j v hv, ← add_smul]
  congr 1
  ring

/-- The endpoint identity is for the actual affine torus homeomorphism. -/
theorem sectionFlatPath_endpoint (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (t : ℝ) :
    flatTorusAffine j v (sectionFlatPath j v (t + 1)) = sectionFlatPath j v t := by
  rw [sectionFlatPath_apply, flatTorusAffine_mkQ, sectionFlatLift_endpoint j v hv]
  rfl

/-- The positive-time cylinder representative of the boundary section. -/
def sectionCylinder (j : Kind) (v : Lattice) : C(ℝ, Boundary j v) where
  toFun t := MappingTorus.mk (flatTorusAffine j v) (t, sectionFlatPath j v t)
  continuous_toFun := (MappingTorus.mk_continuous _).comp
    (continuous_id.prodMk (sectionFlatPath j v).continuous)

@[simp] theorem sectionCylinder_apply (j : Kind) (v : Lattice) (t : ℝ) :
    sectionCylinder j v t =
      MappingTorus.mk (flatTorusAffine j v)
        (t, standardLattice.mkQ (-(t / (j.order : ℝ)) • realCast v)) := rfl

/-- Periodicity follows from the actual mapping-torus gluing and affine endpoint. -/
theorem sectionCylinder_periodic (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : Function.Periodic (sectionCylinder j v) 1 := by
  intro t
  change MappingTorus.mk (flatTorusAffine j v) (t + 1, sectionFlatPath j v (t + 1)) =
    MappingTorus.mk (flatTorusAffine j v) (t, sectionFlatPath j v t)
  rw [MappingTorus.mk_add_one, sectionFlatPath_endpoint j v hv]

/-- The descended actual section of the elliptic boundary's base circle. -/
def boundarySection (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    C(MappingTorus.Circle, Boundary j v) where
  toFun := (sectionCylinder_periodic j v hv).lift
  continuous_toFun := by
    apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
    exact (sectionCylinder j v).continuous

/-- The descended map retains its explicit real representative at every time. -/
@[simp] theorem boundarySection_coe (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (t : ℝ) :
    boundarySection j v hv (t : MappingTorus.Circle) =
      MappingTorus.mk (flatTorusAffine j v)
        (t, standardLattice.mkQ (-(t / (j.order : ℝ)) • realCast v)) := rfl

/-- The actual time projection composed with the section is exactly the identity. -/
@[simp] theorem boundarySection_base (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (t : MappingTorus.Circle) :
    MappingTorus.base (flatTorusAffine j v) (boundarySection j v hv t) = t := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  rfl

theorem base_comp_boundarySection (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    (MappingTorus.base (flatTorusAffine j v)).comp (boundarySection j v hv) =
      ContinuousMap.id MappingTorus.Circle := by
  ext t
  exact boundarySection_base j v hv t

/-- The section is based at the actual zero of the original torus fibre. -/
@[simp] theorem boundarySection_zero (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    boundarySection j v hv 0 =
      MappingTorus.HomologyCover.fibreInclusion (flatTorusAffine j v) 0 := by
  change MappingTorus.mk (flatTorusAffine j v) (0, sectionFlatPath j v 0) =
    MappingTorus.mk (flatTorusAffine j v) (0, 0)
  rw [sectionFlatPath_zero]

/-- The actual section curve in the original whole punctured elliptic filling. -/
def sectionToPunctured (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℝ) (a : Radius j.order r) : C(MappingTorus.Circle, PuncturedFilling j v hv r) :=
  (boundaryInclusion j v hv r a).comp (boundarySection j v hv.1)

/-- Its literal polar finite-quotient representative, including the affine translation. -/
theorem sectionToPunctured_coe (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℝ) (a : Radius j.order r) (t : ℝ) :
    sectionToPunctured j v hv r a (t : MappingTorus.Circle) =
      polarQuotient j v hv r
        (a, (((t / j.order : ℝ) : Circle),
          standardLattice.mkQ (-(t / (j.order : ℝ)) • realCast v))) :=
  boundaryInclusion_mk j v hv r a t _

@[simp] theorem sectionToPunctured_zero (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℝ) (a : Radius j.order r) :
    sectionToPunctured j v hv r a 0 = fibreToPunctured j v hv r a 0 :=
  congrArg (boundaryInclusion j v hv r a) (boundarySection_zero j v hv.1)

/-- The same original section curve, now viewed in the full elliptic filling. -/
def sectionToFilling (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℝ) (a : Radius j.order r) : C(MappingTorus.Circle, Filling j v hv) :=
  (boundaryToFilling j v hv r a).comp (boundarySection j v hv.1)

theorem sectionToFilling_coe (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℝ) (a : Radius j.order r) (t : ℝ) :
    sectionToFilling j v hv r a (t : MappingTorus.Circle) =
      fillingQuotient j v hv
        (root j.order r a ((t / j.order : ℝ) : Circle),
          standardLattice.mkQ (-(t / (j.order : ℝ)) • realCast v)) :=
  boundaryCylinder_apply j v hv r a t _

/-- The actual filling projection of the section curve goes once around the base. -/
theorem sectionToFilling_base (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℝ) (a : Radius j.order r) (t : ℝ) :
    (fillingProjection j v hv (sectionToFilling j v hv r a (t : MappingTorus.Circle)) : ℂ) =
      ((a : ℝ) : ℂ) ^ j.order * exponential (t : ℂ) :=
  boundaryCylinder_base j v hv r a t _

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
