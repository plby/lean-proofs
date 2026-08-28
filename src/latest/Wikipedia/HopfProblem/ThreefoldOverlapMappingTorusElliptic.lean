import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticTopology
import Wikipedia.HopfProblem.MappingTorusHomologyHomotopies

/-!
# Actual boundary homotopy equivalences for the punctured elliptic fillings

The deformation changes only the positive root radius.  On the boundary,
the map is the literal finite quotient of the positive-angle root and the
unchanged real-torus coordinate.  Its endpoint is the actual affine map.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods CuspUniformization Wikipedia.HopfProblem.Elliptic

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (r : ℝ)
  (a : Radius j.order r)

/-- The genuine punctured filling retracts onto its actual affine boundary torus. -/
def puncturedMappingTorusHomotopyEquiv : PuncturedFilling j v hv r ≃ₕ Boundary j v :=
  (puncturedProductHomeomorph j v hv r).toHomotopyEquiv.trans
    (radiusProductHomotopyEquiv a (Boundary j v))

/-- The inverse homotopy equivalence is a concrete boundary inclusion. -/
def boundaryInclusion : C(Boundary j v, PuncturedFilling j v hv r) :=
  ⟨(puncturedMappingTorusHomotopyEquiv j v hv r a).symm,
    (puncturedMappingTorusHomotopyEquiv j v hv r a).symm.continuous⟩

@[simp] theorem boundaryInclusion_mk (t : ℝ) (x : RealTorus₄) :
    boundaryInclusion j v hv r a (MappingTorus.mk (flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r (a, (((t / j.order : ℝ) : Circle), x)) :=
  puncturedProductHomeomorph_symm_mk j v hv r a t x

/-- The boundary map to the original full filling is the literal subtype inclusion. -/
def boundaryToFilling : C(Boundary j v, Filling j v hv) :=
  (⟨Subtype.val, continuous_subtype_val⟩ : C(PuncturedFilling j v hv r, Filling j v hv)).comp
    (boundaryInclusion j v hv r a)

/-- Representatives of the boundary in the actual family quotient. -/
def boundaryCylinder : C(ℝ × RealTorus₄, Filling j v hv) :=
  (boundaryToFilling j v hv r a).comp
    ⟨MappingTorus.mk (flatTorusAffine j v), MappingTorus.mk_continuous _⟩

@[simp] theorem boundaryCylinder_apply (t : ℝ) (x : RealTorus₄) :
    boundaryCylinder j v hv r a (t, x) = fillingQuotient j v hv
      (root j.order r a ((t / j.order : ℝ) : Circle), x) := by
  change (boundaryInclusion j v hv r a (MappingTorus.mk _ (t, x)) : Filling j v hv) = _
  rw [boundaryInclusion_mk]
  rfl

/-- The endpoint relation is checked for the actual affine monodromy. -/
theorem boundaryCylinder_endpoint (t : ℝ) (x : RealTorus₄) :
    boundaryCylinder j v hv r a (t + 1, x) =
      boundaryCylinder j v hv r a (t, flatTorusAffine j v x) :=
  congrArg (boundaryToFilling j v hv r a) (MappingTorus.mk_add_one _ t x)

/-- The original base projection on every boundary representative. -/
theorem boundaryCylinder_base (t : ℝ) (x : RealTorus₄) :
    (fillingProjection j v hv (boundaryCylinder j v hv r a (t, x)) : ℂ) =
      ((a : ℝ) : ℂ) ^ j.order * exponential (t : ℂ) := by
  rw [boundaryCylinder_apply, fillingProjection_fillingQuotient]
  change ((a : ℝ) • (phase (((t / j.order : ℝ) : Circle)) : ℂ)) ^ j.order = _
  rw [phase_real, Complex.real_smul, mul_pow]
  congr 1
  rw [exponential, ← Complex.exp_nat_mul]
  unfold exponential
  congr 1
  push_cast
  have hm : (j.order : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.order_pos.ne'
  field_simp

/-- The boundary fibre map is the genuine rank-four real-period torus inclusion. -/
def fibreToPunctured : C(RealTorus₄, PuncturedFilling j v hv r) :=
  (boundaryInclusion j v hv r a).comp
    (MappingTorus.HomologyCover.fibreInclusion (flatTorusAffine j v))

@[simp] theorem fibreToPunctured_val (x : RealTorus₄) :
    (fibreToPunctured j v hv r a x : Filling j v hv) =
      fillingQuotient j v hv (root j.order r a 0, x) := by
  change boundaryCylinder j v hv r a (0, x) = _
  rw [boundaryCylinder_apply]
  simp only [zero_div, AddCircle.coe_zero]

/-- The retraction followed by the boundary inclusion is homotopic to the
identity on the actual punctured filling. -/
theorem boundary_retraction_homotopic :
    ((boundaryInclusion j v hv r a).comp
      ⟨puncturedMappingTorusHomotopyEquiv j v hv r a,
        (puncturedMappingTorusHomotopyEquiv j v hv r a).continuous⟩).Homotopic
      (ContinuousMap.id _) :=
  (puncturedMappingTorusHomotopyEquiv j v hv r a).left_inv

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
