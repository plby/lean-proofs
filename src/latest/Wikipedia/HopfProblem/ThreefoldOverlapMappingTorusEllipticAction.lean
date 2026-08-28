import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusPolar
import Wikipedia.HopfProblem.EllipticFillings
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusQuotient

/-!
# The actual affine elliptic action in positive polar coordinates

The family generator rotates the root clockwise.  Positive angular
coordinates therefore intertwine the inverse circle twist with that
generator.  The torus translation is retained throughout.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods CuspUniformization Wikipedia.HopfProblem.Elliptic
open Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient

private def homeomorphToPerm : (RealTorus₄ ≃ₜ RealTorus₄) →* Equiv.Perm RealTorus₄ where
  toFun := Homeomorph.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The finite-order assertion for the actual affine torus homeomorphism. -/
theorem affine_pow_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    flatTorusAffine j v ^ j.order = 1 := by
  apply Homeomorph.ext
  intro x
  exact congrArg (fun e : Equiv.Perm RealTorus₄ => e x)
    ((homeomorphToPerm.map_pow (flatTorusAffine j v) j.order).trans
      (flatTorusPermutation_pow_order j v hv))

theorem affine_symm_pow_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (flatTorusAffine j v).symm ^ j.order = 1 := by
  change (flatTorusAffine j v)⁻¹ ^ j.order = 1
  rw [inv_pow, affine_pow_order j v hv, inv_one]

/-- The clockwise actual rotation subtracts `1 / order` from positive angle. -/
theorem root_sub_order (j : Kind) (r : ℝ) (a : Radius j.order r) (t : Circle) :
    root j.order r a (t - (((1 : ℝ) / j.order : ℝ) : Circle)) =
      familyRotation j (root j.order r a t) := by
  apply Subtype.ext
  rw [LogGauge.familyRotation_val_exponential]
  change (a : ℝ) • (phase (t - (((1 : ℝ) / j.order : ℝ) : Circle)) : ℂ) =
    exponential (-(1 / (j.order : ℂ))) * ((a : ℝ) • (phase t : ℂ))
  rw [sub_eq_add_neg, ← AddCircle.coe_neg, phase_add, _root_.Circle.coe_mul, phase_real]
  have he : (((-(1 / (j.order : ℝ))) : ℝ) : ℂ) = -(1 / (j.order : ℂ)) := by
    push_cast
    rfl
  rw [he, Complex.real_smul, Complex.real_smul]
  ring

/-- Moving forward through the root sector applies the inverse rotation. -/
theorem root_add_order (j : Kind) (r : ℝ) (a : Radius j.order r) (t : Circle) :
    root j.order r a (t + (((1 : ℝ) / j.order : ℝ) : Circle)) =
      (familyRotation j).symm (root j.order r a t) := by
  apply (familyRotation j).injective
  exact ((root_sub_order j r a (t + (((1 : ℝ) / j.order : ℝ) : Circle))).symm.trans
    (congrArg (root j.order r a) (add_sub_cancel_right _ _))).trans
      ((familyRotation j).apply_symm_apply _).symm

/-- Actual flat family points above a fixed positive root radius. -/
def polarFamilyAt (j : Kind) (r : ℝ) (a : Radius j.order r)
    (p : Circle × RealTorus₄) : Family j :=
  (root j.order r a p.1, p.2)

theorem polarFamilyAt_injective (j : Kind) (r : ℝ) (a : Radius j.order r) :
    Function.Injective (polarFamilyAt j r a) := by
  intro p q hpq
  apply Prod.ext
  · have hz : polarRoot j.order r (a, p.1) = polarRoot j.order r (a, q.1) :=
      Subtype.ext (congrArg Prod.fst hpq)
    have he := congrArg (rootAngle j.order r) hz
    simpa only [rootAngle_polarRoot] using he
  · exact congrArg (fun y : Family j => y.2) hpq

/-- The positive circle twist retains the genuine inverse affine action. -/
theorem polarFamilyAt_twist (j : Kind) (v : Lattice) (r : ℝ)
    (a : Radius j.order r) (p : Circle × RealTorus₄) :
    polarFamilyAt j r a (twist j.order (flatTorusAffine j v).symm p) =
      (familyPermutation j v).symm (polarFamilyAt j r a p) := by
  change (root j.order r a (p.1 + (((1 : ℝ) / j.order : ℝ) : Circle)),
      (flatTorusAffine j v).symm p.2) =
    ((familyRotation j).symm (root j.order r a p.1), (flatTorusAffine j v).symm p.2)
  exact Prod.ext (root_add_order j r a p.1) rfl

/-- Every residue-class action has the same inverse-orientation formula. -/
theorem polarFamilyAt_smul (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (r : ℝ) (a : Radius j.order r) (g : CyclicGroup j) (p : Circle × RealTorus₄) :
    letI := productAction j.order (flatTorusAffine j v).symm
      (affine_symm_pow_order j v hv)
    letI := familyAction j v hv
    polarFamilyAt j r a (g • p) = g⁻¹ • polarFamilyAt j r a p := by
  let := productAction j.order (flatTorusAffine j v).symm
    (affine_symm_pow_order j v hv)
  let := familyAction j v hv
  have he : g⁻¹ = Multiplicative.ofAdd (-(g.toAdd.val : ℤ) : ZMod j.order) := by
    apply Multiplicative.ext
    simp
  have hright : g⁻¹ • polarFamilyAt j r a p =
      ((familyPermutation j v).symm : Family j → Family j)^[g.toAdd.val]
        (polarFamilyAt j r a p) := by
    rw [he]
    have hc := cyclicAction_ofAdd_intCast_smul j.order (familyPermutation j v)
      (familyPermutation_pow_order j v hv) (-(g.toAdd.val : ℤ)) (polarFamilyAt j r a p)
    simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] at hc
    rw [← inv_pow, Equiv.Perm.coe_pow] at hc
    simpa only [Int.cast_natCast, Equiv.Perm.inv_def] using hc
  rw [hright]
  change polarFamilyAt j r a
      ((twist j.order (flatTorusAffine j v).symm : _ → _)^[g.toAdd.val] p) = _
  exact Function.Semiconj.iterate_right (polarFamilyAt_twist j v r a) g.toAdd.val p

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
