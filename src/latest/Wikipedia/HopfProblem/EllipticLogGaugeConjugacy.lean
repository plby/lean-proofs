import Wikipedia.HopfProblem.EllipticLogGaugeBasic
import Wikipedia.HopfProblem.EllipticLogGaugeRotation
import Wikipedia.HopfProblem.EllipticEquivariantFamilies

/-!
# Logarithmic gauge conjugacy on the actual punctured elliptic family

For any covariant holomorphic period family and invariant integral twist,
the logarithmic translation conjugates the affine cyclic action to the
untwisted action.  The calculation takes place in the actual period
quotient; the integer ambiguity of the logarithm is an integral period.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.LogGauge

open SpecialPeriods CuspUniformization

variable {j : Kind} (D : Equivariant.Data j)

/-- The affine permutation restricted to the complement of the central fibre. -/
def starPermutation (v : Lattice) : Equiv.Perm (FamilyStar D.periods) :=
  (D.permutation v).subtypeEquiv (fun x => by
    change (x.1 : ℂ) ≠ 0 ↔ (familyRotation j x.1 : ℂ) ≠ 0
    rw [familyRotation_val_exponential, mul_ne_zero_iff]
    exact ⟨fun hx => ⟨exponential_ne_zero _, hx⟩, fun hx => hx.2⟩)

@[simp] theorem starPermutation_coe (v : Lattice) (x : FamilyStar D.periods) :
    (starPermutation D v x : D.TotalSpace) = D.permutation v x := rfl

@[simp] theorem starPermutation_base (v : Lattice) (x : FamilyStar D.periods) :
    (starPermutation D v x).1.1 = familyRotation j x.1.1 := rfl

/-- The corresponding explicit complex lift, on the punctured cover. -/
def starLift (v : Lattice) (x : CoverStar) : CoverStar :=
  ⟨D.complexLift v x, familyRotation_ne_zero j x.1.1 x.2⟩

@[simp] theorem starLift_coe (v : Lattice) (x : CoverStar) :
    (starLift D v x : Disc × ComplexPlane₂) = D.complexLift v x := rfl

@[simp] theorem starPermutation_project (v : Lattice) (x : CoverStar) :
    starPermutation D v (project D.periods x) = project D.periods (starLift D v x) := by
  apply Subtype.ext
  exact (D.complexLift_quotientMap v x).symm

/-- Invariance of the integral twist identifies its complex period vectors
under the actual linear monodromy. -/
theorem periodVector_covariance (v : Lattice) (hv : j.matrix *ᵥ v = v) (z : Disc) :
    linearMatrix j (D.periods.point z) *ᵥ periodVector D.periods v z =
      periodVector D.periods v (familyRotation j z) := by
  have h := D.periodEquiv_flatLinear z (realCast v)
  rw [flatLinear_fixes_realCast j v hv] at h
  exact h.symm

theorem complexLift_translation (v : Lattice) (z : Disc) :
    D.periods.periodEquiv z ((1 / (j.order : ℝ)) • realCast v) =
      (1 / (j.order : ℂ)) • periodVector D.periods v z := by
  rw [map_smul]
  ext i
  simp only [periodVector, Pi.smul_apply, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast, smul_eq_mul]

theorem complexLift_formula (v : Lattice) (z : Disc) (u : ComplexPlane₂) :
    D.complexLift v (z, u) =
      (familyRotation j z, linearMatrix j (D.periods.point z) *ᵥ u +
        (1 / (j.order : ℂ)) • periodVector D.periods v (familyRotation j z)) := by
  unfold Equivariant.Data.complexLift
  rw [complexLift_translation]

theorem periodVector_zero (z : Disc) : periodVector D.periods 0 z = 0 := by
  change D.periods.periodEquiv z (realCast 0) = 0
  rw [show realCast 0 = 0 by ext i; simp [realCast], map_zero]

/-- On the complex cover, the two composites differ by an integer period. -/
theorem gaugeLift_starLift_project (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : CoverStar) :
    project D.periods (gaugeLift D.periods v logarithm (starLift D v x)) =
      project D.periods (starLift D 0 (gaugeLift D.periods v logarithm x)) := by
  apply Subtype.ext
  change D.periods.quotientMap
      (familyRotation j x.1.1,
        (D.complexLift v x.1).2 +
          logarithm (familyRotation j x.1.1 : ℂ) •
            periodVector D.periods v (familyRotation j x.1.1)) =
    D.periods.quotientMap
      (D.complexLift 0 (x.1.1,
        x.1.2 + logarithm (x.1.1 : ℂ) • periodVector D.periods v x.1.1))
  rw [show x.1 = (x.1.1, x.1.2) by rfl, complexLift_formula, complexLift_formula]
  simp only [periodVector_zero, smul_zero, add_zero, Matrix.mulVec_add, Matrix.mulVec_smul,
    periodVector_covariance D v hv]
  rw [add_assoc, ← add_smul]
  apply quotientMap_eq_of_scalar_int D.periods v (familyRotation j x.1.1)
    (linearMatrix j (D.periods.point x.1.1) *ᵥ x.1.2)
  obtain ⟨n, hn⟩ := logarithm_familyRotation j x.1.1 x.2
  exact ⟨n, by rw [hn]; ring⟩

/-- The logarithmic translation intertwines the actual affine generator
with the actual untwisted generator. -/
theorem gaugeMap_intertwines (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (x : FamilyStar D.periods) :
    gaugeMap D.periods v (starPermutation D v x) =
      starPermutation D 0 (gaugeMap D.periods v x) := by
  obtain ⟨y, rfl⟩ := project_surjective D.periods x
  rw [starPermutation_project, gaugeMap_project, gaugeMap_project, starPermutation_project]
  exact gaugeLift_starLift_project D v hv y

/-- Conjugacy as an equality of permutations of the actual punctured family. -/
theorem gaugeEquiv_conjugates (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    gaugeEquiv D.periods v * starPermutation D v * (gaugeEquiv D.periods v)⁻¹ =
      starPermutation D 0 := by
  apply Equiv.ext
  intro x
  change gaugeMap D.periods v (starPermutation D v ((gaugeEquiv D.periods v).symm x)) = _
  rw [gaugeMap_intertwines D v hv]
  change starPermutation D 0 (gaugeEquiv D.periods v ((gaugeEquiv D.periods v).symm x)) = _
  rw [Equiv.apply_symm_apply]

theorem starPermutation_iterate_coe (v : Lattice) (r : ℕ) (x : FamilyStar D.periods) :
    ((starPermutation D v)^[r] x : D.TotalSpace) = (D.permutation v)^[r] x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', starPermutation_coe, ih]

theorem starPermutation_pow_order (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    starPermutation D v ^ j.order = 1 := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change ((starPermutation D v ^ j.order) x : D.TotalSpace) = x
  rw [Equiv.Perm.coe_pow, starPermutation_iterate_coe, ← Equiv.Perm.coe_pow,
    D.permutation_pow_order v hv]
  rfl

/-- The finite cyclic action restricted to the punctured family. -/
@[instance_reducible] def starAction (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (CyclicGroup j) (FamilyStar D.periods) :=
  CyclicAction.action (starPermutation D v) (starPermutation_pow_order D v hv)

theorem starAction_coe (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : FamilyStar D.periods) :
    letI := D.action v hv
    letI := starAction D v hv
    ((g • x : FamilyStar D.periods) : D.TotalSpace) = g • (x : D.TotalSpace) := by
  let := D.action v hv
  let := starAction D v hv
  change ((starPermutation D v ^ g.toAdd.val) x : D.TotalSpace) =
    (D.permutation v ^ g.toAdd.val) (x : D.TotalSpace)
  rw [Equiv.Perm.coe_pow, starPermutation_iterate_coe, Equiv.Perm.coe_pow]

/-- The conjugacy is equivariant for every element, not just the generator. -/
theorem gaugeMap_starAction (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : FamilyStar D.periods) :
    gaugeMap D.periods v (@SMul.smul _ _ (starAction D v hv).toSMul g x) =
      @SMul.smul _ _ (starAction D 0 (by simp)).toSMul g (gaugeMap D.periods v x) := by
  have h : Function.Semiconj (gaugeMap D.periods v) (starPermutation D v)
      (starPermutation D 0) := gaugeMap_intertwines D v hv
  change gaugeMap D.periods v ((starPermutation D v ^ g.toAdd.val) x) =
    (starPermutation D 0 ^ g.toAdd.val) (gaugeMap D.periods v x)
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact h.iterate_right g.toAdd.val x

/-- Every invariant twist, including zero, acts freely off the central fibre:
the nontrivial base rotations have no nonzero fixed points. -/
theorem starAction_free (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    IsCancelSMul (CyclicGroup j) (FamilyStar D.periods) := by
  let := starAction D v hv
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hx
  let := D.action v hv
  have hc : g • (x : D.TotalSpace) = (x : D.TotalSpace) :=
    (starAction_coe D v hv g x).symm.trans (congrArg Subtype.val hx)
  have hb : (familyRotation j)^[g.toAdd.val] x.1.1 = x.1.1 := by
    simpa only [D.action_apply v hv g] using congrArg Prod.fst hc
  have hg : g.toAdd.val = 0 := by
    by_contra hg
    have hz := (familyRotation_iterate_fixed_iff j g.toAdd.val
      (Nat.pos_of_ne_zero hg) (ZMod.val_lt _) x.1.1).mp hb
    exact x.2 (congrArg Subtype.val hz)
  apply Multiplicative.ext
  exact (ZMod.val_eq_zero _).mp hg

/-- The restricted cyclic action is holomorphic in the inherited
varying-period charts, for every invariant twist. -/
theorem starAction_holomorphic (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) :
    letI := D.periods.totalChartedSpace
    letI := starAction D v hv
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fun x : FamilyStar D.periods => g • x) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  let := D.action v hv
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ FamilyModel)
      (modelWithCornersSelf ℂ FamilyModel) ω
      (fun y : FamilyStar D.periods => ((g • y : FamilyStar D.periods) : D.TotalSpace)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fun y : FamilyStar D.periods => g • y) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  have h : ContMDiff (modelWithCornersSelf ℂ FamilyModel)
      (modelWithCornersSelf ℂ FamilyModel) ω
      (fun y : FamilyStar D.periods => g • (y : D.TotalSpace)) :=
    (D.action_holomorphic v hv g).comp contMDiff_subtype_val
  simpa only [starAction_coe] using h x

theorem starAction_continuous (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := starAction D v hv
    ContinuousConstSMul (CyclicGroup j) (FamilyStar D.periods) := by
  let := D.periods.totalChartedSpace
  let := starAction D v hv
  exact ⟨fun g => (starAction_holomorphic D v hv g).continuous⟩

end Wikipedia.HopfProblem.Elliptic.LogGauge
