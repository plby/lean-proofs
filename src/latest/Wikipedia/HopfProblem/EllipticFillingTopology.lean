import Wikipedia.HopfProblem.EllipticFillings
import Wikipedia.HopfProblem.EllipticFillingTopologyFundamentalGroup
import Mathlib.Topology.Homotopy.Equiv

/-!
# The radial deformation of the actual elliptic fillings

The underlying local period family is the product of the open disc with a
fixed real torus. Its radial disc contraction commutes with the actual finite
affine action. We descend that contraction to the orbit quotient and exhibit
a strong deformation retraction onto the actual central fibre.
-/

noncomputable section

open Set Topology
open scoped Matrix ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

/-- Radial contraction of the actual open disc, with time zero the identity. -/
def discRadial (t : unitInterval) (z : Disc) : Disc :=
  ⟨(1 - (t : ℝ)) • (z : ℂ), by
    have ha : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
    have ha1 : 1 - (t : ℝ) ≤ 1 := by linarith [t.property.1]
    have hn : ‖(1 - (t : ℝ)) • (z : ℂ)‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      exact (mul_le_of_le_one_left (norm_nonneg _) ha1).trans_lt (disc_norm_lt_one z)
    simpa [unitDisc] using hn⟩

theorem discRadial_continuous :
    Continuous (fun p : unitInterval × Disc => discRadial p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

@[simp] theorem discRadial_zero (z : Disc) : discRadial 0 z = z := by
  apply Subtype.ext
  simp [discRadial]

@[simp] theorem discRadial_one (z : Disc) : discRadial 1 z = Elliptic.discZero := by
  apply Subtype.ext
  simp [discRadial, Elliptic.discZero]

@[simp] theorem discRadial_discZero (t : unitInterval) :
    discRadial t Elliptic.discZero = Elliptic.discZero := by
  apply Subtype.ext
  simp [discRadial, Elliptic.discZero]

theorem discRadial_familyRotation (j : Kind) (t : unitInterval) (z : Disc) :
    discRadial t (familyRotation j z) = familyRotation j (discRadial t z) := by
  cases j <;> apply Subtype.ext
  · change (1 - (t : ℝ)) • (-rho * (z : ℂ)) =
      -rho * ((1 - (t : ℝ)) • (z : ℂ))
    simp only [Complex.real_smul]
    ring
  · change (1 - (t : ℝ)) • (-Complex.I * (z : ℂ)) =
      -Complex.I * ((1 - (t : ℝ)) • (z : ℂ))
    simp only [Complex.real_smul]
    ring

theorem discRadial_familyRotation_iterate (j : Kind) (t : unitInterval)
    (n : ℕ) (z : Disc) :
    discRadial t ((familyRotation j)^[n] z) =
      (familyRotation j)^[n] (discRadial t z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      discRadial_familyRotation, ih]

/-- The contraction keeps the flat real-torus coordinate fixed. -/
def familyRadial (j : Kind) (t : unitInterval) (x : Family j) : Family j :=
  (discRadial t x.1, x.2)

theorem familyRadial_continuous (j : Kind) :
    Continuous (fun p : unitInterval × Family j => familyRadial j p.1 p.2) :=
  (discRadial_continuous.comp
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd)

@[simp] theorem familyRadial_zero (j : Kind) (x : Family j) :
    familyRadial j 0 x = x := by
  exact Prod.ext (discRadial_zero x.1) rfl

@[simp] theorem familyRadial_one (j : Kind) (x : Family j) :
    familyRadial j 1 x = (Elliptic.discZero, x.2) := by
  exact Prod.ext (discRadial_one x.1) rfl

theorem familyRadial_fixed (j : Kind) (t : unitInterval) (x : Family j)
    (hx : x.1 = Elliptic.discZero) : familyRadial j t x = x := by
  exact Prod.ext (by change discRadial t x.1 = x.1; rw [hx, discRadial_discZero]) rfl

/-- Equivariance uses the actual product formula for every cyclic group
element, including the affine translation in the torus coordinate. -/
theorem familyRadial_equivariant (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (t : unitInterval) (x : Family j) :
    letI := familyAction j v hv
    familyRadial j t (g • x) = g • familyRadial j t x := by
  let := familyAction j v hv
  rw [familyAction_apply, familyAction_apply]
  exact Prod.ext (discRadial_familyRotation_iterate j t g.toAdd.val x.1) rfl

/-- The radial deformation descends to the actual orbit quotient. -/
def fillingRadial (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) : Filling j v hv → Filling j v hv := by
  letI := familyAction j v hv.1
  exact FiniteQuotient.descend (fun x => fillingQuotient j v hv (familyRadial j t x))
    (fun g x => by
      rw [familyRadial_equivariant]
      exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g _)

@[simp] theorem fillingRadial_fillingQuotient (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (t : unitInterval) (x : Family j) :
    fillingRadial j v hv t (fillingQuotient j v hv x) =
      fillingQuotient j v hv (familyRadial j t x) := rfl

theorem fillingRadial_continuous (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (fun p : unitInterval × Filling j v hv => fillingRadial j v hv p.1 p.2) := by
  have hq : IsQuotientMap (fillingQuotient j v hv) := isQuotientMap_quotient_mk'
  apply hq.continuous_lift_prod_right
  exact (fillingQuotient_continuous j v hv).comp (familyRadial_continuous j)

@[simp] theorem fillingRadial_zero (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Filling j v hv) : fillingRadial j v hv 0 x = x := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient, familyRadial_zero]

theorem fillingRadial_one_mem_central (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Filling j v hv) :
    fillingRadial j v hv 1 x ∈ fillingProjection j v hv ⁻¹' {Elliptic.discZero} := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient, familyRadial_one]
  exact (discPower_eq_zero_iff j.order j.order_pos Elliptic.discZero).mpr rfl

/-- Every point of the central fibre stays fixed throughout the deformation. -/
theorem fillingRadial_fixed (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (t : unitInterval) (x : Filling j v hv)
    (hx : fillingProjection j v hv x = Elliptic.discZero) :
    fillingRadial j v hv t x = x := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  change discPower j.order j.order_pos y.1 = Elliptic.discZero at hx
  rw [fillingRadial_fillingQuotient,
    familyRadial_fixed j t y ((discPower_eq_zero_iff j.order j.order_pos y.1).mp hx)]

/-- The inclusion of the actual central-fibre subtype. -/
def fillingCentralSubtypeInclusion (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (fillingProjection j v hv ⁻¹' {Elliptic.discZero}) (Filling j v hv) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The retraction is time one of the actual descended radial deformation. -/
def fillingCentralRetraction (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ContinuousMap (Filling j v hv) (fillingProjection j v hv ⁻¹' {Elliptic.discZero}) :=
  ⟨fun x => ⟨fillingRadial j v hv 1 x, fillingRadial_one_mem_central j v hv x⟩,
    ((fillingRadial_continuous j v hv).comp
      (continuous_const.prodMk continuous_id)).subtype_mk _⟩

@[simp] theorem fillingCentralRetraction_comp_inclusion (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (fillingCentralRetraction j v hv).comp (fillingCentralSubtypeInclusion j v hv) =
      ContinuousMap.id _ := by
  ext x
  exact fillingRadial_fixed j v hv 1 x x.property

/-- A strong deformation retraction, given as an actual homotopy relative to
the central fibre. This is the elliptic part of Lemma 7.3(i). -/
def fillingStrongDeformationRetraction (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    (ContinuousMap.id (Filling j v hv)).HomotopyRel
      ((fillingCentralSubtypeInclusion j v hv).comp (fillingCentralRetraction j v hv))
      (range (fillingCentralSubtypeInclusion j v hv)) where
  toFun p := fillingRadial j v hv p.1 p.2
  continuous_toFun := fillingRadial_continuous j v hv
  map_zero_left := fillingRadial_zero j v hv
  map_one_left _ := rfl
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact fillingRadial_fixed j v hv t y y.property

/-- The inclusion of the actual central fibre is a homotopy equivalence. -/
def fillingCentralHomotopyEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    (fillingProjection j v hv ⁻¹' {Elliptic.discZero}) ≃ₕ Filling j v hv :=
  retractionHomotopyEquiv (fillingCentralSubtypeInclusion j v hv)
    (fillingCentralRetraction j v hv) (fillingCentralRetraction_comp_inclusion j v hv)
    (fillingStrongDeformationRetraction j v hv)

/-- The actual central-fibre inclusion induces an isomorphism of pointed
fundamental groups; its inverse is the map of the displayed retraction. -/
def fillingCentralFundamentalGroupEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : fillingProjection j v hv ⁻¹' {Elliptic.discZero}) :
    FundamentalGroup (fillingProjection j v hv ⁻¹' {Elliptic.discZero}) a ≃*
      FundamentalGroup (Filling j v hv) (a : Filling j v hv) :=
  retractionFundamentalGroupEquiv (fillingCentralSubtypeInclusion j v hv)
    (fillingCentralRetraction j v hv) (fillingCentralRetraction_comp_inclusion j v hv)
    (fillingStrongDeformationRetraction j v hv) a

@[simp] theorem fillingCentralFundamentalGroupEquiv_toMonoidHom (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (a : fillingProjection j v hv ⁻¹' {Elliptic.discZero}) :
    (fillingCentralFundamentalGroupEquiv j v hv a).toMonoidHom =
      FundamentalGroup.map (fillingCentralSubtypeInclusion j v hv) a := rfl

end Wikipedia.HopfProblem.Elliptic
