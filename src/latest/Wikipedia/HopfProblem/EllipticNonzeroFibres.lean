import Wikipedia.HopfProblem.EllipticDiscOrbits
import Wikipedia.HopfProblem.EllipticFillings

/-!
# The actual nonzero fibres of the elliptic fillings

A fixed torus in the covering family meets each orbit over its powered
base value.  Away from zero it meets that orbit exactly once, since the
nontrivial disc rotations have no nonzero fixed points.  The resulting
holomorphic map is a closed embedding with the exact filling fibre as
its image.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ FamilyModel

/-- The actual complex torus over a chosen root of the base parameter maps
to the logarithmic filling by its family inclusion and the finite quotient. -/
def torusFibreMap (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (z : Disc) :
    ((familyPeriods j).point z).Torus → Filling j v hv :=
  fillingQuotient j v hv ∘ (familyPeriods j).fibreInclusion z

theorem torusFibreMap_holomorphic (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) : ContMDiff I₂ I₃ ω (torusFibreMap j v hv z) := by
  let := (familyPeriods j).totalChartedSpace
  exact (fillingQuotient_holomorphic j v hv).comp
    ((familyPeriods j).fibreInclusion_holomorphic z)

theorem torusFibreMap_continuous (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) : Continuous (torusFibreMap j v hv z) :=
  (torusFibreMap_holomorphic j v hv z).continuous

@[simp] theorem fillingProjection_torusFibreMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) (x : ((familyPeriods j).point z).Torus) :
    fillingProjection j v hv (torusFibreMap j v hv z x) = discPower j.order j.order_pos z := rfl

/-- The nonzero base condition rules out all identifications within a
single covering torus. -/
theorem torusFibreMap_injective (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (hz : (z : ℂ) ≠ 0) : Function.Injective (torusFibreMap j v hv z) := by
  let := familyAction j v hv.1
  intro x y hxy
  obtain ⟨g, hg⟩ := (FiniteQuotient.project_eq_iff_mem_orbit
    (CyclicGroup j) (Family j) _ _).mp hxy
  change g • (familyPeriods j).fibreInclusion z y = (familyPeriods j).fibreInclusion z x at hg
  have hb : (familyRotation j)^[g.toAdd.val] z = z := by
    have h := congrArg Prod.fst hg
    rw [familyAction_apply] at h
    exact h
  have hg0 : g.toAdd.val = 0 := by
    by_contra hne
    have hzero := (familyRotation_iterate_fixed_iff j g.toAdd.val
      (Nat.pos_of_ne_zero hne) g.toAdd.val_lt z).mp hb
    exact hz (congrArg Subtype.val hzero)
  have hfix : g • (familyPeriods j).fibreInclusion z y =
      (familyPeriods j).fibreInclusion z y := by
    rw [familyAction_apply, hg0]
    rfl
  exact (familyPeriods j).fibreInclusion_injective z ((hfix.symm.trans hg).symm)

/-- Every point of the actual fibre is represented on this one covering
torus; this also describes the central image when the chosen root is zero. -/
theorem range_torusFibreMap (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (z : Disc) :
    range (torusFibreMap j v hv z) =
      fillingProjection j v hv ⁻¹' {discPower j.order j.order_pos z} := by
  let := familyAction j v hv.1
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    exact fillingProjection_torusFibreMap j v hv z x
  · intro hq
    obtain ⟨x, rfl⟩ := fillingQuotient_surjective j v hv q
    have hp : discPower j.order j.order_pos x.1 = discPower j.order j.order_pos z := hq
    obtain ⟨r, hr, hrot⟩ := (discPower_eq_iff_familyRotation j z x.1).mp hp.symm
    let g : CyclicGroup j := Multiplicative.ofAdd (r : ZMod j.order)
    have hg : g.toAdd.val = r := ZMod.val_natCast_of_lt hr
    have hbase : (g • x).1 = z := by
      rw [familyAction_apply, hg]
      exact hrot
    have hx : g • x ∈ range ((familyPeriods j).fibreInclusion z) := by
      rw [(familyPeriods j).range_fibreInclusion]
      exact hbase
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    change fillingQuotient j v hv ((familyPeriods j).fibreInclusion z y) = _
    rw [hy]
    exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g x

theorem torusFibreMap_isClosedEmbedding (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) (hz : (z : ℂ) ≠ 0) :
    IsClosedEmbedding (torusFibreMap j v hv z) :=
  (torusFibreMap_continuous j v hv z).isClosedEmbedding (torusFibreMap_injective j v hv z hz)

/-- The actual nonzero fibre with its subspace topology is homeomorphic
to its specified complex period torus. -/
def torusFibreHomeomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (z : Disc) (hz : (z : ℂ) ≠ 0) :
    ((familyPeriods j).point z).Torus ≃ₜ
      fillingProjection j v hv ⁻¹' {discPower j.order j.order_pos z} :=
  (torusFibreMap_isClosedEmbedding j v hv z hz).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_torusFibreMap j v hv z))

@[simp] theorem torusFibreHomeomorph_coe (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) (hz : (z : ℂ) ≠ 0)
    (x : ((familyPeriods j).point z).Torus) :
    (torusFibreHomeomorph j v hv z hz x : Filling j v hv) = torusFibreMap j v hv z x := rfl

/-- All filling fibres, including the central one, are connected in
their actual subspace topology. -/
theorem fillingProjection_fibre_connected (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) :
    IsConnected (fillingProjection j v hv ⁻¹' {b}) := by
  obtain ⟨z, rfl⟩ := discPower_surjective j.order j.order_pos b
  rw [← range_torusFibreMap j v hv z]
  exact isConnected_range (torusFibreMap_continuous j v hv z)

end Wikipedia.HopfProblem.Elliptic
