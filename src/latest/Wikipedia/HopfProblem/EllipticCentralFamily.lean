import Wikipedia.HopfProblem.EllipticFamilies
import Wikipedia.HopfProblem.EllipticSurfaces

/-!
# The central torus in the elliptic local families

At the center of the actual local base disc, the period is fixed by the
elliptic transformation.  Its complex torus is holomorphically and
closedly embedded as precisely the central fibre of the varying-period
family.  The family action restricts to the previously constructed
affine biholomorphism of this torus.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

@[simp] theorem familyRotation_discZero (j : Kind) :
    familyRotation j SpecialPeriods.discZero = SpecialPeriods.discZero := by
  cases j <;> apply Subtype.ext
  · change -rho * (0 : ℂ) = 0
    exact mul_zero _
  · change -Complex.I * (0 : ℂ) = 0
    exact mul_zero _

theorem familyPeriodPoint_rotation (j : Kind) (z : Disc) :
    (familyPeriods j).point (familyRotation j z) =
      periodStep j ((familyPeriods j).point z) := by
  cases j
  · exact threePeriodMap_rotate z
  · exact fourPeriodMap_rotate z

/-- The actual period at the center of the varying family is a fixed period. -/
def centralPeriod (j : Kind) : FixedPeriod j :=
  ⟨(familyPeriods j).point SpecialPeriods.discZero,
    (familyPeriodPoint_rotation j SpecialPeriods.discZero).symm.trans
      (congrArg (familyPeriods j).point (familyRotation_discZero j))⟩

@[simp] theorem centralPeriod_val (j : Kind) :
    (centralPeriod j).val = (familyPeriods j).point SpecialPeriods.discZero := rfl

/-- The inclusion of the actual fixed-period torus as the central family fibre. -/
def centralInclusion (j : Kind) : (centralPeriod j).val.Torus → Family j :=
  (familyPeriods j).fibreInclusion SpecialPeriods.discZero

theorem centralInclusion_injective (j : Kind) : Function.Injective (centralInclusion j) :=
  (familyPeriods j).fibreInclusion_injective SpecialPeriods.discZero

theorem centralInclusion_continuous (j : Kind) : Continuous (centralInclusion j) :=
  continuous_const.prodMk
    ((familyPeriods j).torusHomeomorph SpecialPeriods.discZero).symm.continuous

theorem centralInclusion_isClosedEmbedding (j : Kind) :
    IsClosedEmbedding (centralInclusion j) :=
  (centralInclusion_continuous j).isClosedEmbedding (centralInclusion_injective j)

@[simp] theorem centralInclusion_mkQ (j : Kind) (z : ComplexPlane₂) :
    centralInclusion j ((centralPeriod j).val.lattice.mkQ z) =
      (familyPeriods j).quotientMap (SpecialPeriods.discZero, z) :=
  (familyPeriods j).fibreInclusion_mkQ SpecialPeriods.discZero z

@[simp] theorem centralInclusion_projection (j : Kind) (x : (centralPeriod j).val.Torus) :
    (familyPeriods j).projection (centralInclusion j x) = SpecialPeriods.discZero := rfl

/-- The image is the complete fibre over the center, not a subset of that fibre. -/
theorem range_centralInclusion (j : Kind) :
    range (centralInclusion j) = (familyPeriods j).projection ⁻¹' {SpecialPeriods.discZero} :=
  (familyPeriods j).range_fibreInclusion SpecialPeriods.discZero

theorem mem_range_centralInclusion_iff (j : Kind) (x : Family j) :
    x ∈ range (centralInclusion j) ↔ x.1 = SpecialPeriods.discZero := by
  rw [range_centralInclusion]
  rfl

/-- The fibre inclusion is holomorphic in the actual varying-period atlas. -/
theorem centralInclusion_holomorphic (j : Kind) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ FamilyModel) ω (centralInclusion j) :=
  (familyPeriods j).fibreInclusion_holomorphic SpecialPeriods.discZero

/-- The two period-coordinate constructions have exactly the same columns. -/
theorem familyPeriodEquiv_eq_periodEquiv (j : Kind) (z : Disc) (x : RealCoordinates) :
    (familyPeriods j).periodEquiv z x = periodEquiv ((familyPeriods j).point z) x := by
  rw [familyPeriodEquiv_matrix, periodEquiv_matrix]

/-- In the topological real-torus trivialization the inclusion fixes the
torus coordinate and inserts the center as the base coordinate. -/
theorem centralInclusion_flatProjection (j : Kind) (x : RealCoordinates) :
    centralInclusion j (flatProjection (centralPeriod j).val x) =
      (SpecialPeriods.discZero, standardLattice.mkQ x) := by
  rw [flatProjection, centralInclusion_mkQ]
  change (SpecialPeriods.discZero,
    standardLattice.mkQ (((familyPeriods j).periodEquiv SpecialPeriods.discZero).symm
      (periodEquiv ((familyPeriods j).point SpecialPeriods.discZero) x))) = _
  rw [← familyPeriodEquiv_eq_periodEquiv, LinearEquiv.symm_apply_apply]

/-- Restricting the actual family permutation gives exactly the affine
biholomorphism on its central fixed-period torus. -/
theorem familyPermutation_centralInclusion (j : Kind) (v : Lattice)
    (x : (centralPeriod j).val.Torus) :
    familyPermutation j v (centralInclusion j x) =
      centralInclusion j (affineBiholomorph j (centralPeriod j) v x) := by
  obtain ⟨y, rfl⟩ := flatProjection_surjective (centralPeriod j).val x
  rw [centralInclusion_flatProjection, familyPermutation_apply,
    affineBiholomorph_flatProjection, centralInclusion_flatProjection,
    familyRotation_discZero, flatTorusAffine_mkQ]

theorem familyPermutation_iterate_centralInclusion (j : Kind) (v : Lattice)
    (n : ℕ) (x : (centralPeriod j).val.Torus) :
    (familyPermutation j v)^[n] (centralInclusion j x) =
      centralInclusion j ((affineBiholomorph j (centralPeriod j) v)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      familyPermutation_centralInclusion]

theorem familyPermutation_pow_centralInclusion (j : Kind) (v : Lattice)
    (n : ℕ) (x : (centralPeriod j).val.Torus) :
    (familyPermutation j v ^ n) (centralInclusion j x) =
      centralInclusion j ((affinePermutation j (centralPeriod j) v ^ n) x) := by
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact familyPermutation_iterate_centralInclusion j v n x

end Wikipedia.HopfProblem.Elliptic
