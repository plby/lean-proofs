import Wikipedia.HopfProblem.EllipticEquivariantFillings
import Wikipedia.HopfProblem.EllipticSurfaces

/-!
# The actual central torus of any equivariant elliptic period family

The existing fibre-inclusion construction applies to the supplied varying
period map at the center. Its flat-coordinate formula proves that the
surrounding finite action restricts to the genuine affine action of the
actual fixed central period. No comparison of complex family atlases is
used.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual fixed central period torus inside the supplied family. -/
def centralInclusion : D.centralPeriod.val.Torus → D.TotalSpace :=
  D.periods.fibreInclusion SpecialPeriods.discZero

theorem centralInclusion_injective : Function.Injective D.centralInclusion :=
  D.periods.fibreInclusion_injective SpecialPeriods.discZero

theorem centralInclusion_continuous : Continuous D.centralInclusion :=
  continuous_const.prodMk (D.periods.torusHomeomorph SpecialPeriods.discZero).symm.continuous

theorem centralInclusion_isClosedEmbedding : IsClosedEmbedding D.centralInclusion :=
  D.centralInclusion_continuous.isClosedEmbedding D.centralInclusion_injective

@[simp] theorem centralInclusion_mkQ (z : ComplexPlane₂) :
    D.centralInclusion (D.centralPeriod.val.lattice.mkQ z) =
      D.periods.quotientMap (SpecialPeriods.discZero, z) :=
  D.periods.fibreInclusion_mkQ SpecialPeriods.discZero z

@[simp] theorem centralInclusion_projection (x : D.centralPeriod.val.Torus) :
    D.periods.projection (D.centralInclusion x) = SpecialPeriods.discZero := rfl

theorem range_centralInclusion :
    range D.centralInclusion = D.periods.projection ⁻¹' {SpecialPeriods.discZero} :=
  D.periods.range_fibreInclusion SpecialPeriods.discZero

theorem mem_range_centralInclusion_iff (x : D.TotalSpace) :
    x ∈ range D.centralInclusion ↔ x.1 = SpecialPeriods.discZero := by
  rw [D.range_centralInclusion]
  rfl

/-- Holomorphicity is for this period map's actual varying-period atlas. -/
theorem centralInclusion_holomorphic :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ FamilyModel) ω D.centralInclusion :=
  D.periods.fibreInclusion_holomorphic SpecialPeriods.discZero

/-- The central inclusion inserts the center and keeps the original
flat torus coordinate. -/
theorem centralInclusion_flatProjection (x : RealCoordinates) :
    D.centralInclusion (flatProjection D.centralPeriod.val x) =
      (SpecialPeriods.discZero, standardLattice.mkQ x) := by
  rw [flatProjection, D.centralInclusion_mkQ]
  change (SpecialPeriods.discZero,
    standardLattice.mkQ ((D.periods.periodEquiv SpecialPeriods.discZero).symm
      (Elliptic.periodEquiv (D.periods.point SpecialPeriods.discZero) x))) = _
  rw [← D.periodEquiv_eq_periodEquiv, LinearEquiv.symm_apply_apply]

/-- The actual family action and the actual central affine map agree
on the central torus, not just on their linear parts. -/
theorem permutation_centralInclusion (v : Lattice) (x : D.centralPeriod.val.Torus) :
    D.permutation v (D.centralInclusion x) =
      D.centralInclusion (affineBiholomorph j D.centralPeriod v x) := by
  obtain ⟨y, rfl⟩ := flatProjection_surjective D.centralPeriod.val x
  rw [D.centralInclusion_flatProjection, D.permutation_apply,
    affineBiholomorph_flatProjection, D.centralInclusion_flatProjection]
  exact Prod.ext (familyRotation_zero j) (flatTorusAffine_mkQ j v y)

theorem permutation_iterate_centralInclusion (v : Lattice) (n : ℕ)
    (x : D.centralPeriod.val.Torus) :
    (D.permutation v)^[n] (D.centralInclusion x) =
      D.centralInclusion ((affineBiholomorph j D.centralPeriod v)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      D.permutation_centralInclusion]

theorem permutation_pow_centralInclusion (v : Lattice) (n : ℕ)
    (x : D.centralPeriod.val.Torus) :
    (D.permutation v ^ n) (D.centralInclusion x) =
      D.centralInclusion ((affinePermutation j D.centralPeriod v ^ n) x) := by
  rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact D.permutation_iterate_centralInclusion v n x

/-- The inclusion intertwines the full finite cyclic actions. -/
theorem centralInclusion_smul (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.centralPeriod.val.Torus) :
    letI := affineAction j D.centralPeriod v hv
    letI := D.action v hv
    D.centralInclusion (g • x) = g • D.centralInclusion x := by
  let := affineAction j D.centralPeriod v hv
  let := D.action v hv
  change D.centralInclusion ((affinePermutation j D.centralPeriod v ^ g.toAdd.val) x) =
    (D.permutation v ^ g.toAdd.val) (D.centralInclusion x)
  exact (D.permutation_pow_centralInclusion v g.toAdd.val x).symm

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
