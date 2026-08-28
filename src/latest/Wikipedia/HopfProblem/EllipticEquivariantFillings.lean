import Wikipedia.HopfProblem.EllipticEquivariantFamilies
import Wikipedia.HopfProblem.EllipticQuotientFibration

/-!
# Logarithmic fillings for arbitrary equivariant period families

The filling is the actual orbit quotient of the supplied holomorphic
period family.  Its complex atlas is selected from that family's atlas,
not from the concrete example with the same underlying real torus bundle.
The invariant power map descends to a proper surjective holomorphic map.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data

open SpecialPeriods

variable {j : Kind} (D : Equivariant.Data j)

local instance discLocallyCompact : LocallyCompactSpace Disc := unitDisc.isOpen.locallyCompactSpace

/-- The invariant power map on the supplied varying-period family. -/
def upstairsProjection (x : D.TotalSpace) : Disc := discPower j.order j.order_pos x.1

theorem upstairsProjection_surjective : Function.Surjective D.upstairsProjection :=
  (discPower_surjective j.order j.order_pos).comp D.periods.projection_surjective

theorem upstairsProjection_proper : IsProperMap D.upstairsProjection :=
  (discPower_isProperMap j.order j.order_pos).comp D.periods.projection_proper

theorem upstairsProjection_holomorphic :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      D.upstairsProjection := by
  let := D.periods.totalChartedSpace
  exact (discPower_holomorphic j.order j.order_pos).comp D.periods.projection_holomorphic

theorem upstairsProjection_invariant (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    D.upstairsProjection (g • x) = D.upstairsProjection x :=
  D.action_discPower v hv g x

/-- A fresh type for the actual finite-orbit quotient.  Its complex
structure is supplied only by `chartedSpace` below. -/
def Space (v : Lattice) (hv : AdmissibleTwist j v) : Type :=
  @FiniteQuotient.Space (CyclicGroup j) D.TotalSpace _ (D.action v hv.1)

/-- The inherited orbit-quotient topology. -/
instance spaceTopology (v : Lattice) (hv : AdmissibleTwist j v) :
    TopologicalSpace (D.Space v hv) :=
  inferInstanceAs (TopologicalSpace
    (@FiniteQuotient.Space (CyclicGroup j) D.TotalSpace _ (D.action v hv.1)))

/-- The actual orbit quotient projection. -/
def quotient (v : Lattice) (hv : AdmissibleTwist j v) : D.TotalSpace → D.Space v hv :=
  @FiniteQuotient.project (CyclicGroup j) D.TotalSpace _ (D.action v hv.1)

theorem quotient_surjective (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Surjective (D.quotient v hv) := Quotient.mk_surjective

theorem quotient_continuous (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (D.quotient v hv) := by
  let := D.action v hv.1
  exact FiniteQuotient.project_continuous (CyclicGroup j) D.TotalSpace

theorem quotient_isQuotientMap (v : Lattice) (hv : AdmissibleTwist j v) :
    IsQuotientMap (D.quotient v hv) := by
  let := D.action v hv.1
  exact FiniteQuotient.project_isQuotientMap (CyclicGroup j) D.TotalSpace

theorem quotient_isOpenQuotientMap (v : Lattice) (hv : AdmissibleTwist j v) :
    IsOpenQuotientMap (D.quotient v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact FiniteQuotient.project_isOpenQuotientMap (CyclicGroup j) D.TotalSpace

theorem quotient_eq_iff_mem_orbit (v : Lattice) (hv : AdmissibleTwist j v)
    (x y : D.TotalSpace) :
    letI := D.action v hv.1
    D.quotient v hv x = D.quotient v hv y ↔ x ∈ MulAction.orbit (CyclicGroup j) y := by
  let := D.action v hv.1
  exact FiniteQuotient.project_eq_iff_mem_orbit (CyclicGroup j) D.TotalSpace x y

@[simp] theorem quotient_smul (v : Lattice) (hv : AdmissibleTwist j v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv.1
    D.quotient v hv (g • x) = D.quotient v hv x := by
  let := D.action v hv.1
  exact FiniteQuotient.project_smul (CyclicGroup j) D.TotalSpace g x

instance spaceT2 (v : Lattice) (hv : AdmissibleTwist j v) : T2Space (D.Space v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact FiniteQuotient.spaceT2Space (CyclicGroup j) D.TotalSpace

instance spaceSecondCountable (v : Lattice) (hv : AdmissibleTwist j v) :
    SecondCountableTopology (D.Space v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact FiniteQuotient.spaceSecondCountableTopology (CyclicGroup j) D.TotalSpace

instance spaceLocallyCompact (v : Lattice) (hv : AdmissibleTwist j v) :
    LocallyCompactSpace (D.Space v hv) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  exact FiniteQuotient.spaceLocallyCompactSpace (CyclicGroup j) D.TotalSpace

/-- Freeness is proved from the arithmetic twist condition, so this is a
genuine unramified quotient covering map. -/
theorem quotientCoveringMap (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.action v hv.1
    IsQuotientCoveringMap (D.quotient v hv) (CyclicGroup j) := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  exact FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) D.TotalSpace

theorem quotient_isCoveringMap (v : Lattice) (hv : AdmissibleTwist j v) :
    IsCoveringMap (D.quotient v hv) := by
  let := D.action v hv.1
  exact (D.quotientCoveringMap v hv).isCoveringMap

theorem quotient_isLocalHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    IsLocalHomeomorph (D.quotient v hv) := (D.quotient_isCoveringMap v hv).isLocalHomeomorph

/-- An actual local inverse of the unramified quotient covering. -/
def localInverse (v : Lattice) (hv : AdmissibleTwist j v) (x : D.TotalSpace) :
    OpenPartialHomeomorph (D.Space v hv) D.TotalSpace := by
  let := D.action v hv.1
  exact CoveringQuotient.localInverse (D.quotientCoveringMap v hv) x

@[simp] theorem localInverse_symm (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.TotalSpace) : (D.localInverse v hv x).symm = D.quotient v hv := by
  let := D.action v hv.1
  exact CoveringQuotient.localInverse_symm (D.quotientCoveringMap v hv) x

theorem quotient_localInverse (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.TotalSpace) {y : D.Space v hv} (hy : y ∈ (D.localInverse v hv x).source) :
    D.quotient v hv (D.localInverse v hv x y) = y := by
  let := D.action v hv.1
  exact CoveringQuotient.project_localInverse (D.quotientCoveringMap v hv) x hy

/-- The complex atlas lifted from the supplied period family.  This is
deliberately a selected structure, not a global analytic instance. -/
@[instance_reducible] def chartedSpace (v : Lattice) (hv : AdmissibleTwist j v) :
    ChartedSpace FamilyModel (D.Space v hv) := by
  let := D.periods.totalChartedSpace
  let := D.action v hv.1
  exact CoveringQuotient.chartedSpace (E := FamilyModel) (D.quotientCoveringMap v hv)

/-- The proved holomorphic action gives a complex manifold for the
quotient atlas selected from the supplied periods. -/
theorem isManifold (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    IsManifold (modelWithCornersSelf ℂ FamilyModel) ω (D.Space v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact CoveringQuotient.isManifold (D.quotientCoveringMap v hv) ω
    (D.action_holomorphic v hv.1)

/-- The quotient map is holomorphic for the specified source and quotient atlases. -/
theorem quotient_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (D.quotient v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact CoveringQuotient.contMDiff_project (D.quotientCoveringMap v hv) ω
    (D.action_holomorphic v hv.1)

/-- The actual local lifts of the quotient covering are holomorphic. -/
theorem localInverse_holomorphic (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.TotalSpace) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    ContMDiffOn (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (D.localInverse v hv x) (D.localInverse v hv x).source := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact CoveringQuotient.localInverse_holomorphic (D.quotientCoveringMap v hv) ω
    (D.action_holomorphic v hv.1) x

/-- Every covering fibre has exactly the prescribed order three or four. -/
theorem quotient_fibre_card (v : Lattice) (hv : AdmissibleTwist j v) (y : D.Space v hv) :
    Nat.card (D.quotient v hv ⁻¹' {y}) = j.order := by
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  calc
    _ = Nat.card (CyclicGroup j) :=
      FiniteQuotient.fibre_card (CyclicGroup j) D.TotalSpace y
    _ = j.order := by simp [CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

/-- The actual quotient lift of the invariant base power map. -/
def projection (v : Lattice) (hv : AdmissibleTwist j v) : D.Space v hv → Disc := by
  let := D.action v hv.1
  exact FiniteQuotient.descend D.upstairsProjection (D.upstairsProjection_invariant v hv.1)

@[simp] theorem projection_quotient (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.TotalSpace) :
    D.projection v hv (D.quotient v hv x) = discPower j.order j.order_pos x.1 := rfl

theorem projection_surjective (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Surjective (D.projection v hv) := by
  let := D.action v hv.1
  exact FiniteQuotient.descend_surjective D.upstairsProjection
    (D.upstairsProjection_invariant v hv.1) D.upstairsProjection_surjective

theorem projection_proper (v : Lattice) (hv : AdmissibleTwist j v) :
    IsProperMap (D.projection v hv) := by
  let := D.action v hv.1
  exact FiniteQuotient.descend_isProperMap D.upstairsProjection
    (D.upstairsProjection_invariant v hv.1) D.upstairsProjection_proper

theorem projection_continuous (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (D.projection v hv) := (D.projection_proper v hv).continuous

theorem projection_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (D.projection v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  let := D.action_continuous v hv.1
  let := D.action_free v hv
  exact FiniteQuotient.descend_holomorphic D.upstairsProjection
    (D.upstairsProjection_invariant v hv.1) (modelWithCornersSelf ℂ ℂ)
    D.upstairsProjection_holomorphic

theorem projection_fibre_compact (v : Lattice) (hv : AdmissibleTwist j v) (b : Disc) :
    IsCompact (D.projection v hv ⁻¹' {b}) :=
  (D.projection_proper v hv).isCompact_preimage isCompact_singleton

/-- The actual central support is the quotient image of the central torus. -/
theorem projection_central_fibre (v : Lattice) (hv : AdmissibleTwist j v) :
    D.projection v hv ⁻¹' {Elliptic.discZero} =
      D.quotient v hv '' {x : D.TotalSpace | x.1 = Elliptic.discZero} := by
  let := D.action v hv.1
  change FiniteQuotient.descend D.upstairsProjection
    (D.upstairsProjection_invariant v hv.1) ⁻¹' {Elliptic.discZero} = _
  rw [FiniteQuotient.descend_preimage_eq_image]
  congr 1
  ext x
  exact discPower_eq_zero_iff j.order j.order_pos x.1

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data
