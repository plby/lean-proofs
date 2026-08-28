import Wikipedia.HopfProblem.EllipticFamilyAction
import Wikipedia.HopfProblem.EllipticQuotientFibration

/-!
# The actual elliptic logarithmic disc fillings

The free finite affine action on each explicitly constructed period family
has an actual Hausdorff smooth complex quotient.  The invariant map `s ↦ s^m`
descends to a proper surjective holomorphic map to the unit disc.  The
quotient topology, complex atlas, freeness, and properness are all proved.

The source's choices `ε` and `-ε'` give these fillings with no twist or
period-existence assumptions.  These are local analytic fillings; gluing
them to a global period family is a further step.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

instance discLocallyCompact : LocallyCompactSpace Disc := unitDisc.isOpen.locallyCompactSpace

/-- The invariant local base map before the finite quotient. -/
def upstairsProjection (j : Kind) (x : Family j) : Disc :=
  discPower j.order j.order_pos x.1

theorem upstairsProjection_surjective (j : Kind) :
    Function.Surjective (upstairsProjection j) :=
  (discPower_surjective j.order j.order_pos).comp (familyPeriods j).projection_surjective

theorem upstairsProjection_proper (j : Kind) : IsProperMap (upstairsProjection j) :=
  (discPower_isProperMap j.order j.order_pos).comp (familyPeriods j).projection_proper

theorem upstairsProjection_holomorphic (j : Kind) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (upstairsProjection j) := by
  let := (familyPeriods j).totalChartedSpace
  exact (discPower_holomorphic j.order j.order_pos).comp (familyPeriods j).projection_holomorphic

theorem upstairsProjection_invariant (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    upstairsProjection j (g • x) = upstairsProjection j x :=
  familyAction_discPower j v hv g x

/-- The actual finite-orbit quotient of the actual varying period family. -/
abbrev Filling (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :=
  @FiniteQuotient.Space (CyclicGroup j) (Family j) _ (familyAction j v hv.1)

/-- The quotient map from the torus family to its logarithmic filling. -/
def fillingQuotient (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Family j → Filling j v hv :=
  @FiniteQuotient.project (CyclicGroup j) (Family j) _ (familyAction j v hv.1)

theorem fillingQuotient_surjective (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Function.Surjective (fillingQuotient j v hv) := Quotient.mk_surjective

theorem fillingQuotient_continuous (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Continuous (fillingQuotient j v hv) := by
  let := familyAction j v hv.1
  exact FiniteQuotient.project_continuous (CyclicGroup j) (Family j)

instance fillingT2 (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    T2Space (Filling j v hv) := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  exact FiniteQuotient.spaceT2Space (CyclicGroup j) (Family j)

instance fillingSecondCountable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    SecondCountableTopology (Filling j v hv) := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  exact FiniteQuotient.spaceSecondCountableTopology (CyclicGroup j) (Family j)

instance fillingLocallyCompact (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    LocallyCompactSpace (Filling j v hv) := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  exact FiniteQuotient.spaceLocallyCompactSpace (CyclicGroup j) (Family j)

instance fillingChartedSpace (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ChartedSpace FamilyModel (Filling j v hv) := by
  letI := (familyPeriods j).totalChartedSpace
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.chartedSpace (E := FamilyModel) (CyclicGroup j) (Family j)

instance fillingIsManifold (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    IsManifold (modelWithCornersSelf ℂ FamilyModel) ω (Filling j v hv) := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).totalSpace_isManifold
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.isManifold (CyclicGroup j) (Family j)
    (familyAction_holomorphic j v hv.1)

/-- The filling quotient map is a genuine unramified topological covering. -/
theorem fillingQuotient_isCoveringMap (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsCoveringMap (fillingQuotient j v hv) := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.project_isCoveringMap (CyclicGroup j) (Family j)

theorem fillingQuotient_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := (familyPeriods j).totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fillingQuotient j v hv) := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).totalSpace_isManifold
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.project_holomorphic (CyclicGroup j) (Family j)
    (familyAction_holomorphic j v hv.1)

theorem fillingQuotient_fibre_card (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv) :
    Nat.card (fillingQuotient j v hv ⁻¹' {y}) = j.order := by
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  change Nat.card (FiniteQuotient.project (CyclicGroup j) (Family j) ⁻¹' {y}) = j.order
  rw [FiniteQuotient.fibre_card (CyclicGroup j) (Family j)]
  simp [CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

/-- The actual proper holomorphic projection of the logarithmic filling. -/
def fillingProjection (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Filling j v hv → Disc := by
  letI := familyAction j v hv.1
  exact FiniteQuotient.descend (upstairsProjection j) (upstairsProjection_invariant j v hv.1)

/-- In the covering coordinates the filling map is exactly `s ↦ s^m`. -/
@[simp] theorem fillingProjection_fillingQuotient (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Family j) :
    fillingProjection j v hv (fillingQuotient j v hv x) =
      discPower j.order j.order_pos x.1 := rfl

theorem fillingProjection_surjective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : Function.Surjective (fillingProjection j v hv) := by
  let := familyAction j v hv.1
  exact FiniteQuotient.descend_surjective (upstairsProjection j)
    (upstairsProjection_invariant j v hv.1) (upstairsProjection_surjective j)

theorem fillingProjection_proper (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : IsProperMap (fillingProjection j v hv) := by
  let := familyAction j v hv.1
  exact FiniteQuotient.descend_isProperMap (upstairsProjection j)
    (upstairsProjection_invariant j v hv.1) (upstairsProjection_proper j)

theorem fillingProjection_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
      (fillingProjection j v hv) := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).totalSpace_isManifold
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  exact FiniteQuotient.descend_holomorphic (upstairsProjection j)
    (upstairsProjection_invariant j v hv.1) (modelWithCornersSelf ℂ ℂ)
    (upstairsProjection_holomorphic j)

theorem fillingProjection_fibre_compact (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) :
    IsCompact (fillingProjection j v hv ⁻¹' {b}) :=
  (fillingProjection_proper j v hv).isCompact_preimage isCompact_singleton

/-- The support of the central fibre is exactly the image of the central
torus under the finite quotient. -/
theorem fillingProjection_central_fibre (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    fillingProjection j v hv ⁻¹' {Elliptic.discZero} =
      fillingQuotient j v hv '' {x : Family j | x.1 = Elliptic.discZero} := by
  let := familyAction j v hv.1
  change FiniteQuotient.descend (upstairsProjection j)
    (upstairsProjection_invariant j v hv.1) ⁻¹' {Elliptic.discZero} = _
  rw [FiniteQuotient.descend_preimage_eq_image]
  congr 1
  ext x
  exact discPower_eq_zero_iff j.order j.order_pos x.1

/-- The source's two chosen local logarithmic fillings. -/
abbrev MainFilling (j : Kind) := Filling j j.twist (mainTwist_admissible j)

instance mainFillingT2 (j : Kind) : T2Space (MainFilling j) :=
  fillingT2 j j.twist (mainTwist_admissible j)

instance mainFillingSecondCountable (j : Kind) : SecondCountableTopology (MainFilling j) :=
  fillingSecondCountable j j.twist (mainTwist_admissible j)

instance mainFillingChartedSpace (j : Kind) : ChartedSpace FamilyModel (MainFilling j) :=
  fillingChartedSpace j j.twist (mainTwist_admissible j)

instance mainFillingIsManifold (j : Kind) :
    IsManifold (modelWithCornersSelf ℂ FamilyModel) ω (MainFilling j) :=
  fillingIsManifold j j.twist (mainTwist_admissible j)

/-- Both local logarithmic disc fillings exist, with all analytic and
arithmetic requirements discharged by their explicit construction. -/
theorem mainFilling_proper_holomorphic (j : Kind) :
    IsProperMap (fillingProjection j j.twist (mainTwist_admissible j)) ∧
      Function.Surjective (fillingProjection j j.twist (mainTwist_admissible j)) ∧
      ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ ℂ) ω
        (fillingProjection j j.twist (mainTwist_admissible j)) :=
  ⟨fillingProjection_proper j j.twist (mainTwist_admissible j),
    fillingProjection_surjective j j.twist (mainTwist_admissible j),
    fillingProjection_holomorphic j j.twist (mainTwist_admissible j)⟩

end Wikipedia.HopfProblem.Elliptic
