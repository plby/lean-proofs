import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardPositiveSection

/-!
# The actual positive infinity Cartier presentation

The numerator is the genuine global section of the original dual base
line, and the denominator is one.  Its literal reciprocal-chart fraction
is `w`, including at the chart centre.  Its only zero is therefore the
actual point at infinity, with analytic and meromorphic order one.
-/

open Bundle Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- Cartier data on the unchanged dual bundle, with the native section
as numerator and the actual finite chart as dense nonvanishing locus. -/
noncomputable def actualCartier : CanonicalGlobal.CartierData 𝓘(ℂ) RiemannSphere Bool where
  transitions := data
  isHolomorphic := inferInstance
  numerator := coefficient
  denominator := fun _ _ => 1
  numerator_holomorphic := coefficient_holomorphic
  denominator_holomorphic _ := contMDiffOn_const
  genericSet := finiteChart
  genericSet_dense := CanonicalGlobal.BaseTwist.finiteChart_dense
  numerator_ne_zero b p hb hp :=
    (coefficient_eq_zero_iff b p hb).not.mpr ((mem_finiteChart p).mp hp)
  denominator_ne_zero _ _ _ _ := one_ne_zero
  ratio a b p hp := by
    simpa only [mul_one] using (coefficient_compatible a b p hp).symm

@[simp] theorem actualCartier_transitions : actualCartier.transitions = data := rfl

@[simp] theorem actualCartier_associatedBundle : actualCartier.associatedBundle = bundle := rfl

@[simp] theorem actualCartier_genericSet : actualCartier.genericSet = finiteChart := rfl

@[simp] theorem actualCartier_numerator (b : Bool) (p : RiemannSphere) :
    actualCartier.numerator b p = coefficient b p := rfl

@[simp] theorem actualCartier_denominator (b : Bool) (p : RiemannSphere) :
    actualCartier.denominator b p = 1 := rfl

@[simp] theorem actualCartier_localFraction (b : Bool) (p : RiemannSphere) :
    actualCartier.localFraction b p = coefficient b p := div_one _

/-- The Cartier section is literally the original native positive section. -/
@[simp] theorem actualCartier_rawSection (p : RiemannSphere) :
    actualCartier.rawSection p = sectionValue p :=
  actualCartier_localFraction (data.indexAt p) p

theorem actualCartier_rawSection_eq : actualCartier.rawSection = sectionValue :=
  funext actualCartier_rawSection

theorem actualCartier_rawSectionMap : actualCartier.rawSectionMap = sectionMap := by
  funext p
  change (⟨p, actualCartier.rawSection p⟩ : bundle.TotalSpace) = ⟨p, sectionValue p⟩
  rw [actualCartier_rawSection]

/-- Unlike a merely generic Cartier section, this native section is
holomorphic on the whole sphere, including the point at infinity. -/
theorem actualCartier_rawSectionMap_holomorphic :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω actualCartier.rawSectionMap := by
  rw [actualCartier_rawSectionMap]
  exact sectionMap_holomorphic

theorem actualCartier_rawSection_eq_zero_iff (p : RiemannSphere) :
    actualCartier.rawSection p = 0 ↔ p = (∞ : RiemannSphere) := by
  rw [actualCartier_rawSection]
  exact section_eq_zero_iff p

/-- The native chart coefficient agrees with the literal Cartier
fraction everywhere on the actual chart, including at its zero. -/
theorem actualCartier_rawSection_localCoefficient (b : Bool) {p : RiemannSphere}
    (hp : p ∈ data.baseSet b) :
    data.localCoefficient actualCartier.rawSection b p = actualCartier.localFraction b p := by
  rw [actualCartier_rawSection_eq, section_localCoefficient b hp,
    actualCartier_localFraction]

@[simp] theorem actualCartier_localFraction_false (p : RiemannSphere) :
    actualCartier.localFraction false p = 1 := actualCartier_localFraction false p

@[simp] theorem actualCartier_localFraction_true (p : RiemannSphere) :
    actualCartier.localFraction true p = CanonicalGlobal.BaseTwist.infinityCoordinate p :=
  actualCartier_localFraction true p

/-- The fraction is literally the original reciprocal coordinate, including at zero. -/
@[simp] theorem actualCartier_localFraction_infinityParametrization (w : ℂ) :
    actualCartier.localFraction true (RiemannSphere.infinityParametrization w) = w := by
  rw [actualCartier_localFraction_true,
    CanonicalGlobal.BaseTwist.infinityCoordinate_infinityParametrization]

theorem actualCartier_infinityFraction_eq_id :
    (fun w : ℂ =>
      actualCartier.localFraction true (RiemannSphere.infinityParametrization w)) = id :=
  funext actualCartier_localFraction_infinityParametrization

theorem actualCartier_infinityFraction_analyticAt (w : ℂ) :
    AnalyticAt ℂ (fun u : ℂ =>
      actualCartier.localFraction true (RiemannSphere.infinityParametrization u)) w := by
  rw [actualCartier_infinityFraction_eq_id]
  exact analyticAt_id

/-- The zero at infinity is simple in the original reciprocal chart. -/
theorem actualCartier_infinity_analyticOrderAt :
    analyticOrderAt (fun w : ℂ =>
      actualCartier.localFraction true (RiemannSphere.infinityParametrization w)) 0 = 1 := by
  rw [actualCartier_infinityFraction_eq_id]
  exact analyticOrderAt_id

theorem actualCartier_infinity_meromorphicOrderAt :
    meromorphicOrderAt (fun w : ℂ =>
      actualCartier.localFraction true (RiemannSphere.infinityParametrization w)) 0 = 1 := by
  rw [actualCartier_infinityFraction_eq_id]
  exact meromorphicOrderAt_id

/-- The actual finite-chart fraction is a unit at every finite point. -/
theorem actualCartier_finite_analyticOrderAt (z : ℂ) :
    analyticOrderAt (fun u : ℂ => actualCartier.localFraction false (u : RiemannSphere)) z =
      0 := by
  have h : (fun u : ℂ => actualCartier.localFraction false (u : RiemannSphere)) =
      (fun _ : ℂ => (1 : ℂ)) := funext fun u => actualCartier_localFraction_false _
  rw [h]
  exact analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero

theorem actualCartier_finite_meromorphicOrderAt (z : ℂ) :
    meromorphicOrderAt (fun u : ℂ => actualCartier.localFraction false (u : RiemannSphere)) z =
      0 := by
  classical
  have h : (fun u : ℂ => actualCartier.localFraction false (u : RiemannSphere)) =
      (fun _ : ℂ => (1 : ℂ)) := funext fun u => actualCartier_localFraction_false _
  rw [h, meromorphicOrderAt_const]
  simp only [one_ne_zero, if_false]

/-- The native section itself has a simple zero, read in its genuine bundle chart. -/
theorem section_infinity_simple_zero :
    analyticOrderAt (fun w : ℂ => data.localCoefficient sectionValue true
      (RiemannSphere.infinityParametrization w)) 0 = 1 := by
  have h : (fun w : ℂ => data.localCoefficient sectionValue true
      (RiemannSphere.infinityParametrization w)) = id := funext section_infinity_coefficient
  rw [h]
  exact analyticOrderAt_id

theorem section_infinity_meromorphicOrderAt :
    meromorphicOrderAt (fun w : ℂ => data.localCoefficient sectionValue true
      (RiemannSphere.infinityParametrization w)) 0 = 1 := by
  have h : (fun w : ℂ => data.localCoefficient sectionValue true
      (RiemannSphere.infinityParametrization w)) = id := funext section_infinity_coefficient
  rw [h]
  exact meromorphicOrderAt_id

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Positive
