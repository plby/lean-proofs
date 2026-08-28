import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticGaugeBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionTriangleBasic
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingOverlap

/-!
# Vertical flow through the actual punctured elliptic comparison

The finite-orbit flow restricts to the punctured filling.  The existing
logarithmic gauge and local-to-global comparison carry this flow to the
original triangle-family translation, with no change of either atlas.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge

open Wikipedia.HopfProblem.Elliptic
open Wikipedia.HopfProblem.Elliptic.LogGauge
open Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
open TrianglePeriodFamily

section Filling

variable {j : Kind} (D : Equivariant.Data j)

/-- The restriction of the original finite-orbit flow to the complement
of its central fibre. -/
def fillingStarFlow (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ)
    (x : FillingStar D v hv) : FillingStar D v hv :=
  ⟨flow D v hv s x.val, by
    change (D.projection v hv (flow D v hv s x.val) : ℂ) ≠ 0
    rw [flow_projection]
    exact x.property⟩

@[simp] theorem fillingStarFlow_coe (v : Lattice) (hv : AdmissibleTwist j v)
    (s : ℂ) (x : FillingStar D v hv) :
    (fillingStarFlow D v hv s x : D.Space v hv) = flow D v hv s x.val := rfl

@[simp] theorem fillingStarFlow_projection (v : Lattice) (hv : AdmissibleTwist j v)
    (s : ℂ) (x : FillingStar D v hv) :
    fillingStarProjection D v hv (fillingStarFlow D v hv s x) =
      fillingStarProjection D v hv x :=
  Subtype.ext (flow_projection D v hv s x.val)

/-- Exact compatibility with the original restricted quotient map. -/
@[simp] theorem fillingStarFlow_project (v : Lattice) (hv : AdmissibleTwist j v)
    (s : ℂ) (x : FamilyStar D.periods) :
    fillingStarFlow D v hv s (fillingStarProject D v hv x) =
      fillingStarProject D v hv (familyFlow D.periods s x) :=
  Subtype.ext (flow_quotient D v hv s x.val)

@[simp] theorem fillingStarFlow_zero (v : Lattice) (hv : AdmissibleTwist j v)
    (x : FillingStar D v hv) : fillingStarFlow D v hv 0 x = x :=
  Subtype.ext (flow_zero D v hv x.val)

theorem fillingStarFlow_add (v : Lattice) (hv : AdmissibleTwist j v)
    (s t : ℂ) (x : FillingStar D v hv) :
    fillingStarFlow D v hv (s + t) x =
      fillingStarFlow D v hv s (fillingStarFlow D v hv t x) :=
  Subtype.ext (flow_add D v hv s t x.val)

@[simp] theorem fillingStarFlow_int_cast (v : Lattice) (hv : AdmissibleTwist j v)
    (n : ℤ) (x : FillingStar D v hv) : fillingStarFlow D v hv (n : ℂ) x = x :=
  Subtype.ext (flow_int_cast D v hv n x.val)

end Filling

section Comparison

variable (P : HolomorphicPeriodMap ℂ ℍ) (j : Kind)

/-- The actual local period restriction and inverse Cayley base map
preserve the original vertical translations. -/
theorem localTotalMap_familyFlow (s : ℂ) (x : FamilyStar (localPeriods P j)) :
    localTotalMap P j (familyFlow (localPeriods P j) s x) =
      Period.flow (regularPeriods P) s (localTotalMap P j x) := by
  rfl

variable
  (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The local-to-global triangle quotient comparison intertwines the
same literal period-family flows. -/
theorem regularMap_familyFlow (s : ℂ) (x : FamilyStar (localPeriods P j)) :
    regularMap P j h₁ h₂ (familyFlow (localPeriods P j) s x) =
      Triangle.flow (regularData P h₁ h₂) s (regularMap P j h₁ h₂ x) := by
  change (regularData P h₁ h₂).quotient
      (localTotalMap P j (familyFlow (localPeriods P j) s x)) =
    Triangle.flow (regularData P h₁ h₂) s
      ((regularData P h₁ h₂).quotient (localTotalMap P j x))
  rw [Triangle.flow_quotient, localTotalMap_familyFlow]
  rfl

/-- The full existing punctured-filling comparison on an actual family
representative is its logarithmic gauge followed by the regular map. -/
theorem puncturedFillingBiholomorph_project (x : FamilyStar (localPeriods P j)) :
    (puncturedFillingBiholomorph P j h₁ h₂
      (fillingStarProject (localData P h₁ h₂ j) j.twist (mainTwist_admissible j) x)).val =
      regularMap P j h₁ h₂ (gaugeMap (localPeriods P j) j.twist x) := by
  change (tautologicalOverlapBiholomorph P j h₁ h₂
    (fillingToTautologicalBiholomorph (localData P h₁ h₂ j) j.twist
      (mainTwist_admissible j)
      (fillingStarProject (localData P h₁ h₂ j) j.twist (mainTwist_admissible j) x))).val = _
  rw [fillingToTautologicalBiholomorph_project]
  exact congrArg Subtype.val (tautologicalOverlapBiholomorph_project P j h₁ h₂
    (gaugeMap (localPeriods P j) j.twist x))

/-- The actual logarithmic punctured-filling biholomorphism intertwines
the finite-orbit vertical flow with the actual triangle-family flow. -/
theorem puncturedFillingBiholomorph_fillingStarFlow (s : ℂ)
    (x : MainFillingStar P j h₁ h₂) :
    (puncturedFillingBiholomorph P j h₁ h₂
      (fillingStarFlow (localData P h₁ h₂ j) j.twist (mainTwist_admissible j) s x)).val =
      Triangle.flow (regularData P h₁ h₂) s
        (puncturedFillingBiholomorph P j h₁ h₂ x).val := by
  obtain ⟨y, rfl⟩ := fillingStarProject_surjective (localData P h₁ h₂ j)
    j.twist (mainTwist_admissible j) x
  rw [fillingStarFlow_project, puncturedFillingBiholomorph_project,
    puncturedFillingBiholomorph_project, localData_periods,
    gaugeMap_familyFlow, regularMap_familyFlow]

end Comparison

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic.Gauge
