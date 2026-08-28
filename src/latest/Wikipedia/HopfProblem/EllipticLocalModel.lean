import Wikipedia.HopfProblem.EllipticFillings
import Wikipedia.HopfProblem.EllipticDiscOrbits

/-!
# Complex-coordinate local models of the elliptic fillings

In the constructed quotient atlas, the actual filling projection is
exactly the positive power of the first complex coordinate.  Thus its
central support is a coordinate hyperplane, and the transverse analytic
order is the prescribed three or four.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

local instance localModelCoveringChartedSpace : ChartedSpace FamilyModel (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

/-- The first coordinate of the actual period-family charts is the base
disc coordinate, despite the varying fibre periods. -/
theorem familyProjection_chart_symm (j : Kind) (x : Family j) (u : FamilyModel) :
    letI := (familyPeriods j).totalChartedSpace
    u ∈ (chartAt FamilyModel x).target →
      ((familyPeriods j).projection ((chartAt FamilyModel x).symm u) : ℂ) = u.1 := by
  let := (familyPeriods j).totalChartedSpace
  let := (familyPeriods j).coveringAction
  intro hu
  let r := CoveringQuotient.representative (familyPeriods j).quotientCoveringMap x
  change u ∈ (CoveringQuotient.chart (E := FamilyModel)
    (familyPeriods j).quotientCoveringMap x).target at hu
  have hubase : u.1 ∈ (chartAt ℂ r.1).target := hu.1.1
  have hs : ((chartAt FamilyModel x).symm : FamilyModel → Family j) =
      fun w => (familyPeriods j).quotientMap ((chartAt ℂ r.1).symm w.1, w.2) := by
    change ((CoveringQuotient.chart (E := FamilyModel)
      (familyPeriods j).quotientCoveringMap x).symm : FamilyModel → Family j) = _
    rw [CoveringQuotient.chart_symm]
    rfl
  rw [hs]
  exact (chartAt ℂ r.1).right_inv hubase

/-- The genuine analytic local equation of the logarithmic filling map. -/
theorem fillingProjection_chart_symm (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv) (u : FamilyModel)
    (hu : u ∈ (chartAt FamilyModel y).target) :
    (fillingProjection j v hv ((chartAt FamilyModel y).symm u) : ℂ) = u.1 ^ j.order := by
  let := (familyPeriods j).totalChartedSpace
  let := familyAction j v hv.1
  let := familyAction_continuous j v hv.1
  let := familyAction_free j v hv
  let hq := FiniteQuotient.project_isQuotientCoveringMap (CyclicGroup j) (Family j)
  let r := CoveringQuotient.representative hq y
  change u ∈ (CoveringQuotient.chart (E := FamilyModel) hq y).target at hu
  have hur : u ∈ (chartAt FamilyModel r).target := hu.1
  have hs : ((chartAt FamilyModel y).symm : FamilyModel → Filling j v hv) =
      fun w => fillingQuotient j v hv ((chartAt FamilyModel r).symm w) := by
    change ((CoveringQuotient.chart (E := FamilyModel) hq y).symm :
      FamilyModel → Filling j v hv) = _
    rw [CoveringQuotient.chart_symm]
    rfl
  rw [hs, fillingProjection_fillingQuotient, discPower_coe]
  change (((familyPeriods j).projection ((chartAt FamilyModel r).symm u) : ℂ)) ^ j.order = _
  rw [familyProjection_chart_symm j r u hur]

/-- The equation can also be read directly in each chart's source. -/
theorem fillingProjection_chart (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y x : Filling j v hv)
    (hx : x ∈ (chartAt FamilyModel y).source) :
    (fillingProjection j v hv x : ℂ) = (chartAt FamilyModel y x).1 ^ j.order := by
  have h := fillingProjection_chart_symm j v hv y (chartAt FamilyModel y x)
    ((chartAt FamilyModel y).map_source hx)
  rwa [(chartAt FamilyModel y).left_inv hx] at h

/-- The reduced central support is a coordinate hyperplane in the actual
smooth complex atlas. -/
theorem fillingCentral_chart_iff (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y x : Filling j v hv)
    (hx : x ∈ (chartAt FamilyModel y).source) :
    fillingProjection j v hv x = Elliptic.discZero ↔ (chartAt FamilyModel y x).1 = 0 := by
  rw [Subtype.ext_iff, discZero_coe, fillingProjection_chart j v hv y x hx]
  exact pow_eq_zero_iff j.order_pos.ne'

/-- The actual projection on a transverse complex coordinate line through
a chosen point of a filling chart. -/
def transverseProjection (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (y : Filling j v hv) (z : ℂ) : ℂ :=
  fillingProjection j v hv
    ((chartAt FamilyModel y).symm (z, (chartAt FamilyModel y y).2))

theorem transverseProjection_eventuallyEq (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv) :
    transverseProjection j v hv y =ᶠ[𝓝 (chartAt FamilyModel y y).1]
      (fun z : ℂ => z ^ j.order) := by
  have ht : (chartAt FamilyModel y).target ∈
      𝓝 ((chartAt FamilyModel y y).1, (chartAt FamilyModel y y).2) :=
    (chartAt FamilyModel y).open_target.mem_nhds (mem_chart_target FamilyModel y)
  have hc : ContinuousAt (fun z : ℂ => (z, (chartAt FamilyModel y y).2))
      (chartAt FamilyModel y y).1 := continuousAt_id.prodMk continuousAt_const
  have he : ∀ᶠ z in 𝓝 (chartAt FamilyModel y y).1,
      (z, (chartAt FamilyModel y y).2) ∈ (chartAt FamilyModel y).target := hc ht
  exact he.mono fun z hz => fillingProjection_chart_symm j v hv y _ hz

/-- The central multiplicity is the exact analytic order of the actual
projection on a transverse coordinate line. -/
theorem fillingCentral_transverse_order (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y = Elliptic.discZero) :
    analyticOrderAt (transverseProjection j v hv y) 0 = (j.order : ℕ∞) := by
  have hc : (chartAt FamilyModel y y).1 = 0 :=
    (fillingCentral_chart_iff j v hv y y (mem_chart_source FamilyModel y)).mp hy
  have he := transverseProjection_eventuallyEq j v hv y
  rw [hc] at he
  rw [analyticOrderAt_congr he, complexPower_order_at_zero]

/-- Away from the central fibre the actual projection has a simple
transverse zero relative to its value at the chosen point. -/
theorem fillingNoncentral_transverse_order (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : Filling j v hv)
    (hy : fillingProjection j v hv y ≠ Elliptic.discZero) :
    analyticOrderAt (fun z : ℂ => transverseProjection j v hv y z -
      (fillingProjection j v hv y : ℂ)) (chartAt FamilyModel y y).1 = 1 := by
  have hc : (chartAt FamilyModel y y).1 ≠ 0 :=
    mt (fillingCentral_chart_iff j v hv y y (mem_chart_source FamilyModel y)).mpr hy
  have he : (fun z : ℂ => transverseProjection j v hv y z -
        (fillingProjection j v hv y : ℂ)) =ᶠ[𝓝 (chartAt FamilyModel y y).1]
      (fun z : ℂ => z ^ j.order - (chartAt FamilyModel y y).1 ^ j.order) :=
    (transverseProjection_eventuallyEq j v hv y).mono fun z hz => by
      dsimp only at hz ⊢
      rw [hz, fillingProjection_chart j v hv y y (mem_chart_source FamilyModel y)]
  rw [analyticOrderAt_congr he]
  exact complexPower_order_at_nonzero j.order j.order_pos _ hc

end Wikipedia.HopfProblem.Elliptic
