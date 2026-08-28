import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyQuotient
import Wikipedia.HopfProblem.CuspPuncturedQuotient

/-!
# Whole-family comparison with the actual punctured cusp

The actual quotient by the varying four-dimensional period lattice,
followed by clockwise integer monodromy, has exactly the full logarithmic
deck relation.  The comparison of the two quotient manifolds is analytic
in both directions by their actual local covering lifts.  Composing with
the toric exponential uniformization identifies the entire punctured
family, over the punctured base disc, with the constructed cusp space.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data

open ToricCharts ToricSpace CuspUniformization

local notation "Ilog" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

variable (D : CuspFamily.Data)

/-- The first period quotient identifies only points already identified
by the full logarithmic deck quotient. -/
theorem totalPeriodQuotientMap_eq_of_familyCover_eq {x y : LogCover D.radius}
    (h : D.familyCover x = D.familyCover y) :
    totalPeriodQuotientMap D.correction D.radius x =
      totalPeriodQuotientMap D.correction D.radius y := by
  obtain ⟨hs, m, n, hmn⟩ := (D.familyCover_eq_iff x y).mp h
  apply (totalPeriodQuotientMap_eq_iff D.correction D.radius x y).mpr
  exact ⟨0, m, n, by simpa only [Int.cast_zero, add_zero] using hs, hmn⟩

theorem iteratedCover_logDeck (g : LogDeck) (x : LogCover D.radius) :
    D.iteratedCover (logCoverTransform D.correction D.radius g x) = D.iteratedCover x := by
  let := D.totalAction
  change D.quotient (D.familyCover (logCoverTransform D.correction D.radius g x)) =
    D.quotient (D.familyCover x)
  rw [D.familyCover_logDeck, D.quotient_smul]

/-- Equality after both genuine quotient operations is exactly the
explicit full period-and-logarithm relation on the original vector cover. -/
theorem iteratedCover_eq_iff (x y : LogCover D.radius) :
    D.iteratedCover x = D.iteratedCover y ↔ TotalPeriodRelated D.correction x y := by
  let := D.totalAction
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (D.quotient_eq_iff (D.familyCover x) (D.familyCover y)).mp h
    let z := logCoverTransform D.correction D.radius ⟨-k.toAdd, 0, 0⟩ y
    have hz : D.familyCover z = k • D.familyCover y := by
      simpa only [neg_neg, ofAdd_toAdd] using
        D.familyCover_logarithmicShift (-k.toAdd) y
    have hxy := D.totalPeriodQuotientMap_eq_of_familyCover_eq (hk.symm.trans hz.symm)
    have hzy : totalPeriodQuotientMap D.correction D.radius z =
        totalPeriodQuotientMap D.correction D.radius y := by
      apply (totalPeriodQuotientMap_eq_iff D.correction D.radius z y).mpr
      exact ⟨-k.toAdd, 0, 0, rfl, rfl⟩
    exact (totalPeriodQuotientMap_eq_iff D.correction D.radius x y).mp (hxy.trans hzy)
  · intro h
    obtain ⟨g, hg⟩ := (totalPeriodRelated_iff_exists_logDeck D.correction x y).mp h
    have he : logCoverTransform D.correction D.radius g y = x := Subtype.ext hg
    rw [← he, D.iteratedCover_logDeck]

/-- The comparison is induced by the two actual quotient projections. -/
def directToIterated : TotalPeriodQuotient D.correction D.radius → D.Space :=
  Quotient.lift D.iteratedCover (fun x y h => (D.iteratedCover_eq_iff x y).mpr h)

@[simp] theorem directToIterated_quotientMap (x : LogCover D.radius) :
    D.directToIterated (totalPeriodQuotientMap D.correction D.radius x) =
      D.iteratedCover x := rfl

theorem directToIterated_bijective : Function.Bijective D.directToIterated := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        intro he
        exact Quotient.sound ((D.iteratedCover_eq_iff x y).mp he)
  · intro y
    obtain ⟨x, rfl⟩ := D.iteratedCover_surjective y
    exact ⟨totalPeriodQuotientMap D.correction D.radius x, rfl⟩

def directToIteratedEquiv : TotalPeriodQuotient D.correction D.radius ≃ D.Space :=
  Equiv.ofBijective D.directToIterated D.directToIterated_bijective

@[simp] theorem directToIteratedEquiv_quotientMap (x : LogCover D.radius) :
    D.directToIteratedEquiv (totalPeriodQuotientMap D.correction D.radius x) =
      D.iteratedCover x := rfl

@[simp] theorem directToIteratedEquiv_symm_iteratedCover (x : LogCover D.radius) :
    D.directToIteratedEquiv.symm (D.iteratedCover x) =
      totalPeriodQuotientMap D.correction D.radius x :=
  D.directToIteratedEquiv.symm_apply_apply (totalPeriodQuotientMap D.correction D.radius x)

theorem directToIterated_holomorphic :
    letI := totalPeriodQuotientChartedSpace D.correction D.radius
      D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    ContMDiff Ilog Ilog ω D.directToIterated := by
  let := logCoverAction D.correction D.radius
  let := totalPeriodQuotientChartedSpace D.correction D.radius
    D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  apply CoveringQuotient.contMDiff_of_comp
    (totalPeriodQuotientMap_covering D.correction D.radius D.radius_pos D.radius_lt_one
      D.holomorphic D.smallDrift) Ilog ω
  exact D.iteratedCover_holomorphic

theorem directToIteratedEquiv_symm_holomorphic :
    letI := totalPeriodQuotientChartedSpace D.correction D.radius
      D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    ContMDiff Ilog Ilog ω D.directToIteratedEquiv.symm := by
  let := totalPeriodQuotientChartedSpace D.correction D.radius
    D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  apply contMDiff_of_comp_localDiffeomorph Ilog Ilog Ilog
    D.iteratedCover_isLocalDiffeomorph D.iteratedCover_surjective
  have he : D.directToIteratedEquiv.symm ∘ D.iteratedCover =
      totalPeriodQuotientMap D.correction D.radius :=
    funext D.directToIteratedEquiv_symm_iteratedCover
  rw [he]
  exact totalPeriodQuotientMap_holomorphic D.correction D.radius
    D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift

/-- The direct full-deck quotient and the iterated lattice-then-monodromy
quotient are biholomorphic in their independently constructed covering atlases. -/
def directQuotientBiholomorph :
    letI := totalPeriodQuotientChartedSpace D.correction D.radius
      D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
    letI := D.chartedSpace
    Diffeomorph Ilog Ilog (TotalPeriodQuotient D.correction D.radius) D.Space ω := by
  let := totalPeriodQuotientChartedSpace D.correction D.radius
    D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
  let := D.chartedSpace
  exact
    { toEquiv := D.directToIteratedEquiv
      contMDiff_toFun := D.directToIterated_holomorphic
      contMDiff_invFun := D.directToIteratedEquiv_symm_holomorphic }

/-- The entire actual period family, after clockwise cusp monodromy,
is biholomorphic to the actual punctured cusp, not just fibrewise. -/
def puncturedFamilyBiholomorph :
    letI := D.chartedSpace
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
      D.holomorphic D.smallDrift
    Diffeomorph Ilog I₃ D.Space (PuncturedQuotient D.correction D.radius) ω := by
  let := D.chartedSpace
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  let := totalPeriodQuotientChartedSpace D.correction D.radius
    D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
  exact D.directQuotientBiholomorph.symm.trans
    (totalUniformizationBiholomorph D.correction D.radius D.radius_pos D.radius_lt_one
      D.holomorphic D.smallDrift)

/-- On the original vector cover, the whole-family comparison is exactly
the actual toric exponential map followed by the cusp quotient. -/
@[simp] theorem puncturedFamilyBiholomorph_iteratedCover (x : LogCover D.radius) :
    letI := D.chartedSpace
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
      D.holomorphic D.smallDrift
    D.puncturedFamilyBiholomorph (D.iteratedCover x) =
      puncturedCuspCover D.correction D.radius x := by
  let := D.chartedSpace
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  let := totalPeriodQuotientChartedSpace D.correction D.radius
    D.radius_pos D.radius_lt_one D.holomorphic D.smallDrift
  change totalUniformizationBiholomorph D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift (D.directToIteratedEquiv.symm (D.iteratedCover x)) = _
  rw [D.directToIteratedEquiv_symm_iteratedCover,
    totalUniformizationBiholomorph_quotientMap]

/-- The whole-space biholomorphism is over the actual punctured base disc. -/
theorem puncturedFamilyBiholomorph_preserves_base (x : D.Space) :
    letI := D.chartedSpace
    letI := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
      D.holomorphic D.smallDrift
    CuspQuotient.projection D.correction D.radius (D.puncturedFamilyBiholomorph x) =
      (D.projection x : ℂ) := by
  let := D.chartedSpace
  let := CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one
    D.holomorphic D.smallDrift
  obtain ⟨y, rfl⟩ := D.iteratedCover_surjective x
  rw [D.puncturedFamilyBiholomorph_iteratedCover, D.projection_iteratedCover]
  exact projection_totalCuspCover D.correction D.radius y

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data
