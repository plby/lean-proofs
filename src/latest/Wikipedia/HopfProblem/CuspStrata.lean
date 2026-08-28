import Wikipedia.HopfProblem.ToricStrata
import Wikipedia.HopfProblem.CuspNormalCrossings

/-!
# The toric triple stratum of the cusp quotient

The chart-independent count of vanishing coordinates descends through
the twisted action. Count three is precisely the image of chart origins.
These origins have exactly two orbits, represented by the lower and
upper reference triangles.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan

theorem time_normalCrossingChartAt (s : Triangle) (z : CoordinateSpace 3)
    (hz : Triangle.time z = 0) :
    NormalCrossingChartAt (vanishingIndices z) time (inclusion s z) := by
  have hp := normalCrossingChartAt_product z (vanishingIndices z)
    ((vanishingIndices_nonempty z).mpr hz)
    (fun j hj => (mem_vanishingIndices z j).mp hj)
    (fun j hj hzero => hj ((mem_vanishingIndices z j).mpr hzero))
  have he : (parametrization s).symm ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self s)
  have hx : inclusion s z ∈ (parametrization s).target := by
    rw [parametrization_target]
    exact mem_range_self z
  have heval : (parametrization s).symm (inclusion s z) = z :=
    (parametrization s).left_inv (Set.mem_univ z)
  have hp' : NormalCrossingChartAt (vanishingIndices z) Triangle.time
      ((parametrization s).symm (inclusion s z)) := by
    simpa only [heval] using hp
  exact hp'.of_chart (parametrization s).symm he hx (fun w _ => time_inclusion s w)

end Wikipedia.HopfProblem.ToricSpace

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

def branchCount : QuotientSpace C ε → ℕ :=
  Quotient.lift (fun x : Tube (disc ε) => ToricSpace.branchCount (x : Space)) (by
    let := tubeAction C (disc ε)
    intro x y h
    change x ∈ MulAction.orbit LatticeGroup y at h
    obtain ⟨g, rfl⟩ := h
    exact branchCount_twistedTranslate C g.toAdd y)

@[simp] theorem branchCount_quotientMap (x : Tube (disc ε)) :
    branchCount C ε (quotientMap C ε x) = ToricSpace.branchCount (x : Space) := rfl

theorem branchCount_le_three (x : QuotientSpace C ε) : branchCount C ε x ≤ 3 := by
  induction x using Quotient.inductionOn with
  | h x => exact ToricSpace.branchCount_le_three x

theorem branchCount_pos_iff (x : QuotientSpace C ε) :
    0 < branchCount C ε x ↔ projection C ε x = 0 := by
  induction x using Quotient.inductionOn with
  | h x => exact ToricSpace.branchCount_pos_iff x

variable (hε : 0 < ε)

@[simp] theorem branchCount_centralChartMap (s : Triangle) (z : centralAffine) :
    branchCount C ε (centralChartMap C ε hε s z) = zeroCount z :=
  ToricSpace.branchCount_inclusion s z

include hε in
theorem branchCount_eq_three (x : QuotientSpace C ε) : branchCount C ε x = 3 ↔
    ∃ s : Triangle, centralChartMap C ε hε s centralOrigin = x := by
  constructor
  · induction x using Quotient.inductionOn with
    | h a =>
      intro ha
      obtain ⟨s, hs⟩ := (ToricSpace.branchCount_eq_three (a : Space)).mp ha
      refine ⟨s, ?_⟩
      apply congrArg (quotientMap C ε)
      exact Subtype.ext hs
  · rintro ⟨s, rfl⟩
    rw [branchCount_centralChartMap]
    exact zeroCount_zero

theorem centralChartMap_origin_eq_iff (s t : Triangle) :
    centralChartMap C ε hε s centralOrigin = centralChartMap C ε hε t centralOrigin ↔
      s.upper = t.upper := by
  let := tubeAction C (disc ε)
  constructor
  · intro he
    have horb := Quotient.exact he
    change centralLift ε hε s centralOrigin ∈
      MulAction.orbit LatticeGroup (centralLift ε hε t centralOrigin) at horb
    obtain ⟨g, hg⟩ := horb
    have he' : twistedTranslate C g.toAdd (inclusion t 0) = inclusion s 0 :=
      congrArg Subtype.val hg
    rw [twistedTranslate_origin] at he'
    have hst := (inclusion_origin_injective _ _).mp he'
    exact (congrArg Triangle.upper hst).symm
  · intro hst
    rw [centralChartMap_origin_reference C ε hε s, centralChartMap_origin_reference C ε hε t, hst]

def lowerTriplePoint : QuotientSpace C ε := centralChartMap C ε hε ⟨0, 0, false⟩ centralOrigin

def upperTriplePoint : QuotientSpace C ε := centralChartMap C ε hε ⟨0, 0, true⟩ centralOrigin

theorem triplePoints_distinct : lowerTriplePoint C ε hε ≠ upperTriplePoint C ε hε := by
  intro he
  have h := (centralChartMap_origin_eq_iff C ε hε ⟨0, 0, false⟩ ⟨0, 0, true⟩).mp he
  exact Bool.false_ne_true h

include hε in
theorem tripleStratum_eq : {x : QuotientSpace C ε | branchCount C ε x = 3} =
    {lowerTriplePoint C ε hε, upperTriplePoint C ε hε} := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, rfl⟩ := (branchCount_eq_three C ε hε x).mp hx
    rw [centralChartMap_origin_reference]
    cases hs : s.upper
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact (branchCount_eq_three C ε hε _).mpr ⟨⟨0, 0, false⟩, rfl⟩
    · exact (branchCount_eq_three C ε hε _).mpr ⟨⟨0, 0, true⟩, rfl⟩

include hε in
theorem tripleStratum_card : ({x : QuotientSpace C ε | branchCount C ε x = 3}).ncard = 2 := by
  rw [tripleStratum_eq C ε hε]
  exact Set.ncard_pair (triplePoints_distinct C ε hε)

@[simp] theorem projection_lowerTriplePoint : projection C ε (lowerTriplePoint C ε hε) = 0 :=
  projection_centralChartMap C ε hε _ _

@[simp] theorem projection_upperTriplePoint : projection C ε (upperTriplePoint C ε hε) = 0 :=
  projection_centralChartMap C ε hε _ _

theorem normalCrossingChart_with_branchCount (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (x : QuotientSpace C ε) (hx : projection C ε x = 0) :
    letI := chartedSpace C ε hε hε1 hC hR
    ∃ J : Finset (Fin 3), J.card = branchCount C ε x ∧ J.Nonempty ∧
      NormalCrossingChartAt J (projection C ε) x := by
  let := tubeAction C (disc ε)
  let hq := quotientMap_covering C ε hε hε1 hC hR
  obtain ⟨a, rfl⟩ := hq.surjective x
  obtain ⟨s, z, hz⟩ := inclusion_jointly_surjective (a : Space)
  have ht : Triangle.time z = 0 := by
    rw [← time_inclusion s z, hz]
    exact hx
  have hup : NormalCrossingChartAt (vanishingIndices z) time (a : Space) := by
    simpa only [hz] using time_normalCrossingChartAt s z ht
  have hrest := hup.restrict (tubeOpen (disc ε)) a
  have h' : NormalCrossingChartAt (vanishingIndices z) (projection C ε ∘ quotientMap C ε) a := by
    simpa only [Function.comp_def, projection_quotientMap] using hrest
  refine ⟨vanishingIndices z, ?_, (vanishingIndices_nonempty z).mpr ht,
    h'.descend hq (fun v => tubeTranslate_holomorphic C (disc ε) v.toAdd hC)⟩
  rw [vanishingIndices_card, branchCount_quotientMap, ← hz, ToricSpace.branchCount_inclusion]

/-- At each of the two points in the toric triple stratum the centred
analytic local equation is exactly `z₀z₁z₂`. -/
theorem triple_local_equation (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (x : QuotientSpace C ε) (hx : branchCount C ε x = 3) :
    letI := chartedSpace C ε hε hε1 hC hR
    ∃ e : OpenPartialHomeomorph (QuotientSpace C ε) (CoordinateSpace 3),
      e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
        (QuotientSpace C ε) ∧ x ∈ e.source ∧ e x = 0 ∧
      ∀ w ∈ e.target, projection C ε (e.symm w) = w 0 * w 1 * w 2 := by
  let := chartedSpace C ε hε hε1 hC hR
  have hx0 : projection C ε x = 0 := (branchCount_pos_iff C ε x).mp (by omega)
  obtain ⟨J, hcard, _, e, he, hxs, hc, hp⟩ :=
    normalCrossingChart_with_branchCount C ε hε hε1 hC hR x hx0
  have hJ : J = Finset.univ := Finset.eq_univ_of_card J (by simpa [hx] using hcard)
  refine ⟨e, he, hxs, hc, ?_⟩
  intro w hw
  rw [hp w hw, hJ]
  simp [Fin.prod_univ_succ, mul_assoc]

end Wikipedia.HopfProblem.CuspQuotient
