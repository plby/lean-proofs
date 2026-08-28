import Wikipedia.HopfProblem.ToricProperAction
import Wikipedia.HopfProblem.CoveringManifold
import Mathlib.GroupTheory.OrderOfElement

/-!
# The complex cusp quotient

The established compact-set estimates make the twisted lattice action
properly discontinuous. Its stabilizers are finite subgroups of a
torsion-free group, so the action is free. This constructs the actual
Hausdorff complex quotient and its holomorphic covering map.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace

abbrev LatticeGroup := Multiplicative (Fin 2 → ℤ)

def disc (ε : ℝ) : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 ε, Metric.isOpen_ball⟩

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

instance tube_locallyCompactSpace : LocallyCompactSpace (Tube (disc ε)) :=
  ChartedSpace.locallyCompactSpace (CoordinateSpace 3) (Tube (disc ε))

theorem continuous_action
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    letI := tubeAction C (disc ε)
    ContinuousConstSMul LatticeGroup (Tube (disc ε)) := by
  let := tubeAction C (disc ε)
  exact ⟨fun v => (tubeTranslate_holomorphic C (disc ε) v.toAdd hC).continuous⟩

theorem proper_action (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := tubeAction C (disc ε)
    ProperlyDiscontinuousSMul LatticeGroup (Tube (disc ε)) := by
  let := tubeAction C (disc ε)
  constructor
  intro K L hK hL
  let K' : Set Space := Subtype.val '' (K ∪ L)
  have hK' : IsCompact K' := (hK.union hL).image continuous_subtype_val
  have hKt : ∀ x ∈ K', ‖time x‖ < ε := by
    rintro _ ⟨x, _, rfl⟩
    have hx : time (x : Space) ∈ Metric.ball 0 ε := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hfinite := compact_translates_finite C hε hε1 hC hR hK' hKt
  have hinj : Function.Injective (fun g : LatticeGroup => g.toAdd) :=
    fun _ _ h => congrArg Multiplicative.ofAdd h
  apply (hfinite.preimage hinj.injOn).subset
  rintro g ⟨q, ⟨p, hp, hpq⟩, hq⟩
  refine ⟨(q : Space), ⟨(p : Space), ⟨p, Or.inl hp, rfl⟩, ?_⟩, ⟨q, Or.inr hq, rfl⟩⟩
  exact congrArg Subtype.val hpq

theorem free_action (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := tubeAction C (disc ε)
    IsCancelSMul LatticeGroup (Tube (disc ε)) := by
  let := tubeAction C (disc ε)
  let := proper_action C ε hε hε1 hC hR
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hg
  let H := MulAction.stabilizer LatticeGroup x
  let : Finite H := ProperlyDiscontinuousSMul.finite_stabilizer x
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite (⟨g, hg⟩ : H)).exists_pow_eq_one
  have he : g ^ n = 1 := congrArg Subtype.val hpow
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, he⟩).eq_one'

def relation : Setoid (Tube (disc ε)) :=
  letI := tubeAction C (disc ε)
  MulAction.orbitRel LatticeGroup (Tube (disc ε))

abbrev QuotientSpace := Quotient (relation C ε)

def quotientMap : Tube (disc ε) → QuotientSpace C ε := Quotient.mk (relation C ε)

theorem quotientMap_continuous : Continuous (quotientMap C ε) := continuous_quotient_mk'

@[simp] theorem quotientMap_translate (v : Fin 2 → ℤ) (x : Tube (disc ε)) :
    quotientMap C ε (tubeTranslate C (disc ε) v x) = quotientMap C ε x := by
  let := tubeAction C (disc ε)
  exact MulAction.orbitRel.Quotient.quotient_smul_eq
    (g := Multiplicative.ofAdd v) (a := x)

/-- The invariant monomial descends to the actual orbit quotient. -/
def projection : QuotientSpace C ε → ℂ :=
  Quotient.lift (fun x : Tube (disc ε) => time (x : Space)) (by
    let := tubeAction C (disc ε)
    intro x y h
    change x ∈ MulAction.orbit LatticeGroup y at h
    obtain ⟨g, rfl⟩ := h
    exact time_twistedTranslate C g.toAdd y)

@[simp] theorem projection_quotientMap (x : Tube (disc ε)) :
    projection C ε (quotientMap C ε x) = time (x : Space) := rfl

theorem projection_mem_disc (x : QuotientSpace C ε) : projection C ε x ∈ disc ε := by
  induction x using Quotient.inductionOn with
  | h x => exact x.2

def baseMap (x : QuotientSpace C ε) : disc ε :=
  ⟨projection C ε x, projection_mem_disc C ε x⟩

theorem projection_continuous : Continuous (projection C ε) :=
  (time_holomorphic.continuous.comp continuous_subtype_val).quotient_lift _

theorem baseMap_continuous : Continuous (baseMap C ε) :=
  (projection_continuous C ε).subtype_mk _

theorem baseMap_surjective : Function.Surjective (baseMap C ε) := by
  intro t
  obtain ⟨x, hx⟩ := time_surjective (t : ℂ)
  have hxt : x ∈ tubeOpen (disc ε) := by
    change time x ∈ disc ε
    rw [hx]
    exact t.2
  exact ⟨quotientMap C ε ⟨x, hxt⟩, Subtype.ext hx⟩

theorem quotientMap_covering (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := tubeAction C (disc ε)
    IsQuotientCoveringMap (quotientMap C ε) LatticeGroup := by
  let := tubeAction C (disc ε)
  let := continuous_action C ε hC
  let := proper_action C ε hε hε1 hC hR
  let := free_action C ε hε hε1 hC hR
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem quotient_t2Space (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : T2Space (QuotientSpace C ε) := by
  let := tubeAction C (disc ε)
  let := continuous_action C ε hC
  let := proper_action C ε hε hε1 hC hR
  change T2Space (Quotient (MulAction.orbitRel LatticeGroup (Tube (disc ε))))
  infer_instance

@[instance_reducible] def chartedSpace (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : ChartedSpace (CoordinateSpace 3) (QuotientSpace C ε) :=
  letI := tubeAction C (disc ε)
  CoveringQuotient.chartedSpace (E := CoordinateSpace 3) (quotientMap_covering C ε hε hε1 hC hR)

theorem isManifold (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    IsManifold (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (QuotientSpace C ε) := by
  let := tubeAction C (disc ε)
  exact CoveringQuotient.isManifold (E := CoordinateSpace 3)
    (quotientMap_covering C ε hε hε1 hC hR) ω
    (fun v => tubeTranslate_holomorphic C (disc ε) v.toAdd hC)

theorem quotientMap_holomorphic (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (quotientMap C ε) := by
  let := tubeAction C (disc ε)
  exact CoveringQuotient.contMDiff_project (E := CoordinateSpace 3)
    (quotientMap_covering C ε hε hε1 hC hR) ω
    (fun v => tubeTranslate_holomorphic C (disc ε) v.toAdd hC)

theorem projection_holomorphic (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ ℂ) ω (projection C ε) := by
  let := tubeAction C (disc ε)
  apply CoveringQuotient.contMDiff_of_comp (E := CoordinateSpace 3)
    (quotientMap_covering C ε hε hε1 hC hR) (modelWithCornersSelf ℂ ℂ) ω
  exact time_holomorphic.comp contMDiff_subtype_val

theorem baseMap_holomorphic (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ ℂ) ω (baseMap C ε) := by
  let := chartedSpace C ε hε hε1 hC hR
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ ℂ) ω (fun y => (baseMap C ε y : ℂ)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 3))
      (modelWithCornersSelf ℂ ℂ) ω (baseMap C ε) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (projection_holomorphic C ε hε hε1 hC hR x)

/-- Holomorphic data on any neighbourhood of zero give an admissible cusp radius. -/
theorem exists_admissible_radius {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ∧ ε < 1 ∧ SmallDrift C ε ∧
      ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε) := by
  have hC0 : ∀ i j, ContinuousAt (fun z => C z i j) 0 := by
    intro i j
    exact (hC i j).continuousOn.continuousAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hr))
  obtain ⟨δ, hδ, hδ1, hR⟩ := exists_smallDrift_radius C hC0
  refine ⟨min δ (r / 2), lt_min hδ (half_pos hr),
    (min_le_right _ _).trans_lt (half_lt_self hr), (min_le_left _ _).trans_lt hδ1,
    hR.mono (min_le_left _ _), ?_⟩
  intro i j
  exact (hC i j).mono (Metric.ball_subset_ball
    ((min_le_right _ _).trans (half_le_self hr.le)))

end Wikipedia.HopfProblem.CuspQuotient
