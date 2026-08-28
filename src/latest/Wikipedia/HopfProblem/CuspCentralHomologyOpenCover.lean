import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverFibres
import Wikipedia.HopfProblem.CuspCentralHomologyRadialGauge

/-!
# The radial open cover of the actual central cusp fibre

The radial coordinate of the literal fundamental hexagon descends to the
original central quotient: an interior representative is unique, and all
other identifications lie on the unit-gauge frontier. Its unit level is
exactly the image of the compact phases over that frontier. The strict
radial sublevel and an outer collar give genuine open subsets covering
the original central fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

def fundamentalRadius (p : FundamentalCell) : ℝ := Radial.cellGauge (p.2 : Plane)

theorem fundamentalRadius_continuous : Continuous fundamentalRadius :=
  Radial.cellGauge_continuous.comp (continuous_subtype_val.comp continuous_snd)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The gauge is constant on the exact fibres of the actual compact
fundamental-cell map, including its boundary identifications. -/
theorem fundamentalRadius_eq_of_map_eq (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    fundamentalRadius p = fundamentalRadius q := by
  change Radial.cellGauge (p.2 : Plane) = Radial.cellGauge (q.2 : Plane)
  rcases fundamentalCellMap_eq_base_or_frontier C ε hε p q h with he | ⟨hp, hq⟩
  · exact congrArg Radial.cellGauge he
  · rw [(Radial.mem_frontier_baseCell_iff _).mp hp,
      (Radial.mem_frontier_baseCell_iff _).mp hq]

/-- The actual radial coordinate on the original central cusp fibre. -/
def centralRadius : QuotientCentralFibre C ε → ℝ :=
  CuspHoneycombHexagon.CommonFibres.descend (fundamentalCellMap C ε hε)
    fundamentalRadius (fundamentalCellMap_surjective C ε hε)

@[simp] theorem centralRadius_fundamentalCellMap (p : FundamentalCell) :
    centralRadius C ε hε (fundamentalCellMap C ε hε p) = Radial.cellGauge (p.2 : Plane) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (fundamentalCellMap C ε hε)
    fundamentalRadius (fundamentalCellMap_surjective C ε hε)
    (fundamentalRadius_eq_of_map_eq C ε hε) p

theorem centralRadius_mem_Icc (q : QuotientCentralFibre C ε) :
    centralRadius C ε hε q ∈ Icc 0 1 := by
  obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
  rw [centralRadius_fundamentalCellMap]
  exact ⟨Radial.cellGauge_nonneg _, (Radial.mem_baseCell_iff _).mp p.2.2⟩

theorem centralRadius_nonneg (q : QuotientCentralFibre C ε) :
    0 ≤ centralRadius C ε hε q := (centralRadius_mem_Icc C ε hε q).1

theorem centralRadius_le_one (q : QuotientCentralFibre C ε) :
    centralRadius C ε hε q ≤ 1 := (centralRadius_mem_Icc C ε hε q).2

private theorem gauge_halfAxis : Radial.cellGauge (![1 / 2, 0] : Plane) = 1 := by
  norm_num [Radial.cellGauge]

/-- A concrete radial interval in the literal fundamental hexagon. -/
def radialAxisPoint (t : unitInterval) : baseCell :=
  ⟨(t : ℝ) • (![1 / 2, 0] : Plane), (Radial.mem_baseCell_iff _).mpr (by
    rw [Radial.cellGauge_smul_of_nonneg _ t.2.1, gauge_halfAxis, mul_one]
    exact t.2.2)⟩

@[simp] theorem radialAxisPoint_gauge (t : unitInterval) :
    Radial.cellGauge (radialAxisPoint t : Plane) = (t : ℝ) := by
  change Radial.cellGauge ((t : ℝ) • (![1 / 2, 0] : Plane)) = _
  rw [Radial.cellGauge_smul_of_nonneg _ t.2.1, gauge_halfAxis, mul_one]

theorem radialAxisPoint_continuous : Continuous radialAxisPoint :=
  (continuous_subtype_val.smul continuous_const).subtype_mk _

/-- Every radius in the closed unit interval is realized by actual points
of the central quotient, along a continuous radial section. -/
def centralRadiusSection (t : unitInterval) : QuotientCentralFibre C ε :=
  fundamentalCellMap C ε hε (1, radialAxisPoint t)

theorem centralRadiusSection_continuous : Continuous (centralRadiusSection C ε hε) :=
  (fundamentalCellMap_continuous C ε hε).comp
    (continuous_const.prodMk radialAxisPoint_continuous)

@[simp] theorem centralRadius_section (t : unitInterval) :
    centralRadius C ε hε (centralRadiusSection C ε hε t) = (t : ℝ) := by
  rw [centralRadiusSection, centralRadius_fundamentalCellMap, radialAxisPoint_gauge]

theorem centralRadius_range : range (centralRadius C ε hε) = Icc 0 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q, rfl⟩
    exact centralRadius_mem_Icc C ε hε q
  · intro r hr
    exact ⟨centralRadiusSection C ε hε ⟨r, hr⟩, centralRadius_section C ε hε ⟨r, hr⟩⟩

/-- The actual boundary locus, defined intrinsically by the descended radius. -/
def centralBoundary : Set (QuotientCentralFibre C ε) := {q | centralRadius C ε hε q = 1}

/-- The outer radial region used in the genuine open cover. -/
def outerRegion (a : ℝ) : Set (QuotientCentralFibre C ε) := {q | a < centralRadius C ε hε q}

/-- The actual open-cell region of the central fibre. -/
def innerRegion : Set (QuotientCentralFibre C ε) := {q | centralRadius C ε hε q < 1}

theorem fundamentalCellMap_mem_centralBoundary_iff (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ centralBoundary C ε hε ↔
      (p.2 : Plane) ∈ frontier baseCell := by
  change centralRadius C ε hε (fundamentalCellMap C ε hε p) = 1 ↔ _
  rw [centralRadius_fundamentalCellMap]
  exact (Radial.mem_frontier_baseCell_iff _).symm

theorem fundamentalCellMap_mem_innerRegion_iff (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ innerRegion C ε hε ↔
      (p.2 : Plane) ∈ interior baseCell := by
  change centralRadius C ε hε (fundamentalCellMap C ε hε p) < 1 ↔ _
  rw [centralRadius_fundamentalCellMap]
  exact (Radial.mem_interior_baseCell_iff _).symm

/-- The radius-one locus is exactly the image of compact phases over the
literal hexagon frontier under the already constructed central collapse. -/
theorem centralBoundary_eq_image :
    centralBoundary C ε hε = honeycombCollapseMap C ε hε ''
      ((univ : Set CompactFibreTorus) ×ˢ frontier baseCell) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
    exact ⟨(p.1, (p.2 : Plane)),
      ⟨mem_univ _, (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mp hq⟩, rfl⟩
  · rintro ⟨⟨φ, x⟩, ⟨_, hx⟩, rfl⟩
    let p : FundamentalCell := (φ, ⟨x, baseCell_isClosed.frontier_subset hx⟩)
    exact (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mpr hx

theorem innerRegion_eq_compl_centralBoundary :
    innerRegion C ε hε = (centralBoundary C ε hε)ᶜ := by
  ext q
  change centralRadius C ε hε q < 1 ↔ ¬centralRadius C ε hε q = 1
  exact ⟨fun h => h.ne, fun h => lt_of_le_of_ne (centralRadius_le_one C ε hε q) h⟩

theorem centralBoundary_subset_outerRegion (a : ℝ) (ha : a < 1) :
    centralBoundary C ε hε ⊆ outerRegion C ε hε a := by
  intro q hq
  change a < centralRadius C ε hε q
  change centralRadius C ε hε q = 1 at hq
  rwa [hq]

/-- These two actual subsets cover the original central fibre for every
collar threshold below one. -/
theorem outerRegion_union_innerRegion (a : ℝ) (ha : a < 1) :
    outerRegion C ε hε a ∪ innerRegion C ε hε = univ := by
  apply Set.eq_univ_of_forall
  intro q
  by_cases hq : centralRadius C ε hε q < 1
  · exact Or.inr hq
  · exact Or.inl (ha.trans_le (le_of_not_gt hq))

section Topology

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR

theorem centralRadius_continuous : Continuous (centralRadius C ε hε) :=
  CuspHoneycombHexagon.CommonFibres.descend_continuous (fundamentalCellMap C ε hε)
    fundamentalRadius (fundamentalCellMap_surjective C ε hε)
    (fundamentalCellMap_isQuotientMap C ε hε hε1 hC hR) fundamentalRadius_continuous
    (fundamentalRadius_eq_of_map_eq C ε hε)

theorem centralBoundary_isClosed : IsClosed (centralBoundary C ε hε) :=
  isClosed_eq (centralRadius_continuous C ε hε hε1 hC hR) continuous_const

theorem outerRegion_isOpen (a : ℝ) : IsOpen (outerRegion C ε hε a) :=
  isOpen_lt continuous_const (centralRadius_continuous C ε hε hε1 hC hR)

theorem innerRegion_isOpen : IsOpen (innerRegion C ε hε) :=
  isOpen_lt (centralRadius_continuous C ε hε hε1 hC hR) continuous_const

end Topology

end Wikipedia.HopfProblem.CuspCentralHomology
