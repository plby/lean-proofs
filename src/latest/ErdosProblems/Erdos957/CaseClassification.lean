import Mathlib
import ErdosProblems.Erdos957.GeometryCore
import ErdosProblems.Erdos957.Case13Bridge
import ErdosProblems.Erdos957.Case3General
import ErdosProblems.Erdos957.Case24Bridge
import ErdosProblems.Erdos957.Locality
import ErdosProblems.Erdos957.GeometryLocalRows
import ErdosProblems.Erdos957.ChartTransport
import ErdosProblems.Erdos957.MiddleLocalization
import ErdosProblems.Erdos957.TwoExtremeFrame
import ErdosProblems.Erdos957.TwoExtremeIncidence
import ErdosProblems.Erdos957.TwoExtremeAligned
import ErdosProblems.Erdos957.BisectorFrame
import ErdosProblems.Erdos957.ContactGraph

/-!
# Exhaustive local case classification for Erdős 957

This file isolates the logical four-way split in Dumitrescu's charging
argument.  The classification is made from the actual shortest-distance
graph and the actual cyclic-hull finset: it is not an abstract case label.

The second half records constructor interfaces for the checked coordinate
implementations of Cases 1--4.  Their hypotheses are incidences, supporting
half-plane statements, and regular-hexagon completion/exclusion facts.  In
particular, no global transfer-capacity or product estimate is assumed.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957CaseClassification

open Erdos957GeometryCore

abbrev ComplexPoint := Erdos957GeometryCore.Point

/-! ## Strict support of the genuine incident-bisector chart -/

namespace StrictBisectorSupport

open Erdos957
open Erdos957HullGeometryBridge
open Erdos957TurnSum
open Erdos957TurnSum.HullOrderBridge
open Erdos957BisectorFrame

/-- Two nonparallel rays have no nonzero common collinear vector. -/
private lemma eq_zero_of_two_det_eq_zero {u w v : ComplexPoint}
    (huw : det u w ≠ 0) (huv : det u v = 0) (hwv : det w v = 0) :
    v = 0 := by
  have hx : det u w * v 0 = 0 := by
    change u 0 * v 1 - u 1 * v 0 = 0 at huv
    change w 0 * v 1 - w 1 * v 0 = 0 at hwv
    change (u 0 * w 1 - u 1 * w 0) * v 0 = 0
    linear_combination w 0 * huv - u 0 * hwv
  have hy : det u w * v 1 = 0 := by
    change u 0 * v 1 - u 1 * v 0 = 0 at huv
    change w 0 * v 1 - w 1 * v 0 = 0 at hwv
    change (u 0 * w 1 - u 1 * w 0) * v 1 = 0
    linear_combination w 1 * huv - u 1 * hwv
  have hv0 : v 0 = 0 := (mul_eq_zero.mp hx).resolve_left huw
  have hv1 : v 1 = 0 := (mul_eq_zero.mp hy).resolve_left huw
  ext j
  fin_cases j
  · exact hv0
  · exact hv1

/-- The two genuine incident supports cannot both vanish away from their
common endpoint.  Their positive combination is the bisector support, so
the latter is strict at every other configuration point. -/
theorem bisectorCoord_snd_neg
    {A : Finset ComplexPoint} {P : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder P) (i : Fin (hullVertexCount A))
    (q : Erdos957GeometryCore.Vertex A)
    (hq : (q : ComplexPoint) ≠ P.vertex i) :
    (bisectorCoord L i q).2 < 0 := by
  exact Erdos957BisectorFrame.bisectorCoord_snd_neg L i q.property hq

/-- Transported strictness for the exact chart used by locality. -/
theorem bisectorAlignedChartData_coord_snd_neg
    {A : Finset ComplexPoint} (P : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder P)
    (source : {p // p ∈ (cyclicHullDataOfOrder P L).H})
    (q : Erdos957GeometryCore.Vertex A) (hq : q ≠ source.1) :
    ((bisectorAlignedChartData P L).coord source q).2 < 0 := by
  simpa [bisectorAlignedChartData] using
    Erdos957BisectorFrame.producedBisectorCoord_snd_neg P L source q hq

end StrictBisectorSupport

/-! ## The genuine graph/hull four-way split -/

/-- Hull vertices at unit distance from `v`. -/
def hullUnitNeighbors {A : Finset ComplexPoint} (P : CyclicHullData A)
    (v : Vertex A) : Finset (Vertex A) :=
  P.H.filter fun w ↦ (unitDistanceGraph A).Adj v w

@[simp] lemma mem_hullUnitNeighbors {A : Finset ComplexPoint}
    {P : CyclicHullData A} {v w : Vertex A} :
    w ∈ hullUnitNeighbors P v ↔ w ∈ P.H ∧ (unitDistanceGraph A).Adj v w := by
  simp [hullUnitNeighbors]

/-- The four alternatives in the paper, indexed by genuine graph data. -/
inductive FourCase {A : Finset ComplexPoint} (P : CyclicHullData A)
    (middle : Vertex A) : Prop
  | case1
      (middle_degree : (unitDistanceGraph A).degree middle = 6)
      (one_hull_neighbor : (hullUnitNeighbors P middle).card = 1)
  | case2
      (middle_degree : (unitDistanceGraph A).degree middle = 6)
      (two_hull_neighbors : (hullUnitNeighbors P middle).card = 2)
  | case3
      (middle_degree : (unitDistanceGraph A).degree middle ≤ 5)
      (one_hull_neighbor : (hullUnitNeighbors P middle).card = 1)
  | case4
      (middle_degree : (unitDistanceGraph A).degree middle ≤ 5)
      (two_hull_neighbors : (hullUnitNeighbors P middle).card = 2)

/-- Membership in `sourceVertices` really supplies all three advertised
properties: diameter endpoint, flatness, and degree three. -/
lemma source_facts {A : Finset ComplexPoint} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {source : Vertex A}
    (hs : source ∈ sourceVertices P W) :
    source ∈ W.D ∧ source ∈ P.flatVertices ∧
      (unitDistanceGraph A).degree source = 3 := by
  have hs' := Finset.mem_filter.mp hs
  exact ⟨(Finset.mem_inter.mp hs'.1).1, (Finset.mem_inter.mp hs'.1).2, hs'.2⟩

/-- Ambient flat-vertex membership is exactly flatness of the corresponding
cyclic index. -/
lemma mem_flatVertices_iff_isFlat {A : Finset ComplexPoint}
    (P : CyclicHullData A) (i : {p // p ∈ P.H}) :
    i.1 ∈ P.flatVertices ↔ P.IsFlat i := by
  classical
  constructor
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, hji⟩
    have hji' : j = i := Subtype.ext hji
    subst j
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    apply Finset.mem_map.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

/-- Unpacking the definition of the seven-flat window: every one of its
seven actual cyclic shifts has exterior turn strictly below one degree. -/
lemma turn_lt_one_degree_of_isFlat {A : Finset ComplexPoint}
    (P : CyclicHullData A) {i : {p // p ∈ P.H}} (hi : P.IsFlat i)
    (j : Fin 7) :
    P.turn (sevenShift P.next j i) < Real.pi / 180 := by
  rw [CyclicHullData.IsFlat, CyclicHullData.nonflatIndices] at hi
  have hnot : ¬ ∃ k : Fin 7,
      Real.pi / 180 ≤ P.turn (sevenShift P.next k i) := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  exact lt_of_not_ge (fun h ↦ hnot ⟨j, h⟩)

/-- A source-indexed form of the preceding fact. -/
lemma source_isFlat {A : Finset ComplexPoint} (P : CyclicHullData A)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) : P.IsFlat source := by
  exact (mem_flatVertices_iff_isFlat P source).mp (source_facts hs).2.1

@[simp] lemma sevenShift_three {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (3 : Fin 7) i = i := by
  simp [sevenShift]

@[simp] lemma sevenShift_four {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (4 : Fin 7) i = next i := by
  simp [sevenShift, pow_succ]

@[simp] lemma sevenShift_two {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (2 : Fin 7) i = next⁻¹ i := by
  simp [sevenShift, pow_succ]

/-- The three most frequently used consequences of seven-flatness. -/
lemma source_prev_self_next_turn_lt {A : Finset ComplexPoint}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (hs : source.1 ∈ sourceVertices P W) :
    P.turn (P.next⁻¹ source) < Real.pi / 180 ∧
      P.turn source < Real.pi / 180 ∧
      P.turn (P.next source) < Real.pi / 180 := by
  have hf := source_isFlat P W source hs
  exact ⟨by simpa using turn_lt_one_degree_of_isFlat P hf (2 : Fin 7),
    by simpa using turn_lt_one_degree_of_isFlat P hf (3 : Fin 7),
    by simpa using turn_lt_one_degree_of_isFlat P hf (4 : Fin 7)⟩

/-- In a triangle whose two sides meeting at `x` have length one, while
the opposite source chord has length at least one, the source angle is at
most sixty degrees.  This is the elementary common-unit-circle estimate
used to rule out simultaneous predecessor and successor incidences. -/
lemma angle_le_pi_div_three_of_common_unit
    {x y : ComplexPoint} (hx : ‖x‖ = 1) (hyx : ‖y - x‖ = 1)
    (hy : 1 ≤ ‖y‖) :
    InnerProductGeometry.angle x y ≤ Real.pi / 3 := by
  have hcosine :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
      y x
  have hynorm : 0 < ‖y‖ := lt_of_lt_of_le (by norm_num) hy
  have hcosEq : ‖y‖ =
      2 * Real.cos (InnerProductGeometry.angle x y) := by
    rw [InnerProductGeometry.angle_comm]
    rw [hyx, hx] at hcosine
    have hmul : ‖y‖ * ‖y‖ =
        ‖y‖ * (2 * Real.cos (InnerProductGeometry.angle y x)) := by
      nlinarith
    exact (mul_left_cancel₀ (ne_of_gt hynorm) hmul)
  have hcosLower : (1 / 2 : ℝ) ≤
      Real.cos (InnerProductGeometry.angle x y) := by
    nlinarith
  by_contra hnot
  have hangle : Real.pi / 3 < InnerProductGeometry.angle x y :=
    lt_of_not_ge hnot
  have hcosStrict := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ Real.pi / 3)
    (InnerProductGeometry.angle_le_pi x y) hangle
  rw [Real.cos_pi_div_three] at hcosStrict
  linarith

/-- At a flat strict-hull source, the selected unit middle cannot also be
unit-adjacent to both cyclic hull neighbours.  Each such incidence would
put the corresponding hull edge within sixty degrees of the inward middle
ray, forcing the hull angle to be at most 120 degrees, whereas flatness
makes it greater than 179 degrees. -/
theorem not_both_cyclic_neighbors_adjacent_to_middle
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (hs : source.1 ∈ sourceVertices P W)
    (middle : Vertex A) (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hprev : (unitDistanceGraph A).Adj middle (P.next⁻¹ source).1)
    (hnext : (unitDistanceGraph A).Adj middle (P.next source).1) : False := by
  let m : ComplexPoint := (middle : ComplexPoint) - source.1.1
  let p : ComplexPoint := (P.next⁻¹ source).1.1 - source.1.1
  let q : ComplexPoint := (P.next source).1.1 - source.1.1
  have hmnorm : ‖m‖ = 1 := by
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsm
    simpa [m, dist_eq_norm, norm_sub_rev] using hsm
  have hpmnorm : ‖p - m‖ = 1 := by
    rw [show p - m = (P.next⁻¹ source).1.1 - (middle : ComplexPoint) by
      dsimp [p, m]; abel]
    change dist (middle : ComplexPoint) (P.next⁻¹ source).1.1 = 1 at hprev
    simpa [dist_eq_norm, norm_sub_rev] using hprev
  have hqmnorm : ‖q - m‖ = 1 := by
    rw [show q - m = (P.next source).1.1 - (middle : ComplexPoint) by
      dsimp [q, m]; abel]
    change dist (middle : ComplexPoint) (P.next source).1.1 = 1 at hnext
    simpa [dist_eq_norm, norm_sub_rev] using hnext
  have hpne : (P.next⁻¹ source).1.1 ≠ source.1.1 := by
    intro h
    exact P.prev_ne_self source (Subtype.ext (Subtype.ext h))
  have hqne : (P.next source).1.1 ≠ source.1.1 := by
    intro h
    exact P.next_ne_self source (Subtype.ext (Subtype.ext h))
  have hpnorm : 1 ≤ ‖p‖ := by
    simpa [p, dist_eq_norm] using hA (P.next⁻¹ source).1
      (P.next⁻¹ source).1.property source.1 source.1.property hpne
  have hqnorm : 1 ≤ ‖q‖ := by
    simpa [q, dist_eq_norm] using hA (P.next source).1
      (P.next source).1.property source.1 source.1.property hqne
  have hamp : InnerProductGeometry.angle m p ≤ Real.pi / 3 :=
    angle_le_pi_div_three_of_common_unit hmnorm hpmnorm hpnorm
  have hamq : InnerProductGeometry.angle m q ≤ Real.pi / 3 :=
    angle_le_pi_div_three_of_common_unit hmnorm hqmnorm hqnorm
  have hpq : InnerProductGeometry.angle p q ≤ 2 * Real.pi / 3 := by
    calc
      InnerProductGeometry.angle p q ≤
          InnerProductGeometry.angle p m + InnerProductGeometry.angle m q :=
        InnerProductGeometry.angle_le_angle_add_angle p m q
      _ = InnerProductGeometry.angle m p + InnerProductGeometry.angle m q := by
        rw [InnerProductGeometry.angle_comm p m]
      _ ≤ 2 * Real.pi / 3 := by linarith
  have hflat := (source_prev_self_next_turn_lt P W source hs).2.1
  rw [P.turn_eq] at hflat
  change Real.pi - InnerProductGeometry.angle p q < Real.pi / 180 at hflat
  linarith [Real.pi_pos]

/-- The exact cyclic-neighbour localization needed after the global
flat-chain/chord argument.  Unlike the earlier `hconsecutive` premise, this
allows both cyclic sides; the flat common-unit estimate proves internally
that they cannot both occur. -/
theorem hullUnitNeighbors_card_le_two_of_cyclic_localization
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (hs : source.1 ∈ sourceVertices P W)
    (middle : Vertex A) (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hlocal : ∀ w : Vertex A, w ∈ P.H →
      (unitDistanceGraph A).Adj middle w →
      w = source.1 ∨ w = (P.next⁻¹ source).1 ∨ w = (P.next source).1) :
    (hullUnitNeighbors P middle).card ≤ 2 := by
  by_cases hp : (P.next⁻¹ source).1 ∈ hullUnitNeighbors P middle
  · have hnextNot : (P.next source).1 ∉ hullUnitNeighbors P middle := by
      intro hn
      exact not_both_cyclic_neighbors_adjacent_to_middle hA P W source hs middle hsm
        (mem_hullUnitNeighbors.mp hp).2 (mem_hullUnitNeighbors.mp hn).2
    refine (Finset.card_le_card (s := hullUnitNeighbors P middle)
      (t := {source.1, (P.next⁻¹ source).1}) ?_).trans Finset.card_le_two
    intro w hw
    rcases hlocal w (mem_hullUnitNeighbors.mp hw).1
      (mem_hullUnitNeighbors.mp hw).2 with h | h | h
    · simp [h]
    · simp [h]
    · exact (hnextNot (h ▸ hw)).elim
  · refine (Finset.card_le_card (s := hullUnitNeighbors P middle)
      (t := {source.1, (P.next source).1}) ?_).trans Finset.card_le_two
    intro w hw
    rcases hlocal w (mem_hullUnitNeighbors.mp hw).1
      (mem_hullUnitNeighbors.mp hw).2 with h | h | h
    · simp [h]
    · exact (hp (h ▸ hw)).elim
    · simp [h]

/-- Which cyclic side supplies the second extreme neighbor. -/
inductive CyclicSide
  | previous
  | next
  deriving DecidableEq

def cyclicSideVertex {A : Finset ComplexPoint} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) : CyclicSide → Vertex A
  | .previous => (P.next⁻¹ source).1
  | .next => (P.next source).1

/-- The formula-retaining witness for the two-extreme branch: the extreme
neighbor finset is exactly the source together with one genuinely adjacent
cyclic hull vertex. -/
structure TwoExtremeCyclicWitness {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) (middle : Vertex A) where
  side : CyclicSide
  neighbors_eq : hullUnitNeighbors P middle =
    {source.1, cyclicSideVertex P source side}
  side_adjacent : (unitDistanceGraph A).Adj middle
    (cyclicSideVertex P source side)

/-- Any further actual unit neighbour of the middle is non-extreme in the
two-extreme branch.  This is the target-exclusion fact used by the arbitrary
Case-4 low-neighbour row. -/
lemma not_mem_hull_of_adj_middle_of_twoExtreme
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle v : Vertex A}
    (T : TwoExtremeCyclicWitness P source middle)
    (hmv : (unitDistanceGraph A).Adj middle v)
    (hneSource : v ≠ source.1)
    (hneSide : v ≠ cyclicSideVertex P source T.side) :
    v ∉ P.H := by
  intro hvH
  have hv : v ∈ hullUnitNeighbors P middle :=
    mem_hullUnitNeighbors.mpr ⟨hvH, hmv⟩
  rw [T.neighbors_eq] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  exact hv.elim hneSource hneSide

/-- A two-extreme localized middle exposes the actual cyclic side, rather
than merely recording cardinality two. -/
theorem twoExtremeCyclicWitness_of_localization
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (hs : source.1 ∈ sourceVertices P W)
    (middle : Vertex A) (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hlocal : ∀ w : Vertex A, w ∈ P.H →
      (unitDistanceGraph A).Adj middle w →
      w = source.1 ∨ w = (P.next⁻¹ source).1 ∨ w = (P.next source).1)
    (htwo : (hullUnitNeighbors P middle).card = 2) :
    Nonempty (TwoExtremeCyclicWitness P source middle) := by
  by_cases hp : (P.next⁻¹ source).1 ∈ hullUnitNeighbors P middle
  · have hnextNot : (P.next source).1 ∉ hullUnitNeighbors P middle := by
      intro hn
      exact not_both_cyclic_neighbors_adjacent_to_middle hA P W source hs middle hsm
        (mem_hullUnitNeighbors.mp hp).2 (mem_hullUnitNeighbors.mp hn).2
    have hsub : hullUnitNeighbors P middle ⊆
        {source.1, (P.next⁻¹ source).1} := by
      intro w hw
      rcases hlocal w (mem_hullUnitNeighbors.mp hw).1
        (mem_hullUnitNeighbors.mp hw).2 with h | h | h
      · simp [h]
      · simp [h]
      · exact (hnextNot (h ▸ hw)).elim
    have heq : hullUnitNeighbors P middle =
        {source.1, (P.next⁻¹ source).1} := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [htwo]
      exact Finset.card_le_two
    exact ⟨{
      side := .previous
      neighbors_eq := heq
      side_adjacent := (mem_hullUnitNeighbors.mp hp).2 }⟩
  · have hsub : hullUnitNeighbors P middle ⊆
        {source.1, (P.next source).1} := by
      intro w hw
      rcases hlocal w (mem_hullUnitNeighbors.mp hw).1
        (mem_hullUnitNeighbors.mp hw).2 with h | h | h
      · simp [h]
      · exact (hp (h ▸ hw)).elim
      · simp [h]
    have heq : hullUnitNeighbors P middle =
        {source.1, (P.next source).1} := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [htwo]
      exact Finset.card_le_two
    have hn : (P.next source).1 ∈ hullUnitNeighbors P middle := by
      rw [heq]
      simp
    exact ⟨{
      side := .next
      neighbors_eq := heq
      side_adjacent := (mem_hullUnitNeighbors.mp hn).2 }⟩

/-- The source itself is an actual hull neighbor of its selected middle
neighbor.  Thus the hull-neighbor count in the classification cannot be
zero. -/
lemma source_mem_hullUnitNeighbors {A : Finset ComplexPoint}
    {P : CyclicHullData A} {W : DiameterWitnessData P}
    {source middle : Vertex A} (hs : source ∈ sourceVertices P W)
    (hsm : (unitDistanceGraph A).Adj source middle) :
    source ∈ hullUnitNeighbors P middle := by
  exact mem_hullUnitNeighbors.mpr
    ⟨sourceVertices_subset_hull P W hs, (unitDistanceGraph A).adj_symm hsm⟩

/-- Exhaustive classification of a degree-three flat diameter source.

The only local-hull input is the geometric statement that the selected
middle neighbor sees at most two strict hull vertices.  The lower bound is
proved here from the actual source incidence.  The degree-six alternative is
exhaustive by the checked planar kissing-number theorem.
-/
theorem four_cases_exhaustive {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (W : DiameterWitnessData P) {source middle : Vertex A}
    (hs : source ∈ sourceVertices P W)
    (hsm : (unitDistanceGraph A).Adj source middle)
    (hatMostTwo : (hullUnitNeighbors P middle).card ≤ 2) :
    FourCase P middle := by
  have hpositive : 1 ≤ (hullUnitNeighbors P middle).card := by
    exact Finset.one_le_card.mpr ⟨source, source_mem_hullUnitNeighbors hs hsm⟩
  have hdegree : (unitDistanceGraph A).degree middle ≤ 6 :=
    degree_unitDistanceGraph_le_six hA middle
  have hcount : (hullUnitNeighbors P middle).card = 1 ∨
      (hullUnitNeighbors P middle).card = 2 := by
    omega
  by_cases hsix : (unitDistanceGraph A).degree middle = 6
  · rcases hcount with hone | htwo
    · exact .case1 hsix hone
    · exact .case2 hsix htwo
  · have hfive : (unitDistanceGraph A).degree middle ≤ 5 := by omega
    rcases hcount with hone | htwo
    · exact .case3 hfive hone
    · exact .case4 hfive htwo

/-- Exhaustive four-case split once the flat-chain/chord layer has proved
the honest three-index localization.  No choice of successor versus
predecessor is assumed. -/
theorem four_cases_of_cyclic_localization
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hs : source.1 ∈ sourceVertices P W)
    (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hlocal : ∀ w : Vertex A, w ∈ P.H →
      (unitDistanceGraph A).Adj middle w →
      w = source.1 ∨ w = (P.next⁻¹ source).1 ∨ w = (P.next source).1) :
    FourCase P middle := by
  exact four_cases_exhaustive hA P W hs hsm
    (hullUnitNeighbors_card_le_two_of_cyclic_localization
      hA P W source hs middle hsm hlocal)

/-- Exhaustive classification after the global chord argument has put every
extreme unit neighbour of the selected middle in the honest seven-vertex
window.  The removal of the two farther vertices on either side is then a
theorem of the common bisector chart, not an assumed cyclic alignment. -/
theorem four_cases_of_seven_window
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (middle : Vertex A) (hs : source.1 ∈ sourceVertices P W)
    (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hcone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (hwindow : ∀ w : Vertex A, w ∈ P.H →
      (unitDistanceGraph A).Adj middle w →
      w ∈ Erdos957MiddleLocalization.sevenHullWindow P source) :
    FourCase P middle := by
  apply four_cases_of_cyclic_localization hA P W source middle hs hsm
  intro w hwH hmw
  exact Erdos957MiddleLocalization.eq_source_or_prev_or_next_of_mem_sevenHullWindow
    F source (source_isFlat P W source hs) hsm hcone hmw
      (hwindow w hwH hmw)

/-- In the two-extreme branch, the same honest window hypothesis produces
the exact cyclic side witness needed to choose the supporting unit-edge
frame for Cases 2 and 4. -/
theorem twoExtremeCyclicWitness_of_seven_window
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (F : P.FlatAlignedFrameData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (middle : Vertex A) (hs : source.1 ∈ sourceVertices P W)
    (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hcone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (hwindow : ∀ w : Vertex A, w ∈ P.H →
      (unitDistanceGraph A).Adj middle w →
      w ∈ Erdos957MiddleLocalization.sevenHullWindow P source)
    (htwo : (hullUnitNeighbors P middle).card = 2) :
    Nonempty (TwoExtremeCyclicWitness P source middle) := by
  apply twoExtremeCyclicWitness_of_localization hA P W source hs middle hsm
    _ htwo
  intro w hwH hmw
  exact Erdos957MiddleLocalization.eq_source_or_prev_or_next_of_mem_sevenHullWindow
    F source (source_isFlat P W source hs) hsm hcone hmw
      (hwindow w hwH hmw)

/-! ### Rectangle-width localization for arbitrary local hull targets -/

/-- Two flat one-separated hull edges already move farther than `7/4` in
the positive bisector direction.  This sharper form is needed for recipients
which are known only to lie in the transfer rectangle, rather than to be
unit neighbours of the selected middle point. -/
lemma right_two_three_fst_gt_seven_four
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) :
    (7 / 4 : ℝ) < (F.chart.rightOrbitCoord P i 2).1 ∧
      (7 / 4 : ℝ) < (F.chart.rightOrbitCoord P i 3).1 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.rightFlatAngles i hi
  obtain ⟨ha0, ha1, ha2, _ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  have d0 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 0) ha0 (F.rightPolar i 0).1
  have d1 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 1) ha1 (F.rightPolar i 1).1
  have d2 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 2) ha2 (F.rightPolar i 2).1
  norm_num at d0 d1 d2
  have hz : (F.chart.rightOrbitCoord P i 0).1 = 0 := by simp
  constructor <;> linarith

/-- The reflected backward orbit satisfies the same two-edge `7/4`
separation estimate. -/
lemma left_two_three_reflected_fst_gt_seven_four
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) :
    (7 / 4 : ℝ) < (F.chart.leftOrbitReflectedCoord P i 2).1 ∧
      (7 / 4 : ℝ) < (F.chart.leftOrbitReflectedCoord P i 3).1 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.leftFlatAngles i hi
  obtain ⟨ha0, ha1, ha2, _ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  have d0 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 0) ha0 (F.leftPolar i 0).1
  have d1 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 1) ha1 (F.leftPolar i 1).1
  have d2 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 2) ha2 (F.leftPolar i 2).1
  norm_num at d0 d1 d2
  have hz : (F.chart.leftOrbitReflectedCoord P i 0).1 = 0 := by simp
  constructor <;> linarith

/-- The two incident cyclic neighbours lie outside the open middle cone's
horizontal strip at a flat source. -/
lemma incident_neighbor_fst_bounds
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) :
    (399 / 400 : ℝ) < (F.chart.coord i (P.next i).1).1 ∧
      (F.chart.coord i (P.next⁻¹ i).1).1 < -(399 / 400 : ℝ) := by
  obtain ⟨hr0, _hr1, _hr2, _hr3⟩ := F.rightFlatAngles i hi
  obtain ⟨hl0, _hl1, _hl2, _hl3⟩ := F.leftFlatAngles i hi
  have hrAngle : |F.rightAngle i 0| ≤ Real.pi / 45 := by
    nlinarith [Real.pi_pos]
  have hlAngle : |F.leftAngle i 0| ≤ Real.pi / 45 := by
    nlinarith [Real.pi_pos]
  have dr :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 0) hrAngle (F.rightPolar i 0).1
  have dl :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 0) hlAngle (F.leftPolar i 0).1
  have hzR : (F.chart.rightOrbitCoord P i 0).1 = 0 := by simp
  have hzL : (F.chart.leftOrbitReflectedCoord P i 0).1 = 0 := by simp
  norm_num at dr dl
  change (399 / 400 : ℝ) <
    (F.chart.coord i ((P.next ^ 1) i).1).1 at dr
  change (399 / 400 : ℝ) <
    -(F.chart.coord i (((P.next⁻¹) ^ 1) i).1).1 at dl
  simp only [pow_one] at dr dl
  constructor
  · exact dr
  · change (F.chart.coord i (P.next⁻¹ i).1).1 < _
    linarith

/-- A selected unit middle point in the open inward cone is distinct from
both cyclic neighbours of the flat source. -/
lemma middle_ne_incident_neighbors_of_openCone
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) {middle : Vertex A}
    (hsm : (unitDistanceGraph A).Adj i.1 middle)
    (hcone : Erdos957Cases13.InOpenMiddleCone (F.chart.coord i middle)) :
    middle ≠ (P.next⁻¹ i).1 ∧ middle ≠ (P.next i).1 := by
  have hunit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (F.chart.coord i middle) = 1 := by
    rw [show Erdos957Cases13.origin = F.chart.coord i i.1 by
      simpa [Erdos957Cases13.origin] using (F.chart.coord_source i).symm]
    rw [F.chart.sqDist_coord]
    change dist (i.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsm
    rw [hsm]
    norm_num
  have hm := Erdos957MiddleLocalization.abs_fst_lt_half_of_unit_of_middleCone
    hunit hcone
  have hiBounds := incident_neighbor_fst_bounds F i hi
  constructor
  · intro h
    rw [h] at hm
    linarith
  · intro h
    rw [h] at hm
    linarith

/-- Every hull vertex in the seven-position window and in the recipient
horizontal strip is one of the source and its two incident cyclic vertices.
Unlike `MiddleLocalization`'s unit-neighbour theorem, this statement needs
no adjacency premise and therefore applies directly to Case 2/4 recipients. -/
theorem eq_source_or_prev_or_next_of_mem_sevenHullWindow_of_abs_fst_le
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) (w : Vertex A)
    (hwWindow : w ∈ Erdos957MiddleLocalization.sevenHullWindow P i)
    (hwHorizontal : |(F.chart.coord i w).1| ≤ (7 : ℝ) / 4) :
    w = i.1 ∨ w = (P.next⁻¹ i).1 ∨ w = (P.next i).1 := by
  have hr := right_two_three_fst_gt_seven_four F i hi
  have hl := left_two_three_reflected_fst_gt_seven_four F i hi
  have hwBounds : -(7 / 4 : ℝ) ≤ (F.chart.coord i w).1 ∧
      (F.chart.coord i w).1 ≤ 7 / 4 := by
    simpa [abs_le] using hwHorizontal
  rcases Finset.mem_image.mp hwWindow with ⟨j, _hj, hjw⟩
  fin_cases j
  · change (((P.next⁻¹) ^ 3) i).1 = w at hjw
    have hx := hl.2
    change (7 / 4 : ℝ) <
      -(F.chart.coord i (((P.next⁻¹) ^ 3) i).1).1 at hx
    rw [hjw] at hx
    exfalso
    linarith

  · have hjw' : (((P.next⁻¹) ^ 2) i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    have hx := hl.1
    change (7 / 4 : ℝ) <
      -(F.chart.coord i (((P.next⁻¹) ^ 2) i).1).1 at hx
    rw [hjw'] at hx
    exfalso
    linarith
  · have hjw' : (P.next⁻¹ i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    exact Or.inr (Or.inl hjw'.symm)
  · have hjw' : i.1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    exact Or.inl hjw'.symm
  · have hjw' : (P.next i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    exact Or.inr (Or.inr hjw'.symm)
  · have hjw' : ((P.next ^ 2) i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    have hx := hr.1
    change (7 / 4 : ℝ) <
      (F.chart.coord i ((P.next ^ 2) i).1).1 at hx
    rw [hjw'] at hx
    exfalso
    linarith
  · have hjw' : ((P.next ^ 3) i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    have hx := hr.2
    change (7 / 4 : ℝ) <
      (F.chart.coord i ((P.next ^ 3) i).1).1 at hx
    rw [hjw'] at hx
    exfalso
    linarith

/-- Honest interface supplied by the global chord/window geometry: every
hull vertex reachable from a source by at most two unit edges belongs to the
seven-position cyclic window around that source. -/
def LocalHullWindowHypothesis {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) : Prop :=
  ∀ v : Vertex A, v ∈ P.H →
    Erdos957GeometryLocalRows.WithinTwoUnitEdges source.1 v →
      v ∈ Erdos957MiddleLocalization.sevenHullWindow P source

/-- A local recipient in the common horizontal strip is non-extreme as soon
as its exact formula rules out the source and the two incident cyclic
vertices.  The only global input is the preceding seven-window locality. -/
theorem not_mem_hull_of_local_window_of_abs_fst_le
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (v : Vertex A)
    (hpath : Erdos957GeometryLocalRows.WithinTwoUnitEdges source.1 v)
    (hhorizontal : |(F.chart.coord source v).1| ≤ (7 : ℝ) / 4)
    (hneSource : v ≠ source.1)
    (hnePrev : v ≠ (P.next⁻¹ source).1)
    (hneNext : v ≠ (P.next source).1) :
    v ∉ P.H := by
  intro hvH
  rcases eq_source_or_prev_or_next_of_mem_sevenHullWindow_of_abs_fst_le
      F source hflat v (hwindow v hvH hpath) hhorizontal with h | h | h
  · exact hneSource h
  · exact hnePrev h
  · exact hneNext h

/-- The selected inward middle neighbour itself is non-extreme.  Flatness
separates it from the two incident cyclic vertices, and the global local
window then leaves no possible hull index for it. -/
theorem middle_not_mem_hull_of_local_window
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hcone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle)) :
    middle ∉ P.H := by
  have hunit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (F.chart.coord source middle) = 1 := by
    rw [show Erdos957Cases13.origin = F.chart.coord source source.1 by
      simpa [Erdos957Cases13.origin] using
        (F.chart.coord_source source).symm]
    rw [F.chart.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsm
    rw [hsm]
    norm_num
  have hm := Erdos957MiddleLocalization.abs_fst_lt_half_of_unit_of_middleCone
    hunit hcone
  have hhorizontal : |(F.chart.coord source middle).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hincident := middle_ne_incident_neighbors_of_openCone
    F source hflat hsm hcone
  apply not_mem_hull_of_local_window_of_abs_fst_le
    F source hflat hwindow middle
  · exact Or.inl hsm
  · exact hhorizontal
  · exact fun h ↦ hsm.ne h.symm
  · exact hincident.1
  · exact hincident.2

/-- Honest arbitrary-angle Case-4 datum.  The low recipient is selected
from the actual unit neighbours of the middle, rather than identified with
a fixed triangular-lattice coordinate. -/
structure Case4LowNeighborData
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle) where
  low : Vertex A
  middle_adj_low : (unitDistanceGraph A).Adj middle low
  low_ne_source : low ≠ source.1
  low_ne_side : low ≠ cyclicSideVertex P source T.side
  low_degree_le_five : (unitDistanceGraph A).degree low ≤ 5

/-- Build the actual Case-4 source row from an arbitrary low-degree
neighbour supplied by the phase-bin kernel.  In the low middle-degree
branch both tokens stay at the middle; in the five-valent branch they split
between the middle and the selected actual neighbour. -/
theorem case4LocalCase_of_lowNeighbor
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Vertex A)
    (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hcone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (T : TwoExtremeCyclicWitness P source middle)
    (hmiddleDegree : (unitDistanceGraph A).degree middle ≤ 5)
    (hlow : (unitDistanceGraph A).degree middle = 5 →
      Nonempty (Case4LowNeighborData source middle T)) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P F.chart source) := by
  have hmiddleNot := middle_not_mem_hull_of_local_window
    F source hflat hwindow middle hsm hcone
  have hmiddleUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (F.chart.coord source middle) = 1 := by
    rw [show Erdos957Cases13.origin = F.chart.coord source source.1 by
      simpa [Erdos957Cases13.origin] using
        (F.chart.coord_source source).symm]
    rw [F.chart.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1 at hsm
    rw [hsm]
    norm_num
  have hmiddleBounds :=
    Erdos957MiddleLocalization.abs_fst_lt_half_of_unit_of_middleCone
      hmiddleUnit hcone
  have hmiddleHorizontal :
      |(F.chart.coord source middle).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hmiddlePath : Erdos957GeometryLocalRows.WithinTwoUnitEdges
      source.1 middle := Or.inl hsm
  let middleTarget := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
    hmiddleDegree hmiddleNot hmiddlePath hmiddleHorizontal
  by_cases hfour : (unitDistanceGraph A).degree middle ≤ 4
  · exact ⟨.case4Primary middleTarget hfour⟩
  · have hfive : (unitDistanceGraph A).degree middle = 5 := by omega
    obtain ⟨D⟩ := hlow hfive
    have hlowNot : D.low ∉ P.H :=
      not_mem_hull_of_adj_middle_of_twoExtreme T D.middle_adj_low
        D.low_ne_source D.low_ne_side
    have hlowPath : Erdos957GeometryLocalRows.WithinTwoUnitEdges
        source.1 D.low := Or.inr ⟨middle, hsm, D.middle_adj_low⟩
    have hdiff := Erdos957MiddleLocalization.abs_fst_sub_le_one_of_adj
      F.chart source D.middle_adj_low
    have hlowHorizontal : |(F.chart.coord source D.low).1| ≤ (7 : ℝ) / 4 := by
      rw [abs_le] at hdiff ⊢
      constructor <;> linarith
    let lowTarget := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
      D.low_degree_le_five hlowNot hlowPath hlowHorizontal
    have hne : middleTarget.vertex ≠ lowTarget.vertex := by
      exact D.middle_adj_low.ne
    exact ⟨.case4SecondarySplit middleTarget lowTarget hne⟩

/-- Cyclic-hull form of the preceding theorem.  This is the formulation used
after the flat-angle geometry proves that the only possible extreme unit
neighbors of the middle point are the source and its cyclic successor. -/
theorem four_cases_of_consecutive_hull_neighbors {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (middle : Vertex A) (hs : source.1 ∈ sourceVertices P W)
    (hsm : (unitDistanceGraph A).Adj source.1 middle)
    (hconsecutive : ∀ w : Vertex A, w ∈ P.H →
      (unitDistanceGraph A).Adj middle w →
      w = source.1 ∨ w = (P.next source).1) :
    FourCase P middle := by
  apply four_cases_exhaustive hA P W hs hsm
  refine (Finset.card_le_card (s := hullUnitNeighbors P middle)
    (t := {source.1, (P.next source).1}) ?_).trans Finset.card_le_two
  intro w hw
  have hw' := mem_hullUnitNeighbors.mp hw
  simpa only [Finset.mem_insert, Finset.mem_singleton] using
    hconsecutive w hw'.1 hw'.2

/-! ## Checked Case 1 and Case 3 realizations -/

namespace PairCases

open Erdos957Cases13
open Erdos957Case13Bridge

abbrev Point := Erdos957Cases13.Point

/-! ### Finite copies in an explicit aligned chart -/

lemma alignedCoord_injective {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) :
    Function.Injective (C.coord source) := by
  intro q r hqr
  apply Subtype.ext
  apply dist_eq_zero.mp
  have hsquare := C.sqDist_coord source q r
  rw [hqr, Erdos957Cases13.sqDist_self] at hsquare
  nlinarith [dist_nonneg (x := (q : ComplexPoint)) (y := (r : ComplexPoint))]

def alignedConfiguration {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) : Finset Point :=
  Finset.univ.map ⟨C.coord source, alignedCoord_injective C source⟩

def alignedHull {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) : Finset Point :=
  P.H.map ⟨C.coord source, alignedCoord_injective C source⟩

lemma coord_mem_alignedConfiguration {A : Finset ComplexPoint}
    {P : CyclicHullData A} (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (q : Vertex A) :
    C.coord source q ∈ alignedConfiguration C source := by
  exact Finset.mem_map.mpr ⟨q, Finset.mem_univ _, rfl⟩

lemma coord_mem_alignedHull {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) {q : Vertex A}
    (hq : q ∈ P.H) : C.coord source q ∈ alignedHull C source := by
  exact Finset.mem_map.mpr ⟨q, hq, rfl⟩

lemma exists_vertex_coord_eq {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) {p : Point}
    (hp : p ∈ alignedConfiguration C source) :
    ∃ v : Vertex A, C.coord source v = p := by
  rcases Finset.mem_map.mp hp with ⟨v, _hv, hvp⟩
  exact ⟨v, hvp⟩

lemma alignedConfiguration_oneSeparated {A : Finset ComplexPoint}
    {P : CyclicHullData A} (hA : IsOneSeparated A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) :
    Erdos957Cases13.IsOneSeparated (alignedConfiguration C source : Set Point) := by
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨p, _hp, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨q, _hq, rfl⟩
  have hpq : p ≠ q := fun h ↦ hxy (congrArg (C.coord source) h)
  change 1 ≤ Erdos957Cases13.sqDist (C.coord source p) (C.coord source q)
  rw [C.sqDist_coord]
  have hd := hA p p.property q q.property (fun h ↦ hpq (Subtype.ext h))
  nlinarith [dist_nonneg (x := (p : ComplexPoint)) (y := (q : ComplexPoint))]

lemma aligned_degree_coord {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H}) (q : Vertex A) :
    Erdos957Case13Bridge.degree (alignedConfiguration C source) (C.coord source q) =
      (unitDistanceGraph A).degree q := by
  classical
  rw [Erdos957Case13Bridge.degree, SimpleGraph.degree]
  apply Finset.card_bij
    (s := Erdos957Case13Bridge.unitNeighbors
      (alignedConfiguration C source) (C.coord source q))
    (t := (unitDistanceGraph A).neighborFinset q)
    (fun p hp ↦ Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1))
  · intro p hp
    let r : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)
    have hrCoord : C.coord source r = p :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)).2
    have hsquare := (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).2
    rw [← hrCoord, C.sqDist_coord] at hsquare
    have hdist : dist (q : ComplexPoint) (r : ComplexPoint) = 1 := by
      nlinarith [dist_nonneg (x := (q : ComplexPoint)) (y := (r : ComplexPoint))]
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := q) r).mpr hdist
  · intro p hp r hr hpr
    let p' : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)
    let r' : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hr).1)
    have hpCoord : C.coord source p' = p :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)).2
    have hrCoord : C.coord source r' = r :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hr).1)).2
    have hvertex : p' = r' := hpr
    rw [← hpCoord, ← hrCoord, hvertex]
  · intro r hr
    refine ⟨C.coord source r, ?_, ?_⟩
    · apply Erdos957Case13Bridge.mem_unitNeighbors.mpr
      refine ⟨coord_mem_alignedConfiguration C source r, ?_⟩
      rw [C.sqDist_coord]
      have hdist := (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A) (v := q) r).mp hr
      rw [hdist]
      norm_num
    · exact alignedCoord_injective C source
        (Classical.choose_spec
          (Finset.mem_map.mp (coord_mem_alignedConfiguration C source r))).2

lemma origin_mem_alignedConfiguration {A : Finset ComplexPoint}
    {P : CyclicHullData A} (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) :
    Erdos957Cases13.origin ∈ alignedConfiguration C source := by
  change (0, 0) ∈ alignedConfiguration C source
  rw [← C.coord_source source]
  exact coord_mem_alignedConfiguration C source source.1

lemma origin_mem_alignedHull {A : Finset ComplexPoint}
    {P : CyclicHullData A} (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) :
    Erdos957Cases13.origin ∈ alignedHull C source := by
  change (0, 0) ∈ alignedHull C source
  rw [← C.coord_source source]
  exact coord_mem_alignedHull C source source.property

lemma alignedConfiguration_below_support {A : Finset ComplexPoint}
    {P : CyclicHullData A} (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) :
    ∀ p ∈ alignedConfiguration C source, p.2 ≤ 0 := by
  intro p hp
  rcases Finset.mem_map.mp hp with ⟨q, _hq, rfl⟩
  exact C.coord_snd_nonpos source q

/-- The middle occupied one-third sector of a three-neighbor strict
half-plane configuration lies in the open 60-degree cone about the inward
normal.  The strictness comes from the actually occupied adjacent sectors,
not from a closed-bin estimate. -/
lemma middle_sector_in_open_cone {z₀ z₁ z₂ : ℂ}
    (hnorm₀ : ‖z₀‖ = 1) (hnorm₁ : ‖z₁‖ = 1) (hnorm₂ : ‖z₂‖ = 1)
    (him₀ : z₀.im < 0) (him₁ : z₁.im < 0) (him₂ : z₂.im < 0)
    (hbin₀ : Erdos957Angle.phaseBin z₀ = (0 : Fin 6))
    (hbin₁ : Erdos957Angle.phaseBin z₁ = (1 : Fin 6))
    (hbin₂ : Erdos957Angle.phaseBin z₂ = (2 : Fin 6))
    (hsep₀₁ : 1 ≤ ‖z₀ - z₁‖) (hsep₁₂ : 1 ≤ ‖z₁ - z₂‖) :
    Erdos957Cases13.InOpenMiddleCone (z₁.re, z₁.im) := by
  let θ₀ := Erdos957Angle.principalPhase z₀
  let θ₁ := Erdos957Angle.principalPhase z₁
  let θ₂ := Erdos957Angle.principalPhase z₂
  have harg₀ : z₀.arg < 0 := Complex.arg_neg_iff.mpr him₀
  have harg₁ : z₁.arg < 0 := Complex.arg_neg_iff.mpr him₁
  have harg₂ : z₂.arg < 0 := Complex.arg_neg_iff.mpr him₂
  have hphase₀ : θ₀ = z₀.arg := by
    simp [θ₀, Erdos957Angle.principalPhase,
      ne_of_lt (harg₀.trans Real.pi_pos)]
  have hphase₁ : θ₁ = z₁.arg := by
    simp [θ₁, Erdos957Angle.principalPhase,
      ne_of_lt (harg₁.trans Real.pi_pos)]
  have hphase₂ : θ₂ = z₂.arg := by
    simp [θ₂, Erdos957Angle.principalPhase,
      ne_of_lt (harg₂.trans Real.pi_pos)]
  have hθ₀negpi : -Real.pi < θ₀ := by
    rw [hphase₀]
    exact Complex.neg_pi_lt_arg z₀
  have hθ₂zero : θ₂ < 0 := by simpa [hphase₂] using harg₂
  have hb₀ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₀
  have hb₁ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₁
  have hb₂ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₂
  norm_num [θ₀, θ₁, θ₂] at hb₀ hb₁ hb₂
  have hangle₀₁ : Real.pi / 3 ≤ InnerProductGeometry.angle z₀ z₁ :=
    Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      hnorm₀ hnorm₁ hsep₀₁
  have hangle₁₂ : Real.pi / 3 ≤ InnerProductGeometry.angle z₁ z₂ :=
    Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      hnorm₁ hnorm₂ hsep₁₂
  have hangleEq₀₁ : InnerProductGeometry.angle z₀ z₁ = θ₁ - θ₀ := by
    apply Erdos957Angle.angle_eq_principalPhase_sub_of_le_of_sub_lt_pi hnorm₀ hnorm₁
    · linarith [hb₀.2, hb₁.1, Real.pi_pos]
    · linarith [hθ₀negpi, hb₁.2, Real.pi_pos]
  have hangleEq₁₂ : InnerProductGeometry.angle z₁ z₂ = θ₂ - θ₁ := by
    apply Erdos957Angle.angle_eq_principalPhase_sub_of_le_of_sub_lt_pi hnorm₁ hnorm₂
    · linarith [hb₁.2, hb₂.1, Real.pi_pos]
    · linarith [hb₁.1, hθ₂zero, Real.pi_pos]
  have hθ₁lower : -(2 * Real.pi / 3) < θ₁ := by
    rw [hangleEq₀₁] at hangle₀₁
    linarith
  have hθ₁upper : θ₁ < -(Real.pi / 3) := by
    rw [hangleEq₁₂] at hangle₁₂
    linarith
  have hexp := Erdos957Angle.exp_principalPhase_mul_I hnorm₁
  have hre : Real.cos θ₁ = z₁.re := by
    simpa [θ₁] using congrArg Complex.re hexp
  have him : Real.sin θ₁ = z₁.im := by
    simpa [θ₁] using congrArg Complex.im hexp
  have hsina : Real.sin (θ₁ + Real.pi / 3) < 0 := by
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · linarith
    · linarith [Real.pi_pos]
  have hsinb : Real.sin (θ₁ - Real.pi / 3) < 0 := by
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · linarith
    · linarith [Real.pi_pos]
  have hsqrt : Erdos957Cases13.sqrtThree = Real.sqrt 3 := rfl
  have hleft : Erdos957Cases13.sqrtThree * z₁.re < -z₁.im := by
    rw [← hre, ← him, hsqrt]
    rw [Real.sin_add, Real.sin_pi_div_three, Real.cos_pi_div_three] at hsina
    nlinarith
  have hright : -Erdos957Cases13.sqrtThree * z₁.re < -z₁.im := by
    rw [← hre, ← him, hsqrt]
    rw [sub_eq_add_neg, Real.sin_add, Real.sin_neg, Real.cos_neg,
      Real.sin_pi_div_three, Real.cos_pi_div_three] at hsinb
    nlinarith
  exact ⟨hleft, hright⟩

/-! ### The actual middle neighbor at a degree-three hull source -/

/-- A degree-three source in the strict supporting half-plane has a genuine
middle unit neighbor.  It is selected as the unique neighbor in phase bin
one; occupancy of bins zero and two makes its cone inequalities strict. -/
theorem exists_middle_neighbor_in_open_cone_of_coord {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (coord : Vertex A → ℝ × ℝ)
    (hcoordSource : coord source.1 = (0, 0))
    (hsqDist : ∀ q r, Erdos957Cases13.sqDist (coord q) (coord r) =
      dist (q : ComplexPoint) (r : ComplexPoint) ^ 2)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (coord q).2 < 0) :
    ∃ middle : Vertex A,
      (unitDistanceGraph A).Adj source.1 middle ∧
      Erdos957Cases13.InOpenMiddleCone (coord middle) := by
  classical
  let N := (unitDistanceGraph A).neighborFinset source.1
  let z : Vertex A → ℂ := fun q ↦
    Erdos957Cases13.toComplex (coord q)
  have hneSource {q : Vertex A} (hq : q ∈ N) : q ≠ source.1 := by
    intro h
    subst q
    exact (SimpleGraph.notMem_neighborFinset_self
      (G := unitDistanceGraph A) (v := source.1)) hq
  have him {q : Vertex A} (hq : q ∈ N) : (z q).im < 0 := by
    simpa [z, Erdos957Cases13.toComplex] using
      hstrict q (hneSource hq)
  have hnorm {q : Vertex A} (hq : q ∈ N) : ‖z q‖ = 1 := by
    have hadj : (unitDistanceGraph A).Adj source.1 q :=
      (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A) (v := source.1) q).mp hq
    have hsquare : Erdos957Cases13.sqDist
        Erdos957Cases13.origin (coord q) = 1 := by
      change Erdos957Cases13.sqDist (0, 0) (coord q) = 1
      rw [← hcoordSource, hsqDist, hadj]
      norm_num
    have hd := (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
      Erdos957Cases13.origin (coord q)).mp hsquare
    change dist 0 (z q) = 1 at hd
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hd
  have hsep {q r : Vertex A} (hq : q ∈ N) (hr : r ∈ N) (hqr : q ≠ r) :
      1 ≤ ‖z q - z r‖ := by
    have hdist := hA q q.property r r.property
      (fun h ↦ hqr (Subtype.ext h))
    have hsquare : 1 ≤ Erdos957Cases13.sqDist
        (coord q) (coord r) := by
      rw [hsqDist]
      nlinarith [(dist_nonneg : 0 ≤ dist (q : ComplexPoint) (r : ComplexPoint))]
    have hd := (Erdos957Cases13.one_le_sqDist_iff_one_le_dist
      (coord q) (coord r)).mp hsquare
    simpa only [z, dist_eq_norm] using hd
  let phase : N → Fin 3 := fun q ↦
    ⟨(Erdos957Angle.phaseBin (z q)).val,
      Erdos957Angle.phaseBin_val_lt_three_of_im_neg (him q.property)⟩
  have hphaseInj : Function.Injective phase := by
    intro q r hqr
    apply Subtype.ext
    by_contra hne
    have hbin : Erdos957Angle.phaseBin (z q) =
        Erdos957Angle.phaseBin (z r) := by
      apply Fin.ext
      simpa [phase] using congrArg Fin.val hqr
    have hangleGe :=
      Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
        (hnorm q.property) (hnorm r.property) (hsep q.property r.property hne)
    have hangleEq := Erdos957Angle.angle_eq_abs_principalPhase_sub_of_phaseBin_eq
      (hnorm q.property) (hnorm r.property) hbin
    have hangleLt := Erdos957Angle.abs_principalPhase_sub_lt_of_phaseBin_eq hbin
    linarith
  have hcardN : Fintype.card N = 3 := by
    rw [Fintype.card_coe]
    change ((unitDistanceGraph A).neighborFinset source.1).card = 3
    rw [← SimpleGraph.degree]
    exact hdegree
  have hphaseBij : Function.Bijective phase := by
    apply (Fintype.bijective_iff_injective_and_card phase).mpr
    exact ⟨hphaseInj, by simpa [hcardN]⟩
  obtain ⟨q₀, hq₀⟩ := hphaseBij.2 (0 : Fin 3)
  obtain ⟨q₁, hq₁⟩ := hphaseBij.2 (1 : Fin 3)
  obtain ⟨q₂, hq₂⟩ := hphaseBij.2 (2 : Fin 3)
  have hbin₀ : Erdos957Angle.phaseBin (z q₀) = (0 : Fin 6) := by
    apply Fin.ext
    simpa [phase] using congrArg Fin.val hq₀
  have hbin₁ : Erdos957Angle.phaseBin (z q₁) = (1 : Fin 6) := by
    apply Fin.ext
    simpa [phase] using congrArg Fin.val hq₁
  have hbin₂ : Erdos957Angle.phaseBin (z q₂) = (2 : Fin 6) := by
    apply Fin.ext
    simpa [phase] using congrArg Fin.val hq₂
  have hq₀q₁ : (q₀ : Vertex A) ≠ q₁ := by
    intro h
    have := congrArg phase (Subtype.ext h)
    rw [hq₀, hq₁] at this
    exact (by decide : (0 : Fin 3) ≠ 1) this
  have hq₁q₂ : (q₁ : Vertex A) ≠ q₂ := by
    intro h
    have := congrArg phase (Subtype.ext h)
    rw [hq₁, hq₂] at this
    exact (by decide : (1 : Fin 3) ≠ 2) this
  refine ⟨q₁, (SimpleGraph.mem_neighborFinset
    (G := unitDistanceGraph A) (v := source.1) q₁).mp q₁.property, ?_⟩
  have hcone := middle_sector_in_open_cone
    (hnorm q₀.property) (hnorm q₁.property) (hnorm q₂.property)
    (him q₀.property) (him q₁.property) (him q₂.property)
    hbin₀ hbin₁ hbin₂
    (hsep q₀.property q₁.property hq₀q₁)
    (hsep q₁.property q₂.property hq₁q₂)
  simpa [z, Erdos957Cases13.toComplex] using hcone

/-- Aligned-chart specialization of the coordinate-free phase-bin
selection theorem. -/
theorem exists_middle_neighbor_in_open_cone_aligned {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0) :
    ∃ middle : Vertex A,
      (unitDistanceGraph A).Adj source.1 middle ∧
      Erdos957Cases13.InOpenMiddleCone (C.coord source middle) := by
  exact exists_middle_neighbor_in_open_cone_of_coord hA P source
    (C.coord source) (C.coord_source source) (C.sqDist_coord source)
    hdegree hstrict

/-- Canonical middle neighbor selected in the same aligned chart later used
by locality.  The strict-support proof is kept explicit because weak support
alone does not determine an occupied middle phase bin. -/
noncomputable def alignedMiddleNeighbor {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0) : Vertex A :=
  Classical.choose
    (exists_middle_neighbor_in_open_cone_aligned hA P C source hdegree hstrict)

lemma alignedMiddleNeighbor_adj {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0) :
    (unitDistanceGraph A).Adj source.1
      (alignedMiddleNeighbor hA P C source hdegree hstrict) :=
  (Classical.choose_spec
    (exists_middle_neighbor_in_open_cone_aligned
      hA P C source hdegree hstrict)).1

lemma alignedMiddleNeighbor_in_open_cone {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0) :
    Erdos957Cases13.InOpenMiddleCone
      (C.coord source
        (alignedMiddleNeighbor hA P C source hdegree hstrict)) :=
  (Classical.choose_spec
    (exists_middle_neighbor_in_open_cone_aligned
      hA P C source hdegree hstrict)).2

/-- Source-indexed selected middle in the common aligned chart. -/
noncomputable def alignedSourceMiddle {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (hs : source.1 ∈ sourceVertices P W)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0) : Vertex A :=
  alignedMiddleNeighbor hA P C source (source_facts hs).2.2 hstrict

lemma alignedSourceMiddle_adj {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (hs : source.1 ∈ sourceVertices P W)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0) :
    (unitDistanceGraph A).Adj source.1
      (alignedSourceMiddle hA P C W source hs hstrict) :=
  alignedMiddleNeighbor_adj hA P C source (source_facts hs).2.2 hstrict

lemma alignedSourceMiddle_in_open_cone {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (W : DiameterWitnessData P)
    (source : {p // p ∈ P.H}) (hs : source.1 ∈ sourceVertices P W)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0) :
    Erdos957Cases13.InOpenMiddleCone
      (C.coord source (alignedSourceMiddle hA P C W source hs hstrict)) :=
  alignedMiddleNeighbor_in_open_cone hA P C source
    (source_facts hs).2.2 hstrict

/-- Canonical middle for the production bisector chart.  Strict support is
a theorem of the cyclic hull order, so this definition has no chart
alignment premise. -/
noncomputable def bisectorSourceMiddle {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (O : Erdos957.CyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L))
    (source : {p // p ∈
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L).H})
    (hs : source.1 ∈ sourceVertices
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) W) : Vertex A :=
  alignedSourceMiddle hA
    (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L)
    (Erdos957BisectorFrame.bisectorAlignedChartData O L) W source hs
    (fun q hq ↦
      Erdos957BisectorFrame.bisectorAlignedChartData_coord_snd_neg
        O L source q hq)

lemma bisectorSourceMiddle_adj {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (O : Erdos957.CyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L))
    (source : {p // p ∈
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L).H})
    (hs : source.1 ∈ sourceVertices
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) W) :
    (unitDistanceGraph A).Adj source.1
      (bisectorSourceMiddle hA O L W source hs) :=
  alignedSourceMiddle_adj hA
    (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L)
    (Erdos957BisectorFrame.bisectorAlignedChartData O L) W source hs
    (fun q hq ↦
      Erdos957BisectorFrame.bisectorAlignedChartData_coord_snd_neg
        O L source q hq)

lemma bisectorSourceMiddle_in_open_cone {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (O : Erdos957.CyclicHullOrder A)
    (L : Erdos957TurnSum.HullOrderBridge.LiftedCyclicHullOrder O)
    (W : DiameterWitnessData (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L))
    (source : {p // p ∈
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L).H})
    (hs : source.1 ∈ sourceVertices
      (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L) W) :
    Erdos957Cases13.InOpenMiddleCone
      ((Erdos957BisectorFrame.bisectorAlignedChartData O L).coord source
        (bisectorSourceMiddle hA O L W source hs)) :=
  alignedSourceMiddle_in_open_cone hA
    (Erdos957HullGeometryBridge.cyclicHullDataOfOrder O L)
    (Erdos957BisectorFrame.bisectorAlignedChartData O L) W source hs
    (fun q hq ↦
      Erdos957BisectorFrame.bisectorAlignedChartData_coord_snd_neg
        O L source q hq)

/-- The local-coordinate specialization of the coordinate-free phase-bin
selection theorem. -/
theorem exists_middle_neighbor_in_open_cone {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3) :
    ∃ middle : Vertex A,
      (unitDistanceGraph A).Adj source.1 middle ∧
      Erdos957Cases13.InOpenMiddleCone (P.localCoord source middle) := by
  exact exists_middle_neighbor_in_open_cone_of_coord hA P source
    (P.localCoord source) (P.localCoord_source source)
    (P.sqDist_localCoord source) hdegree
    (fun q hq ↦ P.localCoord_snd_neg source q hq)

/-- Canonical source-indexed choice of the genuine middle neighbor. -/
noncomputable def middleNeighbor {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3) : Vertex A :=
  Classical.choose (exists_middle_neighbor_in_open_cone hA P source hdegree)

lemma middleNeighbor_adj {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3) :
    (unitDistanceGraph A).Adj source.1 (middleNeighbor hA P source hdegree) :=
  (Classical.choose_spec
    (exists_middle_neighbor_in_open_cone hA P source hdegree)).1

lemma middleNeighbor_in_open_cone {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hdegree : (unitDistanceGraph A).degree source.1 = 3) :
    Erdos957Cases13.InOpenMiddleCone
      (P.localCoord source (middleNeighbor hA P source hdegree)) :=
  (Classical.choose_spec
    (exists_middle_neighbor_in_open_cone hA P source hdegree)).2

/-- The canonical middle associated to an actual emitting source; its degree
proof is extracted from source membership rather than supplied separately. -/
noncomputable def sourceMiddle {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) : Vertex A :=
  middleNeighbor hA P source (source_facts hs).2.2

lemma sourceMiddle_adj {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) :
    (unitDistanceGraph A).Adj source.1 (sourceMiddle hA P W source hs) :=
  middleNeighbor_adj hA P source (source_facts hs).2.2

lemma sourceMiddle_in_open_cone {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) :
    Erdos957Cases13.InOpenMiddleCone
      (P.localCoord source (sourceMiddle hA P W source hs)) :=
  middleNeighbor_in_open_cone hA P source (source_facts hs).2.2

/-- The genuine source--middle edge is unit also in the exact source chart. -/
lemma sourceMiddle_sqDist_eq_one {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) :
    Erdos957Cases13.sqDist Erdos957Cases13.origin
      (P.localCoord source (sourceMiddle hA P W source hs)) = 1 := by
  change Erdos957Cases13.sqDist (0, 0)
    (P.localCoord source (sourceMiddle hA P W source hs)) = 1
  rw [← P.localCoord_source source, P.sqDist_localCoord,
    sourceMiddle_adj hA P W source hs]
  norm_num

/-- The actual selected middle lies in the transfer rectangle, independently
of which of the four cases occurs. -/
lemma sourceMiddle_in_localRectangle {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) :
    Erdos957GeometryLocalRows.InLocalRectangle P C source
      (sourceMiddle hA P W source hs) := by
  apply Erdos957Cases13.unit_point_in_sourceRectangle
  · change Erdos957Cases13.sqDist (0, 0)
      (C.coord source (sourceMiddle hA P W source hs)) = 1
    rw [← C.coord_source source, C.sqDist_coord,
      sourceMiddle_adj hA P W source hs]
    norm_num
  exact Erdos957GeometryLocalRows.sourceCoordinates_second_nonpos
    P C source (sourceMiddle hA P W source hs)

/-- Once the geometric hull-neighbor classification proves that the selected
middle is interior, it immediately becomes an actual local-row target. -/
def sourceMiddleLocalTarget {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hdegree : (unitDistanceGraph A).degree
      (sourceMiddle hA P W source hs) ≤ 5)
    (hnotHull : sourceMiddle hA P W source hs ∉ P.H) :
    Erdos957GeometryLocalRows.LocalTarget P C source where
  vertex := sourceMiddle hA P W source hs
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := sourceMiddle_in_localRectangle hA P C W source hs
  within_two := Or.inl (sourceMiddle_adj hA P W source hs)

/-- Any genuine unit neighbor of a source is an admissible local target as
soon as the geometric classification proves it is not extreme.  This is the
coordinate-free factory used by the generalized Case-3 kernel. -/
def unitNeighborLocalTarget {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (v : Vertex A)
    (hsv : (unitDistanceGraph A).Adj source.1 v)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) :
    Erdos957GeometryLocalRows.LocalTarget P C source where
  vertex := v
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := by
    apply Erdos957Cases13.unit_point_in_sourceRectangle
    · change Erdos957Cases13.sqDist (0, 0) (C.coord source v) = 1
      rw [← C.coord_source source, C.sqDist_coord, hsv]
      norm_num
    · exact Erdos957GeometryLocalRows.sourceCoordinates_second_nonpos P C source v
  within_two := Or.inl hsv

/-- Arbitrary-frame low Case 3: the actual middle receives the whole row.
No normalization to `(0,-1)` is present. -/
theorem case3Low_actualLocalCase {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hmiddleNotHull : sourceMiddle hA P W source hs ∉ P.H)
    (hmiddleDegree :
      (unitDistanceGraph A).degree (sourceMiddle hA P W source hs) ≤ 4) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P C source) := by
  exact ⟨Erdos957GeometryLocalRows.LocalCase.case3Low
    (sourceMiddleLocalTarget hA P C W source hs (by omega) hmiddleNotHull)
    hmiddleDegree⟩

/-- Arbitrary-frame high Case 3 from a genuine common unit neighbor.  The
middle/secondary roles and their graph incidences remain visible; no target
capacity or fixed-coordinate alignment is assumed. -/
theorem case3High_actualLocalCase_of_commonNeighbor {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W)
    (hmiddleNotHull : sourceMiddle hA P W source hs ∉ P.H)
    {secondary : Vertex A}
    (hsourceSecondary : (unitDistanceGraph A).Adj source.1 secondary)
    (hmiddleSecondary :
      (unitDistanceGraph A).Adj (sourceMiddle hA P W source hs) secondary)
    (hsecondaryNotHull : secondary ∉ P.H)
    (hmiddleDegree :
      (unitDistanceGraph A).degree (sourceMiddle hA P W source hs) = 5)
    (hsecondaryDegree : (unitDistanceGraph A).degree secondary ≤ 5) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P C source) := by
  let middleTarget :=
    sourceMiddleLocalTarget hA P C W source hs (by omega) hmiddleNotHull
  let secondaryTarget :=
    unitNeighborLocalTarget P C source secondary hsourceSecondary
      hsecondaryDegree hsecondaryNotHull
  have hdistinct : middleTarget.vertex ≠ secondaryTarget.vertex := by
    intro h
    have h' : sourceMiddle hA P W source hs = secondary := h
    rw [← h'] at hmiddleSecondary
    exact (unitDistanceGraph A).loopless.irrefl _ hmiddleSecondary
  exact ⟨Erdos957GeometryLocalRows.LocalCase.case3High
    middleTarget secondaryTarget hdistinct⟩

/-! ### Metric localization of every competing hull neighbor

This part needs neither a picture nor a cyclic-alignment premise.  A hull
vertex joined to the actual middle is reached from the source by two genuine
unit edges.  Isometry of the source chart therefore puts it in the much
smaller box `[-2,2] × [-2,0]`, and hence in the competing-source rectangle
used by the flat-chain locality argument.
-/

/-- Every unit neighbor of the actual middle is at Euclidean distance at most
two from the source. -/
lemma sourceMiddle_neighbor_dist_le_two {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) {w : Vertex A}
    (hmw : (unitDistanceGraph A).Adj (sourceMiddle hA P W source hs) w) :
    dist (source.1 : ComplexPoint) (w : ComplexPoint) ≤ 2 := by
  have htriangle := dist_triangle (source.1 : ComplexPoint)
    (sourceMiddle hA P W source hs : ComplexPoint) (w : ComplexPoint)
  rw [sourceMiddle_adj hA P W source hs, hmw] at htriangle
  norm_num at htriangle ⊢
  exact htriangle

/-- The source chart of any unit neighbor of the actual middle lies in the
strong box `[-2,2] × [-2,0]`. -/
lemma sourceMiddle_neighbor_local_box {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) {w : Vertex A}
    (hmw : (unitDistanceGraph A).Adj (sourceMiddle hA P W source hs) w) :
    -(2 : ℝ) ≤ (C.coord source w).1 ∧
      (C.coord source w).1 ≤ 2 ∧
      -(2 : ℝ) ≤ (C.coord source w).2 ∧
      (C.coord source w).2 ≤ 0 := by
  let z := C.coord source w
  have hdist := sourceMiddle_neighbor_dist_le_two hA P W source hs hmw
  have hsq : Erdos957Cases13.sqDist Erdos957Cases13.origin z ≤ 4 := by
    change Erdos957Cases13.sqDist (0, 0) z ≤ 4
    rw [← C.coord_source source]
    rw [C.sqDist_coord]
    nlinarith [dist_nonneg (x := (source.1 : ComplexPoint)) (y := (w : ComplexPoint))]
  have hxy : z.1 ^ 2 + z.2 ^ 2 ≤ 4 := by
    simpa [Erdos957Cases13.sqDist, Erdos957Cases13.origin] using hsq
  have hxSq : z.1 ^ 2 ≤ 4 := by nlinarith [sq_nonneg z.2]
  have hySq : z.2 ^ 2 ≤ 4 := by nlinarith [sq_nonneg z.1]
  have hxLower : -(2 : ℝ) ≤ z.1 := by nlinarith [sq_nonneg (z.1 + 2)]
  have hxUpper : z.1 ≤ 2 := by nlinarith [sq_nonneg (z.1 - 2)]
  have hyLower : -(2 : ℝ) ≤ z.2 := by nlinarith [sq_nonneg (z.2 + 2)]
  have hyUpper : z.2 ≤ 0 := by
    exact Erdos957GeometryLocalRows.sourceCoordinates_second_nonpos P C source w
  exact ⟨hxLower, hxUpper, hyLower, hyUpper⟩

/-- In particular every extreme unit neighbor of the actual middle is in
the enlarged competing-source rectangle of the global locality lemma. -/
lemma hullUnitNeighbor_mem_competingSourceRectangle {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData)
    (W : DiameterWitnessData P) (source : {p // p ∈ P.H})
    (hs : source.1 ∈ sourceVertices P W) {w : Vertex A}
    (hw : w ∈ hullUnitNeighbors P (sourceMiddle hA P W source hs)) :
    Erdos957Locality.InCompetingSourceRectangle (C.coord source w) := by
  have hbox := sourceMiddle_neighbor_local_box hA P C W source hs
    (mem_hullUnitNeighbors.mp hw).2
  rcases hbox with ⟨hxl, hxu, hyl, hyu⟩
  exact ⟨by linarith, by linarith, by linarith, hyu⟩

/-! ### Constructor-level target roles retained by actual local rows -/

/-- The seven finite target slots used by the per-source local rules. -/
inductive TargetRoleName
  | case1Left | case1Right
  | case2Outer | case2Secondary
  | case3Middle | case3Secondary
  | case4Primary | case4SecondaryLow
  | case4SplitLeft | case4SplitRight
  deriving DecidableEq

/-- A constructor-sensitive role assertion.  In addition to the finite role
name it retains the actual equality to the corresponding `LocalTarget`
vertex; this is the first half of the collision adapter's role descriptor.
Canonical coordinate equations are supplied by the geometric realization
which constructed the row. -/
def HasTargetRole {A : Finset ComplexPoint} {P : CyclicHullData A}
    {chart : P.AlignedChartData}
    {i : {p // p ∈ P.H}} (C : Erdos957GeometryLocalRows.LocalCase P chart i)
    (v : Vertex A) : TargetRoleName → Prop
  | .case1Left => match C with
      | .case1 left _ _ => v = left.vertex
      | _ => False
  | .case1Right => match C with
      | .case1 _ right _ => v = right.vertex
      | _ => False
  | .case2Outer => match C with
      | .case2 outer _ _ => v = outer.vertex
      | _ => False
  | .case2Secondary => match C with
      | .case2 _ secondary _ => v = secondary.vertex
      | _ => False
  | .case3Middle => match C with
      | .case3Low middle _ => v = middle.vertex
      | .case3High middle _ _ => v = middle.vertex
      | _ => False
  | .case3Secondary => match C with
      | .case3High _ secondary _ => v = secondary.vertex
      | _ => False
  | .case4Primary => match C with
      | .case4Primary middle _ => v = middle.vertex
      | _ => False
  | .case4SecondaryLow => match C with
      | .case4SecondaryLow low _ => v = low.vertex
      | _ => False
  | .case4SplitLeft => match C with
      | .case4SecondarySplit left _ _ => v = left.vertex
      | _ => False
  | .case4SplitRight => match C with
      | .case4SecondarySplit _ right _ => v = right.vertex
      | _ => False

/-- Every positive token has one of the finite actual target roles. -/
theorem positive_target_role {A : Finset ComplexPoint} {P : CyclicHullData A}
    {chart : P.AlignedChartData}
    {i : {p // p ∈ P.H}} (C : Erdos957GeometryLocalRows.LocalCase P chart i)
    {v : Vertex A} (hpos : 0 < C.tokens v) :
    ∃ role, HasTargetRole C v role := by
  cases C with
  | case1 left right hne =>
      simp only [Erdos957GeometryLocalRows.LocalCase.tokens] at hpos
      by_cases hl : v = left.vertex
      · exact ⟨.case1Left, hl⟩
      · by_cases hr : v = right.vertex
        · exact ⟨.case1Right, hr⟩
        · simp [hl, hr] at hpos
  | case2 outer secondary hne =>
      simp only [Erdos957GeometryLocalRows.LocalCase.tokens] at hpos
      by_cases ho : v = outer.vertex
      · exact ⟨.case2Outer, ho⟩
      · by_cases hs : v = secondary.vertex
        · exact ⟨.case2Secondary, hs⟩
        · simp [ho, hs] at hpos
  | case3Low middle hfour =>
      simp only [Erdos957GeometryLocalRows.LocalCase.tokens] at hpos
      by_cases hm : v = middle.vertex
      · exact ⟨.case3Middle, hm⟩
      · simp [hm] at hpos
  | case3High middle secondary hne =>
      simp only [Erdos957GeometryLocalRows.LocalCase.tokens] at hpos
      by_cases hm : v = middle.vertex
      · exact ⟨.case3Middle, hm⟩
      · by_cases hs : v = secondary.vertex
        · exact ⟨.case3Secondary, hs⟩
        · simp [hm, hs] at hpos
  | case4Primary middle hfour =>
      simp only [Erdos957GeometryLocalRows.LocalCase.tokens] at hpos
      by_cases hm : v = middle.vertex
      · exact ⟨.case4Primary, hm⟩
      · simp [hm] at hpos
  | case4SecondaryLow low hfour =>
      simp only [Erdos957GeometryLocalRows.LocalCase.tokens] at hpos
      by_cases hl : v = low.vertex
      · exact ⟨.case4SecondaryLow, hl⟩
      · simp [hl] at hpos
  | case4SecondarySplit left right hne =>
      simp only [Erdos957GeometryLocalRows.LocalCase.tokens] at hpos
      by_cases hl : v = left.vertex
      · exact ⟨.case4SplitLeft, hl⟩
      · by_cases hr : v = right.vertex
        · exact ⟨.case4SplitRight, hr⟩
        · simp [hl, hr] at hpos

/-- Role descriptor carried to collision assembly.  Besides the finite
constructor slot and equality to its actual `LocalTarget`, it names the
target's exact coordinate in the source chart.  Generalized geometric
kernels can strengthen `coordinate` to their affine/canonical formula
without changing the collision-facing shape of this record. -/
structure PositiveTargetRole {A : Finset ComplexPoint} {P : CyclicHullData A}
    {chart : P.AlignedChartData}
    {i : {p // p ∈ P.H}} (C : Erdos957GeometryLocalRows.LocalCase P chart i)
    (v : Vertex A) where
  role : TargetRoleName
  has_role : HasTargetRole C v role
  coordinate : Erdos957Cases13.Point
  coordinate_eq : Erdos957GeometryLocalRows.sourceCoordinates P chart i v = coordinate

/-- Every positive target has a concrete role and an exact source-chart
coordinate equation. -/
theorem positive_target_role_with_coordinate
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {chart : P.AlignedChartData}
    {i : {p // p ∈ P.H}} (C : Erdos957GeometryLocalRows.LocalCase P chart i)
    {v : Vertex A} (hpos : 0 < C.tokens v) :
    Nonempty (PositiveTargetRole C v) := by
  obtain ⟨role, hrole⟩ := positive_target_role C hpos
  exact ⟨{
    role := role
    has_role := hrole
    coordinate := Erdos957GeometryLocalRows.sourceCoordinates P chart i v
    coordinate_eq := rfl }⟩

/-- Honest normalized local geometry for Case 1.  The alignment fields say
which two already known neighbors are consecutive in the regular hexagon;
the degree bounds used by the transfer are derived by the checked bridge. -/
structure Case1Geometry (A hull : Finset Point) (middle : Point) where
  oneSeparated : IsOneSeparated (A : Set Point)
  support : ∀ p ∈ A, p.2 ≤ 0
  source_mem : origin ∈ A
  source_hull : origin ∈ hull
  source_degree : degree A origin = 3
  middle_mem : middle ∈ A
  middle_unit : sqDist origin middle = 1
  middle_in_cone : InOpenMiddleCone middle
  left_mem : case1Left middle ∈ A
  right_mem : case1Right middle ∈ A
  unique_hull_neighbor : ∀ p ∈ hull, sqDist middle p = 1 → p = origin
  left_alignment : degree A (case1Left middle) = 6 →
    ∃ hex : OrderedHexagonAt A (case1Left middle),
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = middle
  right_alignment : degree A (case1Right middle) = 6 →
    ∃ hex : OrderedHexagonAt A (case1Right middle),
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = middle

/-- Instantiation of the checked Case 1 constructor from local geometry. -/
theorem Case1Geometry.realize {A hull : Finset Point} {middle : Point}
    (G : Case1Geometry A hull middle) :
    Nonempty (Erdos957Case13Bridge.LocalTransfer A hull origin) := by
  exact case1_localTransfer G.oneSeparated G.support G.source_mem G.source_hull
    G.source_degree G.middle_mem G.middle_unit G.middle_in_cone
    G.left_mem G.right_mem G.unique_hull_neighbor
    G.left_alignment G.right_alignment

/-- Membership in the genuine finite local-coordinate copy has an actual
configuration vertex as a preimage.  This small inverse bridge is used to
turn the coordinate constructors into `GeometryLocalRows.LocalCase`s. -/
lemma exists_vertex_localCoord_eq {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) {p : Point}
    (hp : p ∈ P.localConfiguration source) :
    ∃ v : Vertex A, P.localCoord source v = p := by
  rcases Finset.mem_map.mp hp with ⟨v, _hv, hvp⟩
  exact ⟨v, hvp⟩

/-- A Case-1 row together with the two canonical coordinate equations from
which it was built.  Keeping these equations in the witness prevents the
collision layer from having to recover geometry from an erased `LocalCase`.
-/
structure Case1ActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Point) where
  left : Erdos957GeometryLocalRows.LocalTarget P C source
  right : Erdos957GeometryLocalRows.LocalTarget P C source
  left_coordinate : Erdos957GeometryLocalRows.sourceCoordinates P C source left.vertex =
    Erdos957Cases13.case1Left middle
  right_coordinate : Erdos957GeometryLocalRows.sourceCoordinates P C source right.vertex =
    Erdos957Cases13.case1Right middle
  distinct : left.vertex ≠ right.vertex

def Case1ActualRow.localCase {A : Finset ComplexPoint}
    {P : CyclicHullData A} {C : P.AlignedChartData}
    {source : {p // p ∈ P.H}} {middle : Point}
    (R : Case1ActualRow P C source middle) :
    Erdos957GeometryLocalRows.LocalCase P C source :=
  .case1 R.left R.right R.distinct

/-- An honest Case-1 coordinate picture over a genuine source chart produces
an actual per-source row.  The two targets are pulled back through the
injective chart; their non-hull facts are proved from the genuine unique
extreme-neighbor statement, and no target-capacity premise is used. -/
theorem Case1Geometry.toActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {middle : Point}
    (G : Case1Geometry (alignedConfiguration C source) (alignedHull C source) middle) :
    Nonempty (Case1ActualRow P C source middle) := by
  obtain ⟨left, hleftCoord⟩ :=
    exists_vertex_coord_eq C source G.left_mem
  obtain ⟨right, hrightCoord⟩ :=
    exists_vertex_coord_eq C source G.right_mem
  have hleftNotHull : left ∉ P.H := by
    intro hleftHull
    have hleftLocalHull := coord_mem_alignedHull C source hleftHull
    have heq := G.unique_hull_neighbor _ hleftLocalHull
      (by simpa [hleftCoord] using
        (Erdos957Cases13.case1Left_common_unit G.middle_unit).2)
    have hunit := (Erdos957Cases13.case1Left_common_unit G.middle_unit).1
    have hcanonical : Erdos957Cases13.case1Left middle =
        Erdos957Cases13.origin := hleftCoord.symm.trans heq
    rw [hcanonical, Erdos957Cases13.sqDist_self] at hunit
    norm_num at hunit
  have hrightNotHull : right ∉ P.H := by
    intro hrightHull
    have hrightLocalHull := coord_mem_alignedHull C source hrightHull
    have heq := G.unique_hull_neighbor _ hrightLocalHull
      (by simpa [hrightCoord] using
        (Erdos957Cases13.case1Right_common_unit G.middle_unit).2)
    have hunit := (Erdos957Cases13.case1Right_common_unit G.middle_unit).1
    have hcanonical : Erdos957Cases13.case1Right middle =
        Erdos957Cases13.origin := hrightCoord.symm.trans heq
    rw [hcanonical, Erdos957Cases13.sqDist_self] at hunit
    norm_num at hunit
  have hleftDegreeCoord : Erdos957Case13Bridge.degree
      (alignedConfiguration C source) (Erdos957Cases13.case1Left middle) ≤ 5 :=
    Erdos957Case13Bridge.case1_left_degree_le_five
      G.oneSeparated G.support G.middle_in_cone G.left_alignment
  have hrightDegreeCoord : Erdos957Case13Bridge.degree
      (alignedConfiguration C source) (Erdos957Cases13.case1Right middle) ≤ 5 :=
    Erdos957Case13Bridge.case1_right_degree_le_five
      G.oneSeparated G.support G.middle_in_cone G.right_alignment
  have hleftDegree : (unitDistanceGraph A).degree left ≤ 5 := by
    rw [← aligned_degree_coord C source left, hleftCoord]
    exact hleftDegreeCoord
  have hrightDegree : (unitDistanceGraph A).degree right ≤ 5 := by
    rw [← aligned_degree_coord C source right, hrightCoord]
    exact hrightDegreeCoord
  let leftTarget : Erdos957GeometryLocalRows.LocalTarget P C source :=
    Erdos957GeometryLocalRows.LocalTarget.ofCase1Left
      G.middle_unit G.middle_in_cone hleftCoord hleftDegree hleftNotHull
  let rightTarget : Erdos957GeometryLocalRows.LocalTarget P C source :=
    Erdos957GeometryLocalRows.LocalTarget.ofCase1Right
      G.middle_unit G.middle_in_cone hrightCoord hrightDegree hrightNotHull
  have hlr : leftTarget.vertex ≠ rightTarget.vertex := by
    intro h
    have hcoord := congrArg (C.coord source) h
    change C.coord source left = C.coord source right at hcoord
    rw [hleftCoord, hrightCoord] at hcoord
    exact (Erdos957Case13Bridge.case1Left_ne_case1Right G.middle_unit) hcoord
  exact ⟨{
    left := leftTarget
    right := rightTarget
    left_coordinate := hleftCoord
    right_coordinate := hrightCoord
    distinct := hlr }⟩

/-- Erasing the retained Case-1 formulas gives the row expected by the
global transfer assembly. -/
theorem Case1Geometry.toActualLocalCase {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {middle : Point}
    (G : Case1Geometry (alignedConfiguration C source) (alignedHull C source) middle) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P C source) := by
  obtain ⟨R⟩ := G.toActualRow P C source
  exact ⟨R.localCase⟩

/-!
The fixed `verticalDown` Case-3 adapter below is retained only as historical
text while the production proof uses the arbitrary-middle adapter following
it.  In particular none of these declarations are compiled or exported.

/-- Common factual inputs to the reflected Case 3 pictures. -/
structure Case3CommonGeometry (A hull : Finset Point) (candidate : Point) where
  oneSeparated : IsOneSeparated (A : Set Point)
  support : ∀ p ∈ A, p.2 ≤ 0
  source_mem : origin ∈ A
  source_hull : origin ∈ hull
  source_degree : degree A origin = 3
  middle_mem : verticalDown ∈ A
  candidate_mem : candidate ∈ A
  middle_degree_le_five : degree A verticalDown ≤ 5
  middle_not_hull : verticalDown ∉ hull
  unique_hull_neighbor : ∀ p ∈ hull,
    sqDist verticalDown p = 1 → p = origin
  candidate_source_unit : sqDist origin candidate = 1
  candidate_away_middle : 1 ≤ sqDist verticalDown candidate
  candidate_below : candidate.2 < 0

/-- Right-oriented Case 3 selection data. -/
structure Case3RightGeometry (A hull : Finset Point) (candidate selected : Point)
    extends Case3CommonGeometry A hull candidate where
  candidate_right : 0 ≤ candidate.1
  selected_mem : selected ∈ A
  selected_middle_unit : sqDist verticalDown selected = 1
  selected_away_source : 1 ≤ sqDist origin selected
  selected_high : verticalDown.2 ≤ selected.2
  selected_right : 0 ≤ selected.1
  selected_alignment : degree A selected = 6 →
    ∃ hex : OrderedHexagonAt A selected,
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = verticalDown

/-- Left-oriented Case 3 selection data. -/
structure Case3LeftGeometry (A hull : Finset Point) (candidate selected : Point)
    extends Case3CommonGeometry A hull candidate where
  candidate_left : candidate.1 ≤ 0
  selected_mem : selected ∈ A
  selected_middle_unit : sqDist verticalDown selected = 1
  selected_away_source : 1 ≤ sqDist origin selected
  selected_high : verticalDown.2 ≤ selected.2
  selected_left : selected.1 ≤ 0
  selected_alignment : degree A selected = 6 →
    ∃ hex : OrderedHexagonAt A selected,
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = verticalDown

theorem Case3RightGeometry.realize {A hull : Finset Point}
    {candidate selected : Point} (G : Case3RightGeometry A hull candidate selected) :
    Nonempty (Erdos957Case13Bridge.LocalTransfer A hull origin) := by
  exact case3_right_localTransfer G.oneSeparated G.support G.source_mem
    G.source_hull G.source_degree G.middle_mem G.candidate_mem G.selected_mem
    rfl G.middle_degree_le_five G.middle_not_hull G.unique_hull_neighbor
    G.candidate_source_unit G.candidate_away_middle G.candidate_below
    G.candidate_right G.selected_middle_unit G.selected_away_source
    G.selected_high G.selected_right G.selected_alignment

theorem Case3LeftGeometry.realize {A hull : Finset Point}
    {candidate selected : Point} (G : Case3LeftGeometry A hull candidate selected) :
    Nonempty (Erdos957Case13Bridge.LocalTransfer A hull origin) := by
  exact case3_left_localTransfer G.oneSeparated G.support G.source_mem
    G.source_hull G.source_degree G.middle_mem G.candidate_mem G.selected_mem
    rfl G.middle_degree_le_five G.middle_not_hull G.unique_hull_neighbor
    G.candidate_source_unit G.candidate_away_middle G.candidate_below
    G.candidate_left G.selected_middle_unit G.selected_away_source
    G.selected_high G.selected_left G.selected_alignment

/-- A normalized Case-3 row retaining the exact middle and common-neighbor
coordinates.  Even in the low branch the checked common-neighbor witness is
kept, so later collision arguments can use the same canonical chart data.
-/
inductive Case3ActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) (selected : Point)
    where
  | low (middle secondary : Erdos957GeometryLocalRows.LocalTarget P source)
      (middle_coordinate : Erdos957GeometryLocalRows.sourceCoordinates P source
        middle.vertex = Erdos957Cases13.verticalDown)
      (secondary_coordinate : Erdos957GeometryLocalRows.sourceCoordinates P source
        secondary.vertex = selected)
      (selected_source_unit : Erdos957Cases13.sqDist Erdos957Cases13.origin selected = 1)
      (selected_middle_unit : Erdos957Cases13.sqDist
        Erdos957Cases13.verticalDown selected = 1)
      (distinct : middle.vertex ≠ secondary.vertex)
      (middle_degree_le_four : (unitDistanceGraph A).degree middle.vertex ≤ 4)
  | high (middle secondary : Erdos957GeometryLocalRows.LocalTarget P source)
      (middle_coordinate : Erdos957GeometryLocalRows.sourceCoordinates P source
        middle.vertex = Erdos957Cases13.verticalDown)
      (secondary_coordinate : Erdos957GeometryLocalRows.sourceCoordinates P source
        secondary.vertex = selected)
      (selected_source_unit : Erdos957Cases13.sqDist Erdos957Cases13.origin selected = 1)
      (selected_middle_unit : Erdos957Cases13.sqDist
        Erdos957Cases13.verticalDown selected = 1)
      (distinct : middle.vertex ≠ secondary.vertex)

def Case3ActualRow.localCase {A : Finset ComplexPoint}
    {P : CyclicHullData A} {source : {p // p ∈ P.H}} {selected : Point} :
    Case3ActualRow P source selected → Erdos957GeometryLocalRows.LocalCase P source
  | .low middle _ _ _ _ _ _ hfour => .case3Low middle hfour
  | .high middle secondary _ _ _ _ hne => .case3High middle secondary hne

/-- Pull a checked Case-3 common-neighbor picture back to two actual
vertices of the original configuration.  The low/high split is computed
from the genuine degree in the source chart. -/
theorem case3_toActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) {selected : Point}
    (hmiddleMem : Erdos957Cases13.verticalDown ∈ P.localConfiguration source)
    (hselectedMem : selected ∈ P.localConfiguration source)
    (hmiddleNotHull : Erdos957Cases13.verticalDown ∉ P.localHull source)
    (hunique : ∀ p ∈ P.localHull source,
      Erdos957Cases13.sqDist Erdos957Cases13.verticalDown p = 1 →
        p = Erdos957Cases13.origin)
    (hselectedSource : Erdos957Cases13.sqDist Erdos957Cases13.origin selected = 1)
    (hselectedMiddle :
      Erdos957Cases13.sqDist Erdos957Cases13.verticalDown selected = 1)
    (hmiddleDegree : Erdos957Case13Bridge.degree
      (P.localConfiguration source) Erdos957Cases13.verticalDown ≤ 5)
    (hselectedDegree : Erdos957Case13Bridge.degree
      (P.localConfiguration source) selected ≤ 5) :
    Nonempty (Case3ActualRow P source selected) := by
  obtain ⟨middle, hmiddleCoord⟩ :=
    exists_vertex_localCoord_eq P source hmiddleMem
  obtain ⟨secondary, hsecondaryCoord⟩ :=
    exists_vertex_localCoord_eq P source hselectedMem
  have hmiddleNot : middle ∉ P.H := by
    intro hmH
    apply hmiddleNotHull
    have hmLocal := P.localCoord_mem_localHull source hmH
    simpa [hmiddleCoord] using hmLocal
  have hsecondaryNot : secondary ∉ P.H := by
    intro hsH
    have hsLocal := P.localCoord_mem_localHull source hsH
    have heq := hunique selected (by simpa [hsecondaryCoord] using hsLocal)
      hselectedMiddle
    have hunit := hselectedSource
    rw [heq, Erdos957Cases13.sqDist_self] at hunit
    norm_num at hunit
  have hmiddleActualDegree : (unitDistanceGraph A).degree middle ≤ 5 := by
    rw [← P.case13_degree_localCoord source middle, hmiddleCoord]
    exact hmiddleDegree
  have hsecondaryActualDegree : (unitDistanceGraph A).degree secondary ≤ 5 := by
    rw [← P.case13_degree_localCoord source secondary, hsecondaryCoord]
    exact hselectedDegree
  let middleTarget : Erdos957GeometryLocalRows.LocalTarget P source :=
    Erdos957GeometryLocalRows.LocalTarget.ofCase3Middle
      hmiddleCoord hmiddleActualDegree hmiddleNot
  have hselectedBelow : selected.2 ≤ 0 := by
    have h := Erdos957GeometryLocalRows.sourceCoordinates_second_nonpos
      P source secondary
    simpa [Erdos957GeometryLocalRows.sourceCoordinates, hsecondaryCoord] using h
  let secondaryTarget : Erdos957GeometryLocalRows.LocalTarget P source :=
    Erdos957GeometryLocalRows.LocalTarget.ofCase3Secondary
      hselectedSource hselectedMiddle hselectedBelow
      hsecondaryCoord hsecondaryActualDegree hsecondaryNot
  have hdistinct : middleTarget.vertex ≠ secondaryTarget.vertex := by
    intro h
    have hcoord := congrArg (P.localCoord source) h
    change P.localCoord source middle = P.localCoord source secondary at hcoord
    rw [hmiddleCoord, hsecondaryCoord] at hcoord
    exact (Erdos957Case13Bridge.verticalDown_ne_of_sqDist_origin_eq_one
      hselectedSource hselectedMiddle) hcoord
  by_cases hlow : Erdos957Case13Bridge.degree
      (P.localConfiguration source) Erdos957Cases13.verticalDown ≤ 4
  · have hlowActual : (unitDistanceGraph A).degree middle ≤ 4 := by
      rw [← P.case13_degree_localCoord source middle, hmiddleCoord]
      exact hlow
    exact ⟨.low middleTarget secondaryTarget hmiddleCoord hsecondaryCoord
      hselectedSource hselectedMiddle hdistinct hlowActual⟩
  · exact ⟨.high middleTarget secondaryTarget hmiddleCoord hsecondaryCoord
      hselectedSource hselectedMiddle hdistinct⟩

/-- Erasure of the retained normalized Case-3 formulas. -/
theorem case3_toActualLocalCase {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) {selected : Point}
    (hmiddleMem : Erdos957Cases13.verticalDown ∈ P.localConfiguration source)
    (hselectedMem : selected ∈ P.localConfiguration source)
    (hmiddleNotHull : Erdos957Cases13.verticalDown ∉ P.localHull source)
    (hunique : ∀ p ∈ P.localHull source,
      Erdos957Cases13.sqDist Erdos957Cases13.verticalDown p = 1 →
        p = Erdos957Cases13.origin)
    (hselectedSource : Erdos957Cases13.sqDist Erdos957Cases13.origin selected = 1)
    (hselectedMiddle :
      Erdos957Cases13.sqDist Erdos957Cases13.verticalDown selected = 1)
    (hmiddleDegree : Erdos957Case13Bridge.degree
      (P.localConfiguration source) Erdos957Cases13.verticalDown ≤ 5)
    (hselectedDegree : Erdos957Case13Bridge.degree
      (P.localConfiguration source) selected ≤ 5) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P source) := by
  obtain ⟨R⟩ := case3_toActualRow P source hmiddleMem hselectedMem
    hmiddleNotHull hunique hselectedSource hselectedMiddle
    hmiddleDegree hselectedDegree
  exact ⟨R.localCase⟩

/-- Right-oriented Case 3 yields a source-indexed row retaining its canonical
middle and common-neighbor coordinates. -/
theorem Case3RightGeometry.toActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    {candidate selected : Point}
    (G : Case3RightGeometry (P.localConfiguration source)
      (P.localHull source) candidate selected) :
    Nonempty (Case3ActualRow P source selected) := by
  have heq := Erdos957Cases13.case3_right_candidate_eq_existing_of_oneSeparated
    G.oneSeparated G.candidate_mem G.selected_mem
    G.candidate_source_unit G.candidate_away_middle G.candidate_below
    G.candidate_right G.selected_middle_unit G.selected_away_source
    G.selected_high G.selected_right
  have hselectedSource :
      Erdos957Cases13.sqDist Erdos957Cases13.origin selected = 1 := by
    simpa [heq] using G.candidate_source_unit
  have hselectedDegree :=
    Erdos957Case13Bridge.case3_secondary_degree_le_five G.oneSeparated
      G.support hselectedSource G.selected_middle_unit G.selected_alignment
  exact case3_toActualRow P source G.middle_mem G.selected_mem
    G.middle_not_hull G.unique_hull_neighbor hselectedSource
    G.selected_middle_unit G.middle_degree_le_five hselectedDegree

/-- Erasure of a right-oriented realized Case-3 row. -/
theorem Case3RightGeometry.toActualLocalCase {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    {candidate selected : Point}
    (G : Case3RightGeometry (P.localConfiguration source)
      (P.localHull source) candidate selected) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P source) := by
  obtain ⟨R⟩ := G.toActualRow P source
  exact ⟨R.localCase⟩

/-- Left-oriented Case 3 yields a source-indexed row retaining its canonical
middle and common-neighbor coordinates. -/
theorem Case3LeftGeometry.toActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    {candidate selected : Point}
    (G : Case3LeftGeometry (P.localConfiguration source)
      (P.localHull source) candidate selected) :
    Nonempty (Case3ActualRow P source selected) := by
  have hsep := Erdos957Cases13.eq_or_one_le_sqDist_of_oneSeparated
    G.oneSeparated G.candidate_mem G.selected_mem
  have heq := Erdos957Cases13.case3_left_candidate_eq_existing
    G.candidate_source_unit G.candidate_away_middle G.candidate_below
    G.candidate_left G.selected_middle_unit G.selected_away_source
    G.selected_high G.selected_left hsep
  have hselectedSource :
      Erdos957Cases13.sqDist Erdos957Cases13.origin selected = 1 := by
    simpa [heq] using G.candidate_source_unit
  have hselectedDegree :=
    Erdos957Case13Bridge.case3_secondary_degree_le_five G.oneSeparated
      G.support hselectedSource G.selected_middle_unit G.selected_alignment
  exact case3_toActualRow P source G.middle_mem G.selected_mem
    G.middle_not_hull G.unique_hull_neighbor hselectedSource
    G.selected_middle_unit G.middle_degree_le_five hselectedDegree

/-- Erasure of a left-oriented realized Case-3 row. -/
theorem Case3LeftGeometry.toActualLocalCase {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    {candidate selected : Point}
    (G : Case3LeftGeometry (P.localConfiguration source)
      (P.localHull source) candidate selected) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P source) := by
  obtain ⟨R⟩ := G.toActualRow P source
  exact ⟨R.localCase⟩

-/

/-! ### Arbitrary-middle Case 3 in the common aligned chart -/

/-- Honest Case-3 geometry in the chart actually shared with locality. -/
structure Case3Geometry (A hull : Finset Point) (middle secondary : Point) where
  oneSeparated : IsOneSeparated (A : Set Point)
  support : ∀ p ∈ A, p.2 ≤ 0
  source_mem : origin ∈ A
  source_hull : origin ∈ hull
  source_degree : degree A origin = 3
  middle_mem : middle ∈ A
  secondary_mem : secondary ∈ A
  middle_degree_le_five : degree A middle ≤ 5
  middle_not_hull : middle ∉ hull
  unique_hull_neighbor : ∀ p ∈ hull, sqDist middle p = 1 → p = origin
  middle_unit : sqDist origin middle = 1
  middle_in_cone : InOpenMiddleCone middle
  secondary_source_unit : sqDist origin secondary = 1
  secondary_middle_unit : sqDist middle secondary = 1
  secondary_high : middle.2 < secondary.2

/-- The production arbitrary-middle kernel produces the intended transfer
without rotating the middle to `verticalDown`. -/
theorem Case3Geometry.realize {A hull : Finset Point} {middle secondary : Point}
    (G : Case3Geometry A hull middle secondary) :
    Nonempty (Erdos957Case13Bridge.LocalTransfer A hull origin) := by
  exact Erdos957Case3General.localTransfer_of_common_neighbor
    G.oneSeparated G.support G.source_mem G.source_hull G.source_degree
    G.middle_mem G.secondary_mem rfl G.middle_degree_le_five
    G.middle_not_hull G.unique_hull_neighbor G.middle_unit G.middle_in_cone
    G.secondary_source_unit G.secondary_middle_unit G.secondary_high

/-- A source-unit target at an arbitrary formula in the shared aligned
chart.  Rectangle membership and the graph incidence are derived from the
formula, rather than supplied as charging assumptions. -/
def alignedUnitLocalTarget {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (v : Vertex A) (q : Point)
    (hcoord : C.coord source v = q)
    (hunit : Erdos957Cases13.sqDist Erdos957Cases13.origin q = 1)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hnotHull : v ∉ P.H) :
    Erdos957GeometryLocalRows.LocalTarget P C source where
  vertex := v
  not_hull := hnotHull
  degree_le_five := hdegree
  in_rectangle := by
    rw [Erdos957GeometryLocalRows.InLocalRectangle,
      Erdos957GeometryLocalRows.sourceCoordinates, hcoord]
    exact Erdos957Cases13.unit_point_in_sourceRectangle hunit
      (by simpa [hcoord] using C.coord_snd_nonpos source v)
  within_two := by
    apply Or.inl
    have hsquare : dist (source.1 : ComplexPoint) (v : ComplexPoint) ^ 2 = 1 := by
      rw [← C.sqDist_coord source source.1 v, C.coord_source, hcoord]
      exact hunit
    rcases sq_eq_one_iff.mp hsquare with h | h
    · exact h
    · exfalso
      nlinarith [dist_nonneg (x := (source.1 : ComplexPoint)) (y := (v : ComplexPoint))]

/-- Formula-retaining arbitrary-middle Case-3 row. -/
inductive Case3ActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middleCoord : Point) where
  | low (middle : Erdos957GeometryLocalRows.LocalTarget P C source)
      (middle_coordinate : C.coord source middle.vertex = middleCoord)
      (middle_unit : sqDist origin middleCoord = 1)
      (middle_degree_le_four : (unitDistanceGraph A).degree middle.vertex ≤ 4)
  | high (secondaryCoord : Point)
      (middle secondary : Erdos957GeometryLocalRows.LocalTarget P C source)
      (middle_coordinate : C.coord source middle.vertex = middleCoord)
      (secondary_coordinate : C.coord source secondary.vertex = secondaryCoord)
      (middle_unit : sqDist origin middleCoord = 1)
      (secondary_source_unit : sqDist origin secondaryCoord = 1)
      (secondary_middle_unit : sqDist middleCoord secondaryCoord = 1)
      (distinct : middle.vertex ≠ secondary.vertex)

def Case3ActualRow.localCase {A : Finset ComplexPoint}
    {P : CyclicHullData A} {C : P.AlignedChartData}
    {source : {p // p ∈ P.H}} {middleCoord : Point} :
    Case3ActualRow P C source middleCoord →
      Erdos957GeometryLocalRows.LocalCase P C source
  | .low middle _ _ hfour => .case3Low middle hfour
  | .high _ middle secondary _ _ _ _ _ hne => .case3High middle secondary hne

/-- The distinguished middle recipient retained by either Case-3 row. -/
def Case3ActualRow.middleTarget {A : Finset ComplexPoint}
    {P : CyclicHullData A} {C : P.AlignedChartData}
    {source : {p // p ∈ P.H}} {middleCoord : Point} :
    Case3ActualRow P C source middleCoord →
      Erdos957GeometryLocalRows.LocalTarget P C source
  | .low middle _ _ _ => middle
  | .high _ middle _ _ _ _ _ _ _ => middle

/-- Pull the arbitrary-middle coordinate row back to genuine vertices. -/
theorem Case3Geometry.toActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {middle secondary : Point}
    (G : Case3Geometry (alignedConfiguration C source) (alignedHull C source)
      middle secondary) :
    Nonempty (Case3ActualRow P C source middle) := by
  obtain ⟨middleVertex, hmiddleCoord⟩ :=
    exists_vertex_coord_eq C source G.middle_mem
  obtain ⟨secondaryVertex, hsecondaryCoord⟩ :=
    exists_vertex_coord_eq C source G.secondary_mem
  have hmiddleNot : middleVertex ∉ P.H := by
    intro hmH
    exact G.middle_not_hull (by
      simpa [hmiddleCoord] using coord_mem_alignedHull C source hmH)
  have hsecondaryNot : secondaryVertex ∉ P.H := by
    intro hsH
    have hsLocal := coord_mem_alignedHull C source hsH
    have heq := G.unique_hull_neighbor secondary
      (by simpa [hsecondaryCoord] using hsLocal) G.secondary_middle_unit
    have hu := G.secondary_source_unit
    rw [heq, Erdos957Cases13.sqDist_self] at hu
    norm_num at hu
  have hmiddleDegree : (unitDistanceGraph A).degree middleVertex ≤ 5 := by
    rw [← aligned_degree_coord C source middleVertex, hmiddleCoord]
    exact G.middle_degree_le_five
  have hsecondaryDegreeCoord : Erdos957Case13Bridge.degree
      (alignedConfiguration C source) secondary ≤ 5 :=
    Erdos957Case3General.secondary_degree_le_five G.oneSeparated G.support
      G.source_mem G.middle_mem G.middle_unit G.secondary_source_unit
      G.secondary_middle_unit G.secondary_high
  have hsecondaryDegree : (unitDistanceGraph A).degree secondaryVertex ≤ 5 := by
    rw [← aligned_degree_coord C source secondaryVertex, hsecondaryCoord]
    exact hsecondaryDegreeCoord
  let middleTarget := alignedUnitLocalTarget C source middleVertex middle
    hmiddleCoord G.middle_unit hmiddleDegree hmiddleNot
  let secondaryTarget := alignedUnitLocalTarget C source secondaryVertex secondary
    hsecondaryCoord G.secondary_source_unit hsecondaryDegree hsecondaryNot
  have hdistinct : middleTarget.vertex ≠ secondaryTarget.vertex := by
    intro h
    have hcoord := congrArg (C.coord source) h
    change C.coord source middleVertex = C.coord source secondaryVertex at hcoord
    rw [hmiddleCoord, hsecondaryCoord] at hcoord
    exact (Erdos957Case3General.middle_ne_secondary_of_unit
      G.secondary_middle_unit) hcoord
  by_cases hlow : Erdos957Case13Bridge.degree
      (alignedConfiguration C source) middle ≤ 4
  · have hlowActual : (unitDistanceGraph A).degree middleVertex ≤ 4 := by
      rw [← aligned_degree_coord C source middleVertex, hmiddleCoord]
      exact hlow
    exact ⟨.low middleTarget hmiddleCoord G.middle_unit hlowActual⟩
  · exact ⟨.high secondary middleTarget secondaryTarget hmiddleCoord hsecondaryCoord
      G.middle_unit G.secondary_source_unit G.secondary_middle_unit hdistinct⟩

/-- Erasure into the global row interface. -/
theorem Case3Geometry.toActualLocalCase {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {middle secondary : Point}
    (G : Case3Geometry (alignedConfiguration C source) (alignedHull C source)
      middle secondary) :
    Nonempty (Erdos957GeometryLocalRows.LocalCase P C source) := by
  obtain ⟨R⟩ := G.toActualRow P C source
  exact ⟨R.localCase⟩

end PairCases

/-! ## Incoming unit-edge frame to the genuine bisector chart -/

namespace ActualCase24Rows

open Erdos957
open Erdos957TurnSum
open Erdos957TurnSum.HullOrderBridge
open Erdos957HullGeometryBridge
open Erdos957BisectorFrame
open Erdos957EdgeFrame
open Erdos957ChartTransport
open Erdos957Case24Bridge.Framed

/-- A distance-preserving rigid chart preserves the elementary obstruction
that an extreme point cannot lie strictly between two configuration points.
This form is convenient because the edge chart itself need not expose its
affine formula to the later canonical case analysis. -/
lemma actual_right_not_mem_of_middle_extreme
    {A : Finset ComplexPoint} (F : RigidChart)
    {left middle right : Erdos957Cases24.Point}
    (hleft : F.actual left ∈ A)
    (hmiddleExtreme : F.actual middle ∈
      (convexHull ℝ (A : Set ComplexPoint)).extremePoints ℝ)
    (hsum : dist left middle + dist middle right = dist left right)
    (hleftNe : left ≠ middle) (hrightNe : right ≠ middle) :
    F.actual right ∉ A := by
  intro hright
  have hsegment : F.actual middle ∈
      segment ℝ (F.actual left) (F.actual right) := by
    rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff]
    simpa only [F.dist_actual] using hsum
  have hleftHull : F.actual left ∈ convexHull ℝ (A : Set ComplexPoint) :=
    (subset_convexHull ℝ (A : Set ComplexPoint)) hleft
  have hrightHull : F.actual right ∈ convexHull ℝ (A : Set ComplexPoint) :=
    (subset_convexHull ℝ (A : Set ComplexPoint)) hright
  have hend := (mem_extremePoints_iff_forall_segment.mp hmiddleExtreme).2
    (F.actual left) hleftHull (F.actual right) hrightHull hsegment
  rcases hend with h | h
  · exact hleftNe (F.actual_injective h)
  · exact hrightNe (F.actual_injective h)

/-- The terminal chart of an actual consecutive unit hull edge has strict
lower-half-plane support away from its two endpoints.  Closed edge support
gives `y ≤ 0`.  If equality held, separation forces the third point beyond
one endpoint of the unit segment, so that endpoint would cease to be an
extreme point of the convex hull. -/
theorem terminalUnitEdgeRigidChart_strictlyBelowOutside
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (hunit : dist ((P.next⁻¹ source).1.1 : ComplexPoint)
      (source.1.1 : ComplexPoint) = 1) :
    let F := terminalUnitEdgeRigidChart
      (P.next⁻¹ source).1.1 source.1.1 hunit
    Erdos957Case24Bridge.StrictlyBelowOutside (F.image A)
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u} := by
  let p : ComplexPoint := (P.next⁻¹ source).1.1
  let o : ComplexPoint := source.1.1
  let F := terminalUnitEdgeRigidChart p o hunit
  have hpA : F.actual Erdos957Cases24.Case2.uPrev ∈ A := by
    rw [terminalUnitEdgeRigidChart_actual_case2_uPrev]
    exact (P.next⁻¹ source).1.property
  have hoA : F.actual Erdos957Cases24.Case2.u ∈ A := by
    rw [terminalUnitEdgeRigidChart_actual_case2_u]
    exact source.1.property
  have hpExtreme : F.actual Erdos957Cases24.Case2.uPrev ∈
      (convexHull ℝ (A : Set ComplexPoint)).extremePoints ℝ := by
    rw [terminalUnitEdgeRigidChart_actual_case2_uPrev]
    exact (P.hull_exact (P.next⁻¹ source).1).mp (P.next⁻¹ source).property
  have hoExtreme : F.actual Erdos957Cases24.Case2.u ∈
      (convexHull ℝ (A : Set ComplexPoint)).extremePoints ℝ := by
    rw [terminalUnitEdgeRigidChart_actual_case2_u]
    exact (P.hull_exact source.1).mp source.property
  have hsep := F.image_oneSeparated hA
  change Erdos957Case24Bridge.StrictlyBelowOutside (F.image A)
    {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u}
  intro z hzB hzBoundary
  have hzA : F.actual z ∈ A := F.mem_image_iff.mp hzB
  let q : Erdos957GeometryCore.Vertex A := ⟨F.actual z, hzA⟩
  have hyLe : z 1 ≤ 0 := by
    have hs := P.edge_support (P.next⁻¹ source) q
    have hnext : P.next (P.next⁻¹ source) = source := by simp
    rw [hnext] at hs
    rw [← F.toCanonical_actual z,
      terminalUnitEdgeRigidChart_toCanonical, edgePointCoord_apply_one]
    simp only [edgePairCoord, Erdos957GeometryCore.cross, PiLp.sub_apply,
      Prod.snd] at hs ⊢
    nlinarith
  refine lt_of_le_of_ne hyLe ?_
  intro hyZero
  have hzNePrev : z ≠ Erdos957Cases24.Case2.uPrev := by
    intro h
    apply hzBoundary
    simp [h]
  have hzNeU : z ≠ Erdos957Cases24.Case2.u := by
    intro h
    apply hzBoundary
    simp [h]
  have hsepU : 1 ≤ dist z Erdos957Cases24.Case2.u :=
    hsep z hzB Erdos957Cases24.Case2.u
      (F.mem_image_iff.mpr hoA) hzNeU
  have hsepPrev : 1 ≤ dist z Erdos957Cases24.Case2.uPrev :=
    hsep z hzB Erdos957Cases24.Case2.uPrev
      (F.mem_image_iff.mpr hpA) hzNePrev
  have hsepUSq : 1 ≤ dist z Erdos957Cases24.Case2.u ^ 2 := by
    nlinarith [dist_nonneg (x := z) (y := Erdos957Cases24.Case2.u)]
  have hsepPrevSq : 1 ≤ dist z Erdos957Cases24.Case2.uPrev ^ 2 := by
    nlinarith [dist_nonneg (x := z) (y := Erdos957Cases24.Case2.uPrev)]
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsepUSq hsepPrevSq
  simp only [Erdos957Cases24.Case2.u,
    Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one] at hsepUSq hsepPrevSq
  have hxNeNegOne : z 0 ≠ -1 := by
    intro hx
    apply hzNePrev
    apply Erdos957Cases24.point_ext
    · simpa [Erdos957Cases24.Case2.uPrev] using hx
    · simpa [Erdos957Cases24.Case2.uPrev] using hyZero
  by_cases hxNonneg : 0 ≤ z 0
  · have hxOne : 1 ≤ z 0 := by
      nlinarith [sq_nonneg (z 0 - 1)]
    have hsum : dist Erdos957Cases24.Case2.uPrev
        Erdos957Cases24.Case2.u +
        dist Erdos957Cases24.Case2.u z =
        dist Erdos957Cases24.Case2.uPrev z := by
      have huSq := Erdos957Cases24.dist_sq_eq_coordinates
        Erdos957Cases24.Case2.u z
      have hpSq := Erdos957Cases24.dist_sq_eq_coordinates
        Erdos957Cases24.Case2.uPrev z
      have huNonneg := dist_nonneg (x := Erdos957Cases24.Case2.u) (y := z)
      have hpNonneg := dist_nonneg (x := Erdos957Cases24.Case2.uPrev) (y := z)
      have huEqSq : dist Erdos957Cases24.Case2.u z ^ 2 = (z 0) ^ 2 := by
        calc
          _ = (0 - z 0) ^ 2 + (0 - z 1) ^ 2 := by
            simpa [Erdos957Cases24.Case2.u] using huSq
          _ = _ := by rw [hyZero]; ring
      have hpEqSq : dist Erdos957Cases24.Case2.uPrev z ^ 2 =
          (z 0 + 1) ^ 2 := by
        calc
          _ = (-1 - z 0) ^ 2 + (0 - z 1) ^ 2 := by
            simpa [Erdos957Cases24.Case2.uPrev] using hpSq
          _ = _ := by rw [hyZero]; ring
      have huDist : dist Erdos957Cases24.Case2.u z = z 0 :=
        (sq_eq_sq₀ huNonneg hxNonneg).mp huEqSq
      have hpDist : dist Erdos957Cases24.Case2.uPrev z = z 0 + 1 :=
        (sq_eq_sq₀ hpNonneg (by linarith)).mp hpEqSq
      rw [Erdos957Cases24.Case2.dist_uPrev_u]
      rw [huDist, hpDist]
      ring
    exact actual_right_not_mem_of_middle_extreme F hpA hoExtreme hsum
      (by norm_num [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u, Erdos957Cases24.point_inj])
      hzNeU hzA
  · have hxNeg : z 0 < 0 := lt_of_not_ge hxNonneg
    have hxLeNegOne : z 0 ≤ -1 := by
      nlinarith [sq_nonneg (z 0 + 1)]
    have hxLtNegOne : z 0 < -1 := lt_of_le_of_ne hxLeNegOne hxNeNegOne
    have hxLeNegTwo : z 0 ≤ -2 := by
      nlinarith [sq_nonneg (z 0 + 2)]
    have hsum : dist z Erdos957Cases24.Case2.uPrev +
        dist Erdos957Cases24.Case2.uPrev Erdos957Cases24.Case2.u =
        dist z Erdos957Cases24.Case2.u := by
      have hpSq := Erdos957Cases24.dist_sq_eq_coordinates z
        Erdos957Cases24.Case2.uPrev
      have huSq := Erdos957Cases24.dist_sq_eq_coordinates z
        Erdos957Cases24.Case2.u
      have hpNonneg := dist_nonneg (x := z)
        (y := Erdos957Cases24.Case2.uPrev)
      have huNonneg := dist_nonneg (x := z)
        (y := Erdos957Cases24.Case2.u)
      have hpEqSq : dist z Erdos957Cases24.Case2.uPrev ^ 2 =
          (-(z 0 + 1)) ^ 2 := by
        calc
          _ = (z 0 - -1) ^ 2 + (z 1 - 0) ^ 2 := by
            simpa [Erdos957Cases24.Case2.uPrev] using hpSq
          _ = _ := by rw [hyZero]; ring
      have huEqSq : dist z Erdos957Cases24.Case2.u ^ 2 =
          (-z 0) ^ 2 := by
        calc
          _ = (z 0 - 0) ^ 2 + (z 1 - 0) ^ 2 := by
            simpa [Erdos957Cases24.Case2.u] using huSq
          _ = _ := by rw [hyZero]; ring
      have hpDist : dist z Erdos957Cases24.Case2.uPrev = -(z 0 + 1) :=
        (sq_eq_sq₀ hpNonneg (by linarith)).mp hpEqSq
      have huDist : dist z Erdos957Cases24.Case2.u = -z 0 :=
        (sq_eq_sq₀ huNonneg (by linarith)).mp huEqSq
      rw [Erdos957Cases24.Case2.dist_uPrev_u]
      rw [hpDist, huDist]
      ring
    have := actual_right_not_mem_of_middle_extreme F hoA hpExtreme
      (by simpa [dist_comm, add_comm] using hsum)
      (by norm_num [Erdos957Cases24.Case2.u,
        Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_inj])
      hzNePrev hzA
    exact this

/-- The coordinate-file degree and the actual unit-distance-graph degree are
the same count; the former forgets only the membership proof carried by a
`Vertex`. -/
lemma graph_degree_eq_unitDegree {A : Finset ComplexPoint}
    (v : Erdos957GeometryCore.Vertex A) :
    (unitDistanceGraph A).degree v =
      Erdos957Case24Bridge.unitDegree A (v : ComplexPoint) := by
  classical
  rw [SimpleGraph.degree, Erdos957Case24Bridge.unitDegree]
  apply Finset.card_bij
    (s := (unitDistanceGraph A).neighborFinset v)
    (t := Erdos957Cases24.unitNeighbors A (v : ComplexPoint))
    (fun w _ ↦ (w : ComplexPoint))
  · intro w hw
    apply Erdos957Cases24.mem_unitNeighbors.mpr
    refine ⟨w.property, ?_⟩
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := v) w).mp hw
  · intro w _ z _ hwz
    exact Subtype.ext hwz
  · intro p hp
    let w : Erdos957GeometryCore.Vertex A :=
      ⟨p, (Erdos957Cases24.mem_unitNeighbors.mp hp).1⟩
    refine ⟨w, ?_, rfl⟩
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := v) w).mpr
        (Erdos957Cases24.mem_unitNeighbors.mp hp).2

/-- The actual vertex represented by one canonical point of a rigid chart. -/
def actualVertex {A : Finset ComplexPoint} (F : RigidChart)
    (q : Erdos957Cases24.Point) (hq : F.actual q ∈ A) :
    Erdos957GeometryCore.Vertex A := ⟨F.actual q, hq⟩

@[simp] lemma actualVertex_coe {A : Finset ComplexPoint} (F : RigidChart)
    (q : Erdos957Cases24.Point) (hq : F.actual q ∈ A) :
    ((actualVertex F q hq : Erdos957GeometryCore.Vertex A) : ComplexPoint) =
      F.actual q := rfl

/-- A canonical unit edge transports to an actual graph edge once both
endpoints are known members of the configuration. -/
lemma actualVertex_adj {A : Finset ComplexPoint} (F : RigidChart)
    {p q : Erdos957Cases24.Point} (hp : F.actual p ∈ A)
    (hq : F.actual q ∈ A) (hpq : dist p q = 1) :
    (unitDistanceGraph A).Adj (actualVertex F p hp) (actualVertex F q hq) := by
  change dist (F.actual p) (F.actual q) = 1
  rw [F.dist_actual]
  exact hpq

/-- The lower intersection of the two unit circles centered at the two
canonical hull-edge endpoints is exactly the Case-2/4 middle point. -/
lemma eq_case2_v_of_unit_to_u_uPrev_of_snd_nonpos
    {z : Erdos957Cases24.Point}
    (hu : dist z Erdos957Cases24.Case2.u = 1)
    (hp : dist z Erdos957Cases24.Case2.uPrev = 1)
    (hz : z 1 ≤ 0) : z = Erdos957Cases24.Case2.v := by
  have huSq := congrArg (fun r : ℝ ↦ r ^ 2) hu
  have hpSq := congrArg (fun r : ℝ ↦ r ^ 2) hp
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at huSq hpSq
  simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at huSq hpSq
  have hx : z 0 = -(1 / 2 : ℝ) := by nlinarith
  have hy : z 1 = -(Erdos957Cases24.sqrtThree / 2) := by
    have hsqrtPos := Erdos957Cases24.sqrtThree_pos
    have hsqrtSq := Erdos957Cases24.sqrtThree_sq
    nlinarith [sq_nonneg (z 1 + Erdos957Cases24.sqrtThree / 2)]
  exact Erdos957Cases24.point_ext hx (by
    simpa [Erdos957Cases24.Case2.v] using hy)

lemma case2_v_add_u_sub_uPrev_eq_b :
    Erdos957Cases24.Case2.v + Erdos957Cases24.Case2.u -
      Erdos957Cases24.Case2.uPrev = Erdos957Cases24.Case2.b := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.b]
  norm_num

lemma case2_v_add_b_sub_u_eq_w :
    Erdos957Cases24.Case2.v + Erdos957Cases24.Case2.b -
      Erdos957Cases24.Case2.u = Erdos957Cases24.Case2.w := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.w]
  ring

lemma case4_v_add_w_sub_b_eq_a :
    Erdos957Cases24.Case4.v + Erdos957Cases24.Case4.w -
      Erdos957Cases24.Case4.b = Erdos957Cases24.Case4.a := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case4.v, Erdos957Cases24.Case4.w,
      Erdos957Cases24.Case4.b, Erdos957Cases24.Case4.a,
      Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.w,
      Erdos957Cases24.Case2.b]
  ring

/-- Degree six at the normalized middle and the two equilateral hull-edge
endpoints force the entire five-point Case-4 display.  Each new point is an
oriented regular-hexagon completion, so no diagram incidence is assumed. -/
theorem case4_displayedFiveAtV_subset_of_degree_six
    {B : Finset Erdos957Cases24.Point}
    (hsep : Erdos957Cases24.IsOneSeparated B)
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ B)
    (hu : Erdos957Cases24.Case2.u ∈ B)
    (hdegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case4.v = 6) :
    Erdos957Cases24.Case4.displayedFiveAtV ⊆ B := by
  have hb : Erdos957Cases24.Case4.b ∈ B := by
    change Erdos957Cases24.Case2.b ∈ B
    rw [← case2_v_add_u_sub_uPrev_eq_b]
    exact Erdos957Case24Bridge.hexagon_completion_mem hsep hu huPrev
      (by simpa [Erdos957Cases24.Case4.v, dist_comm] using
        Erdos957Cases24.Case2.dist_u_v)
      (by simpa [Erdos957Cases24.Case4.v, dist_comm] using
        Erdos957Cases24.Case2.dist_uPrev_v)
      (by simpa [dist_comm] using Erdos957Cases24.Case2.dist_uPrev_u) hdegree
  have hw : Erdos957Cases24.Case4.w ∈ B := by
    change Erdos957Cases24.Case2.w ∈ B
    rw [← case2_v_add_b_sub_u_eq_w]
    exact Erdos957Case24Bridge.hexagon_completion_mem hsep hb hu
      (by simpa [Erdos957Cases24.Case4.v, Erdos957Cases24.Case4.b]
        using Erdos957Cases24.Case2.dist_v_b)
      (by simpa [Erdos957Cases24.Case4.v, dist_comm]
        using Erdos957Cases24.Case2.dist_u_v)
      (by simpa [Erdos957Cases24.Case4.b, dist_comm] using
        Erdos957Cases24.Case2.dist_u_b) hdegree
  have ha : Erdos957Cases24.Case4.a ∈ B := by
    rw [← case4_v_add_w_sub_b_eq_a]
    exact Erdos957Case24Bridge.hexagon_completion_mem hsep hw hb
      (by simpa [Erdos957Cases24.Case4.v, Erdos957Cases24.Case4.w]
        using Erdos957Cases24.Case2.dist_v_w)
      (by simpa using Erdos957Cases24.Case4.dist_v_b)
      Erdos957Cases24.Case4.dist_w_b hdegree
  intro q hq
  simp only [Erdos957Cases24.Case4.displayedFiveAtV,
    Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact huPrev
  · exact hu
  · exact hb
  · exact hw
  · exact ha

lemma case2_w_add_b_sub_v_eq_wNext :
    Erdos957Cases24.Case2.w + Erdos957Cases24.Case2.b -
      Erdos957Cases24.Case2.v = Erdos957Cases24.Case2.wNext := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.b,
      Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.wNext]
  ring

lemma case2_wNext_add_b_sub_w_eq_e :
    Erdos957Cases24.Case2.wNext + Erdos957Cases24.Case2.b -
      Erdos957Cases24.Case2.w = Erdos957Cases24.Case2.e := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.b,
      Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.e]
  ring

/-- All canonical data actually consumed by one Case-2 source row.  In
particular this record does not assume that the entire five-point display
around `b` is present: `wNext` and `e` are constructed only in the degree
branches in which they are selected. -/
structure Case2CanonicalRowData (B : Finset Erdos957Cases24.Point) where
  outer_mem : Erdos957Cases24.Case2.b ∈ B
  secondary_mem :
    Erdos957Cases24.Case2.secondaryRecipient
      (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.w)
      (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.wNext) ∈ B
  outer_degree_le_five :
    Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.b ≤ 5
  endpoint_degree_le_four :
    Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.e ≤ 4
  secondary_degree_le_five :
    Erdos957Case24Bridge.unitDegree B
      (Erdos957Cases24.Case2.secondaryRecipient
        (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.w)
        (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.wNext)) ≤ 5

/-- Starting only from degree six at the normalized middle, regular-hexagon
completion supplies exactly the later lattice points selected by the
three-branch Case-2 rule. -/
theorem case2CanonicalRowData_of_middle_degree_six
    {B : Finset Erdos957Cases24.Point}
    (hsep : Erdos957Cases24.IsOneSeparated B)
    (hstrict : Erdos957Case24Bridge.StrictlyBelowOutside B
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ B)
    (hu : Erdos957Cases24.Case2.u ∈ B)
    (hv : Erdos957Cases24.Case2.v ∈ B)
    (hdegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case2.v = 6) :
    Case2CanonicalRowData B := by
  have hdisplay := case4_displayedFiveAtV_subset_of_degree_six
    hsep huPrev hu (by simpa [Erdos957Cases24.Case4.v] using hdegree)
  have hb : Erdos957Cases24.Case2.b ∈ B := by
    exact hdisplay (by simp [Erdos957Cases24.Case4.displayedFiveAtV,
      Erdos957Cases24.Case4.b])
  have hw : Erdos957Cases24.Case2.w ∈ B := by
    exact hdisplay (by simp [Erdos957Cases24.Case4.displayedFiveAtV,
      Erdos957Cases24.Case4.w])
  have hbDegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case2.b ≤ 5 := by
    have hle := Erdos957Case24Bridge.unitDegree_le_six hsep
      Erdos957Cases24.Case2.b
    have hne : Erdos957Case24Bridge.unitDegree B
        Erdos957Cases24.Case2.b ≠ 6 := by
      intro hsix
      have hnext := Erdos957Case24Bridge.Case4.b_six_forces_uNext_mem
        hsep hu hv hsix
      exact (Erdos957Case24Bridge.case2_uNext_not_mem_of_strict_support
        hstrict) hnext
    omega
  have heDegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case2.e ≤ 4 :=
    Erdos957Case24Bridge.Case2.unitDegree_e_le_four_of_strict_support
      hsep hstrict hb
  let dw := Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.w
  let dwn := Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.wNext
  have hsecondary : Erdos957Cases24.Case2.secondaryRecipient dw dwn ∈ B := by
    by_cases hwFive : dw ≤ 5
    · simpa [Erdos957Cases24.Case2.secondaryRecipient, hwFive] using hw
    · have hwSix : dw = 6 := by
        have := Erdos957Case24Bridge.unitDegree_le_six hsep
          Erdos957Cases24.Case2.w
        omega
      have hwn : Erdos957Cases24.Case2.wNext ∈ B := by
        rw [← case2_w_add_b_sub_v_eq_wNext]
        exact Erdos957Case24Bridge.hexagon_completion_mem hsep hb hv
          (by simpa [dist_comm] using Erdos957Cases24.Case2.dist_b_w)
          (by simpa [dist_comm] using Erdos957Cases24.Case2.dist_v_w)
          (by simpa [dist_comm] using Erdos957Cases24.Case2.dist_v_b) hwSix
      by_cases hwnFive : dwn ≤ 5
      · simpa [Erdos957Cases24.Case2.secondaryRecipient, hwFive,
          hwnFive] using hwn
      · have hwnSix : dwn = 6 := by
          have := Erdos957Case24Bridge.unitDegree_le_six hsep
            Erdos957Cases24.Case2.wNext
          omega
        have he : Erdos957Cases24.Case2.e ∈ B := by
          rw [← case2_wNext_add_b_sub_w_eq_e]
          exact Erdos957Case24Bridge.hexagon_completion_mem hsep hb hw
            (by simpa [dist_comm] using
              Erdos957Cases24.Case2.dist_b_wNext)
            (by simpa [dist_comm] using
              Erdos957Cases24.Case2.dist_w_wNext)
            Erdos957Cases24.Case2.dist_b_w hwnSix
        simpa [Erdos957Cases24.Case2.secondaryRecipient, hwFive,
          hwnFive] using he
  refine {
    outer_mem := hb
    secondary_mem := ?_
    outer_degree_le_five := hbDegree
    endpoint_degree_le_four := heDegree
    secondary_degree_le_five := ?_ }
  · simpa [dw, dwn] using hsecondary
  · exact Erdos957Case24Bridge.Case2.secondary_degree_le_five B heDegree

/-- Formula-retaining Case-2 output.  The exact roles stay in the rigid edge
chart, while both targets are already certified in the common aligned chart
used by locality. -/
def hullPoints {A : Finset ComplexPoint} (P : CyclicHullData A) :
    Finset ComplexPoint := P.H.image fun v : Erdos957GeometryCore.Vertex A ↦
      (v : ComplexPoint)

lemma actualVertex_not_mem_hullPoints {A : Finset ComplexPoint}
    (P : CyclicHullData A) (F : RigidChart) (q : Erdos957Cases24.Point)
    (hq : F.actual q ∈ A) (hnot : actualVertex F q hq ∉ P.H) :
    F.actual q ∉ hullPoints P := by
  intro h
  rcases Finset.mem_image.mp h with ⟨w, hwH, hw⟩
  apply hnot
  have heq : actualVertex F q hq = w := by
    apply Subtype.ext
    exact hw.symm
  exact heq.symm ▸ hwH

structure Case2ActualRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (F : RigidChart) where
  outer : Erdos957GeometryLocalRows.LocalTarget P C source
  secondary : Erdos957GeometryLocalRows.LocalTarget P C source
  outer_edge_coordinate :
    F.toCanonical (outer.vertex : ComplexPoint) = Erdos957Cases24.Case2.b
  secondary_edge_coordinate :
    F.toCanonical (secondary.vertex : ComplexPoint) =
      Erdos957Cases24.Case2.secondaryRecipient
        (Erdos957Case24Bridge.unitDegree (F.image A)
          Erdos957Cases24.Case2.w)
        (Erdos957Case24Bridge.unitDegree (F.image A)
          Erdos957Cases24.Case2.wNext)
  distinct : outer.vertex ≠ secondary.vertex
  checked_transfer : Nonempty
    (Erdos957Case24Bridge.Framed.FramedLocalTransfer F A (hullPoints P)
      (F.actual Erdos957Cases24.Case2.u) 2)

def Case2ActualRow.localCase {A : Finset ComplexPoint}
    {P : CyclicHullData A} {C : P.AlignedChartData}
    {source : {p // p ∈ P.H}} {F : RigidChart}
    (R : Case2ActualRow P C source F) :
    Erdos957GeometryLocalRows.LocalCase P C source :=
  .case2 R.outer R.secondary R.distinct

/-- The canonical Case-2 paths lift to actual graph paths because the
chosen intermediate (`v` or `b`) is a proved configuration point. -/
lemma actual_case2_secondary_within_two
    {A : Finset ComplexPoint} (F : RigidChart)
    (hu : F.actual Erdos957Cases24.Case2.u ∈ A)
    (hv : F.actual Erdos957Cases24.Case2.v ∈ A)
    (hb : F.actual Erdos957Cases24.Case2.b ∈ A)
    (hs : F.actual (Erdos957Cases24.Case2.secondaryRecipient
      (Erdos957Case24Bridge.unitDegree (F.image A) Erdos957Cases24.Case2.w)
      (Erdos957Case24Bridge.unitDegree (F.image A)
        Erdos957Cases24.Case2.wNext)) ∈ A) :
    Erdos957GeometryLocalRows.WithinTwoUnitEdges
      (actualVertex F Erdos957Cases24.Case2.u hu)
      (actualVertex F
        (Erdos957Cases24.Case2.secondaryRecipient
          (Erdos957Case24Bridge.unitDegree (F.image A)
            Erdos957Cases24.Case2.w)
          (Erdos957Case24Bridge.unitDegree (F.image A)
            Erdos957Cases24.Case2.wNext)) hs) := by
  by_cases hw : Erdos957Case24Bridge.unitDegree (F.image A)
      Erdos957Cases24.Case2.w ≤ 5
  · have hs' : F.actual Erdos957Cases24.Case2.w ∈ A := by
      simpa only [Erdos957Cases24.Case2.secondaryRecipient, if_pos hw] using hs
    have ht : actualVertex F
        (Erdos957Cases24.Case2.secondaryRecipient
          (Erdos957Case24Bridge.unitDegree (F.image A)
            Erdos957Cases24.Case2.w)
          (Erdos957Case24Bridge.unitDegree (F.image A)
            Erdos957Cases24.Case2.wNext)) hs =
        actualVertex F Erdos957Cases24.Case2.w hs' := by
      apply Subtype.ext
      simp [Erdos957Cases24.Case2.secondaryRecipient, hw]
    rw [ht]
    exact Or.inr ⟨actualVertex F Erdos957Cases24.Case2.v hv,
      actualVertex_adj F hu hv Erdos957Cases24.Case2.dist_u_v,
      actualVertex_adj F hv hs' Erdos957Cases24.Case2.dist_v_w⟩
  · by_cases hwNext : Erdos957Case24Bridge.unitDegree (F.image A)
        Erdos957Cases24.Case2.wNext ≤ 5
    · have hs' : F.actual Erdos957Cases24.Case2.wNext ∈ A := by
        simpa only [Erdos957Cases24.Case2.secondaryRecipient, if_neg hw,
          if_pos hwNext] using hs
      have ht : actualVertex F
          (Erdos957Cases24.Case2.secondaryRecipient
            (Erdos957Case24Bridge.unitDegree (F.image A)
              Erdos957Cases24.Case2.w)
            (Erdos957Case24Bridge.unitDegree (F.image A)
              Erdos957Cases24.Case2.wNext)) hs =
          actualVertex F Erdos957Cases24.Case2.wNext hs' := by
        apply Subtype.ext
        simp [Erdos957Cases24.Case2.secondaryRecipient, hw, hwNext]
      rw [ht]
      exact Or.inr ⟨actualVertex F Erdos957Cases24.Case2.b hb,
        actualVertex_adj F hu hb Erdos957Cases24.Case2.dist_u_b,
        actualVertex_adj F hb hs' Erdos957Cases24.Case2.dist_b_wNext⟩
    · have hs' : F.actual Erdos957Cases24.Case2.e ∈ A := by
        simpa only [Erdos957Cases24.Case2.secondaryRecipient, if_neg hw,
          if_neg hwNext] using hs
      have ht : actualVertex F
          (Erdos957Cases24.Case2.secondaryRecipient
            (Erdos957Case24Bridge.unitDegree (F.image A)
              Erdos957Cases24.Case2.w)
            (Erdos957Case24Bridge.unitDegree (F.image A)
              Erdos957Cases24.Case2.wNext)) hs =
          actualVertex F Erdos957Cases24.Case2.e hs' := by
        apply Subtype.ext
        simp [Erdos957Cases24.Case2.secondaryRecipient, hw, hwNext]
      rw [ht]
      exact Or.inr ⟨actualVertex F Erdos957Cases24.Case2.b hb,
        actualVertex_adj F hu hb Erdos957Cases24.Case2.dist_u_b,
        actualVertex_adj F hb hs' Erdos957Cases24.Case2.dist_b_e⟩

/-- Turn canonical Case-2 data into the actual local row.  The only chart
premise is the already transported horizontal estimate in the common chart;
all degrees, membership, paths, formulas, and the checked transfer itself
are derived here. -/
theorem case2ActualRow_of_canonicalData
    {A : Finset ComplexPoint} (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (F : RigidChart) (D : Case2CanonicalRowData (F.image A))
    (hsource : F.actual Erdos957Cases24.Case2.u = (source.1 : ComplexPoint))
    (hv : F.actual Erdos957Cases24.Case2.v ∈ A)
    (houterNot : actualVertex F Erdos957Cases24.Case2.b
      (F.mem_image_iff.mp D.outer_mem) ∉ P.H)
    (hsecondaryNot : actualVertex F
      (Erdos957Cases24.Case2.secondaryRecipient
        (Erdos957Case24Bridge.unitDegree (F.image A)
          Erdos957Cases24.Case2.w)
        (Erdos957Case24Bridge.unitDegree (F.image A)
          Erdos957Cases24.Case2.wNext))
      (F.mem_image_iff.mp D.secondary_mem) ∉ P.H)
    (houterHorizontal :
      |(C.coord source (actualVertex F Erdos957Cases24.Case2.b
        (F.mem_image_iff.mp D.outer_mem))).1| ≤ (7 : ℝ) / 4)
    (hsecondaryHorizontal :
      |(C.coord source (actualVertex F
        (Erdos957Cases24.Case2.secondaryRecipient
          (Erdos957Case24Bridge.unitDegree (F.image A)
            Erdos957Cases24.Case2.w)
          (Erdos957Case24Bridge.unitDegree (F.image A)
            Erdos957Cases24.Case2.wNext))
        (F.mem_image_iff.mp D.secondary_mem))).1| ≤ (7 : ℝ) / 4) :
    Nonempty (Case2ActualRow P C source F) := by
  let B := F.image A
  let s := Erdos957Cases24.Case2.secondaryRecipient
    (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.w)
    (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.wNext)
  have hu : F.actual Erdos957Cases24.Case2.u ∈ A := by
    rw [hsource]
    exact source.1.property
  let outerV := actualVertex F Erdos957Cases24.Case2.b
    (F.mem_image_iff.mp D.outer_mem)
  let secondaryV := actualVertex F s (F.mem_image_iff.mp D.secondary_mem)
  have hsourceVertex :
      actualVertex F Erdos957Cases24.Case2.u hu = source.1 := by
    apply Subtype.ext
    exact hsource
  have houterPath : Erdos957GeometryLocalRows.WithinTwoUnitEdges
      source.1 outerV := by
    rw [← hsourceVertex]
    exact Or.inl (actualVertex_adj F hu (F.mem_image_iff.mp D.outer_mem)
      Erdos957Cases24.Case2.dist_u_b)
  have hsecondaryPath : Erdos957GeometryLocalRows.WithinTwoUnitEdges
      source.1 secondaryV := by
    rw [← hsourceVertex]
    exact actual_case2_secondary_within_two F hu hv
      (F.mem_image_iff.mp D.outer_mem) (F.mem_image_iff.mp D.secondary_mem)
  have houterDegree : (unitDistanceGraph A).degree outerV ≤ 5 := by
    rw [graph_degree_eq_unitDegree]
    change Erdos957Case24Bridge.unitDegree A
      (F.actual Erdos957Cases24.Case2.b) ≤ 5
    rw [← F.unitDegree_image_actual A Erdos957Cases24.Case2.b]
    exact D.outer_degree_le_five
  have hsecondaryDegree : (unitDistanceGraph A).degree secondaryV ≤ 5 := by
    rw [graph_degree_eq_unitDegree]
    change Erdos957Case24Bridge.unitDegree A (F.actual s) ≤ 5
    rw [← F.unitDegree_image_actual A s]
    exact D.secondary_degree_le_five
  let outer := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
    houterDegree houterNot houterPath houterHorizontal
  let secondary := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
    hsecondaryDegree hsecondaryNot hsecondaryPath hsecondaryHorizontal
  have hne : outer.vertex ≠ secondary.vertex := by
    intro h
    have hactual : F.actual Erdos957Cases24.Case2.b = F.actual s :=
      congrArg Subtype.val h
    have hcanonical : Erdos957Cases24.Case2.b = s :=
      F.actual_injective hactual
    exact Erdos957Case24Bridge.Case2.b_ne_secondaryRecipient _ _ hcanonical
  have hrec : Erdos957Cases24.Case2.recipientSet
      (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.w)
      (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.wNext) ⊆ B := by
    intro q hq
    simp only [Erdos957Cases24.Case2.recipientSet,
      Finset.mem_insert, Finset.mem_singleton] at hq
    exact hq.elim (fun h ↦ h ▸ D.outer_mem) (fun h ↦ h ▸ D.secondary_mem)
  have hnot : ∀ q ∈ Erdos957Cases24.Case2.recipientSet
      (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.w)
      (Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.wNext),
      q ∉ F.image (hullPoints P) := by
    intro q hq hqH
    have hactualH : F.actual q ∈ hullPoints P := F.mem_image_iff.mp hqH
    simp only [Erdos957Cases24.Case2.recipientSet,
      Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (actualVertex_not_mem_hullPoints P F _ _ houterNot) hactualH
    · exact (actualVertex_not_mem_hullPoints P F _ _ hsecondaryNot) hactualH
  obtain ⟨T⟩ := Erdos957Case24Bridge.Case2.localTransfer_of_target_exclusion
    B (F.image (hullPoints P)) hnot hrec D.outer_degree_le_five
      D.endpoint_degree_le_four
  have hchecked : Nonempty
      (Erdos957Case24Bridge.Framed.FramedLocalTransfer F A (hullPoints P)
        (F.actual Erdos957Cases24.Case2.u) 2) :=
    ⟨Erdos957Case24Bridge.Framed.transportLocalTransfer F A (hullPoints P)
      Erdos957Cases24.Case2.u 2 T⟩
  exact ⟨{
    outer := outer
    secondary := secondary
    outer_edge_coordinate := by
      change F.toCanonical (F.actual Erdos957Cases24.Case2.b) = _
      exact F.toCanonical_actual _
    secondary_edge_coordinate := by
      change F.toCanonical (F.actual s) = _
      simpa [s, B] using F.toCanonical_actual s
    distinct := hne
    checked_transfer := hchecked }⟩

/-- A unit incoming hull edge is literally the unit direction selected by
the lifted cyclic order.  The positive scale in the lift cannot hide any
renormalization because the actual edge has length one. -/
lemma incoming_edge_eq_unitDirection
    {A : Finset ComplexPoint} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (hunit : dist (O.vertex (previousIndex a)) (O.vertex a) = 1) :
    O.vertex a - O.vertex (previousIndex a) =
      unitDirection (L.lift.angle (previousIndex a).1) := by
  let b := previousIndex a
  have hba : finRotate (hullVertexCount A) b = a := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply a
  have hedge := L.edge_eq b
  rw [hba] at hedge
  have hnorm : ‖O.vertex a - O.vertex b‖ = 1 := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using hunit
  have hscale : L.edgeScale b = 1 := by
    rw [hedge, norm_smul, norm_unitDirection, mul_one,
      Real.norm_eq_abs, abs_of_pos (L.edgeScale_pos b)] at hnorm
    exact hnorm
  simpa [b, hscale] using hedge

/-- In the terminal incoming-edge chart, the outgoing hull vertex remains
within `1/10` of the supporting axis at a flat source, provided it is within
two units of the source.  This separates it from every Case-2 recipient,
whose canonical depth is at least `sqrt 3 / 2`. -/
lemma outgoing_edge_terminal_height_abs_lt_one_tenth
    {A : Finset ComplexPoint} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (hunit : dist (O.vertex (previousIndex a)) (O.vertex a) = 1)
    (hturn : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) < Real.pi / 180)
    (hradius : dist (O.vertex a)
      (O.vertex (finRotate (hullVertexCount A) a)) ≤ 2) :
    |(edgePairCoord (O.vertex a)
      (O.vertex a - O.vertex (previousIndex a))
      (O.vertex (finRotate (hullVertexCount A) a))).2| < (1 : ℝ) / 10 := by
  let b := previousIndex a
  have hba : finRotate (hullVertexCount A) b = a := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply a
  have hin := incoming_edge_eq_unitDirection L a hunit
  have hout := L.successor_edge_eq b
  rw [hba] at hout
  have hturnEq : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) = L.lift.turn b := by
    rw [← hba]
    exact cyclicHullDataOfOrder_turn_successor_indexEquiv O L b
  have hdeltaPos : 0 < L.lift.turn b := by
    simpa [incidentTurn, previousIndex, b] using incidentTurn_pos L a
  have hdeltaLt : L.lift.turn b < Real.pi / 180 := by
    rwa [hturnEq] at hturn
  have hscale : L.edgeScale a ≤ 2 := by
    have hn : ‖O.vertex (finRotate (hullVertexCount A) a) - O.vertex a‖ ≤ 2 := by
      rw [← dist_eq_norm]
      simpa [dist_comm] using hradius
    rw [hout, norm_smul, norm_unitDirection, mul_one,
      Real.norm_eq_abs, abs_of_pos (L.edgeScale_pos a)] at hn
    exact hn
  have hsinNonneg : 0 ≤ Real.sin (L.lift.turn b) :=
    (Real.sin_pos_of_pos_of_lt_pi hdeltaPos
      (hdeltaLt.trans (by nlinarith [Real.pi_pos]))).le
  have hsinLt : Real.sin (L.lift.turn b) < (1 : ℝ) / 45 := by
    have habs : |Real.sin (L.lift.turn b)| ≤ |L.lift.turn b| :=
      Real.abs_sin_le_abs
    rw [abs_of_nonneg hdeltaPos.le] at habs
    rw [abs_of_nonneg hsinNonneg] at habs
    have hpi : Real.pi / 180 < (1 : ℝ) / 45 := by
      nlinarith [Real.pi_lt_four]
    linarith
  have hy : (edgePairCoord (O.vertex a)
      (O.vertex a - O.vertex (previousIndex a))
      (O.vertex (finRotate (hullVertexCount A) a))).2 =
      -L.edgeScale a * Real.sin (L.lift.turn b) := by
    rw [show O.vertex a - O.vertex (previousIndex a) =
      unitDirection (L.lift.angle b.1) by simpa [b] using hin]
    simp only [edgePairCoord]
    change (unitDirection (L.lift.angle b.1)) 1 *
        (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a) 0 -
      (unitDirection (L.lift.angle b.1)) 0 *
        (O.vertex (finRotate (hullVertexCount A) a) - O.vertex a) 1 = _
    rw [hout]
    have hangle : L.lift.angle b.1 + L.lift.turn b =
        L.lift.angle (b.1 + 1) := by
      simp only [DirectionLift.turn]
      ring
    rw [← hangle]
    simp only [PiLp.smul_apply, smul_eq_mul]
    calc
      _ = -L.edgeScale a * det (unitDirection (L.lift.angle b.1))
          (unitDirection (L.lift.angle b.1 + L.lift.turn b)) := by
        change
          (unitDirection (L.lift.angle b.1)) 1 *
                (L.edgeScale a *
                  (unitDirection (L.lift.angle b.1 + L.lift.turn b)) 0) -
              (unitDirection (L.lift.angle b.1)) 0 *
                (L.edgeScale a *
                  (unitDirection (L.lift.angle b.1 + L.lift.turn b)) 1) =
            -L.edgeScale a *
              ((unitDirection (L.lift.angle b.1)) 0 *
                  (unitDirection (L.lift.angle b.1 + L.lift.turn b)) 1 -
                (unitDirection (L.lift.angle b.1)) 1 *
                  (unitDirection (L.lift.angle b.1 + L.lift.turn b)) 0)
        ring
      _ = _ := by rw [det_unitDirection]; ring
  rw [hy, abs_mul, abs_neg, abs_of_pos (L.edgeScale_pos a),
    abs_of_nonneg hsinNonneg]
  have hprod : L.edgeScale a * Real.sin (L.lift.turn b) < 2 / 45 := by
    nlinarith [L.edgeScale_pos a]
  norm_num at hprod ⊢
  linarith

/-- The true incident-edge bisector differs from the incoming edge direction
by half the exterior turn.  A source turn below one degree therefore gives
the exact angular premise required by the chart-transport estimate. -/
lemma abs_bisectorAngle_sub_incoming_le_one_degree
    {A : Finset ComplexPoint} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (hturn : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) < Real.pi / 180) :
    |bisectorAngle L a - L.lift.angle (previousIndex a).1| ≤
      Real.pi / 180 := by
  let b := previousIndex a
  have hba : finRotate (hullVertexCount A) b = a := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply a
  have hturnEq : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) = L.lift.turn b := by
    rw [← hba]
    exact cyclicHullDataOfOrder_turn_successor_indexEquiv O L b
  have hbnonneg : 0 ≤ L.lift.turn b := L.lift.turn_nonneg b
  rw [hturnEq] at hturn
  rw [bisectorAngle, incidentTurn]
  change |L.lift.angle b.1 + L.lift.turn b / 2 - L.lift.angle b.1| ≤ _
  rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_pos]

/-- Sharp recipient transport for the incoming-edge normalization used by
Case 2 and by the terminal source of Case 4.  The conclusion is stated in
the literal production bisector `AlignedChartData`; no equality between the
edge chart and the bisector chart is asserted. -/
theorem incoming_edge_recipient_horizontal_le_seven_four
    {A : Finset ComplexPoint} {O : CyclicHullOrder A}
    (L : LiftedCyclicHullOrder O) (a : Fin (hullVertexCount A))
    (q : Erdos957GeometryCore.Vertex A)
    (hunit : dist (O.vertex (previousIndex a)) (O.vertex a) = 1)
    (hturn : (cyclicHullDataOfOrder O L).turn
      (indexEquivLiftedHull O a) < Real.pi / 180)
    (hradius : dist (O.vertex a) (q : ComplexPoint) ≤ 2)
    (hedge : |(edgePairCoord (O.vertex a)
      (O.vertex a - O.vertex (previousIndex a)) (q : ComplexPoint)).1| ≤
        (3 : ℝ) / 2) :
    |((bisectorAlignedChartData O L).coord
      (indexEquivLiftedHull O a) q).1| ≤ (7 : ℝ) / 4 := by
  have hangle :
      |bisectorAngle L
          ((indexEquivLiftedHull O).symm (indexEquivLiftedHull O a)) -
        L.lift.angle (previousIndex a).1| ≤ Real.pi / 180 := by
    simpa using abs_bisectorAngle_sub_incoming_le_one_degree L a hturn
  have hradius' :
      dist (O.vertex
        ((indexEquivLiftedHull O).symm (indexEquivLiftedHull O a)))
          (q : ComplexPoint) ≤ 2 := by
    simpa using hradius
  have hedge' :
      |(edgePairCoord
          (O.vertex
            ((indexEquivLiftedHull O).symm (indexEquivLiftedHull O a)))
          (O.vertex a - O.vertex (previousIndex a))
          (q : ComplexPoint)).1| ≤ (3 : ℝ) / 2 := by
    simpa using hedge
  exact
    abs_bisectorAlignedChartData_coord_fst_le_seven_four_of_edgePairCoord
      L (indexEquivLiftedHull O a) q
      (O.vertex a - O.vertex (previousIndex a))
      (L.lift.angle (previousIndex a).1)
      (incoming_edge_eq_unitDirection L a hunit)
      hangle
      hradius' hedge'

/-! ### Enriched normalized Case-4 rows -/

/-- The literal source-normalized rigid chart determined by the cyclic side
of a two-extreme witness.  On the predecessor side it is the incoming
terminal chart.  On the successor side it is the endpoint-swapping
reflection of the outgoing terminal chart. -/
def sideNormalizedRigidChart
    {A : Finset ComplexPoint} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (side : CyclicSide)
    (hunit : dist (source.1.1 : ComplexPoint)
      ((cyclicSideVertex P source side).1 : ComplexPoint) = 1) : RigidChart :=
  match side with
  | .previous =>
      Erdos957EdgeFrame.terminalUnitEdgeRigidChart
        (P.next⁻¹ source).1.1 source.1.1
        (by simpa [cyclicSideVertex, dist_comm] using hunit)
  | .next =>
      Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source (by simpa [cyclicSideVertex] using hunit)

/-- Proof-irrelevance-friendly specification of the literal normalized
chart.  The side equality and the correctly oriented unit-edge proof are
stored in the corresponding constructor, avoiding dependent transport
through a match on `side`. -/
inductive SideNormalizedFrameSpec
    {A : Finset ComplexPoint} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (side : CyclicSide) (frame : RigidChart) : Prop
  | previous
      (hside : side = .previous)
      (hunit : dist ((P.next⁻¹ source).1.1 : ComplexPoint)
        (source.1.1 : ComplexPoint) = 1)
      (hframe : frame = Erdos957EdgeFrame.terminalUnitEdgeRigidChart
        (P.next⁻¹ source).1.1 source.1.1 hunit)
  | next
      (hside : side = .next)
      (hunit : dist (source.1.1 : ComplexPoint)
        ((P.next source).1.1 : ComplexPoint) = 1)
      (hframe : frame =
        Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
          P source hunit)

/-- A two-extreme pair normalized so that the current source is canonical
`u`, the incident side vertex is `uPrev`, and the selected middle is `v`.
This common interface is implemented by the incoming terminal chart on the
previous side and by the horizontally reflected successor chart on the next
side. -/
structure TwoExtremeNormalizedFrame
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (source : {p // p ∈ P.H})
    (middle : Erdos957GeometryCore.Vertex A)
    (T : TwoExtremeCyclicWitness P source middle) where
  frame : RigidChart
  side_unit : dist (source.1.1 : ComplexPoint)
    ((cyclicSideVertex P source T.side).1 : ComplexPoint) = 1
  frame_spec : SideNormalizedFrameSpec P source T.side frame
  source_actual : frame.actual Erdos957Cases24.Case2.u = source.1
  side_actual : frame.actual Erdos957Cases24.Case2.uPrev =
    cyclicSideVertex P source T.side
  middle_actual : frame.actual Erdos957Cases24.Case2.v = middle
  strict_support : Erdos957Case24Bridge.StrictlyBelowOutside (frame.image A)
    {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u}

/-- An honest two-extreme witness has a normalized edge frame on either
cyclic side.  The successor case uses the reflected chart, so both sides
share the literal Case-2 coordinates `u`, `uPrev`, and `v`. -/
theorem exists_twoExtremeNormalizedFrame
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H})
    (middle : Erdos957GeometryCore.Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (hstrict : ∀ q : Erdos957GeometryCore.Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (C.coord source middle)) :
    Nonempty (TwoExtremeNormalizedFrame source middle T) := by
  cases hside : T.side with
  | previous =>
      have hsourceSide : (unitDistanceGraph A).Adj source.1
          (P.next⁻¹ source).1 := by
        apply Erdos957TwoExtremeFrame.source_adj_incidentCyclicVertex_of_middle_adj_aligned
          hA P C source middle (P.next⁻¹ source).1 hstrict hdegree
          hsourceMiddle hmiddleCone
        · exact Or.inl rfl
        · simpa [cyclicSideVertex, hside] using T.side_adjacent
      have hunit : dist ((P.next⁻¹ source).1.1 : ComplexPoint)
          source.1.1 = 1 := by
        change dist (source.1.1 : ComplexPoint) (P.next⁻¹ source).1.1 = 1
          at hsourceSide
        simpa [dist_comm] using hsourceSide
      let F := Erdos957EdgeFrame.terminalUnitEdgeRigidChart
        (P.next⁻¹ source).1.1 source.1.1 hunit
      have hmiddleCoord : F.toCanonical middle = Erdos957Cases24.Case2.v := by
        exact Erdos957TwoExtremeIncidence.terminalUnitEdgeRigidChart_toCanonical_middle_eq_case2_v
            P source middle hunit hsourceMiddle
              (by simpa [cyclicSideVertex, hside] using T.side_adjacent.symm)
      refine ⟨{
        frame := F
        side_unit := ?_
        frame_spec := ?_
        source_actual := ?_
        side_actual := ?_
        middle_actual := ?_
        strict_support := ?_ }⟩
      · simpa [cyclicSideVertex, hside, dist_comm] using hunit
      · exact .previous hside hunit rfl
      · exact Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_u
          _ _ hunit
      · simpa [F, cyclicSideVertex, hside] using
          (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev
            (P.next⁻¹ source).1.1 source.1.1 hunit)
      · apply F.toCanonical.injective
        rw [F.toCanonical_actual, hmiddleCoord]
      · exact Erdos957TwoExtremeIncidence.terminalUnitEdgeRigidChart_strictlyBelowOutside
          hA P source hunit
  | next =>
      have hsourceSide : (unitDistanceGraph A).Adj source.1
          (P.next source).1 := by
        apply Erdos957TwoExtremeFrame.source_adj_incidentCyclicVertex_of_middle_adj_aligned
          hA P C source middle (P.next source).1 hstrict hdegree
          hsourceMiddle hmiddleCone
        · exact Or.inr rfl
        · simpa [cyclicSideVertex, hside] using T.side_adjacent
      have hunit : dist (source.1.1 : ComplexPoint)
          (P.next source).1.1 = 1 := by
        exact hsourceSide
      let F := Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit
      have hmiddleCoord : F.toCanonical middle = Erdos957Cases24.Case2.v := by
        exact Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_toCanonical_middle_eq_case2_v
            P source middle hunit hsourceMiddle
              (by simpa [cyclicSideVertex, hside] using T.side_adjacent.symm)
      refine ⟨{
        frame := F
        side_unit := ?_
        frame_spec := ?_
        source_actual := ?_
        side_actual := ?_
        middle_actual := ?_
        strict_support := ?_ }⟩
      · simpa [cyclicSideVertex, hside] using hunit
      · exact .next hside hunit rfl
      · exact Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_actual_case2_u
          P source hunit
      · simpa [F, cyclicSideVertex, hside] using
          (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_actual_case2_uPrev
              P source hunit)
      · apply F.toCanonical.injective
        rw [F.toCanonical_actual, hmiddleCoord]
      · exact Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_strictlyBelowOutside
            hA P source hunit

/-- The directed hull edge underlying a two-extreme source/side pair.  It is
the predecessor edge when the side witness is previous, and the outgoing
edge when the side witness is next.  Thus both endpoints of the same
undirected hull pair compute the same directed base edge. -/
def case4PairEdgeBase
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Erdos957GeometryCore.Vertex A}
    (T : TwoExtremeCyclicWitness P source middle) : {p // p ∈ P.H} :=
  match T.side with
  | .previous => P.next⁻¹ source
  | .next => source

/-- Whether the current source is the right/terminal endpoint of the common
directed edge chart. -/
def case4SourceIsRight
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Erdos957GeometryCore.Vertex A}
    (T : TwoExtremeCyclicWitness P source middle) : Bool :=
  match T.side with
  | .previous => true
  | .next => false

/-- One literal terminal-edge chart shared by both endpoints of a Case-4
hull pair.  Unlike `TwoExtremeNormalizedFrame`, this chart is not reflected
to put the current source at `u`; the `sourceIsRight` bit records whether the
current endpoint is `uPrev` or `u`. -/
structure TwoExtremeCommonPairFrame
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (source : {p // p ∈ P.H})
    (middle : Erdos957GeometryCore.Vertex A)
    (T : TwoExtremeCyclicWitness P source middle) where
  edge_unit : dist ((case4PairEdgeBase T).1.1 : ComplexPoint)
    ((P.next (case4PairEdgeBase T)).1.1 : ComplexPoint) = 1
  middle_coordinate :
    (Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (case4PairEdgeBase T).1.1
      (P.next (case4PairEdgeBase T)).1.1 edge_unit).toCanonical middle =
        Erdos957Cases24.Case2.v
  strict_support : Erdos957Case24Bridge.StrictlyBelowOutside
    ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (case4PairEdgeBase T).1.1
      (P.next (case4PairEdgeBase T)).1.1 edge_unit).image A)
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u}

def TwoExtremeCommonPairFrame.frame
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (E : TwoExtremeCommonPairFrame source middle T) : RigidChart :=
  Erdos957EdgeFrame.terminalUnitEdgeRigidChart
    (case4PairEdgeBase T).1.1
    (P.next (case4PairEdgeBase T)).1.1 E.edge_unit

@[simp] theorem TwoExtremeCommonPairFrame.middle_actual
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (E : TwoExtremeCommonPairFrame source middle T) :
    E.frame.actual Erdos957Cases24.Case2.v = middle := by
  apply E.frame.toCanonical.injective
  rw [E.frame.toCanonical_actual]
  exact E.middle_coordinate.symm

@[simp] theorem TwoExtremeCommonPairFrame.source_coordinate
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (E : TwoExtremeCommonPairFrame source middle T) :
    E.frame.toCanonical source.1 =
      Erdos957Case24Bridge.Case4.sideSource (case4SourceIsRight T) := by
  cases hside : T.side with
  | previous =>
      have hunit : dist ((P.next⁻¹ source).1.1 : ComplexPoint)
          source.1.1 = 1 := by
        simpa [case4PairEdgeBase, hside] using E.edge_unit
      have hactual : E.frame.actual Erdos957Cases24.Case2.u = source.1 := by
        simpa [TwoExtremeCommonPairFrame.frame, case4PairEdgeBase, hside]
          using (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_u
            (P.next⁻¹ source).1.1 source.1.1 hunit)
      rw [← hactual, E.frame.toCanonical_actual]
      simp [case4SourceIsRight, hside,
        Erdos957Case24Bridge.Case4.sideSource]
  | next =>
      have hunit : dist (source.1.1 : ComplexPoint)
          (P.next source).1.1 = 1 := by
        simpa [case4PairEdgeBase, hside] using E.edge_unit
      have hactual : E.frame.actual Erdos957Cases24.Case2.uPrev = source.1 := by
        simpa [TwoExtremeCommonPairFrame.frame, case4PairEdgeBase, hside]
          using (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev
            source.1.1 (P.next source).1.1 hunit)
      rw [← hactual, E.frame.toCanonical_actual]
      simp [case4SourceIsRight, hside,
        Erdos957Case24Bridge.Case4.sideSource]

@[simp] theorem TwoExtremeCommonPairFrame.side_coordinate
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (E : TwoExtremeCommonPairFrame source middle T) :
    E.frame.toCanonical (cyclicSideVertex P source T.side) =
      Erdos957Case24Bridge.Case4.sideSource (!(case4SourceIsRight T)) := by
  cases hside : T.side with
  | previous =>
      have hunit : dist ((P.next⁻¹ source).1.1 : ComplexPoint)
          source.1.1 = 1 := by
        simpa [case4PairEdgeBase, hside] using E.edge_unit
      have hactual : E.frame.actual Erdos957Cases24.Case2.uPrev =
          (P.next⁻¹ source).1 := by
        simpa [TwoExtremeCommonPairFrame.frame, case4PairEdgeBase, hside]
          using (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev
            (P.next⁻¹ source).1.1 source.1.1 hunit)
      change E.frame.toCanonical (P.next⁻¹ source).1 = _
      rw [← hactual, E.frame.toCanonical_actual]
      simp [case4SourceIsRight, hside,
        Erdos957Case24Bridge.Case4.sideSource]
  | next =>
      have hunit : dist (source.1.1 : ComplexPoint)
          (P.next source).1.1 = 1 := by
        simpa [case4PairEdgeBase, hside] using E.edge_unit
      have hactual : E.frame.actual Erdos957Cases24.Case2.u =
          (P.next source).1 := by
        simpa [TwoExtremeCommonPairFrame.frame, case4PairEdgeBase, hside]
          using (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_u
            source.1.1 (P.next source).1.1 hunit)
      change E.frame.toCanonical (P.next source).1 = _
      rw [← hactual, E.frame.toCanonical_actual]
      simp [case4SourceIsRight, hside,
        Erdos957Case24Bridge.Case4.sideSource]

/-- Construct the common directed-edge chart from the honest two-extreme
incidences.  The next-side case deliberately uses the unreflected terminal
chart at `source → next source`. -/
theorem exists_twoExtremeCommonPairFrame
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H})
    (middle : Erdos957GeometryCore.Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (hstrict : ∀ q : Erdos957GeometryCore.Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (C.coord source middle)) :
    Nonempty (TwoExtremeCommonPairFrame source middle T) := by
  have hsourceSide : (unitDistanceGraph A).Adj source.1
      (cyclicSideVertex P source T.side) := by
    apply Erdos957TwoExtremeFrame.source_adj_incidentCyclicVertex_of_middle_adj_aligned
      hA P C source middle (cyclicSideVertex P source T.side) hstrict
      hdegree hsourceMiddle hmiddleCone
    · cases T.side <;> simp [Erdos957TwoExtremeFrame.IsIncidentCyclicVertex,
        cyclicSideVertex]
    · exact T.side_adjacent
  cases hside : T.side with
  | previous =>
      have hunit : dist ((P.next⁻¹ source).1.1 : ComplexPoint)
          source.1.1 = 1 := by
        have hs : (unitDistanceGraph A).Adj source.1
            (P.next⁻¹ source).1 := by
          simpa [cyclicSideVertex, hside] using hsourceSide
        change dist (source.1.1 : ComplexPoint)
          (P.next⁻¹ source).1.1 = 1 at hs
        simpa [dist_comm] using hs
      have hmiddleCoord :=
        Erdos957TwoExtremeIncidence.terminalUnitEdgeRigidChart_toCanonical_middle_eq_case2_v
          P source middle hunit hsourceMiddle
            (by simpa [cyclicSideVertex, hside] using T.side_adjacent.symm)
      refine ⟨{ edge_unit := ?_, middle_coordinate := ?_, strict_support := ?_ }⟩
      · simpa [case4PairEdgeBase, hside] using hunit
      · simpa [case4PairEdgeBase, hside] using hmiddleCoord
      · simpa [case4PairEdgeBase, hside] using
          (Erdos957TwoExtremeIncidence.terminalUnitEdgeRigidChart_strictlyBelowOutside
            hA P source hunit)
  | next =>
      have hunit : dist (source.1.1 : ComplexPoint)
          (P.next source).1.1 = 1 := by
        have hs : (unitDistanceGraph A).Adj source.1
            (P.next source).1 := by
          simpa [cyclicSideVertex, hside] using hsourceSide
        exact hs
      have hmiddleCoord :=
        Erdos957TwoExtremeIncidence.terminalUnitEdgeRigidChart_toCanonical_middle_eq_case2_v
          P (P.next source) middle
            (by simpa using hunit)
            (by simpa [cyclicSideVertex, hside] using T.side_adjacent.symm)
            (by simpa using hsourceMiddle)
      refine ⟨{ edge_unit := ?_, middle_coordinate := ?_, strict_support := ?_ }⟩
      · simpa [case4PairEdgeBase, hside] using hunit
      · simpa [case4PairEdgeBase, hside] using hmiddleCoord
      · simpa [case4PairEdgeBase, hside] using
          (Erdos957TwoExtremeIncidence.terminalUnitEdgeRigidChart_strictlyBelowOutside
            hA P (P.next source) (by simpa using hunit))

/-- Formula-retaining actual Case-4 row.  The degree-five branch remembers
the lexicographically farthest-below residual neighbor.  If it is
six-valent, the entire ordered pair of source-specific contacts is retained;
the current normalized source uses the right contact. -/
inductive Case4ActualRow {A : Finset ComplexPoint}
    {P : CyclicHullData A} (C : P.AlignedChartData)
    (source : {p // p ∈ P.H})
    (middle : Erdos957GeometryCore.Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T) : Type
  | whole
      (middleTarget : Erdos957GeometryLocalRows.LocalTarget P C source)
      (middle_edge_coordinate :
        N.frame.toCanonical middleTarget.vertex = Erdos957Cases24.Case2.v)
      (middle_degree_le_four :
        (unitDistanceGraph A).degree middleTarget.vertex ≤ 4)
  | orderedLow
      (farthest : Erdos957Case24Bridge.Case4.FarthestBelowData
        (N.frame.image A))
      (farthest_degree_le_five : Erdos957Case24Bridge.unitDegree
        (N.frame.image A) farthest.point ≤ 5)
      (middleTarget lowTarget :
        Erdos957GeometryLocalRows.LocalTarget P C source)
      (middle_edge_coordinate :
        N.frame.toCanonical middleTarget.vertex = Erdos957Cases24.Case2.v)
      (low_edge_coordinate :
        N.frame.toCanonical lowTarget.vertex = farthest.point)
      (distinct : middleTarget.vertex ≠ lowTarget.vertex)
  | orderedHigh
      (farthest : Erdos957Case24Bridge.Case4.FarthestBelowData
        (N.frame.image A))
      (farthest_degree_six : Erdos957Case24Bridge.unitDegree
        (N.frame.image A) farthest.point = 6)
      (recipients : Erdos957Case24Bridge.Case4.HighFarthestRecipients
        (N.frame.image A) farthest)
      (middleTarget sideTarget :
        Erdos957GeometryLocalRows.LocalTarget P C source)
      (middle_edge_coordinate :
        N.frame.toCanonical middleTarget.vertex = Erdos957Cases24.Case2.v)
      (side_edge_coordinate :
        N.frame.toCanonical sideTarget.vertex = recipients.right)
      (distinct : middleTarget.vertex ≠ sideTarget.vertex)
  | pairedSplit
      (commonFrame : RigidChart)
      (farthest : Erdos957Case24Bridge.Case4.FarthestBelowData
        (commonFrame.image A))
      (branch : Erdos957Case24Bridge.Case4.FarthestBranchData
        (commonFrame.image A) farthest)
      (rightSource : Bool)
      (right_source_eq : rightSource = case4SourceIsRight T)
      (middleTarget secondaryTarget :
        Erdos957GeometryLocalRows.LocalTarget P C source)
      (source_common_coordinate :
        commonFrame.toCanonical source.1 =
          Erdos957Case24Bridge.Case4.sideSource rightSource)
      (middle_common_coordinate :
        commonFrame.toCanonical middleTarget.vertex =
          Erdos957Cases24.Case2.v)
      (secondary_common_coordinate :
        commonFrame.toCanonical secondaryTarget.vertex =
          branch.sourceRecipient rightSource)
      (distinct : middleTarget.vertex ≠ secondaryTarget.vertex)

def Case4ActualRow.middleTarget
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    {N : TwoExtremeNormalizedFrame source middle T} :
    Case4ActualRow C source middle T N →
      Erdos957GeometryLocalRows.LocalTarget P C source
  | .whole middleTarget _ _ => middleTarget
  | .orderedLow _ _ middleTarget _ _ _ _ => middleTarget
  | .orderedHigh _ _ _ middleTarget _ _ _ _ => middleTarget
  | .pairedSplit _ _ _ _ _ middleTarget _ _ _ _ _ => middleTarget

def Case4ActualRow.localCase
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    {N : TwoExtremeNormalizedFrame source middle T} :
    Case4ActualRow C source middle T N →
      Erdos957GeometryLocalRows.LocalCase P C source
  | .whole middleTarget _ hfour => .case4Primary middleTarget hfour
  | .orderedLow _ _ middleTarget lowTarget _ _ hne =>
      .case4SecondarySplit middleTarget lowTarget hne
  | .orderedHigh _ _ _ middleTarget sideTarget _ _ hne =>
      .case4SecondarySplit middleTarget sideTarget hne
  | .pairedSplit _ _ _ _ _ middleTarget secondaryTarget _ _ _ hne =>
      .case4SecondarySplit middleTarget secondaryTarget hne

/-- Pull one source-specific farthest-below branch back to the actual
configuration.  The farthest datum and (in the high branch) its orientation
certificate remain in the resulting row.  The current normalized source is
canonical `u`, hence it uses the `true`/right source recipient. -/
theorem case4ActualRow_of_farthestBranch
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Erdos957GeometryCore.Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData (N.frame.image A))
    (B : Erdos957Case24Bridge.Case4.FarthestBranchData
      (N.frame.image A) D) :
    ∃ row : Case4ActualRow F.chart source middle T N,
      row.middleTarget.vertex = middle := by
  let q := B.sourceRecipient true
  have hvA : N.frame.actual Erdos957Cases24.Case2.v ∈ A := by
    rw [N.middle_actual]
    exact middle.property
  have hqImage : q ∈ N.frame.image A :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
      (B.sourceRecipient_mem true)).1
  have hqA : N.frame.actual q ∈ A := N.frame.mem_image_iff.mp hqImage
  let qVertex := actualVertex N.frame q hqA
  have hmiddleNot : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source hflat hwindow middle
      hsourceMiddle hmiddleCone
  have hmiddleUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (F.chart.coord source middle) = 1 := by
    rw [show Erdos957Cases13.origin = F.chart.coord source source.1 by
      simpa [Erdos957Cases13.origin] using
        (F.chart.coord_source source).symm]
    rw [F.chart.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1
      at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hmiddleX :=
    Erdos957MiddleLocalization.abs_fst_lt_half_of_unit_of_middleCone
      hmiddleUnit hmiddleCone
  have hmiddleHorizontal : |(F.chart.coord source middle).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hmiddlePath : Erdos957GeometryLocalRows.WithinTwoUnitEdges
      source.1 middle := Or.inl hsourceMiddle
  let middleTarget := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
    (by omega : (unitDistanceGraph A).degree middle ≤ 5)
    hmiddleNot hmiddlePath hmiddleHorizontal
  have hqDist : dist Erdos957Cases24.Case2.v q = 1 :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
      (B.sourceRecipient_mem true)).2.1
  have hmiddleQ : (unitDistanceGraph A).Adj middle qVertex := by
    have hactual := actualVertex_adj N.frame hvA hqA hqDist
    have hmiddleVertex : actualVertex N.frame Erdos957Cases24.Case2.v hvA =
        middle := by
      apply Subtype.ext
      exact N.middle_actual
    simpa [hmiddleVertex] using hactual
  have hqNeSource : qVertex ≠ source.1 := by
    intro h
    have hactual : N.frame.actual q =
        N.frame.actual Erdos957Cases24.Case2.u := by
      rw [N.source_actual]
      exact congrArg Subtype.val h
    have hqU := N.frame.actual_injective hactual
    exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
      (B.sourceRecipient_mem true)).2.2.2 hqU
  have hqNeSide : qVertex ≠ cyclicSideVertex P source T.side := by
    intro h
    have hactual : N.frame.actual q =
        N.frame.actual Erdos957Cases24.Case2.uPrev := by
      rw [N.side_actual]
      exact congrArg Subtype.val h
    have hqPrev := N.frame.actual_injective hactual
    exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
      (B.sourceRecipient_mem true)).2.2.1 hqPrev
  have hqNot : qVertex ∉ P.H :=
    not_mem_hull_of_adj_middle_of_twoExtreme T hmiddleQ hqNeSource hqNeSide
  have hqDegree : (unitDistanceGraph A).degree qVertex ≤ 5 := by
    rw [graph_degree_eq_unitDegree]
    change Erdos957Case24Bridge.unitDegree A (N.frame.actual q) ≤ 5
    rw [← N.frame.unitDegree_image_actual A q]
    exact B.sourceRecipient_degree_le_five true
  have hqPath : Erdos957GeometryLocalRows.WithinTwoUnitEdges
      source.1 qVertex := Or.inr ⟨middle, hsourceMiddle, hmiddleQ⟩
  have hdiff := Erdos957MiddleLocalization.abs_fst_sub_le_one_of_adj
    F.chart source hmiddleQ
  have hqHorizontal : |(F.chart.coord source qVertex).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le] at hdiff ⊢
    constructor <;> linarith
  let qTarget := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
    hqDegree hqNot hqPath hqHorizontal
  have hmiddleEdge : N.frame.toCanonical middleTarget.vertex =
      Erdos957Cases24.Case2.v := by
    change N.frame.toCanonical middle = _
    rw [← N.middle_actual, N.frame.toCanonical_actual]
  have hqEdge : N.frame.toCanonical qTarget.vertex = q := by
    change N.frame.toCanonical (N.frame.actual q) = q
    exact N.frame.toCanonical_actual q
  have hne : middleTarget.vertex ≠ qTarget.vertex := hmiddleQ.ne
  cases B with
  | low hdegree =>
      exact ⟨.orderedLow D hdegree middleTarget qTarget hmiddleEdge hqEdge hne, rfl⟩
  | high hsix recipients =>
      exact ⟨.orderedHigh D hsix recipients middleTarget qTarget
        hmiddleEdge hqEdge hne, rfl⟩

/-- Build either endpoint's actual Case-4 row from one branch in a shared
pair chart.  This is the reflection-safe constructor: the partner endpoint
uses the same `D` and `B` terms with `rightSource = false`, rather than
re-running the lexicographic farthest choice in its reflected local frame. -/
theorem case4PairedActualRow_of_commonBranch
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hflat : P.IsFlat source) (hwindow : LocalHullWindowHypothesis P source)
    (middle : Erdos957GeometryCore.Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (F.chart.coord source middle))
    (T : TwoExtremeCyclicWitness P source middle)
    (N : TwoExtremeNormalizedFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5)
    (commonFrame : RigidChart)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData (commonFrame.image A))
    (B : Erdos957Case24Bridge.Case4.FarthestBranchData
      (commonFrame.image A) D)
    (rightSource : Bool)
    (hrightSource : rightSource = case4SourceIsRight T)
    (hsourceCommon : commonFrame.toCanonical source.1 =
      Erdos957Case24Bridge.Case4.sideSource rightSource)
    (hsideCommon : commonFrame.toCanonical
      (cyclicSideVertex P source T.side) =
        Erdos957Case24Bridge.Case4.sideSource (!rightSource))
    (hmiddleCommon : commonFrame.toCanonical middle =
      Erdos957Cases24.Case2.v) :
    ∃ row : Case4ActualRow F.chart source middle T N,
      row.middleTarget.vertex = middle := by
  let q := B.sourceRecipient rightSource
  have hqResidual : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors
      (commonFrame.image A) := B.sourceRecipient_mem rightSource
  have hqImage : q ∈ commonFrame.image A :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqResidual).1
  have hqA : commonFrame.actual q ∈ A := commonFrame.mem_image_iff.mp hqImage
  let qVertex := actualVertex commonFrame q hqA
  have hmiddleNot : middle ∉ P.H :=
    middle_not_mem_hull_of_local_window F source hflat hwindow middle
      hsourceMiddle hmiddleCone
  have hmiddleUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (F.chart.coord source middle) = 1 := by
    rw [show Erdos957Cases13.origin = F.chart.coord source source.1 by
      simpa [Erdos957Cases13.origin] using
        (F.chart.coord_source source).symm]
    rw [F.chart.sqDist_coord]
    change dist (source.1 : ComplexPoint) (middle : ComplexPoint) = 1
      at hsourceMiddle
    rw [hsourceMiddle]
    norm_num
  have hmiddleX :=
    Erdos957MiddleLocalization.abs_fst_lt_half_of_unit_of_middleCone
      hmiddleUnit hmiddleCone
  have hmiddleHorizontal : |(F.chart.coord source middle).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le]
    constructor <;> linarith
  let middleTarget := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
    (by omega : (unitDistanceGraph A).degree middle ≤ 5)
    hmiddleNot (Or.inl hsourceMiddle) hmiddleHorizontal
  have hqDist : dist Erdos957Cases24.Case2.v q = 1 :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqResidual).2.1
  have hmiddleQ : (unitDistanceGraph A).Adj middle qVertex := by
    change dist (middle : ComplexPoint) (commonFrame.actual q) = 1
    rw [← commonFrame.dist_eq, hmiddleCommon,
      commonFrame.toCanonical_actual, hqDist]
  have hqNeSideSource (b : Bool) :
      q ≠ Erdos957Case24Bridge.Case4.sideSource b := by
    cases b
    · exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        hqResidual).2.2.1
    · exact (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        hqResidual).2.2.2
  have hqNeSource : qVertex ≠ source.1 := by
    intro h
    apply hqNeSideSource rightSource
    rw [← hsourceCommon]
    rw [← commonFrame.toCanonical_actual q]
    exact congrArg (fun x : Erdos957GeometryCore.Vertex A ↦
      commonFrame.toCanonical (x : ComplexPoint)) h
  have hqNeSide : qVertex ≠ cyclicSideVertex P source T.side := by
    intro h
    apply hqNeSideSource (!rightSource)
    rw [← hsideCommon]
    rw [← commonFrame.toCanonical_actual q]
    exact congrArg (fun x : Erdos957GeometryCore.Vertex A ↦
      commonFrame.toCanonical (x : ComplexPoint)) h
  have hqNot : qVertex ∉ P.H :=
    not_mem_hull_of_adj_middle_of_twoExtreme T hmiddleQ hqNeSource hqNeSide
  have hqDegree : (unitDistanceGraph A).degree qVertex ≤ 5 := by
    rw [graph_degree_eq_unitDegree]
    change Erdos957Case24Bridge.unitDegree A (commonFrame.actual q) ≤ 5
    rw [← commonFrame.unitDegree_image_actual A q]
    exact B.sourceRecipient_degree_le_five rightSource
  have hqPath : Erdos957GeometryLocalRows.WithinTwoUnitEdges
      source.1 qVertex := Or.inr ⟨middle, hsourceMiddle, hmiddleQ⟩
  have hdiff := Erdos957MiddleLocalization.abs_fst_sub_le_one_of_adj
    F.chart source hmiddleQ
  have hqHorizontal : |(F.chart.coord source qVertex).1| ≤ (7 : ℝ) / 4 := by
    rw [abs_le] at hdiff ⊢
    constructor <;> linarith
  let qTarget := Erdos957GeometryLocalRows.LocalTarget.ofPathOfAbs
    hqDegree hqNot hqPath hqHorizontal
  have hne : middleTarget.vertex ≠ qTarget.vertex := hmiddleQ.ne
  exact ⟨.pairedSplit commonFrame D B rightSource hrightSource middleTarget qTarget
    hsourceCommon hmiddleCommon (commonFrame.toCanonical_actual q) hne, rfl⟩

end ActualCase24Rows

/-! ## Formula-retaining source-indexed exhaustive rows -/

/-- The enriched row family used by collision analysis.  Every constructor
retains the exact formula witness from which its `LocalCase` erasure is
built, together with the genuine `FourCase` classification of the selected
middle. -/
inductive RealizedSourceRow {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) : Type
  | case1 (middle : Erdos957GeometryCore.Vertex A)
      (middle_degree : (unitDistanceGraph A).degree middle = 6)
      (one_hull_neighbor : (hullUnitNeighbors P middle).card = 1)
      (middleCoord : Erdos957Cases13.Point)
      (middle_coordinate : C.coord source middle = middleCoord)
      (middle_not_hull : middle ∉ P.H)
      (middle_unit : Erdos957Cases13.sqDist Erdos957Cases13.origin middleCoord = 1)
      (row : PairCases.Case1ActualRow P C source middleCoord)
  | case2 (middle : Erdos957GeometryCore.Vertex A)
      (middle_degree : (unitDistanceGraph A).degree middle = 6)
      (two_hull_neighbors : (hullUnitNeighbors P middle).card = 2)
      (middle_not_hull : middle ∉ P.H)
      (twoExtreme : TwoExtremeCyclicWitness P source middle)
      (normalized : ActualCase24Rows.TwoExtremeNormalizedFrame
        source middle twoExtreme)
      (row : ActualCase24Rows.Case2ActualRow P C source normalized.frame)
  | case3 (middle : Erdos957GeometryCore.Vertex A)
      (middle_degree : (unitDistanceGraph A).degree middle ≤ 5)
      (one_hull_neighbor : (hullUnitNeighbors P middle).card = 1)
      (middleCoord : Erdos957Cases13.Point)
      (row : PairCases.Case3ActualRow P C source middleCoord)
      (middle_vertex : row.middleTarget.vertex = middle)
  | case4 (middle : Erdos957GeometryCore.Vertex A)
      (middle_degree : (unitDistanceGraph A).degree middle ≤ 5)
      (two_hull_neighbors : (hullUnitNeighbors P middle).card = 2)
      (twoExtreme : TwoExtremeCyclicWitness P source middle)
      (normalized : ActualCase24Rows.TwoExtremeNormalizedFrame
        source middle twoExtreme)
      (row : ActualCase24Rows.Case4ActualRow C source middle
        twoExtreme normalized)
      (middle_vertex : row.middleTarget.vertex = middle)

def RealizedSourceRow.localCase
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}} :
    RealizedSourceRow P C source →
      Erdos957GeometryLocalRows.LocalCase P C source
  | .case1 _ _ _ _ _ _ _ row => row.localCase
  | .case2 _ _ _ _ _ _ row => row.localCase
  | .case3 _ _ _ _ row _ => row.localCase
  | .case4 _ _ _ _ _ row _ => row.localCase

/-- The actual target stored at a realized formula role.  Unlike the earlier
`PositiveTargetRole.coordinate` wrapper, this selector is not tautological:
case analysis recovers the canonical coordinate equation retained by the
corresponding actual row. -/
def RealizedSourceRow.targetAtRole
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source) (role : PairCases.TargetRoleName) :
      Option (Erdos957GeometryLocalRows.LocalTarget P C source) :=
  match R with
  | .case1 _ _ _ _ _ _ _ row =>
      match role with
      | .case1Left => some row.left
      | .case1Right => some row.right
      | _ => none
  | .case2 _ _ _ _ _ _ row =>
      match role with
      | .case2Outer => some row.outer
      | .case2Secondary => some row.secondary
      | _ => none
  | .case3 _ _ _ _ row _ =>
      match row, role with
      | .low middle _ _ _, .case3Middle => some middle
      | .high _ middle _ _ _ _ _ _ _, .case3Middle => some middle
      | .high _ _ secondary _ _ _ _ _ _, .case3Secondary => some secondary
      | _, _ => none
  | .case4 _ _ _ _ _ row _ =>
      match row, role with
      | .whole middle _ _, .case4Primary => some middle
      | .orderedLow _ _ middle _ _ _ _, .case4SplitLeft => some middle
      | .orderedLow _ _ _ low _ _ _, .case4SplitRight => some low
      | .orderedHigh _ _ _ middle _ _ _ _, .case4SplitLeft => some middle
      | .orderedHigh _ _ _ _ side _ _ _, .case4SplitRight => some side
      | .pairedSplit _ _ _ _ _ middle _ _ _ _ _, .case4SplitLeft => some middle
      | .pairedSplit _ _ _ _ _ _ secondary _ _ _ _, .case4SplitRight =>
          some secondary
      | _, _ => none

/-- A positive recipient with its exact formula-row slot.  The equality to
`targetAtRole` ties the target to the stored Case-1/2/3/4 equation. -/
structure RealizedPositiveTarget
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source)
    (v : Erdos957GeometryCore.Vertex A) where
  role : PairCases.TargetRoleName
  target : Erdos957GeometryLocalRows.LocalTarget P C source
  target_at_role : R.targetAtRole role = some target
  vertex_eq : v = target.vertex

/-- Every positive token of a realized row has a precise retained formula
role. -/
theorem RealizedSourceRow.positive_target_role
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source)
    {v : Erdos957GeometryCore.Vertex A}
    (hpos : 0 < R.localCase.tokens v) :
    Nonempty (RealizedPositiveTarget R v) := by
  obtain ⟨role, hrole⟩ :=
    PairCases.positive_target_role R.localCase hpos
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNotHull hunit row =>
      rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
      · exact ⟨.case1Left, row.left, rfl, hrole⟩
      · exact ⟨.case1Right, row.right, rfl, hrole⟩
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
  | case2 middle hdegree htwo hmiddleNotHull twoExtreme normalized row =>
      rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
      · contradiction
      · contradiction
      · exact ⟨.case2Outer, row.outer, rfl, hrole⟩
      · exact ⟨.case2Secondary, row.secondary, rfl, hrole⟩
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
      · contradiction
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row with
      | low middleTarget hm hu hfour =>
          rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · exact ⟨.case3Middle, middleTarget, rfl, hrole⟩
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
      | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
          rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · exact ⟨.case3Middle, middleTarget, rfl, hrole⟩
          · exact ⟨.case3Secondary, secondaryTarget, rfl, hrole⟩
          · contradiction
          · contradiction
          · contradiction
          · contradiction
  | case4 middle hdegree htwo twoExtreme normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hcoord hfour =>
          rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · exact ⟨.case4Primary, middleTarget, rfl, hrole⟩
          · contradiction
          · contradiction
          · contradiction
      | orderedLow farthest hdegree middleTarget lowTarget hm hl hne =>
          rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · exact ⟨.case4SplitLeft, middleTarget, rfl, hrole⟩
          · exact ⟨.case4SplitRight, lowTarget, rfl, hrole⟩
      | orderedHigh farthest hdegree recipients middleTarget sideTarget hm hs hne =>
          rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · exact ⟨.case4SplitLeft, middleTarget, rfl, hrole⟩
          · exact ⟨.case4SplitRight, sideTarget, rfl, hrole⟩
      | pairedSplit commonFrame farthest branch rightSource hrightSource middleTarget
          secondaryTarget hsource hm hs hne =>
          rcases role with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _)
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · exact ⟨.case4SplitLeft, middleTarget, rfl, hrole⟩
          · exact ⟨.case4SplitRight, secondaryTarget, rfl, hrole⟩

/-- Roles whose retained formula is a genuine unit edge from the emitting
source.  Secondary Case-2 and split-right Case-4 roles are deliberately
excluded: those are in general only two-edge recipients. -/
def IsDirectTargetRole : PairCases.TargetRoleName → Prop
  | .case1Left | .case1Right | .case2Outer
  | .case3Middle | .case3Secondary
  | .case4Primary | .case4SecondaryLow | .case4SplitLeft => True
  | _ => False

private lemma adj_of_aligned_coordinate_unit
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (target : Erdos957GeometryCore.Vertex A) (q : Erdos957Cases13.Point)
    (hcoord : C.coord source target = q)
    (hunit : Erdos957Cases13.sqDist Erdos957Cases13.origin q = 1) :
    (unitDistanceGraph A).Adj source.1 target := by
  change dist (source.1 : ComplexPoint) (target : ComplexPoint) = 1
  have hsq : dist (source.1 : ComplexPoint) (target : ComplexPoint) ^ 2 = 1 := by
    rw [← C.sqDist_coord source source.1 target, C.coord_source, hcoord]
    simpa [Erdos957Cases13.origin] using hunit
  nlinarith [dist_nonneg (x := (source.1 : ComplexPoint))
    (y := (target : ComplexPoint))]

private lemma adj_of_rigid_coordinates
    {A : Finset ComplexPoint} (F : Erdos957Case24Bridge.Framed.RigidChart)
    (source target : Erdos957GeometryCore.Vertex A)
    (p q : Erdos957Cases24.Point)
    (hsource : F.toCanonical source = p)
    (htarget : F.toCanonical target = q) (hunit : dist p q = 1) :
    (unitDistanceGraph A).Adj source target := by
  change dist (source : ComplexPoint) (target : ComplexPoint) = 1
  rw [← F.dist_eq, hsource, htarget, hunit]

/-- Incidence projection used by collision analysis: every realized target
in a direct formula slot is genuinely unit-adjacent to its emitting source. -/
theorem RealizedPositiveTarget.adj_source_of_directRole
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source}
    {v : Erdos957GeometryCore.Vertex A}
    (D : RealizedPositiveTarget R v) (hdirect : IsDirectTargetRole D.role) :
    (unitDistanceGraph A).Adj source.1 v := by
  rcases D with ⟨role, target, hrole, hv⟩
  subst v
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNotHull hunit row =>
      cases role <;>
        simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
      · subst target
        exact adj_of_aligned_coordinate_unit row.left.vertex
          (Erdos957Cases13.case1Left middleCoord) row.left_coordinate
          (Erdos957Cases13.case1Left_common_unit hunit).1
      · subst target
        exact adj_of_aligned_coordinate_unit row.right.vertex
          (Erdos957Cases13.case1Right middleCoord) row.right_coordinate
          (Erdos957Cases13.case1Right_common_unit hunit).1
  | case2 middle hdegree htwo hmiddleNotHull twoExtreme normalized row =>
      cases role <;>
        simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
      subst target
      apply adj_of_rigid_coordinates normalized.frame source.1 row.outer.vertex
        Erdos957Cases24.Case2.u Erdos957Cases24.Case2.b
      · rw [← normalized.source_actual, normalized.frame.toCanonical_actual]
      · exact row.outer_edge_coordinate
      · exact Erdos957Cases24.Case2.dist_u_b
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row with
      | low middleTarget hm hu hfour =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          exact adj_of_aligned_coordinate_unit middleTarget.vertex middleCoord
            hm hu
      | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          · subst target
            exact adj_of_aligned_coordinate_unit middleTarget.vertex middleCoord
              hm hu
          · subst target
            exact adj_of_aligned_coordinate_unit secondaryTarget.vertex
              secondaryCoord hs hsu
  | case4 middle hdegree htwo twoExtreme normalized row hmiddleVertex =>
      cases row with
      | whole middleTarget hm hfour =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          apply adj_of_rigid_coordinates normalized.frame source.1
            middleTarget.vertex Erdos957Cases24.Case2.u
              Erdos957Cases24.Case2.v
          · rw [← normalized.source_actual, normalized.frame.toCanonical_actual]
          · exact hm
          · exact Erdos957Cases24.Case2.dist_u_v
      | orderedLow farthest hfive middleTarget lowTarget hm hl hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          apply adj_of_rigid_coordinates normalized.frame source.1
            middleTarget.vertex Erdos957Cases24.Case2.u
              Erdos957Cases24.Case2.v
          · rw [← normalized.source_actual, normalized.frame.toCanonical_actual]
          · exact hm
          · exact Erdos957Cases24.Case2.dist_u_v
      | orderedHigh farthest hsix recipients middleTarget sideTarget hm hs hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          apply adj_of_rigid_coordinates normalized.frame source.1
            middleTarget.vertex Erdos957Cases24.Case2.u
              Erdos957Cases24.Case2.v
          · rw [← normalized.source_actual, normalized.frame.toCanonical_actual]
          · exact hm
          · exact Erdos957Cases24.Case2.dist_u_v
      | pairedSplit commonFrame farthest branch rightSource hrightSource middleTarget
          secondaryTarget hsource hm hs hne =>
          cases role <;>
            simp [IsDirectTargetRole, RealizedSourceRow.targetAtRole] at hdirect hrole
          subst target
          apply adj_of_rigid_coordinates commonFrame source.1
            middleTarget.vertex (Erdos957Case24Bridge.Case4.sideSource rightSource)
              Erdos957Cases24.Case2.v hsource hm
          cases rightSource
          · simpa [Erdos957Case24Bridge.Case4.sideSource, dist_comm] using
              Erdos957Cases24.Case2.dist_uPrev_v
          · simpa [Erdos957Case24Bridge.Case4.sideSource] using
              Erdos957Cases24.Case2.dist_u_v

/-- Collision-facing form: the only non-direct realized roles are the
Case-2 secondary and Case-4 split-right recipients. -/
theorem RealizedPositiveTarget.direct_target_adj
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source}
    {v : Erdos957GeometryCore.Vertex A}
    (D : RealizedPositiveTarget R v)
    (hneCase2 : D.role ≠ PairCases.TargetRoleName.case2Secondary)
    (hneCase4 : D.role ≠ PairCases.TargetRoleName.case4SplitRight) :
    (unitDistanceGraph A).Adj source.1 v := by
  apply D.adj_source_of_directRole
  cases hrole : D.role <;>
    simp [IsDirectTargetRole, hrole] at hneCase2 hneCase4 ⊢

/-! ### Formula-derived arrival side and weight -/

/-- Cyclic association of a realized arrival.  Every positive arrival is
assigned to one of the two incident cyclic sides by its retained formula. -/
inductive ArrivalAssociation
  | fromPrevious | fromNext
  deriving DecidableEq

/-- Whether the selected row puts one or two doubled-charge tokens at this
recipient. -/
inductive ArrivalWeight
  | half | whole
  deriving DecidableEq

def ArrivalWeight.tokens : ArrivalWeight → ℕ
  | .half => 1
  | .whole => 2

def cyclicSideAssociation : CyclicSide → ArrivalAssociation
  | .previous => .fromPrevious
  | .next => .fromNext

/-- Case 2 extends away from the incident hull partner: the incoming-edge
picture therefore reverses the side named by its two-extreme witness. -/
def oppositeCyclicSideAssociation : CyclicSide → ArrivalAssociation
  | .previous => .fromNext
  | .next => .fromPrevious

/-- The successor-oriented aligned chart turns the sign of the horizontal
coordinate into the corresponding cyclic side.  The closed left convention
at zero makes this a total definition; later collision arguments treat the
possible vertical tie geometrically. -/
def horizontalAssociation (x : ℝ) : ArrivalAssociation :=
  if x ≤ 0 then .fromPrevious else .fromNext

/-- Convert the horizontal sign in the source-normalized Case-4 chart to
the globally oriented cyclic direction.  At a vertical tie the endpoint
orientation breaks the tie: the terminal/right endpoint assigns zero to
`fromPrevious`, while the reflected initial/left endpoint assigns zero to
`fromNext`.  This is the paper's deterministic one-left/one-right
convention for a recipient on an endpoint's vertical ray. -/
def orientedHorizontalAssociation (side : CyclicSide)
    (x : ℝ) : ArrivalAssociation :=
  match side with
  | .previous => horizontalAssociation x
  | .next => if x ≤ 0 then .fromNext else .fromPrevious

/-- Recipient-relative cyclic direction in the unreflected common directed
edge chart used by coherent paired Case-4 rows. -/
def commonPairHorizontalAssociation
    {B : Finset ComplexPoint}
    {D : Erdos957Case24Bridge.Case4.FarthestBelowData B}
    (branch : Erdos957Case24Bridge.Case4.FarthestBranchData B D)
    (rightSource : Bool) : ArrivalAssociation :=
  let dx := branch.sourceRecipient rightSource 0 -
    Erdos957Case24Bridge.Case4.sideSource rightSource 0
  if rightSource then horizontalAssociation dx
  else if dx < 0 then .fromPrevious else .fromNext

@[simp] theorem commonPairHorizontalAssociation_right
    {B : Finset ComplexPoint}
    {D : Erdos957Case24Bridge.Case4.FarthestBelowData B}
    (branch : Erdos957Case24Bridge.Case4.FarthestBranchData B D) :
    commonPairHorizontalAssociation branch true =
      horizontalAssociation
        (branch.sourceRecipient true 0 -
          Erdos957Case24Bridge.Case4.sideSource true 0) := by
  rfl

@[simp] theorem commonPairHorizontalAssociation_left
    {B : Finset ComplexPoint}
    {D : Erdos957Case24Bridge.Case4.FarthestBelowData B}
    (branch : Erdos957Case24Bridge.Case4.FarthestBranchData B D) :
    commonPairHorizontalAssociation branch false =
      if branch.sourceRecipient false 0 -
          Erdos957Case24Bridge.Case4.sideSource false 0 < 0 then
        .fromPrevious else .fromNext := by
  rfl

@[simp] theorem orientedHorizontalAssociation_case2_v
    (side : CyclicSide) :
    orientedHorizontalAssociation side (Erdos957Cases24.Case2.v 0) =
      cyclicSideAssociation side := by
  cases side <;>
    simp [orientedHorizontalAssociation, horizontalAssociation,
      cyclicSideAssociation, Erdos957Cases24.Case2.v,
      Erdos957Cases24.point]

@[simp] theorem pairedMiddleHorizontalAssociation
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {middle : Vertex A}
    (T : TwoExtremeCyclicWitness P source middle) :
    horizontalAssociation
        (Erdos957Cases24.Case2.v 0 -
          Erdos957Case24Bridge.Case4.sideSource
            (ActualCase24Rows.case4SourceIsRight T) 0) =
      cyclicSideAssociation T.side := by
  rcases T with ⟨side, neighbors_eq, side_adjacent⟩
  cases side <;>
    simp [horizontalAssociation, cyclicSideAssociation,
      ActualCase24Rows.case4SourceIsRight,
      Erdos957Case24Bridge.Case4.sideSource,
      Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point] <;>
    norm_num

/-- The association is computed only from retained geometric data.  In the
Case-3 secondary branch the sign is the actual signed area of the stored
source--middle--secondary formula. -/
def RealizedSourceRow.roleAssociation
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source) :
    PairCases.TargetRoleName → ArrivalAssociation :=
  match R with
  | .case1 _ _ _ _ _ _ _ _ => fun role ↦
      match role with
      | .case1Left => .fromPrevious
      | .case1Right => .fromNext
      | _ => .fromPrevious
  | .case2 _ _ _ _ T _ _ => fun _ ↦ oppositeCyclicSideAssociation T.side
  | .case3 _ _ _ middleCoord row _ => fun role ↦
      match row, role with
      | .high secondaryCoord _ _ _ _ _ _ _ _, .case3Secondary =>
          if Erdos957Case3General.crossFrom Erdos957Cases13.origin
              middleCoord secondaryCoord ≤ 0 then .fromPrevious else .fromNext
      | _, .case3Middle => horizontalAssociation middleCoord.1
      | _, _ => .fromPrevious
  | .case4 _ _ _ T _ row _ => fun role ↦
      match row, role with
      | .whole .., .case4Primary =>
          orientedHorizontalAssociation T.side (Erdos957Cases24.Case2.v 0)
      | .orderedLow .., .case4SplitLeft =>
          orientedHorizontalAssociation T.side (Erdos957Cases24.Case2.v 0)
      | .orderedLow D _ _ _ _ _ _, .case4SplitRight =>
          orientedHorizontalAssociation T.side (D.point 0)
      | .orderedHigh .., .case4SplitLeft =>
          orientedHorizontalAssociation T.side (Erdos957Cases24.Case2.v 0)
      | .orderedHigh _ _ recipients _ _ _ _ _, .case4SplitRight =>
          orientedHorizontalAssociation T.side (recipients.right 0)
      | .pairedSplit _ _ _ rightSource _ _ _ _ _ _ _, .case4SplitLeft =>
          horizontalAssociation
            (Erdos957Cases24.Case2.v 0 -
              Erdos957Case24Bridge.Case4.sideSource rightSource 0)
      | .pairedSplit _ _ branch rightSource _ _ _ _ _ _ _,
          .case4SplitRight =>
          commonPairHorizontalAssociation branch rightSource
      | _, _ => .fromPrevious

def RealizedSourceRow.roleWeight
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source) :
    PairCases.TargetRoleName → ArrivalWeight :=
  match R with
  | .case3 _ _ _ _ (.low ..) _ => fun role ↦
      if role = .case3Middle then .whole else .half
  | .case4 _ _ _ _ _ (.whole ..) _ => fun role ↦
      if role = .case4Primary then .whole else .half
  | _ => fun _ ↦ .half

/-- The certificate behind an arrival label.  It retains the target's exact
row slot and canonical formula; the Case-3 secondary additionally carries
the signed-area inequality that selected its cyclic side.  Case-4 labels
use the recipient's signed horizontal displacement from its actual source,
with the reflected successor chart corrected by
`orientedHorizontalAssociation`. -/
def RealizedSourceRow.ArrivalCertificate
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source)
    (role : PairCases.TargetRoleName)
    (target : Erdos957GeometryLocalRows.LocalTarget P C source)
    (side : ArrivalAssociation) : Prop :=
  match R with
  | .case1 _ _ _ middleCoord _ _ _ row =>
      match role with
      | .case1Left => side = .fromPrevious ∧ row.left = target ∧
          C.coord source row.left.vertex = Erdos957Cases13.case1Left middleCoord
      | .case1Right => side = .fromNext ∧ row.right = target ∧
          C.coord source row.right.vertex = Erdos957Cases13.case1Right middleCoord
      | _ => False
  | .case2 _ _ _ _ T normalized row =>
      match role with
      | .case2Outer => side = oppositeCyclicSideAssociation T.side ∧
          row.outer = target ∧
          normalized.frame.toCanonical row.outer.vertex =
            Erdos957Cases24.Case2.b
      | .case2Secondary => side = oppositeCyclicSideAssociation T.side ∧
          row.secondary = target ∧
          normalized.frame.toCanonical row.secondary.vertex =
            Erdos957Cases24.Case2.secondaryRecipient
              (Erdos957Case24Bridge.unitDegree
                (normalized.frame.image A) Erdos957Cases24.Case2.w)
              (Erdos957Case24Bridge.unitDegree
                (normalized.frame.image A) Erdos957Cases24.Case2.wNext)
      | _ => False
  | .case3 classifiedMiddle _ hone middleCoord row hmiddleVertex =>
      match row, role with
      | .low middle hm _ _, .case3Middle =>
          middle = target ∧ C.coord source middle.vertex = middleCoord ∧
            middle.vertex = classifiedMiddle ∧
            (hullUnitNeighbors P classifiedMiddle).card = 1 ∧
            ((middleCoord.1 ≤ 0 ∧ side = .fromPrevious) ∨
              (0 < middleCoord.1 ∧ side = .fromNext))
      | .high _ middle _ hm _ _ _ _ _, .case3Middle =>
          middle = target ∧ C.coord source middle.vertex = middleCoord ∧
            middle.vertex = classifiedMiddle ∧
            (hullUnitNeighbors P classifiedMiddle).card = 1 ∧
            ((middleCoord.1 ≤ 0 ∧ side = .fromPrevious) ∨
              (0 < middleCoord.1 ∧ side = .fromNext))
      | .high secondaryCoord _ secondary _ hs _ _ _ _, .case3Secondary =>
          secondary = target ∧ C.coord source secondary.vertex = secondaryCoord ∧
            ((Erdos957Case3General.crossFrom Erdos957Cases13.origin
                middleCoord secondaryCoord ≤ 0 ∧ side = .fromPrevious) ∨
              (0 < Erdos957Case3General.crossFrom Erdos957Cases13.origin
                middleCoord secondaryCoord ∧ side = .fromNext))
      | _, _ => False
  | .case4 _ _ _ T normalized row hmiddleVertex =>
      match row, role with
      | .whole middle hm _, .case4Primary =>
          side = orientedHorizontalAssociation T.side
              (Erdos957Cases24.Case2.v 0) ∧ middle = target ∧
            normalized.frame.toCanonical middle.vertex = Erdos957Cases24.Case2.v
      | .orderedLow _ _ middle _ hm _ _, .case4SplitLeft =>
          side = orientedHorizontalAssociation T.side
              (Erdos957Cases24.Case2.v 0) ∧ middle = target ∧
            normalized.frame.toCanonical middle.vertex = Erdos957Cases24.Case2.v
      | .orderedLow D _ _ low _ hl _, .case4SplitRight =>
          side = orientedHorizontalAssociation T.side (D.point 0) ∧ low = target ∧
            normalized.frame.toCanonical low.vertex = D.point
      | .orderedHigh _ _ _ middle _ hm _ _, .case4SplitLeft =>
          side = orientedHorizontalAssociation T.side
              (Erdos957Cases24.Case2.v 0) ∧ middle = target ∧
            normalized.frame.toCanonical middle.vertex = Erdos957Cases24.Case2.v
      | .orderedHigh _ _ recipients _ secondary _ hs _, .case4SplitRight =>
          side = orientedHorizontalAssociation T.side (recipients.right 0) ∧
            secondary = target ∧
            normalized.frame.toCanonical secondary.vertex = recipients.right
      | .pairedSplit commonFrame _ branch rightSource hright middle _ hs hm _ _,
          .case4SplitLeft =>
          side = horizontalAssociation
              (Erdos957Cases24.Case2.v 0 -
                Erdos957Case24Bridge.Case4.sideSource rightSource 0) ∧
            middle = target ∧
            rightSource = ActualCase24Rows.case4SourceIsRight T ∧
            commonFrame.toCanonical middle.vertex = Erdos957Cases24.Case2.v
      | .pairedSplit commonFrame _ branch rightSource hright _ secondary hs _ hq _,
          .case4SplitRight =>
          side = commonPairHorizontalAssociation branch rightSource ∧
            secondary = target ∧
            rightSource = ActualCase24Rows.case4SourceIsRight T ∧
            commonFrame.toCanonical secondary.vertex =
              branch.sourceRecipient rightSource
      | _, _ => False

/-- Collision-facing descriptor of one actual positive arrival. -/
structure RealizedArrivalDescriptor
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source)
    (role : PairCases.TargetRoleName)
    (target : Erdos957GeometryLocalRows.LocalTarget P C source) where
  association : ArrivalAssociation
  weight : ArrivalWeight
  association_eq : association = R.roleAssociation role
  weight_eq : weight = R.roleWeight role
  certificate : R.ArrivalCertificate role target association

theorem RealizedSourceRow.arrivalCertificate_of_targetAtRole
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source)
    (role : PairCases.TargetRoleName)
    (target : Erdos957GeometryLocalRows.LocalTarget P C source)
    (htarget : R.targetAtRole role = some target) :
    R.ArrivalCertificate role target (R.roleAssociation role) := by
  let side := R.roleAssociation role
  change R.ArrivalCertificate role target side
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNotHull hunit row =>
      cases row
      cases hrole : role <;>
        simp_all [side, RealizedSourceRow.roleAssociation,
          RealizedSourceRow.ArrivalCertificate,
          RealizedSourceRow.targetAtRole, hrole] <;>
        subst target <;>
        first | assumption | simp_all [Erdos957GeometryLocalRows.sourceCoordinates]

  | case2 middle hdegree htwo hmiddleNotHull T normalized row =>
      cases row
      cases hrole : role <;>
        simp_all [side, RealizedSourceRow.roleAssociation,
          RealizedSourceRow.ArrivalCertificate,
          RealizedSourceRow.targetAtRole, hrole] <;>
        subst target <;> simp_all
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      by_cases hx : middleCoord.1 ≤ 0
      · cases row with
        | low middleTarget hm hu hfour =>
            change middleTarget.vertex = middle at hmiddleVertex
            cases hrole : role <;>
              simp_all [side, RealizedSourceRow.roleAssociation,
                RealizedSourceRow.ArrivalCertificate,
                RealizedSourceRow.targetAtRole, horizontalAssociation, hx, hrole] <;>
              subst target <;>
              first
              | exact (by simpa [← hmiddleVertex] using hm)
              | simp_all [PairCases.Case3ActualRow.middleTarget]
        | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
            change middleTarget.vertex = middle at hmiddleVertex
            by_cases hcross : Erdos957Case3General.crossFrom
                Erdos957Cases13.origin middleCoord secondaryCoord ≤ 0
            · cases hrole : role <;>
                simp_all [side, RealizedSourceRow.roleAssociation,
                  RealizedSourceRow.ArrivalCertificate,
                  RealizedSourceRow.targetAtRole, horizontalAssociation, hx,
                  hcross, hrole] <;> subst target <;>
                  first
                  | exact (by simpa [← hmiddleVertex] using hm)
                  | simp_all [PairCases.Case3ActualRow.middleTarget]
            · have hcrossPos : 0 < Erdos957Case3General.crossFrom
                  Erdos957Cases13.origin middleCoord secondaryCoord := lt_of_not_ge hcross
              cases hrole : role <;>
                simp_all [side, RealizedSourceRow.roleAssociation,
                  RealizedSourceRow.ArrivalCertificate,
                  RealizedSourceRow.targetAtRole, horizontalAssociation, hx,
                  hcross, hrole] <;> subst target <;>
                  first
                  | exact (by simpa [← hmiddleVertex] using hm)
                  | simp_all [PairCases.Case3ActualRow.middleTarget]
      · have hxPos : 0 < middleCoord.1 := lt_of_not_ge hx
        cases row with
        | low middleTarget hm hu hfour =>
            change middleTarget.vertex = middle at hmiddleVertex
            cases hrole : role <;>
              simp_all [side, RealizedSourceRow.roleAssociation,
                RealizedSourceRow.ArrivalCertificate,
                RealizedSourceRow.targetAtRole, horizontalAssociation, hx, hrole] <;>
              subst target <;>
              first
              | exact (by simpa [← hmiddleVertex] using hm)
              | simp_all [PairCases.Case3ActualRow.middleTarget]
        | high secondaryCoord middleTarget secondaryTarget hm hs hu hsu hmu hne =>
            change middleTarget.vertex = middle at hmiddleVertex
            by_cases hcross : Erdos957Case3General.crossFrom
                Erdos957Cases13.origin middleCoord secondaryCoord ≤ 0
            · cases hrole : role <;>
                simp_all [side, RealizedSourceRow.roleAssociation,
                  RealizedSourceRow.ArrivalCertificate,
                  RealizedSourceRow.targetAtRole, horizontalAssociation, hx,
                  hcross, hrole] <;> subst target <;>
                  first
                  | exact (by simpa [← hmiddleVertex] using hm)
                  | simp_all [PairCases.Case3ActualRow.middleTarget]
            · have hcrossPos : 0 < Erdos957Case3General.crossFrom
                  Erdos957Cases13.origin middleCoord secondaryCoord := lt_of_not_ge hcross
              cases hrole : role <;>
                simp_all [side, RealizedSourceRow.roleAssociation,
                  RealizedSourceRow.ArrivalCertificate,
                  RealizedSourceRow.targetAtRole, horizontalAssociation, hx,
                  hcross, hrole] <;> subst target <;>
                  first
                  | exact (by simpa [← hmiddleVertex] using hm)
                  | simp_all [PairCases.Case3ActualRow.middleTarget]
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      cases row <;> cases hrole : role <;>
        simp_all [side, RealizedSourceRow.roleAssociation,
          RealizedSourceRow.ArrivalCertificate,
          RealizedSourceRow.targetAtRole, hrole] <;>
        subst target <;> simp_all
  all_goals subst_vars
  all_goals simp_all [Erdos957GeometryLocalRows.sourceCoordinates]

theorem RealizedPositiveTarget.arrivalDescriptor
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source} {v : Erdos957GeometryCore.Vertex A}
    (D : RealizedPositiveTarget R v) :
    Nonempty (RealizedArrivalDescriptor R D.role D.target) := by
  exact ⟨⟨R.roleAssociation D.role, R.roleWeight D.role, rfl, rfl,
    R.arrivalCertificate_of_targetAtRole D.role D.target D.target_at_role⟩⟩

/-- The actual token multiplicity is exactly the descriptor's retained
half/whole weight. -/
theorem RealizedSourceRow.token_eq_roleWeight_of_targetAtRole
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source)
    (role : PairCases.TargetRoleName)
    (target : Erdos957GeometryLocalRows.LocalTarget P C source)
    (htarget : R.targetAtRole role = some target) :
    R.localCase.tokens target.vertex = (R.roleWeight role).tokens := by
  cases R with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNotHull hunit row =>
      cases row
      cases hrole : role <;>
        simp_all [RealizedSourceRow.localCase, PairCases.Case1ActualRow.localCase,
          RealizedSourceRow.roleWeight, ArrivalWeight.tokens,
          RealizedSourceRow.targetAtRole,
          Erdos957GeometryLocalRows.LocalCase.tokens, hrole] <;>
        subst target <;> simp_all [eq_comm]
  | case2 middle hdegree htwo hmiddleNotHull T normalized row =>
      cases row
      cases hrole : role <;>
        simp_all [RealizedSourceRow.localCase, ActualCase24Rows.Case2ActualRow.localCase,
          RealizedSourceRow.roleWeight, ArrivalWeight.tokens,
          RealizedSourceRow.targetAtRole,
          Erdos957GeometryLocalRows.LocalCase.tokens, hrole] <;>
        subst target <;> simp_all [eq_comm]
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> cases hrole : role <;>
        simp_all [RealizedSourceRow.localCase, PairCases.Case3ActualRow.localCase,
          RealizedSourceRow.roleWeight, ArrivalWeight.tokens,
          RealizedSourceRow.targetAtRole,
          Erdos957GeometryLocalRows.LocalCase.tokens, hrole] <;>
        subst target <;> simp_all [eq_comm]
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      cases row <;> cases hrole : role <;>
        simp_all [RealizedSourceRow.localCase, ActualCase24Rows.Case4ActualRow.localCase,
          RealizedSourceRow.roleWeight, ArrivalWeight.tokens,
          RealizedSourceRow.targetAtRole,
          Erdos957GeometryLocalRows.LocalCase.tokens, hrole] <;>
        subst target <;> simp_all [eq_comm]
  all_goals subst target
  all_goals simp_all [eq_comm]

theorem RealizedPositiveTarget.token_eq_roleWeight
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    {R : RealizedSourceRow P C source} {v : Erdos957GeometryCore.Vertex A}
    (D : RealizedPositiveTarget R v) :
    R.localCase.tokens v = (R.roleWeight D.role).tokens := by
  calc
    R.localCase.tokens v = R.localCase.tokens D.target.vertex :=
      congrArg R.localCase.tokens D.vertex_eq
    _ = (R.roleWeight D.role).tokens :=
      R.token_eq_roleWeight_of_targetAtRole D.role D.target D.target_at_role

/-- The selected source-indexed enriched rows.  This is dependent data, not
pointwise mere existence, so its erasure is definitionally the same local
row inspected by collision arguments. -/
def HasRealizedSourceRows {A : Finset ComplexPoint}
    (P : CyclicHullData A) (W : DiameterWitnessData P)
    (C : P.AlignedChartData) : Type :=
  ∀ (u : Vertex A) (hu : u ∈ sourceVertices P W),
    RealizedSourceRow P C
      (Erdos957GeometryLocalRows.sourceIndex P W u hu)

/-- Erasing the retained formulas produces exactly the `HasLocalCases`
interface consumed by the transfer assembly. -/
def HasRealizedSourceRows.hasLocalCases
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    (hrows : HasRealizedSourceRows P W C) :
    Erdos957GeometryLocalRows.HasLocalCases P W C :=
  fun u hu ↦ (hrows u hu).localCase

/-! ### Coherent Case-4 hull-pair data -/

/-- One farthest branch selected once in the common normalized chart of the
two hull endpoints.  The right endpoint is the original source (`u`) and
the left endpoint is its cyclic-side partner (`uPrev`). -/
structure Case4HullPairBranch
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T) where
  farthest : Erdos957Case24Bridge.Case4.FarthestBelowData (N.frame.image A)
  branch : Erdos957Case24Bridge.Case4.FarthestBranchData
    (N.frame.image A) farthest

/-- The common normalized hull-pair chart contains an honest ordered
farthest branch whenever the shared middle has degree five.  In particular,
the branch is selected once at pair level; no reflected endpoint performs a
second lexicographic choice. -/
theorem nonempty_case4HullPairBranch
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    {P : CyclicHullData A} {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5) :
    Nonempty (Case4HullPairBranch N) := by
  have huPrevA : Erdos957Cases24.Case2.uPrev ∈ N.frame.image A := by
    apply N.frame.mem_image_iff.mpr
    rw [N.side_actual]
    exact (cyclicSideVertex P source T.side).property
  have huA : Erdos957Cases24.Case2.u ∈ N.frame.image A := by
    apply N.frame.mem_image_iff.mpr
    rw [N.source_actual]
    exact source.1.property
  have hvA : Erdos957Cases24.Case4.v ∈ N.frame.image A := by
    apply N.frame.mem_image_iff.mpr
    rw [Erdos957Cases24.Case4.v, N.middle_actual]
    exact middle.property
  have hvDegree : Erdos957Case24Bridge.unitDegree (N.frame.image A)
      Erdos957Cases24.Case4.v = 5 := by
    rw [N.frame.unitDegree_image_actual A, Erdos957Cases24.Case4.v,
      N.middle_actual]
    rw [← ActualCase24Rows.graph_degree_eq_unitDegree]
    exact hmiddleDegree
  obtain ⟨D⟩ := Erdos957Case24Bridge.Case4.exists_farthestBelowData
    huPrevA huA hvDegree
  obtain ⟨B⟩ := Erdos957ContactGraph.nonempty_farthestBranchData
    (N.frame.image_oneSeparated hA) N.strict_support hvA huPrevA huA
      hvDegree D
  exact ⟨⟨D, B⟩⟩

/-- The actual recipient selected for the left (`false`) or right (`true`)
hull endpoint of a coherent Case-4 pair. -/
def Case4HullPairBranch.actualRecipient
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    {N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T}
    (B : Case4HullPairBranch N) (rightSource : Bool) :
    Erdos957GeometryCore.Vertex A :=
  let q := B.branch.sourceRecipient rightSource
  ⟨N.frame.actual q,
    N.frame.mem_image_iff.mp
      ((Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        (B.branch.sourceRecipient_mem rightSource)).1)⟩

@[simp] theorem Case4HullPairBranch.actualRecipient_coe
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    {N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T}
    (B : Case4HullPairBranch N) (rightSource : Bool) :
    ((B.actualRecipient rightSource : Erdos957GeometryCore.Vertex A) :
      ComplexPoint) =
      N.frame.actual (B.branch.sourceRecipient rightSource) := rfl

/-- In the low branch both hull endpoints use literally the same actual
farthest point. -/
theorem Case4HullPairBranch.actualRecipient_eq_of_low
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}}
    {middle : Erdos957GeometryCore.Vertex A}
    {T : TwoExtremeCyclicWitness P source middle}
    {N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T}
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData (N.frame.image A))
    (hdegree : Erdos957Case24Bridge.unitDegree (N.frame.image A) D.point ≤ 5) :
    let B : Case4HullPairBranch N :=
      ⟨D, Erdos957Case24Bridge.Case4.FarthestBranchData.low hdegree⟩
    B.actualRecipient false = B.actualRecipient true := by
  rfl

/-- A selected row is in the split Case-4 branch exactly when its retained
right split role exists. -/
def RealizedSourceRow.IsCase4Split
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {C : P.AlignedChartData} {source : {p // p ∈ P.H}}
    (R : RealizedSourceRow P C source) : Prop :=
  ∃ target, R.targetAtRole PairCases.TargetRoleName.case4SplitRight = some target

/-- The exact coherence certificate for a selected Case-4 row.  The cyclic
side endpoint is always retained as a hull partner.  It need not itself be
an emitting source; if it is one, the selected partner row is required to
use the same actual middle and the `false` recipient of the one common
pair-level branch. -/
structure PairedCase4Rows
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    (rows : HasRealizedSourceRows P W C)
    (u : Erdos957GeometryCore.Vertex A) (hu : u ∈ sourceVertices P W) where
  middle : Erdos957GeometryCore.Vertex A
  middle_degree_five : (unitDistanceGraph A).degree middle = 5
  twoExtreme : TwoExtremeCyclicWitness P
    (Erdos957GeometryLocalRows.sourceIndex P W u hu) middle
  normalized : ActualCase24Rows.TwoExtremeNormalizedFrame
    (Erdos957GeometryLocalRows.sourceIndex P W u hu) middle twoExtreme
  pairBranch : Case4HullPairBranch normalized
  currentMiddleTarget :
    Erdos957GeometryLocalRows.LocalTarget P C
      (Erdos957GeometryLocalRows.sourceIndex P W u hu)
  currentSecondaryTarget :
    Erdos957GeometryLocalRows.LocalTarget P C
      (Erdos957GeometryLocalRows.sourceIndex P W u hu)
  current_middle_role :
    (rows u hu).targetAtRole PairCases.TargetRoleName.case4SplitLeft =
      some currentMiddleTarget
  current_secondary_role :
    (rows u hu).targetAtRole PairCases.TargetRoleName.case4SplitRight =
      some currentSecondaryTarget
  current_middle_vertex : currentMiddleTarget.vertex = middle
  current_secondary_vertex :
    currentSecondaryTarget.vertex = pairBranch.actualRecipient true
  partner_absent_or_coherent :
    cyclicSideVertex P (Erdos957GeometryLocalRows.sourceIndex P W u hu)
        twoExtreme.side ∉ sourceVertices P W ∨
      ∀ hp : cyclicSideVertex P
          (Erdos957GeometryLocalRows.sourceIndex P W u hu)
            twoExtreme.side ∈ sourceVertices P W,
        ∃ (partnerMiddleTarget partnerSecondaryTarget :
            Erdos957GeometryLocalRows.LocalTarget P C
              (Erdos957GeometryLocalRows.sourceIndex P W
                (cyclicSideVertex P
                  (Erdos957GeometryLocalRows.sourceIndex P W u hu)
                    twoExtreme.side) hp)),
          (rows (cyclicSideVertex P
              (Erdos957GeometryLocalRows.sourceIndex P W u hu)
                twoExtreme.side) hp).targetAtRole
              PairCases.TargetRoleName.case4SplitLeft =
                some partnerMiddleTarget ∧
          (rows (cyclicSideVertex P
              (Erdos957GeometryLocalRows.sourceIndex P W u hu)
                twoExtreme.side) hp).targetAtRole
              PairCases.TargetRoleName.case4SplitRight =
                some partnerSecondaryTarget ∧
          partnerMiddleTarget.vertex = middle ∧
          partnerSecondaryTarget.vertex = pairBranch.actualRecipient false

/-- Globally selected realized rows together with conditional coherence for
every split Case-4 row. -/
structure CoherentRealizedSourceRows
    {A : Finset ComplexPoint} (P : CyclicHullData A)
    (W : DiameterWitnessData P) (C : P.AlignedChartData) where
  rows : HasRealizedSourceRows P W C
  case4_pair : ∀ (u : Erdos957GeometryCore.Vertex A)
      (hu : u ∈ sourceVertices P W),
    (rows u hu).IsCase4Split → PairedCase4Rows rows u hu

/-- Coherent selected rows erase definitionally to the local cases used by
the global transfer. -/
def CoherentRealizedSourceRows.hasLocalCases
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    {W : DiameterWitnessData P} {C : P.AlignedChartData}
    (R : CoherentRealizedSourceRows P W C) :
    Erdos957GeometryLocalRows.HasLocalCases P W C :=
  R.rows.hasLocalCases

/-! ## Checked Case 2 and Case 4 realizations -/

namespace EuclideanCases

open Erdos957Cases24
open Erdos957Case24Bridge

abbrev Point := Erdos957Cases24.Point

/-- Coordinate identification used only to import the already checked
planar kissing-number bound into the `EuclideanSpace` model of Cases 2/4. -/
def toPair (p : Point) : ℝ × ℝ := (p 0, p 1)

lemma toPair_injective : Function.Injective toPair := by
  intro p q hpq
  ext i
  fin_cases i
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq

def toPairEmbedding : Point ↪ ℝ × ℝ := ⟨toPair, toPair_injective⟩

def pairImage (A : Finset Point) : Finset (ℝ × ℝ) :=
  A.map toPairEmbedding

@[simp] lemma mem_pairImage {A : Finset Point} {p : Point} :
    toPair p ∈ pairImage A ↔ p ∈ A := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, hqp⟩
    simpa [toPair_injective hqp] using hq
  · exact fun hp ↦ Finset.mem_map.mpr ⟨p, hp, rfl⟩

lemma sqDist_toPair (p q : Point) :
    Erdos957Cases13.sqDist (toPair p) (toPair q) = dist p q ^ 2 := by
  rw [Erdos957Cases24.dist_sq_eq_coordinates]
  rfl

lemma pairImage_oneSeparated {A : Finset Point}
    (hA : Erdos957Cases24.IsOneSeparated A) :
    Erdos957Cases13.IsOneSeparated (pairImage A : Set (ℝ × ℝ)) := by
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨p, hp, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨q, hq, rfl⟩
  have hpq : p ≠ q := fun h ↦ hxy (congrArg toPair h)
  change 1 ≤ Erdos957Cases13.sqDist (toPair p) (toPair q)
  rw [sqDist_toPair]
  have hd := hA p hp q hq hpq
  nlinarith [(dist_nonneg : 0 ≤ dist p q)]

lemma pair_degree_eq (A : Finset Point) (p : Point) :
    Erdos957Case13Bridge.degree (pairImage A) (toPair p) =
      Erdos957Case24Bridge.unitDegree A p := by
  classical
  rw [Erdos957Case13Bridge.degree, Erdos957Case24Bridge.unitDegree]
  apply Finset.card_bij
    (s := Erdos957Case13Bridge.unitNeighbors (pairImage A) (toPair p))
    (t := Erdos957Cases24.unitNeighbors A p)
    (fun q hq ↦ Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).1))
  · intro q hq
    let r : Point := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).1)
    have hrA : r ∈ A :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).1)).1
    have hrq : toPair r = q :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).1)).2
    have hsquare := (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).2
    rw [← hrq, sqDist_toPair] at hsquare
    have hdist : dist p r = 1 := by
      nlinarith [(dist_nonneg : 0 ≤ dist p r)]
    exact Erdos957Cases24.mem_unitNeighbors.mpr ⟨hrA, hdist⟩
  · intro q hq r hr hqr
    have hqspec := (Classical.choose_spec
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).1)).2
    have hrspec := (Classical.choose_spec
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hr).1)).2
    exact hqspec.symm.trans ((congrArg toPair hqr).trans hrspec)
  · intro q hq
    refine ⟨toPair q, ?_, ?_⟩
    · apply Erdos957Case13Bridge.mem_unitNeighbors.mpr
      refine ⟨mem_pairImage.mpr (Erdos957Cases24.mem_unitNeighbors.mp hq).1, ?_⟩
      rw [sqDist_toPair, (Erdos957Cases24.mem_unitNeighbors.mp hq).2]
      norm_num
    · exact toPair_injective
        (Classical.choose_spec
          (Finset.mem_map.mp (mem_pairImage.mpr
            (Erdos957Cases24.mem_unitNeighbors.mp hq).1))).2

/-- Every target in the Euclidean coordinate model has unit degree at most
six, derived from separation rather than supplied as a capacity assumption. -/
theorem unitDegree_le_six {A : Finset Point}
    (hA : Erdos957Cases24.IsOneSeparated A) (p : Point) :
    Erdos957Case24Bridge.unitDegree A p ≤ 6 := by
  rw [← pair_degree_eq A p]
  exact Erdos957Case13Bridge.degree_le_six (pairImage_oneSeparated hA) (toPair p)

/-- Four explicit candidate positions around the terminal Case 2 recipient.
The paper's final-sector argument proves precisely this containment. -/
noncomputable def case2ECandidates : Finset Point :=
  {Case2.b, Case2.wNext, Case2.eSouthEast, Case2.eEast}

lemma card_case2ECandidates_le_four : case2ECandidates.card ≤ 4 := by
  exact Finset.card_le_four

/-- The final-sector incidence statement implies the degree bound at `e`;
the bound is not postulated as transfer capacity. -/
lemma case2_e_degree_le_four {A : Finset Point}
    (hsector : unitNeighbors A Case2.e ⊆ case2ECandidates) :
    Erdos957Case24Bridge.unitDegree A Case2.e ≤ 4 := by
  exact (Finset.card_le_card hsector).trans card_case2ECandidates_le_four

/-- Honest normalized right-hand Case 2 data. -/
structure Case2Geometry (A H : Finset Point) where
  hull_above : HullAboveSupport H
  oneSeparated : Erdos957Cases24.IsOneSeparated A
  outer_mem : Case2.b ∈ A
  displayed_five_mem : Case2.displayedFiveAtB ⊆ A
  no_straight_continuation : Case2.uNext ∉ A
  final_sector : unitNeighbors A Case2.e ⊆ case2ECandidates

/-- Case 2 realization.  The only numerical inputs to the underlying
constructor are derived here from angular packing and the final-sector
incidence statement. -/
theorem Case2Geometry.realize {A H : Finset Point} (G : Case2Geometry A H)
    : Nonempty (Erdos957Case24Bridge.LocalTransfer A H Case2.u 2) := by
  exact Erdos957Case24Bridge.Case2.localTransfer_of_no_straight_continuation
    A H G.hull_above G.oneSeparated G.outer_mem G.displayed_five_mem
    (unitDegree_le_six G.oneSeparated Case2.b) G.no_straight_continuation
    (case2_e_degree_le_four G.final_sector)

/-- If the middle point has degree at most four, the Case 4 rule gives all
four doubled tokens to that point.  This branch does not mention the unused
common-neighbor targets. -/
theorem case4_localTransfer_of_middle_le_four {A H : Finset Point}
    (hH : HullAboveSupport H) (hvA : Case4.v ∈ A)
    (hv : Erdos957Case24Bridge.unitDegree A Case4.v ≤ 4) :
    Nonempty (Erdos957Case24Bridge.LocalTransfer A H Case2.u 4) := by
  let R := Case4.recipientSet
    (Erdos957Case24Bridge.unitDegree A Case4.v)
    (Erdos957Case24Bridge.unitDegree A Case4.w)
  have hR : R = {Case4.v} := by simp [R, Case4.recipientSet, hv]
  refine ⟨{
    recipients := R
    tokens := Erdos957Case24Bridge.Case4.tokens A
    positive_iff_mem := ?_
    recipients_subset_configuration := ?_
    row_sum := ?_
    target_not_hull := ?_
    target_capacity := ?_
    target_horizontal_le_three_halves := ?_
    target_in_rectangle := ?_
    target_below_support := ?_
    target_within_two := ?_ }⟩
  · intro p
    simpa [R] using Erdos957Case24Bridge.Case4.tokens_positive_iff_mem A p
  · intro p hp
    rw [hR] at hp
    have hpv : p = Case4.v := by simpa using hp
    exact hpv ▸ hvA
  · simp [Erdos957Case24Bridge.Case4.tokens, hv, hvA]
  · intro p hp
    have hpv : p = Case4.v := by simpa [hR] using hp
    subst p
    exact not_mem_hull_of_belowSupport hH Case4.v_below_support
  · intro p hp
    have hpv : p = Case4.v := by simpa [hR] using hp
    subst p
    simp [Erdos957Case24Bridge.Case4.tokens, hv]
    omega
  · intro p hp
    have hpv : p = Case4.v := by simpa [hR] using hp
    subst p
    norm_num [Case4.v, Case2.v, Erdos957Cases24.point]
  · intro p hp
    have hpv : p = Case4.v := by simpa [hR] using hp
    simpa [hpv] using Case4.v_in_rectangle
  · intro p hp
    have hpv : p = Case4.v := by simpa [hR] using hp
    simpa [hpv] using Case4.v_below_support
  · intro p hp
    have hpv : p = Case4.v := by simpa [hR] using hp
    simpa [hpv] using Case4.u_within_two_v

/-- Honest completion/exclusion data for all of Case 4.  The displayed
five-neighbor picture and its completions are requested only in the
five-valent subcase; the degree-at-most-four branch is handled directly. -/
structure Case4Geometry (A H : Finset Point) where
  hull_above : HullAboveSupport H
  oneSeparated : Erdos957Cases24.IsOneSeparated A
  middle_mem : Case4.v ∈ A
  middle_degree_le_five : Erdos957Case24Bridge.unitDegree A Case4.v ≤ 5
  displayed_five_mem : Erdos957Case24Bridge.unitDegree A Case4.v = 5 →
    Case4.displayedFiveAtV ⊆ A
  left_completion : Erdos957Case24Bridge.unitDegree A Case4.v = 5 →
    Erdos957Case24Bridge.unitDegree A Case4.a = 6 → Case4.vMissing ∈ A
  continuation : Point
  right_completion : Erdos957Case24Bridge.unitDegree A Case4.v = 5 →
    Erdos957Case24Bridge.unitDegree A Case4.b = 6 → continuation ∈ A
  no_straight_continuation : continuation ∉ A

/-- Instantiation of the checked Case 4 constructor.  Both degree-five
recipient bounds are consequences of completion/exclusion facts. -/
theorem Case4Geometry.realize {A H : Finset Point} (G : Case4Geometry A H) :
    Nonempty (Erdos957Case24Bridge.LocalTransfer A H Case2.u 4) := by
  by_cases hlow : Erdos957Case24Bridge.unitDegree A Case4.v ≤ 4
  · exact case4_localTransfer_of_middle_le_four G.hull_above G.middle_mem hlow
  · have hle := G.middle_degree_le_five
    have hfive : Erdos957Case24Bridge.unitDegree A Case4.v = 5 := by omega
    exact Erdos957Case24Bridge.Case4.localTransfer_of_completions A H
      G.hull_above G.middle_mem (G.displayed_five_mem hfive) hfive
      (unitDegree_le_six G.oneSeparated Case4.a) (G.left_completion hfive)
      G.continuation (unitDegree_le_six G.oneSeparated Case4.b)
      (G.right_completion hfive) G.no_straight_continuation

end EuclideanCases

end Erdos957CaseClassification
