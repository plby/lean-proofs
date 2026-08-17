/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos1027.FiniteExpect

/-!
# Finite counting lemmas for the DGK argument

This file contains the cardinality calculations which sit between the
deterministic threat structure and the analytic fixed-edge estimate in the
Duraj--Gutowski--Kozik proof.  Everything is done on finite uniform sample
spaces.

The main calculation is `expect_indicator_conditionalThreat`.  After all
data outside a fixed edge have been exposed, let `high v` be the set of
priority values which permit an initially opposite-coloured vertex `v` to
be flipped.  At each vertex the allowed labels are

* the target colour with an arbitrary priority, or
* the opposite colour with priority in `high v`.

The initially-all-target-colour assignments are impossible for a final
monochromatic edge and are removed.  The resulting conditional probability
is exactly

`2^(-|e|) * (prod v in e (1 + |high v| / N) - 1)`.
-/

open scoped BigOperators

namespace Erdos1027.DGKCounts

open Finset
open Erdos1027.FiniteExpect

/-! ## Pointwise events and elementary finite bounds -/

/-- Cardinality union bound for predicates on a finite sample space. -/
lemma card_filter_biExists_le_sum {Ω ι : Type*} [DecidableEq Ω]
    (sample : Finset Ω) (I : Finset ι) (P : ι → Ω → Prop)
    [∀ i ω, Decidable (P i ω)] :
    (sample.filter fun ω ↦ ∃ i ∈ I, P i ω).card ≤
      ∑ i ∈ I, (sample.filter fun ω ↦ P i ω).card := by
  classical
  by_cases hI : I.Nonempty
  · have hle :
        sample.filter (fun ω ↦ ∃ i ∈ I, P i ω) ⊆
          I.biUnion (fun i ↦ sample.filter fun ω ↦ P i ω) := by
        intro ω hω
        obtain ⟨hmem, i, hi, hPi⟩ := Finset.mem_filter.mp hω
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hmem, hPi⟩⟩
    exact (Finset.card_le_card hle).trans (Finset.card_biUnion_le)
  · have hIe : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    simp

/-- Division-free Markov bound for a natural-valued statistic. -/
lemma threshold_mul_card_filter_le_sum {Ω : Type*} [DecidableEq Ω]
    (sample : Finset Ω) (Z : Ω → ℕ) (a : ℕ) :
    a * (sample.filter (fun ω ↦ a ≤ Z ω)).card ≤ (∑ ω ∈ sample, Z ω) := by
  calc
    a * (sample.filter (fun ω ↦ a ≤ Z ω)).card =
        ∑ _ω ∈ sample.filter (fun ω ↦ a ≤ Z ω), a := by simp [mul_comm]
    _ ≤ ∑ ω ∈ sample.filter (fun ω ↦ a ≤ Z ω), Z ω := by
      exact Finset.sum_le_sum fun ω hω ↦ (Finset.mem_filter.mp hω).2
    _ ≤ ∑ ω ∈ sample, Z ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)

/-! ## Almost-monochromatic Boolean colourings -/

/-- Deleting `v` leaves a set monochromatic. -/
abbrev MonochromaticAway {V : Type*} [DecidableEq V]
    (edge : Finset V) (v : V) (colour : V → Bool) : Prop :=
  IsMonochromatic (edge.erase v) colour

/-- A colouring is almost monochromatic if deletion of some edge vertex
leaves a monochromatic set. -/
def AlmostMonochromatic {V : Type*} [DecidableEq V]
    (edge : Finset V) (colour : V → Bool) : Prop :=
  ∃ v ∈ edge, MonochromaticAway edge v colour

instance almostMonochromaticDecidable {V : Type*} [DecidableEq V]
    (edge : Finset V) (colour : V → Bool) :
    Decidable (AlmostMonochromatic edge colour) := by
  unfold AlmostMonochromatic
  infer_instance

/-- Exact count for a fixed deleted vertex.  The hypothesis `2 ≤ edge.card`
ensures that `edge.erase v` is nonempty, so its monochromatic colour is
unique. -/
lemma card_monochromaticAway_colorings {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) {v : V} (hv : v ∈ edge) (hedge : 2 ≤ edge.card) :
    Fintype.card {colour : V → Bool // MonochromaticAway edge v colour} =
      2 ^ (Fintype.card V - edge.card + 2) := by
  have hne : (edge.erase v).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hcard : (edge.erase v).card = 0 := by simp [he]
    rw [Finset.card_erase_of_mem hv] at hcard
    omega
  rw [card_monochromaticColorings (edge.erase v) hne]
  rw [Finset.card_erase_of_mem hv]
  have hle : edge.card ≤ Fintype.card V := edge.card_le_univ
  congr 1
  omega

/-- Union-bound count for all possible deleted vertices. -/
lemma card_almostMonochromatic_colorings_le {V : Type*} [Fintype V]
    [DecidableEq V] (edge : Finset V) (hedge : 2 ≤ edge.card) :
    Fintype.card {colour : V → Bool // AlmostMonochromatic edge colour} ≤
      edge.card * 2 ^ (Fintype.card V - edge.card + 2) := by
  classical
  rw [Fintype.card_subtype (fun colour : V → Bool ↦
    AlmostMonochromatic edge colour)]
  calc
    (Finset.univ.filter fun colour : V → Bool ↦ AlmostMonochromatic edge colour).card ≤
        ∑ v ∈ edge, (Finset.univ.filter fun colour : V → Bool ↦
          MonochromaticAway edge v colour).card := by
      simpa [AlmostMonochromatic] using
        card_filter_biExists_le_sum (Finset.univ : Finset (V → Bool)) edge
          (fun v colour ↦ MonochromaticAway edge v colour)
    _ = edge.card * 2 ^ (Fintype.card V - edge.card + 2) := by
      calc
        ∑ v ∈ edge, (Finset.univ.filter fun colour : V → Bool ↦
            MonochromaticAway edge v colour).card =
            ∑ _v ∈ edge, 2 ^ (Fintype.card V - edge.card + 2) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [← Fintype.card_subtype (fun colour : V → Bool ↦
            MonochromaticAway edge v colour)]
          exact card_monochromaticAway_colorings edge hv hedge
        _ = edge.card * 2 ^ (Fintype.card V - edge.card + 2) := by simp

/-! ## The conditional product count for a fixed edge -/

/-- Labels on the fixed edge: an initial colour and a discrete priority. -/
abbrev EdgeLabels {V : Type*} (edge : Finset V) (N : ℕ) :=
  (v : ↥edge) → Bool × Fin N

/-- At vertex `v`, either use the target colour with arbitrary priority or
the opposite colour with a priority in `high v`. -/
def targetOrExceptionalLabels {V : Type*} {N : ℕ} (target : Bool)
    (high : V → Finset (Fin N)) (v : V) : Finset (Bool × Fin N) :=
  ({target} ×ˢ (Finset.univ : Finset (Fin N))) ∪
    ({!target} ×ˢ high v)

/-- Assignments satisfying the target-or-exceptional condition at every
vertex of the fixed edge. -/
def targetOrExceptionalAssignments {V : Type*} [DecidableEq V]
    (edge : Finset V) (N : ℕ) (target : Bool)
    (high : V → Finset (Fin N)) : Finset (EdgeLabels edge N) :=
  Fintype.piFinset fun v : ↥edge ↦ targetOrExceptionalLabels target high v

/-- Assignments initially of the target colour everywhere, with arbitrary
priorities. -/
def allTargetAssignments {V : Type*} [DecidableEq V]
    (edge : Finset V) (N : ℕ) (target : Bool) : Finset (EdgeLabels edge N) :=
  Fintype.piFinset fun _v : ↥edge ↦
    ({target} ×ˢ (Finset.univ : Finset (Fin N)))

/-- Conditional threat assignments: all vertices satisfy the local
target-or-exceptional condition, but the edge was not initially all in the
target colour. -/
def conditionalThreatAssignments {V : Type*} [DecidableEq V]
    (edge : Finset V) (N : ℕ) (target : Bool)
    (high : V → Finset (Fin N)) : Finset (EdgeLabels edge N) :=
  targetOrExceptionalAssignments edge N target high \
    allTargetAssignments edge N target

@[simp] lemma card_targetOrExceptionalLabels {V : Type*} {N : ℕ}
    (target : Bool) (high : V → Finset (Fin N)) (v : V) :
    (targetOrExceptionalLabels target high v).card = N + (high v).card := by
  rw [targetOrExceptionalLabels, Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_univ, and_true] at hq₁
    simp only [Finset.mem_product, Finset.mem_singleton] at hq₂
    have := hq₁.symm.trans hq₂.1
    cases target <;> simp at this

lemma allTargetAssignments_subset_targetOrExceptionalAssignments
    {V : Type*} [DecidableEq V] (edge : Finset V) (N : ℕ) (target : Bool)
    (high : V → Finset (Fin N)) :
    allTargetAssignments edge N target ⊆
      targetOrExceptionalAssignments edge N target high := by
  intro assignment ha
  rw [allTargetAssignments, Fintype.mem_piFinset] at ha
  rw [targetOrExceptionalAssignments, Fintype.mem_piFinset]
  intro v
  exact Finset.mem_union_left _ (ha v)

@[simp] lemma card_allTargetAssignments {V : Type*} [DecidableEq V]
    (edge : Finset V) (N : ℕ) (target : Bool) :
    (allTargetAssignments edge N target).card = N ^ edge.card := by
  rw [allTargetAssignments, Fintype.card_piFinset]
  simp

/-- Exact, division-free form of the conditional fixed-edge count. -/
theorem card_conditionalThreatAssignments {V : Type*} [DecidableEq V]
    (edge : Finset V) (N : ℕ) (target : Bool)
    (high : V → Finset (Fin N)) :
    (conditionalThreatAssignments edge N target high).card =
      (∏ v : ↥edge, (N + (high v).card)) - N ^ edge.card := by
  rw [conditionalThreatAssignments,
    Finset.card_sdiff_of_subset (allTargetAssignments_subset_targetOrExceptionalAssignments
      edge N target high)]
  rw [targetOrExceptionalAssignments, Fintype.card_piFinset,
    card_allTargetAssignments]
  simp only [card_targetOrExceptionalLabels]

/-- Membership form of the conditional threat event. -/
lemma mem_conditionalThreatAssignments_iff {V : Type*} [DecidableEq V]
    {edge : Finset V} {N : ℕ} {target : Bool}
    {high : V → Finset (Fin N)} {assignment : EdgeLabels edge N} :
    assignment ∈ conditionalThreatAssignments edge N target high ↔
      (∀ v : ↥edge, assignment v ∈ targetOrExceptionalLabels target high v) ∧
      ¬(∀ v, (assignment v).1 = target) := by
  simp only [conditionalThreatAssignments, Finset.mem_sdiff,
    targetOrExceptionalAssignments, allTargetAssignments,
    Fintype.mem_piFinset, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_univ, and_true]

/-- Exact normalized conditional fixed-edge probability. -/
theorem expect_indicator_conditionalThreat {V : Type*} [DecidableEq V]
    (edge : Finset V) {N : ℕ} (hN : 0 < N) (target : Bool)
    (high : V → Finset (Fin N)) :
    (𝔼 assignment : EdgeLabels edge N,
      indicator (assignment ∈ conditionalThreatAssignments edge N target high)) =
      ((1 : ℚ) / 2) ^ edge.card *
        ((∏ v : ↥edge, (1 + ((high v).card : ℚ) / N)) - 1) := by
  classical
  rw [Fintype.expect_eq_sum_div_card]
  rw [show (∑ assignment : EdgeLabels edge N,
      indicator (assignment ∈ conditionalThreatAssignments edge N target high)) =
        ((conditionalThreatAssignments edge N target high).card : ℚ) by
      rw [sum_indicator_eq_card_subtype]
      exact_mod_cast (Fintype.card_subtype
        (fun assignment : EdgeLabels edge N ↦
          assignment ∈ conditionalThreatAssignments edge N target high)).trans (by simp)]
  rw [card_conditionalThreatAssignments]
  simp only [Fintype.card_pi, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hprod :
      (∏ v : ↥edge, ((N : ℚ) + ((high v).card : ℚ))) =
        (N : ℚ) ^ edge.card *
          ∏ v : ↥edge, (1 + ((high v).card : ℚ) / N) := by
    calc
      (∏ v : ↥edge, ((N : ℚ) + ((high v).card : ℚ))) =
          ∏ v : ↥edge, (N : ℚ) *
            (1 + ((high v).card : ℚ) / N) := by
              apply Finset.prod_congr rfl
              intro v hv
              field_simp
      _ = (∏ _v : ↥edge, (N : ℚ)) *
          ∏ v : ↥edge, (1 + ((high v).card : ℚ) / N) := by
            rw [Finset.prod_mul_distrib]
      _ = (N : ℚ) ^ edge.card *
          ∏ v : ↥edge, (1 + ((high v).card : ℚ) / N) := by simp
  rw [Nat.cast_sub]
  · push_cast
    rw [hprod]
    simp only [div_pow, one_pow]
    field_simp
    ring
  · calc
      N ^ edge.card = ∏ _v : ↥edge, N := by simp
      _ ≤ ∏ v : ↥edge, (N + (high v).card) := by
        exact Finset.prod_le_prod' fun v _ ↦ Nat.le_add_right _ _

/-- Any event whose exposed fiber satisfies the coordinatewise threat
conditions has at most the exact conditional-threat cardinality. -/
theorem card_event_le_conditionalThreat {V : Type*} [DecidableEq V]
    (edge : Finset V) (N : ℕ) (target : Bool)
    (high : V → Finset (Fin N)) (event : EdgeLabels edge N → Prop)
    [DecidablePred event]
    (hevent : ∀ assignment, event assignment →
      assignment ∈ conditionalThreatAssignments edge N target high) :
    (Finset.univ.filter event).card ≤
      (∏ v : ↥edge, (N + (high v).card)) - N ^ edge.card := by
  classical
  rw [← card_conditionalThreatAssignments edge N target high]
  apply Finset.card_le_card
  intro assignment ha
  exact hevent assignment (Finset.mem_filter.mp ha).2

/-- Probability bound for an arbitrary exposed fixed-edge fiber.  This is
the direct interface used by the recolouring argument: the only input is the
deterministic implication from the actual final-edge event to the local
target-or-exceptional event. -/
theorem expect_indicator_event_le_conditionalThreat
    {V : Type*} [DecidableEq V]
    (edge : Finset V) {N : ℕ} (hN : 0 < N) (target : Bool)
    (high : V → Finset (Fin N)) (event : EdgeLabels edge N → Prop)
    (hevent : ∀ assignment, event assignment →
      assignment ∈ conditionalThreatAssignments edge N target high) :
    (𝔼 assignment : EdgeLabels edge N, indicator (event assignment)) ≤
      ((1 : ℚ) / 2) ^ edge.card *
        ((∏ v : ↥edge, (1 + ((high v).card : ℚ) / N)) - 1) := by
  classical
  rw [← expect_indicator_conditionalThreat edge hN target high]
  apply Finset.expect_le_expect
  intro assignment _
  by_cases h : event assignment
  · rw [indicator_of_true h,
      indicator_of_true (hevent assignment h)]
  · rw [indicator_of_false h]
    exact indicator_nonneg _

/-- Substitute an abstract severity density into the conditional product.
For the discrete DGK priority space, the priority-counting lemmas prove
`|high v| / N = d / severity v`. -/
theorem expect_indicator_event_le_severityProduct
    {V : Type*} [DecidableEq V]
    (edge : Finset V) {N : ℕ} (hN : 0 < N) (target : Bool)
    (high : V → Finset (Fin N)) (severity : V → ℕ) (d : ℚ)
    (event : EdgeLabels edge N → Prop)
    (hevent : ∀ assignment, event assignment →
      assignment ∈ conditionalThreatAssignments edge N target high)
    (hdensity : ∀ v : ↥edge,
      ((high v).card : ℚ) / N = d / severity v) :
    (𝔼 assignment : EdgeLabels edge N, indicator (event assignment)) ≤
      ((1 : ℚ) / 2) ^ edge.card *
        ((∏ v : ↥edge, (1 + d / severity v)) - 1) := by
  calc
    (𝔼 assignment : EdgeLabels edge N, indicator (event assignment)) ≤
        ((1 : ℚ) / 2) ^ edge.card *
          ((∏ v : ↥edge, (1 + ((high v).card : ℚ) / N)) - 1) :=
      expect_indicator_event_le_conditionalThreat edge hN target high event hevent
    _ = ((1 : ℚ) / 2) ^ edge.card *
        ((∏ v : ↥edge, (1 + d / severity v)) - 1) := by
      congr 2
      apply Finset.prod_congr rfl
      intro v hv
      rw [hdensity v]

end Erdos1027.DGKCounts
