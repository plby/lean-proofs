/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import ErdosProblems.Erdos1027.Tree
import ErdosProblems.Erdos1027.DGKOutcome
import ErdosProblems.Erdos1027.DGKThreatLoad
import ErdosProblems.Erdos1027.DGKFiber
import ErdosProblems.Erdos1027.DGKBadEvents
import ErdosProblems.Erdos1027.DGKUnion

/-!
# The corrected fixed-budget Property-B theorem

This file assembles the finite random-greedy argument of
Duraj--Gutowski--Kozik.  Its exported theorem is the fixed-budget input used
by the decision-tree proof of Erdős problem 1027.
-/

namespace Erdos1027.DGKPropertyB

open scoped BigOperators
open Finset

universe u

/-- The size of the top priority window in the DGK argument. -/
def priorityWindow (Q : ℕ) : ℕ := 128 * Q

/-- The Markov cutoff for the almost-monochromatic mass. -/
def almostMonoCutoff (Q : ℕ) : ℕ := 16 * Q

/-- The deterministic cap on the sum of exceptional priority densities. -/
def exponentCutoff (Q : ℕ) : ℕ :=
  priorityWindow Q * almostMonoCutoff Q

/-- A deliberately generous threshold which makes the three error terms
strictly smaller than one. -/
def dgkThreshold (Q : ℕ) : ℕ :=
  max (priorityWindow Q)
    (32 * Q ^ 2 * priorityWindow Q * 3 ^ exponentCutoff Q) + 1

abbrev Hypergraph (V : Type*) := Tree.Hypergraph V

lemma priorityWindow_lt_threshold (Q : ℕ) :
    priorityWindow Q < dgkThreshold Q := by
  simp [priorityWindow, dgkThreshold]

lemma threshold_error_bound (Q : ℕ) :
    Q ^ 2 * priorityWindow Q * 3 ^ exponentCutoff Q * 16 <
      dgkThreshold Q := by
  have h :
      Q ^ 2 * priorityWindow Q * 3 ^ exponentCutoff Q * 16 ≤
        32 * Q ^ 2 * priorityWindow Q * 3 ^ exponentCutoff Q := by
    nlinarith [Nat.zero_le (Q ^ 2 * priorityWindow Q * 3 ^ exponentCutoff Q)]
  exact h.trans_lt (by simp [dgkThreshold])

section Assembly

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {N : ℕ}

abbrev Outcome (V : Type*) (N : ℕ) := DGKOutcome.Outcome V N

/-- Project an exposed colour--priority assignment to its colour part. -/
def outsideColour {e : Finset V}
    (outside : FiniteExposure.OutsideAssignment (A := Bool × Fin N) e) :
    DGKThreatLoad.OutsideColouring e := fun v ↦ (outside v).1

/-- Project an inside assignment to its colour part. -/
def insideColour {e : Finset V}
    (inside : FiniteExposure.InsideAssignment (A := Bool × Fin N) e) :
    FiniteExposure.InsideAssignment (A := Bool) e := fun v ↦ (inside v).1

lemma initial_glue {e : Finset V}
    (outside : FiniteExposure.OutsideAssignment (A := Bool × Fin N) e)
    (inside : FiniteExposure.InsideAssignment (A := Bool × Fin N) e) :
    DGKOutcome.initial (FiniteExposure.glue e outside inside) =
      FiniteExposure.glue e (outsideColour outside) (insideColour inside) := by
  funext v
  by_cases hv : v ∈ e <;>
    simp [DGKOutcome.initial, DGKPriorities.colour, outsideColour, insideColour, hv]

/-- The possible threat edges visible from the exposed outside colours. -/
noncomputable def threatEdges (H : Hypergraph V) (e : Finset V) (target : Bool)
    (outside : DGKThreatLoad.OutsideColouring e) (v : V) : Hypergraph V :=
  by
    classical
    exact H.filter fun F ↦
      DGKThreatLoad.OutsideThreat H e target outside v F

/-- All exceptional priority values supplied by visible threat edges.  A
union is used rather than choosing one threat; the union bound on its
cardinality is exactly the focused threat load. -/
noncomputable def highUnion (H : Hypergraph V) (e : Finset V) (target : Bool)
    (outside : DGKThreatLoad.OutsideColouring e) (N d : ℕ) (v : V) :
    Finset (Fin N) :=
  (threatEdges H e target outside v).biUnion fun F ↦
    DGKPriorities.highValues N d F.card

/-- Sum of the priority-window densities at one focused vertex. -/
noncomputable def unionPenalty (H : Hypergraph V) (e : Finset V)
    (target : Bool) (outside : DGKThreatLoad.OutsideColouring e)
    (d : ℕ) (v : V) : ℝ := by
  classical
  exact ∑ F ∈ H,
    if DGKThreatLoad.OutsideThreat H e target outside v F then
      (d : ℝ) / F.card else 0

lemma unionPenalty_nonneg (H : Hypergraph V) (e : Finset V)
    (target : Bool) (outside : DGKThreatLoad.OutsideColouring e)
    (d : ℕ) (v : V) :
    0 ≤ unionPenalty H e target outside d v := by
  classical
  unfold unionPenalty
  exact Finset.sum_nonneg fun F _ ↦ by split_ifs <;> positivity

lemma card_highValues_div
    {N d j : ℕ} (hN : 0 < N) (hdj : d ≤ j) (hdiv : j ∣ N) :
    ((DGKPriorities.highValues N d j).card : ℝ) / N = (d : ℝ) / j := by
  rw [DGKPriorities.card_highValues N d j hdj, DGKPriorities.highCount]
  have hj : 0 < j := Nat.pos_of_dvd_of_pos hdiv hN
  obtain ⟨q, rfl⟩ := hdiv
  simp [hj.ne']
  have hqNat : 0 < q := Nat.pos_of_mul_pos_left hN
  have hq : (q : ℝ) ≠ 0 := by
    exact_mod_cast hqNat.ne'
  field_simp [hq]

/-- The density of the union of exceptional windows is at most the sum of
their densities. -/
lemma highUnion_density_le
    (H : Hypergraph V) (e : Finset V) (target : Bool)
    (outside : DGKThreatLoad.OutsideColouring e)
    {N d : ℕ} (hN : 0 < N)
    (hdiv : ∀ F ∈ H, F.card ∣ N)
    (hmin : ∀ F ∈ H, d ≤ F.card) (v : V) :
    ((highUnion H e target outside N d v).card : ℝ) / N ≤
      unionPenalty H e target outside d v := by
  classical
  have hcard :
      (highUnion H e target outside N d v).card ≤
        ∑ F ∈ threatEdges H e target outside v,
          (DGKPriorities.highValues N d F.card).card := by
    exact Finset.card_biUnion_le
  calc
    ((highUnion H e target outside N d v).card : ℝ) / N ≤
        ((∑ F ∈ threatEdges H e target outside v,
          (DGKPriorities.highValues N d F.card).card : ℕ) : ℝ) / N := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = ∑ F ∈ threatEdges H e target outside v,
          ((DGKPriorities.highValues N d F.card).card : ℝ) / N := by
      push_cast
      rw [Finset.sum_div]
    _ = ∑ F ∈ threatEdges H e target outside v,
          (d : ℝ) / F.card := by
      apply Finset.sum_congr rfl
      intro F hF
      have hFH := (Finset.mem_filter.mp hF).1
      exact card_highValues_div hN (hmin F hFH) (hdiv F hFH)
    _ = unionPenalty H e target outside d v := by
      unfold unionPenalty threatEdges
      rw [Finset.sum_filter]

lemma sum_unionPenalty_eq_outsideThreatLoad
    (H : Hypergraph V) (e : Finset V) (target : Bool)
    (outside : DGKThreatLoad.OutsideColouring e) (d : ℕ) :
    (∑ v ∈ e, unionPenalty H e target outside d v) =
      DGKThreatLoad.outsideThreatLoad H e target outside d := by
  rfl

/-- The complement of the light-edge event is the deterministic `NoLight`
condition required by the greedy certificate. -/
lemma noLight_of_not_hasLightEdge
    {H : Hypergraph V} {w : Outcome V N} {d : ℕ}
    (h : ¬ DGKUnion.HasLightEdge H d w) : DGKOutcome.NoLight H w d := by
  classical
  intro F hFH hmono
  by_contra hhigh
  push_neg at hhigh
  apply h
  refine ⟨F, hFH, hmono, ?_⟩
  intro v hv
  by_contra hlow
  exact hhigh v hv ((DGKPriorities.not_low_iff_high _).mp hlow)

/-- The target-specific pair mass is bounded by the ordinary
almost-monochromatic pair mass used in the Markov event. -/
lemma targetAlmostMass_le_outcomeAlmostPairMass
    (H : Hypergraph V) (w : Outcome V N) (target : Bool) :
    DGKThreatLoad.targetAlmostMass H (DGKOutcome.initial w) target ≤
      (DGKBadEvents.outcomeAlmostPairMassQ H w : ℝ) := by
  classical
  unfold DGKThreatLoad.targetAlmostMass
  unfold DGKBadEvents.outcomeAlmostPairMassQ DGKBadEvents.almostPairMassQ
  push_cast
  apply Finset.sum_le_sum
  intro F hFH
  apply Finset.sum_le_sum
  intro v hvF
  by_cases ht : DGKThreatLoad.TargetAlmostAt
      (DGKOutcome.initial w) target F v
  · have ha : DGKBadEvents.AlmostMonoAt
        (DGKOutcome.initial w) F v := by
      refine ⟨!target, ?_⟩
      intro u hu
      have hue := Finset.mem_erase.mp hu
      exact ht.2 u hue.2 hue.1
    change DGKBadEvents.AlmostMonoAt
      (DGKBadEvents.initialColour w) F v at ha
    simp [ht, ha, FiniteExpect.indicator, one_div]
  · simp only [ht, if_false]
    have hind : (0 : ℚ) ≤ FiniteExpect.indicator
        (DGKBadEvents.AlmostMonoAt (DGKBadEvents.initialColour w) F v) :=
      FiniteExpect.indicator_nonneg _
    exact div_nonneg (by exact_mod_cast hind) (Nat.cast_nonneg _)

/-- The event estimated in the fixed-edge calculation: a prescribed edge
finishes in `target`, while neither of the two global preliminary bad events
occurs. -/
def ControlledFinal (H : Hypergraph V) (hne : ∀ F ∈ H, F.Nonempty)
    (Q d : ℕ) (target : Bool) (edge : Finset V) (w : Outcome V N) : Prop :=
  DGKUnion.FinalMonoInColour (fun w ↦ DGKOutcome.finalColour H w hne)
      target edge w ∧
    ¬ DGKUnion.HasLightEdge H d w ∧
    DGKBadEvents.outcomeAlmostPairMassQ H w < (16 * Q : ℕ)

lemma controlledFinal_not_all_target
    {H : Hypergraph V} {hne : ∀ F ∈ H, F.Nonempty}
    {Q d : ℕ} {target : Bool} {edge : Finset V} (heH : edge ∈ H)
    {w : Outcome V N} (h : ControlledFinal H hne Q d target edge w) :
    ¬ (∀ v ∈ edge, DGKOutcome.initial w v = target) := by
  intro hinitial
  exact DGKOutcome.initiallyMonochromatic_not_finish_initialColour
    hne heH hinitial h.1

/-- The deterministic greedy certificate puts every controlled fixed-edge
outcome in the target-or-exceptional cylinder counted by `DGKCounts`. -/
lemma controlledFinal_fiber_subset
    {H : Hypergraph V} {hne : ∀ F ∈ H, F.Nonempty}
    {Q d : ℕ} {target : Bool} {edge : Finset V} (heH : edge ∈ H)
    (outside : FiniteExposure.OutsideAssignment (A := Bool × Fin N) edge)
    (inside : FiniteExposure.InsideAssignment (A := Bool × Fin N) edge)
    (h : ControlledFinal H hne Q d target edge
      (FiniteExposure.glue edge outside inside)) :
    inside ∈ DGKCounts.conditionalThreatAssignments edge N target
      (highUnion H edge target (outsideColour outside) N d) := by
  classical
  let w : Outcome V N := FiniteExposure.glue edge outside inside
  have hNoLight : DGKOutcome.NoLight H w d :=
    noLight_of_not_hasLightEdge h.2.1
  rw [DGKCounts.mem_conditionalThreatAssignments_iff]
  constructor
  · intro v
    by_cases hvtarget : DGKOutcome.initial w v = target
    · have hfirst : (inside v).1 = target := by
        simpa [w, DGKOutcome.initial, DGKPriorities.colour,
          FiniteExposure.glue_apply_of_mem, v.2] using hvtarget
      apply Finset.mem_union_left
      exact Finset.mem_product.mpr ⟨by simpa using hfirst, Finset.mem_univ _⟩
    · obtain ⟨hvS, F, hFH, hFmono, hFopp, hmax, hFflip,
          hFedge, hvHigh⟩ :=
        DGKOutcome.opposite_vertex_has_high_threat hne hNoLight h.1 v.2 hvtarget
      have hout : DGKThreatLoad.OutsideThreat H edge target
          (outsideColour outside) v F := by
        refine ⟨hFH, hFedge, ?_⟩
        intro u huF huv
        have huEdge : u ∉ edge := by
          intro hue
          have hu : u ∈ F ∩ edge := Finset.mem_inter.mpr ⟨huF, hue⟩
          rw [hFedge] at hu
          exact huv (Finset.mem_singleton.mp hu)
        have hcolour := hFopp u huF
        rw [DGKThreatLoad.exposedColour,
          FiniteExposure.glue_apply_of_not_mem
            (outsideColour outside) (fun _ ↦ target) huEdge]
        simpa [w, DGKOutcome.initial, DGKPriorities.colour, outsideColour,
          FiniteExposure.glue_apply_of_not_mem outside inside huEdge] using hcolour
      have hFmem : F ∈ threatEdges H edge target (outsideColour outside) v :=
        Finset.mem_filter.mpr ⟨hFH, hout⟩
      have hpHigh : (inside v).2 ∈ DGKPriorities.highValues N d F.card := by
        have : DGKPriorities.priority w v = (inside v).2 := by
          simp [w, DGKPriorities.priority, FiniteExposure.glue_apply_of_mem,
            v.2]
        simpa [DGKPriorities.highValues, this] using hvHigh
      have hpUnion : (inside v).2 ∈
          highUnion H edge target (outsideColour outside) N d v := by
        exact Finset.mem_biUnion.mpr ⟨F, hFmem, hpHigh⟩
      have hfirst : (inside v).1 = !target := by
        have hopp : DGKOutcome.initial w v = !target :=
          Bool.eq_not_of_ne hvtarget
        simpa [w, DGKOutcome.initial, DGKPriorities.colour,
          FiniteExposure.glue_apply_of_mem, v.2] using hopp
      apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨by simpa using hfirst, hpUnion⟩
  · intro hall
    apply controlledFinal_not_all_target heH h
    intro v hv
    have hvall := hall ⟨v, hv⟩
    simpa [w, DGKOutcome.initial, DGKPriorities.colour,
      FiniteExposure.glue_apply_of_mem, hv] using hvall

/-- Marginalizing independent priorities does not change the expectation of
a real statistic which only sees the colour coordinates. -/
lemma expect_colourStatisticR
    {U : Type*} [Fintype U] [DecidableEq U] {N : ℕ} (hN : 0 < N)
    (f : (U → Bool) → ℝ) :
    (𝔼 w : DGKPriorities.Outcome U N,
      f (fun u ↦ DGKPriorities.colour w u)) =
      𝔼 colour : U → Bool, f colour := by
  classical
  have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  let e := Equiv.arrowProdEquivProdArrow U
    (fun _ : U ↦ Bool) (fun _ : U ↦ Fin N)
  calc
    (𝔼 w : DGKPriorities.Outcome U N,
        f (fun u ↦ DGKPriorities.colour w u)) =
        𝔼 p : (U → Bool) × (U → Fin N), f p.1 := by
      apply Fintype.expect_equiv e
      intro w
      rfl
    _ = 𝔼 colour : U → Bool,
          𝔼 _priority : U → Fin N, f colour := by
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product
          (Finset.univ : Finset (U → Bool))
          (Finset.univ : Finset (U → Fin N))
          (fun p : (U → Bool) × (U → Fin N) ↦ f p.1))
    _ = 𝔼 colour : U → Bool, f colour := by simp

/-- Expected sum of the exceptional-window union-bound penalties. -/
lemma expect_unionPenalty_le
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    {N d r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hmin : ∀ F ∈ H, r ≤ F.card) :
    (𝔼 outside : FiniteExposure.OutsideAssignment
        (A := Bool × Fin N) edge,
      ∑ v ∈ edge,
        unionPenalty H edge target (outsideColour outside) d v) ≤
      DGKWeight.qWeightR H * (d : ℝ) / r := by
  let f : DGKThreatLoad.OutsideColouring edge → ℝ :=
    fun outside ↦ ∑ v ∈ edge, unionPenalty H edge target outside d v
  calc
    (𝔼 outside : FiniteExposure.OutsideAssignment
        (A := Bool × Fin N) edge,
      ∑ v ∈ edge,
        unionPenalty H edge target (outsideColour outside) d v) =
        𝔼 outside : DGKThreatLoad.OutsideColouring edge, f outside := by
      change (𝔼 outside :
          (u : ↑((Finset.univ : Finset V) \ edge)) → Bool × Fin N,
          f (fun u ↦ (outside u).1)) =
        𝔼 outside : (u : ↑((Finset.univ : Finset V) \ edge)) → Bool,
          f outside
      exact expect_colourStatisticR (U :=
        ↑((Finset.univ : Finset V) \ edge)) hN f
    _ = 𝔼 outside : DGKThreatLoad.OutsideColouring edge,
          DGKThreatLoad.outsideThreatLoad H edge target outside d := by
      apply Finset.expect_congr rfl
      intro outside _
      exact sum_unionPenalty_eq_outsideThreatLoad H edge target outside d
    _ ≤ DGKWeight.qWeightR H * (d : ℝ) / r := by
      rw [DGKThreatLoad.expect_outsideThreatLoad_eq_expect_globalThreatLoad]
      exact DGKThreatLoad.expect_globalThreatLoad_le H edge target d r hr hmin

/-- Conditional estimate for a fixed exposed outside assignment. -/
lemma controlledFinal_fiber_bound
    {H : Hypergraph V} {hne : ∀ F ∈ H, F.Nonempty}
    {Q : ℕ} {edge : Finset V} (heH : edge ∈ H) (target : Bool)
    {N r : ℕ} (hN : 0 < N)
    (hdiv : ∀ F ∈ H, F.card ∣ N)
    (hmin : ∀ F ∈ H, r ≤ F.card)
    (hdr : priorityWindow Q ≤ r)
    (outside : FiniteExposure.OutsideAssignment
      (A := Bool × Fin N) edge) :
    ((((𝔼 inside : FiniteExposure.InsideAssignment
        (A := Bool × Fin N) edge,
      FiniteExpect.indicator
        (ControlledFinal H hne Q (priorityWindow Q) target edge
          (FiniteExposure.glue edge outside inside))) : ℚ)) : ℝ) ≤
      DGKFixedEdge.invTwoPow edge.card * Real.exp (exponentCutoff Q) *
        ∑ v ∈ edge,
          unionPenalty H edge target (outsideColour outside)
            (priorityWindow Q) v := by
  classical
  let event : Outcome V N → Prop :=
    ControlledFinal H hne Q (priorityWindow Q) target edge
  by_cases hex : ∃ inside : FiniteExposure.InsideAssignment
      (A := Bool × Fin N) edge,
      event (FiniteExposure.glue edge outside inside)
  · obtain ⟨inside₀, hins₀⟩ := hex
    let w₀ : Outcome V N := FiniteExposure.glue edge outside inside₀
    have htargetMass :
        DGKThreatLoad.targetAlmostMass H (DGKOutcome.initial w₀) target ≤
          (DGKBadEvents.outcomeAlmostPairMassQ H w₀ : ℝ) :=
      targetAlmostMass_le_outcomeAlmostPairMass H w₀ target
    have hmass :
        (DGKBadEvents.outcomeAlmostPairMassQ H w₀ : ℝ) ≤
          (16 * Q : ℕ) := by
      exact_mod_cast (le_of_lt hins₀.2.2)
    have hload :
        (∑ v ∈ edge,
          unionPenalty H edge target (outsideColour outside)
            (priorityWindow Q) v) ≤
          (priorityWindow Q : ℝ) *
            DGKThreatLoad.targetAlmostMass H (DGKOutcome.initial w₀) target := by
      calc
        (∑ v ∈ edge,
            unionPenalty H edge target (outsideColour outside)
              (priorityWindow Q) v) =
            DGKThreatLoad.outsideThreatLoad H edge target
              (outsideColour outside) (priorityWindow Q) :=
          sum_unionPenalty_eq_outsideThreatLoad H edge target
            (outsideColour outside) (priorityWindow Q)
        _ = DGKThreatLoad.globalThreatLoad H (DGKOutcome.initial w₀)
              edge target (priorityWindow Q) := by
          rw [initial_glue outside inside₀]
          exact (DGKThreatLoad.globalThreatLoad_glue_eq_outsideThreatLoad
            H edge target (outsideColour outside) (insideColour inside₀)
              (priorityWindow Q)).symm
        _ ≤ (priorityWindow Q : ℝ) *
              DGKThreatLoad.targetAlmostMass H (DGKOutcome.initial w₀) target :=
          DGKThreatLoad.globalThreatLoad_le_mul_targetAlmostMass
            H (DGKOutcome.initial w₀) edge target (priorityWindow Q)
    have hcap :
        (∑ v ∈ edge,
          unionPenalty H edge target (outsideColour outside)
            (priorityWindow Q) v) ≤ exponentCutoff Q := by
      calc
        _ ≤ (priorityWindow Q : ℝ) *
              DGKThreatLoad.targetAlmostMass H (DGKOutcome.initial w₀) target := hload
        _ ≤ (priorityWindow Q : ℝ) * (16 * Q : ℕ) :=
          mul_le_mul_of_nonneg_left (htargetMass.trans hmass) (by positivity)
        _ = exponentCutoff Q := by
          norm_num [exponentCutoff, almostMonoCutoff]
    exact DGKFiber.exposed_fiber_indicator_le_exp_penalty
      edge hN target outside
      (highUnion H edge target (outsideColour outside) N (priorityWindow Q))
      (unionPenalty H edge target (outsideColour outside) (priorityWindow Q))
      (exponentCutoff Q) event
      (fun inside h ↦ controlledFinal_fiber_subset heH outside inside h)
      (fun v ↦ highUnion_density_le H edge target (outsideColour outside)
        hN hdiv (fun F hF ↦ hdr.trans (hmin F hF)) v)
      (fun v ↦ unionPenalty_nonneg H edge target (outsideColour outside)
        (priorityWindow Q) v) hcap
  · have hz :
        (𝔼 inside : FiniteExposure.InsideAssignment
          (A := Bool × Fin N) edge,
          FiniteExpect.indicator
            (event (FiniteExposure.glue edge outside inside))) = 0 := by
      apply Finset.expect_eq_zero
      intro inside _
      have hn : ¬ event (FiniteExposure.glue edge outside inside) := by
        intro hi
        exact hex ⟨inside, hi⟩
      simp [FiniteExpect.indicator, hn]
    rw [hz]
    rw [Rat.cast_zero]
    exact mul_nonneg
      (mul_nonneg (DGKFixedEdge.invTwoPow_nonneg _)
        (Real.exp_pos _).le)
      (Finset.sum_nonneg fun v _ ↦
        unionPenalty_nonneg H edge target (outsideColour outside)
          (priorityWindow Q) v)

lemma expect_realIndicator_eq_cast_indicator
    {O : Type*} [Fintype O] (P : O → Prop) :
    (𝔼 x : O, DGKUnion.realIndicator (P x)) =
      (((𝔼 x : O, FiniteExpect.indicator (P x)) : ℚ) : ℝ) :=
  DGKUnion.expect_realIndicator_eq_ratCast_expect_indicator P

/-- The exposed-fiber estimate averaged over the outside coordinates. -/
lemma controlledFinal_expect_le
    {H : Hypergraph V} {hne : ∀ F ∈ H, F.Nonempty}
    {Q : ℕ} {edge : Finset V} (heH : edge ∈ H) (target : Bool)
    {N r : ℕ} (hN : 0 < N)
    (hdiv : ∀ F ∈ H, F.card ∣ N)
    (hr : 0 < r) (hmin : ∀ F ∈ H, r ≤ F.card)
    (hdr : priorityWindow Q ≤ r) :
    (𝔼 w : Outcome V N,
      DGKUnion.realIndicator
        (ControlledFinal H hne Q (priorityWindow Q) target edge w)) ≤
      DGKFixedEdge.invTwoPow edge.card * Real.exp (exponentCutoff Q) *
        (DGKWeight.qWeightR H * (priorityWindow Q : ℝ) / r) := by
  classical
  let event : Outcome V N → Prop :=
    ControlledFinal H hne Q (priorityWindow Q) target edge
  rw [expect_realIndicator_eq_cast_indicator]
  exact DGKFiber.global_indicator_le_of_exposed_fiber_penalty
    edge event
    (fun outside ↦ ∑ v ∈ edge,
      unionPenalty H edge target (outsideColour outside)
        (priorityWindow Q) v)
    (exponentCutoff Q)
    (DGKWeight.qWeightR H * (priorityWindow Q : ℝ) / r)
    (fun outside ↦
      controlledFinal_fiber_bound heH target hN hdiv hmin hdr outside)
    (expect_unionPenalty_le H edge target hN hr hmin)

/-- Some edge has a controlled final monochromatic colour. -/
def HasControlledFinal (H : Hypergraph V)
    (hne : ∀ F ∈ H, F.Nonempty) (Q d : ℕ) (w : Outcome V N) : Prop :=
  ∃ target : Bool, ∃ edge ∈ H, ControlledFinal H hne Q d target edge w

private lemma invTwoPow_eq_zpow_neg (k : ℕ) :
    DGKFixedEdge.invTwoPow k = (2 : ℝ) ^ (-(k : ℤ)) := by
  rw [DGKFixedEdge.invTwoPow, zpow_neg, zpow_natCast, inv_pow]

/-- Union of the controlled fixed-edge estimates over both colours and all
edges. -/
lemma hasControlledFinal_expect_le
    {H : Hypergraph V} {hne : ∀ F ∈ H, F.Nonempty}
    {Q N r : ℕ} (hN : 0 < N)
    (hdiv : ∀ F ∈ H, F.card ∣ N)
    (hr : 0 < r) (hmin : ∀ F ∈ H, r ≤ F.card)
    (hdr : priorityWindow Q ≤ r) :
    (𝔼 w : Outcome V N,
      DGKUnion.realIndicator
        (HasControlledFinal H hne Q (priorityWindow Q) w)) ≤
      DGKWeight.qWeightR H * Real.exp (exponentCutoff Q) *
        (DGKWeight.qWeightR H * (priorityWindow Q : ℝ) / r) := by
  classical
  calc
    (𝔼 w : Outcome V N,
        DGKUnion.realIndicator
          (HasControlledFinal H hne Q (priorityWindow Q) w)) ≤
        ∑ target : Bool, ∑ edge ∈ H,
          𝔼 w : Outcome V N,
            DGKUnion.realIndicator
              (ControlledFinal H hne Q (priorityWindow Q) target edge w) := by
      simpa [HasControlledFinal] using
        (DGKUnion.expect_realIndicator_biExists_le_sum
          (Finset.univ : Finset Bool)
          (fun target w ↦ ∃ edge ∈ H,
            ControlledFinal H hne Q (priorityWindow Q) target edge w)).trans
          (Finset.sum_le_sum fun target _ ↦
            DGKUnion.expect_realIndicator_biExists_le_sum H
              (fun edge w ↦
                ControlledFinal H hne Q (priorityWindow Q) target edge w))
    _ ≤ ∑ target : Bool, ∑ edge ∈ H,
          DGKFixedEdge.invTwoPow edge.card * Real.exp (exponentCutoff Q) *
            (DGKWeight.qWeightR H * (priorityWindow Q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro target _
      apply Finset.sum_le_sum
      intro edge he
      exact controlledFinal_expect_le he target hN hdiv hr hmin hdr
    _ = DGKWeight.qWeightR H * Real.exp (exponentCutoff Q) *
          (DGKWeight.qWeightR H * (priorityWindow Q : ℝ) / r) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        nsmul_eq_mul, Nat.cast_ofNat]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [DGKWeight.qWeightR, DGKWeight.booleanWeightR]
      simp_rw [invTwoPow_eq_zpow_neg]
      ring

/-- Pointwise decomposition of a final monochromatic edge into the two
preliminary bad events or the controlled fixed-edge event. -/
lemma finalBad_indicator_le_three
    {H : Hypergraph V} {hne : ∀ F ∈ H, F.Nonempty}
    (Q : ℕ) (w : Outcome V N) :
    DGKUnion.realIndicator
        (DGKUnion.HasFinalMonochromaticEdge H
          (fun w ↦ DGKOutcome.finalColour H w hne) w) ≤
      DGKUnion.realIndicator
        (DGKUnion.HasLightEdge H (priorityWindow Q) w) +
      DGKUnion.realIndicator
        ((((16 * Q : ℕ) : ℚ) ≤
          DGKBadEvents.outcomeAlmostPairMassQ H w)) +
      DGKUnion.realIndicator
        (HasControlledFinal H hne Q (priorityWindow Q) w) := by
  classical
  by_cases hbad : DGKUnion.HasFinalMonochromaticEdge H
      (fun w ↦ DGKOutcome.finalColour H w hne) w
  · have hbad' := hbad
    obtain ⟨target, edge, heH, hfinal⟩ := hbad
    by_cases hlight : DGKUnion.HasLightEdge H (priorityWindow Q) w
    · simp only [DGKUnion.realIndicator, if_pos hbad', if_pos hlight]
      split_ifs <;> norm_num
    · by_cases hmass : (((16 * Q : ℕ) : ℚ) ≤
          DGKBadEvents.outcomeAlmostPairMassQ H w)
      · simp only [DGKUnion.realIndicator, if_pos hbad', if_neg hlight,
          if_pos hmass]
        split_ifs <;> norm_num
      · have hcontrolled : HasControlledFinal H hne Q (priorityWindow Q) w :=
          ⟨target, edge, heH, hfinal, hlight, lt_of_not_ge hmass⟩
        simp only [DGKUnion.realIndicator, if_pos hbad', if_neg hlight,
          if_neg hmass, if_pos hcontrolled]
        norm_num
  · simp only [DGKUnion.realIndicator, if_neg hbad]
    split_ifs <;> norm_num

/-- Convert a proper Boolean colouring to the red-set formulation used by
the decision-tree development. -/
lemma treeProperColoring_of_boolean
    {H : Hypergraph V} {colour : V → Bool}
    (h : DGKUnion.ProperBooleanColouring H colour) :
    ∃ R : Finset V, Tree.ProperColoring H R := by
  classical
  let R : Finset V := Finset.univ.filter fun v ↦ colour v = true
  refine ⟨R, ?_⟩
  intro edge heH
  obtain ⟨x, hx, y, hy, hxy⟩ := h edge heH
  cases hcx : colour x <;> cases hcy : colour y
  · exact (hxy (hcx.trans hcy.symm)).elim
  · constructor
    · exact ⟨y, Finset.mem_inter.mpr ⟨hy, by simp [R, hcy]⟩⟩
    · exact ⟨x, Finset.mem_sdiff.mpr ⟨hx, by simp [R, hcx]⟩⟩
  · constructor
    · exact ⟨x, Finset.mem_inter.mpr ⟨hx, by simp [R, hcx]⟩⟩
    · exact ⟨y, Finset.mem_sdiff.mpr ⟨hy, by simp [R, hcy]⟩⟩
  · exact (hxy (hcx.trans hcy.symm)).elim

/-- The finite DGK experiment produces a proper colouring under the scaled
fixed-budget hypotheses. -/
theorem fixedBudget
    (C n : ℕ) (hC : 0 < C) :
    Tree.BeckFixedBudget (C := C) (n := n) (r := dgkThreshold (8 * C))
      (α := V) := by
  classical
  intro H hmin hweight
  let Q : ℕ := 8 * C
  let r : ℕ := dgkThreshold Q
  let d : ℕ := priorityWindow Q
  let M : ℕ := exponentCutoff Q
  let N : ℕ := DGKOutcome.commonDenominator H
  have hQ : 0 < Q := by simp [Q, hC]
  have hr : 0 < r := by simp [r, dgkThreshold]
  have hdrlt : d < r := by
    exact priorityWindow_lt_threshold Q
  have hdr : d ≤ r := by
    exact hdrlt.le
  have hne : ∀ F ∈ H, F.Nonempty := by
    intro F hF
    exact Finset.card_pos.mp (hr.trans_le (hmin F hF))
  have hN : 0 < N := DGKOutcome.commonDenominator_pos hne
  let : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hdiv : ∀ F ∈ H, F.card ∣ N := by
    intro F hF
    exact DGKOutcome.card_dvd_commonDenominator hF
  have hminD : ∀ F ∈ H, d ≤ F.card := by
    intro F hF
    exact hdr.trans (hmin F hF)
  have hminTwo : ∀ F ∈ H, 2 ≤ F.card := by
    intro F hF
    have : 2 ≤ r := by
      have hdpos : 0 < d := by simp [d, priorityWindow, hQ]
      omega
    exact this.trans (hmin F hF)
  have hqQ : DGKWeight.qWeightQ H ≤ Q := by
    have h := DGKWeight.qWeightQ_le_two_mul_of_scaledWeight_le hweight
    calc
      DGKWeight.qWeightQ H ≤ 2 * ((4 * C : ℕ) : ℚ) := h
      _ = Q := by norm_num [Q]; ring
  have hqR : DGKWeight.qWeightR H ≤ Q := by
    have h := DGKWeight.qWeightR_le_two_mul_of_scaledWeight_le hweight
    calc
      DGKWeight.qWeightR H ≤ 2 * ((4 * C : ℕ) : ℝ) := h
      _ = Q := by norm_num [Q]; ring
  have hlightQ :
      (𝔼 w : Outcome V N,
        FiniteExpect.indicator (DGKUnion.HasLightEdge H d w)) <
        (1 : ℚ) / 128 := by
    simpa [d, priorityWindow, DGKUnion.HasLightEdge, DGKUnion.LightEdge,
      DGKBadEvents.HasLightEdge, DGKBadEvents.LightEdge] using
      (DGKBadEvents.hasLightEdge_lt_one_over_128 H hN hQ hdiv hminD hqQ)
  have hlightR :
      (𝔼 w : Outcome V N,
        DGKUnion.realIndicator (DGKUnion.HasLightEdge H d w)) <
        (1 : ℝ) / 128 := by
    rw [expect_realIndicator_eq_cast_indicator]
    simpa using (Rat.cast_lt (K := ℝ)).2 hlightQ
  have hmassQ :
      (𝔼 w : Outcome V N,
        FiniteExpect.indicator
          ((((16 * Q : ℕ) : ℚ) ≤
            DGKBadEvents.outcomeAlmostPairMassQ H w))) ≤
        (1 : ℚ) / 8 :=
    DGKBadEvents.almostPairMass_bad_le_one_eighth
      H hN hQ hminTwo hqQ
  have hmassR :
      (𝔼 w : Outcome V N,
        DGKUnion.realIndicator
          ((((16 * Q : ℕ) : ℚ) ≤
            DGKBadEvents.outcomeAlmostPairMassQ H w))) ≤
        (1 : ℝ) / 8 := by
    rw [expect_realIndicator_eq_cast_indicator]
    simpa using (Rat.cast_le (K := ℝ)).2 hmassQ
  have hcontrolledBound :=
    hasControlledFinal_expect_le (V := V) (H := H) (hne := hne)
      (Q := Q) (N := N) (r := r) hN hdiv hr hmin hdr
  have hExp : Real.exp M ≤ (3 : ℝ) ^ M := by
    exact DGKAnalytic.exp_le_three_pow_of_le_natCast (by simp)
  have hcontrolledNumeric :
      DGKWeight.qWeightR H * Real.exp M *
          (DGKWeight.qWeightR H * (d : ℝ) / r) <
        (1 : ℝ) / 16 := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hfirst :
        DGKWeight.qWeightR H * Real.exp M ≤
          (Q : ℝ) * (3 : ℝ) ^ M :=
      mul_le_mul hqR hExp (Real.exp_pos _).le (by positivity)
    have hsecond :
        DGKWeight.qWeightR H * (d : ℝ) / r ≤
          (Q : ℝ) * (d : ℝ) / r := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hqR (by positivity)) hrR.le
    calc
      DGKWeight.qWeightR H * Real.exp M *
          (DGKWeight.qWeightR H * (d : ℝ) / r) ≤
          (Q : ℝ) * (3 : ℝ) ^ M *
            ((Q : ℝ) * (d : ℝ) / r) := by
        exact mul_le_mul hfirst hsecond
          (div_nonneg
            (mul_nonneg (DGKWeight.qWeightR_nonneg H) (by positivity)) hrR.le)
          (mul_nonneg (by positivity) (pow_nonneg (by norm_num) _))
      _ = ((Q : ℝ) ^ 2 * d * 3 ^ M) / r := by ring
      _ < (1 : ℝ) / 16 := by
        apply DGKUnion.final_error_lt_one_sixteenth
        simpa [r, d, M] using threshold_error_bound Q
  have hcontrolledR :
      (𝔼 w : Outcome V N,
        DGKUnion.realIndicator (HasControlledFinal H hne Q d w)) <
        (1 : ℝ) / 16 := by
    exact lt_of_le_of_lt (by simpa [d, M] using hcontrolledBound)
      hcontrolledNumeric
  let final : Outcome V N → V → Bool :=
    fun w ↦ DGKOutcome.finalColour H w hne
  have hbad :
      (𝔼 w : Outcome V N,
        DGKUnion.realIndicator
          (DGKUnion.HasFinalMonochromaticEdge H final w)) < 1 := by
    calc
      (𝔼 w : Outcome V N,
          DGKUnion.realIndicator
            (DGKUnion.HasFinalMonochromaticEdge H final w)) ≤
          𝔼 w : Outcome V N,
            (DGKUnion.realIndicator (DGKUnion.HasLightEdge H d w) +
              DGKUnion.realIndicator
                ((((16 * Q : ℕ) : ℚ) ≤
                  DGKBadEvents.outcomeAlmostPairMassQ H w)) +
              DGKUnion.realIndicator (HasControlledFinal H hne Q d w)) := by
        apply Finset.expect_le_expect
        intro w _
        simpa [final, d] using finalBad_indicator_le_three (H := H)
          (hne := hne) Q w
      _ = (𝔼 w : Outcome V N,
            DGKUnion.realIndicator (DGKUnion.HasLightEdge H d w)) +
          (𝔼 w : Outcome V N,
            DGKUnion.realIndicator
              ((((16 * Q : ℕ) : ℚ) ≤
                DGKBadEvents.outcomeAlmostPairMassQ H w))) +
          (𝔼 w : Outcome V N,
            DGKUnion.realIndicator (HasControlledFinal H hne Q d w)) := by
        rw [Finset.expect_add_distrib, Finset.expect_add_distrib]
      _ < 1 := by linarith
  obtain ⟨w, hw⟩ :=
    DGKUnion.exists_properColouring_of_finalMono_expect_lt_one H final hbad
  exact treeProperColoring_of_boolean hw

/-- Uniform-in-the-finite-vertex-type form consumed by the decision-tree
proof. -/
theorem universalBeckFixedBudget (ambient : Type u) (C n : ℕ) (hC : 0 < C) :
    Tree.UniversalBeckFixedBudget ambient C n (dgkThreshold (8 * C)) := by
  intro V hFV hDec
  let : LinearOrder V := (Fintype.equivFin V).linearOrder
  let : DecidableEq V := hDec
  exact fixedBudget (V := V) C n hC

end Assembly

end Erdos1027.DGKPropertyB
