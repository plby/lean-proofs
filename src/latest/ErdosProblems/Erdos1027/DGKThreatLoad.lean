/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1027.DGKWeight
import ErdosProblems.Erdos1027.FiniteExposure
import ErdosProblems.Erdos1027.FiniteExpect

/-!
# Threat loads after exposing a fixed edge

This file contains the severity calculation in the fixed-edge part of the
Duraj--Gutowski--Kozik argument.  Fix an edge `edge` which is supposed to
finish in colour `target`, and expose the initial colours outside `edge`.
A threat to `v ∈ edge` is an edge meeting `edge` exactly in `v` whose other
vertices all have colour `!target`.  An endangered vertex is assigned a
threat of minimum cardinality; this cardinality is its severity and its
penalty is `d / severity`.

Two estimates are kept separate.

* Pointwise, the chosen threats are distinct.  Consequently the total
  penalty is at most `d` times the target-almost-monochromatic mass, for
  every completion of the colours on `edge`.
* On average over the exposed outside colours, the total penalty is at most
  `q(H) d / r` when every edge has cardinality at least `r`.  The extra
  factor `1/r` comes from directly summing the possible threat edges; it
  does not follow from the coarser pointwise estimate.
-/

namespace Erdos1027.DGKThreatLoad

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

abbrev Hypergraph (V : Type*) := DGKWeight.Hypergraph V

/-! ## Structural and exposed threats -/

/-- A global colouring makes `F` a possible threat to `v` of the focused
edge: `F` meets the focused edge only at `v`, and every other vertex of `F`
has the colour opposite to the desired final colour. -/
def PotentialThreat {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (colour : V → Bool) (edge : Finset V)
    (target : Bool) (v : V) (F : Finset V) : Prop :=
  F ∈ H ∧ F ∩ edge = {v} ∧
    ∀ u ∈ F, u ≠ v → colour u = !target

/-- The exposed outside Boolean coordinates. -/
abbrev OutsideColouring {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) :=
  FiniteExposure.OutsideAssignment (A := Bool) edge

/-- Complete exposed outside colours by the target colour on the focused
edge.  The particular completion is immaterial to all threat predicates. -/
def exposedColour {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (outside : OutsideColouring edge)
    (target : Bool) : V → Bool :=
  FiniteExposure.glue edge outside (fun _ ↦ target)

/-- The outside-exposed version of `PotentialThreat`. -/
def OutsideThreat {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (v : V) (F : Finset V) : Prop :=
  PotentialThreat H (exposedColour edge outside target) edge target v F

lemma potentialThreat_glue_iff_outsideThreat
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge)
    (inside : FiniteExposure.InsideAssignment (A := Bool) edge)
    (v : V) (F : Finset V) :
    PotentialThreat H (FiniteExposure.glue edge outside inside)
        edge target v F ↔
      OutsideThreat H edge target outside v F := by
  constructor
  · rintro ⟨hFH, hinter, hcolour⟩
    refine ⟨hFH, hinter, ?_⟩
    intro u huF huv
    have huEdge : u ∉ edge := by
      intro hue
      have hu : u ∈ F ∩ edge := Finset.mem_inter.mpr ⟨huF, hue⟩
      rw [hinter] at hu
      exact huv (Finset.mem_singleton.mp hu)
    have hsame :
        FiniteExposure.glue edge outside inside u =
          exposedColour edge outside target u := by
      rw [FiniteExposure.glue_apply_of_not_mem outside inside huEdge]
      rw [exposedColour,
        FiniteExposure.glue_apply_of_not_mem outside (fun _ ↦ target) huEdge]
    rw [← hsame]
    exact hcolour u huF huv
  · rintro ⟨hFH, hinter, hcolour⟩
    refine ⟨hFH, hinter, ?_⟩
    intro u huF huv
    have huEdge : u ∉ edge := by
      intro hue
      have hu : u ∈ F ∩ edge := Finset.mem_inter.mpr ⟨huF, hue⟩
      rw [hinter] at hu
      exact huv (Finset.mem_singleton.mp hu)
    have hsame :
        FiniteExposure.glue edge outside inside u =
          exposedColour edge outside target u := by
      rw [FiniteExposure.glue_apply_of_not_mem outside inside huEdge]
      rw [exposedColour,
        FiniteExposure.glue_apply_of_not_mem outside (fun _ ↦ target) huEdge]
    rw [hsame]
    exact hcolour u huF huv

/-- A vertex is endangered when it has at least one exposed threat. -/
def Endangered {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (v : V) : Prop :=
  ∃ F, OutsideThreat H edge target outside v F

private lemma exists_threat_card_of_endangered
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {edge : Finset V} {target : Bool}
    {outside : OutsideColouring edge} {v : V}
    (h : Endangered H edge target outside v) :
    ∃ j, ∃ F, OutsideThreat H edge target outside v F ∧ F.card = j := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.card, F, hF, rfl⟩

/-- The least cardinality of a threat to `v`; it is set to `1` for a vertex
which is not endangered. -/
noncomputable def severity {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (v : V) : ℕ :=
  if h : Endangered H edge target outside v then
    Nat.find (exists_threat_card_of_endangered h)
  else 1

/-- A minimum-cardinality certifying threat, with the empty set used at
non-endangered vertices. -/
noncomputable def chosenThreat {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (v : V) : Finset V :=
  if h : Endangered H edge target outside v then
    Classical.choose (Nat.find_spec (exists_threat_card_of_endangered h))
  else ∅

lemma chosenThreat_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {edge : Finset V} {target : Bool}
    {outside : OutsideColouring edge} {v : V}
    (h : Endangered H edge target outside v) :
    OutsideThreat H edge target outside v
        (chosenThreat H edge target outside v) ∧
      (chosenThreat H edge target outside v).card =
        severity H edge target outside v := by
  classical
  simp only [chosenThreat, severity, dif_pos h]
  exact Classical.choose_spec
    (Nat.find_spec (exists_threat_card_of_endangered h))

lemma severity_le_card_of_threat
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {edge : Finset V} {target : Bool}
    {outside : OutsideColouring edge} {v : V} {F : Finset V}
    (hF : OutsideThreat H edge target outside v F) :
    severity H edge target outside v ≤ F.card := by
  classical
  have hend : Endangered H edge target outside v := ⟨F, hF⟩
  rw [severity, dif_pos hend]
  exact Nat.find_min' (exists_threat_card_of_endangered hend)
    ⟨F, hF, rfl⟩

lemma severity_pos_of_endangered
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {edge : Finset V} {target : Bool}
    {outside : OutsideColouring edge} {v : V}
    (h : Endangered H edge target outside v) :
    0 < severity H edge target outside v := by
  have hs := chosenThreat_spec h
  rw [← hs.2]
  apply Finset.card_pos.mpr
  refine ⟨v, ?_⟩
  have hv : v ∈ chosenThreat H edge target outside v ∩ edge := by
    rw [hs.1.2.1]
    simp
  exact (Finset.mem_inter.mp hv).1

lemma minEdge_le_severity
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {edge : Finset V} {target : Bool}
    {outside : OutsideColouring edge} {v : V} {r : ℕ}
    (hmin : ∀ F ∈ H, r ≤ F.card)
    (h : Endangered H edge target outside v) :
    r ≤ severity H edge target outside v := by
  have hs := chosenThreat_spec h
  rw [← hs.2]
  exact hmin _ hs.1.1

/-- Chosen threats of two endangered focused vertices are distinct. -/
lemma chosenThreat_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {edge : Finset V} {target : Bool}
    {outside : OutsideColouring edge} {v w : V}
    (hv : Endangered H edge target outside v)
    (hw : Endangered H edge target outside w)
    (heq : chosenThreat H edge target outside v =
      chosenThreat H edge target outside w) : v = w := by
  have hsv := (chosenThreat_spec hv).1
  have hsw := (chosenThreat_spec hw).1
  have hsingle : ({v} : Finset V) = {w} := by
    calc
      ({v} : Finset V) = chosenThreat H edge target outside v ∩ edge :=
        hsv.2.1.symm
      _ = chosenThreat H edge target outside w ∩ edge := by rw [heq]
      _ = ({w} : Finset V) := hsw.2.1
  simpa using hsingle

lemma chosenThreat_injOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) :
    Set.InjOn (chosenThreat H edge target outside)
      ((edge.filter fun v ↦ Endangered H edge target outside v : Finset V) : Set V) := by
  intro v hv w hw heq
  exact chosenThreat_injective
    (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2 heq

/-! ## Penalty and the pointwise almost-mass bound -/

/-- The target-specific almost-monochromatic event obtained by deleting
`v`.  Unlike the usual two-colour event, the surviving colour is fixed to
be `!target`. -/
def TargetAlmostAt {V : Type*} [DecidableEq V]
    (colour : V → Bool) (target : Bool) (F : Finset V) (v : V) : Prop :=
  v ∈ F ∧ ∀ u ∈ F, u ≠ v → colour u = !target

/-- Size-normalized target-almost-monochromatic mass. -/
noncomputable def targetAlmostMass {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (colour : V → Bool) (target : Bool) : ℝ :=
  ∑ F ∈ H, ∑ v ∈ F,
    if TargetAlmostAt colour target F v then (F.card : ℝ)⁻¹ else 0

/-- The minimum-severity penalty. -/
noncomputable def penalty {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (d : ℕ) (v : V) : ℝ :=
  if Endangered H edge target outside v then
    (d : ℝ) / severity H edge target outside v
  else 0

lemma penalty_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (d : ℕ) (v : V) :
    0 ≤ penalty H edge target outside d v := by
  unfold penalty
  split_ifs
  · positivity
  · exact le_rfl

/-- Sum all possible structural threat contributions for a global colour. -/
noncomputable def globalThreatLoad {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (colour : V → Bool) (edge : Finset V)
    (target : Bool) (d : ℕ) : ℝ :=
  ∑ v ∈ edge, ∑ F ∈ H,
    if PotentialThreat H colour edge target v F then
      (d : ℝ) / F.card else 0

/-- The same load expressed purely in terms of the exposed outside colour. -/
noncomputable def outsideThreatLoad
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (d : ℕ) : ℝ :=
  globalThreatLoad H (exposedColour edge outside target) edge target d

lemma penalty_le_threatLoad_at
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (d : ℕ) (v : V) :
    penalty H edge target outside d v ≤
      ∑ F ∈ H,
        if OutsideThreat H edge target outside v F then
          (d : ℝ) / F.card else 0 := by
  classical
  by_cases hend : Endangered H edge target outside v
  · have hs := chosenThreat_spec hend
    rw [penalty, if_pos hend, ← hs.2]
    calc
      (d : ℝ) / (chosenThreat H edge target outside v).card =
          if OutsideThreat H edge target outside v
              (chosenThreat H edge target outside v) then
            (d : ℝ) / (chosenThreat H edge target outside v).card else 0 := by
        simp [hs.1]
      _ ≤ ∑ F ∈ H,
          if OutsideThreat H edge target outside v F then
            (d : ℝ) / F.card else 0 := by
        apply Finset.single_le_sum
          (s := H)
          (f := fun F ↦
            if OutsideThreat H edge target outside v F then
              (d : ℝ) / F.card else 0)
          (fun F hF ↦ ?_) hs.1.1
        split_ifs <;> positivity
  · rw [penalty, if_neg hend]
    exact Finset.sum_nonneg fun F hF ↦ by
      split_ifs <;> positivity

lemma penaltySum_le_outsideThreatLoad
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge) (d : ℕ) :
    (∑ v ∈ edge, penalty H edge target outside d v) ≤
      outsideThreatLoad H edge target outside d := by
  classical
  unfold outsideThreatLoad globalThreatLoad
  apply Finset.sum_le_sum
  intro v hv
  change penalty H edge target outside d v ≤
    ∑ F ∈ H,
      if OutsideThreat H edge target outside v F then
        (d : ℝ) / F.card else 0
  exact penalty_le_threatLoad_at H edge target outside d v

lemma potentialThreat_implies_targetAlmostAt
    {V : Type*} [DecidableEq V]
    {H : Hypergraph V} {colour : V → Bool} {edge F : Finset V}
    {target : Bool} {v : V}
    (h : PotentialThreat H colour edge target v F) :
    TargetAlmostAt colour target F v := by
  refine ⟨?_, h.2.2⟩
  have hv : v ∈ F ∩ edge := by rw [h.2.1]; simp
  exact (Finset.mem_inter.mp hv).1

/-- Pointwise threat load is bounded by the target-almost-monochromatic
mass.  A threat edge can meet the focused edge at only one vertex. -/
lemma globalThreatLoad_le_mul_targetAlmostMass
    {V : Type*} [DecidableEq V]
    (H : Hypergraph V) (colour : V → Bool) (edge : Finset V)
    (target : Bool) (d : ℕ) :
    globalThreatLoad H colour edge target d ≤
      d * targetAlmostMass H colour target := by
  classical
  unfold globalThreatLoad targetAlmostMass
  rw [Finset.sum_comm]
  calc
    (∑ F ∈ H, ∑ v ∈ edge,
        if PotentialThreat H colour edge target v F then
          (d : ℝ) / F.card else 0) ≤
        ∑ F ∈ H, (d : ℝ) *
          (∑ v ∈ F,
            if TargetAlmostAt colour target F v then
              (F.card : ℝ)⁻¹ else 0) := by
      apply Finset.sum_le_sum
      intro F hFH
      by_cases hex : ∃ v ∈ edge, PotentialThreat H colour edge target v F
      · obtain ⟨v, hvEdge, hv⟩ := hex
        have hleft :
            (∑ w ∈ edge,
                if PotentialThreat H colour edge target w F then
                  (d : ℝ) / F.card else 0) =
              (d : ℝ) / F.card := by
          rw [Finset.sum_eq_single v]
          · simp [hv]
          · intro w hwEdge hwv
            have hn : ¬PotentialThreat H colour edge target w F := by
              intro hw
              apply hwv
              have hs : ({w} : Finset V) = {v} := hw.2.1.symm.trans hv.2.1
              simpa using hs
            simp [hn]
          · exact fun hvnot ↦ (hvnot hvEdge).elim
        rw [hleft]
        have hvF : v ∈ F := (potentialThreat_implies_targetAlmostAt hv).1
        have hterm :
            (F.card : ℝ)⁻¹ ≤
              ∑ w ∈ F,
                if TargetAlmostAt colour target F w then
                  (F.card : ℝ)⁻¹ else 0 := by
          calc
            (F.card : ℝ)⁻¹ =
                if TargetAlmostAt colour target F v then
                  (F.card : ℝ)⁻¹ else 0 := by
              simp [potentialThreat_implies_targetAlmostAt hv]
            _ ≤ ∑ w ∈ F,
                if TargetAlmostAt colour target F w then
                  (F.card : ℝ)⁻¹ else 0 := by
              apply Finset.single_le_sum
                (s := F)
                (f := fun w ↦
                  if TargetAlmostAt colour target F w then
                    (F.card : ℝ)⁻¹ else 0)
                (fun w hwF ↦ ?_) hvF
              split_ifs <;> positivity
        calc
          (d : ℝ) / F.card = (d : ℝ) * (F.card : ℝ)⁻¹ := by
            rw [div_eq_mul_inv]
          _ ≤ (d : ℝ) *
              (∑ w ∈ F,
                if TargetAlmostAt colour target F w then
                  (F.card : ℝ)⁻¹ else 0) :=
            mul_le_mul_of_nonneg_left hterm (by positivity)
      · have hzero :
            (∑ v ∈ edge,
              if PotentialThreat H colour edge target v F then
                (d : ℝ) / F.card else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hvEdge
          simp only [ite_eq_right_iff]
          exact fun h ↦ (hex ⟨v, hvEdge, h⟩).elim
        rw [hzero]
        positivity
    _ = (d : ℝ) * ∑ F ∈ H,
        ∑ v ∈ F,
          if TargetAlmostAt colour target F v then
            (F.card : ℝ)⁻¹ else 0 := by
      rw [Finset.mul_sum]

lemma globalThreatLoad_glue_eq_outsideThreatLoad
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge)
    (inside : FiniteExposure.InsideAssignment (A := Bool) edge)
    (d : ℕ) :
    globalThreatLoad H (FiniteExposure.glue edge outside inside)
        edge target d = outsideThreatLoad H edge target outside d := by
  classical
  unfold globalThreatLoad outsideThreatLoad
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro F hF
  have hiff :=
    potentialThreat_glue_iff_outsideThreat H edge target outside inside v F
  by_cases h : PotentialThreat H (FiniteExposure.glue edge outside inside)
      edge target v F
  · have hout := hiff.mp h
    change PotentialThreat H (exposedColour edge outside target)
      edge target v F at hout
    simp only [if_pos h, if_pos hout]
  · have hout : ¬ OutsideThreat H edge target outside v F :=
      fun ht ↦ h (hiff.mpr ht)
    change ¬ PotentialThreat H (exposedColour edge outside target)
      edge target v F at hout
    simp only [if_neg h, if_neg hout]

/-- The pointwise cap used on the good event, valid for every completion of
the unexposed inside colours. -/
theorem penaltySum_le_mul_targetAlmostMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (outside : OutsideColouring edge)
    (inside : FiniteExposure.InsideAssignment (A := Bool) edge)
    (d : ℕ) :
    (∑ v ∈ edge, penalty H edge target outside d v) ≤
      d * targetAlmostMass H
        (FiniteExposure.glue edge outside inside) target := by
  calc
    (∑ v ∈ edge, penalty H edge target outside d v) ≤
        outsideThreatLoad H edge target outside d :=
      penaltySum_le_outsideThreatLoad H edge target outside d
    _ = globalThreatLoad H (FiniteExposure.glue edge outside inside)
        edge target d :=
      (globalThreatLoad_glue_eq_outsideThreatLoad
        H edge target outside inside d).symm
    _ ≤ d * targetAlmostMass H
        (FiniteExposure.glue edge outside inside) target :=
      globalThreatLoad_le_mul_targetAlmostMass H
        (FiniteExposure.glue edge outside inside) edge target d

/-! ## Direct expectation bound -/

open Erdos1027.FiniteExpect

private lemma expect_indicator_prescribed_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset V) (v : V) (hv : v ∈ F) (target : Bool) :
    (𝔼 colour : V → Bool,
        (indicator (∀ u ∈ F, u ≠ v → colour u = !target) : ℝ)) =
      1 / (2 : ℝ) ^ (F.card - 1) := by
  let g : V → Bool := fun _ ↦ !target
  have hevent (colour : V → Bool) :
      (∀ u ∈ F, u ≠ v → colour u = !target) ↔
        AgreesOn (F.erase v) g colour := by
    simp only [AgreesOn, Finset.mem_erase, g]
    aesop
  calc
    (𝔼 colour : V → Bool,
        (indicator (∀ u ∈ F, u ≠ v → colour u = !target) : ℝ)) =
        𝔼 colour : V → Bool,
          (indicator (AgreesOn (F.erase v) g colour) : ℝ) := by
            apply Finset.expect_congr rfl
            intro colour _
            rw [propext (hevent colour)]
    _ = ((𝔼 colour : V → Bool,
          indicator (AgreesOn (F.erase v) g colour) : ℚ) : ℝ) := by
            exact (algebraMap.coe_expect (N := ℝ) Finset.univ
              (fun colour : V → Bool ↦
                indicator (AgreesOn (F.erase v) g colour))).symm
    _ = (1 / (2 : ℚ) ^ (F.erase v).card : ℚ) := by
            rw [expect_indicator_agreesOn]
            norm_num [Fintype.card_bool]
    _ = 1 / (2 : ℝ) ^ (F.card - 1) := by
            rw [Finset.card_erase_of_mem hv]
            norm_num [Fintype.card_bool]

private lemma expect_single_threat_term
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge F : Finset V) (target : Bool) (d : ℕ)
    (v : V) (hF : F ∈ H) (hv : F ∩ edge = {v}) :
    (𝔼 colour : V → Bool,
        if PotentialThreat H colour edge target v F then
          (d : ℝ) / F.card else 0) =
      (1 / (2 : ℝ) ^ (F.card - 1)) * ((d : ℝ) / F.card) := by
  have hvF : v ∈ F := by
    have : v ∈ F ∩ edge := by rw [hv]; simp
    exact (Finset.mem_inter.mp this).1
  have hiff (colour : V → Bool) :
      PotentialThreat H colour edge target v F ↔
        ∀ u ∈ F, u ≠ v → colour u = !target := by
    simp [PotentialThreat, hF, hv]
  calc
    (𝔼 colour : V → Bool,
        if PotentialThreat H colour edge target v F then
          (d : ℝ) / F.card else 0) =
        𝔼 colour : V → Bool,
          (indicator (∀ u ∈ F, u ≠ v → colour u = !target) : ℝ) *
            ((d : ℝ) / F.card) := by
              apply Finset.expect_congr rfl
              intro colour _
              by_cases h : PotentialThreat H colour edge target v F
              · have hp := (hiff colour).mp h
                rw [if_pos h, indicator_of_true hp]
                norm_num
              · have hp : ¬(∀ u ∈ F, u ≠ v → colour u = !target) :=
                  fun hp ↦ h ((hiff colour).mpr hp)
                rw [if_neg h, indicator_of_false hp]
                norm_num
    _ = (𝔼 colour : V → Bool,
          (indicator (∀ u ∈ F, u ≠ v → colour u = !target) : ℝ)) *
            ((d : ℝ) / F.card) := by
              exact (Finset.expect_mul Finset.univ
                (fun colour : V → Bool ↦
                  (indicator
                    (∀ u ∈ F, u ≠ v → colour u = !target) : ℝ))
                ((d : ℝ) / F.card)).symm
    _ = (1 / (2 : ℝ) ^ (F.card - 1)) * ((d : ℝ) / F.card) := by
              rw [expect_indicator_prescribed_erase F v hvF target]

private lemma qWeightR_eq_sum_invTwoPow_sub_one
    {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (hnonempty : ∀ F ∈ H, 0 < F.card) :
    DGKWeight.qWeightR H =
      ∑ F ∈ H, 1 / (2 : ℝ) ^ (F.card - 1) := by
  classical
  unfold DGKWeight.qWeightR DGKWeight.booleanWeightR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [zpow_neg, zpow_natCast]
  have hpos := hnonempty F hF
  have hcard : F.card = (F.card - 1) + 1 := by omega
  rw [hcard, pow_succ]
  field_simp
  congr 1 <;> omega

/-- Expected global possible-threat load.  The `1/r` is obtained before
summing over threat edges, from `d / |F| ≤ d / r`. -/
theorem expect_globalThreatLoad_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool) (d r : ℕ)
    (hr : 0 < r) (hmin : ∀ F ∈ H, r ≤ F.card) :
    (𝔼 colour : V → Bool, globalThreatLoad H colour edge target d) ≤
      DGKWeight.qWeightR H * (d : ℝ) / r := by
  classical
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  unfold globalThreatLoad
  rw [Finset.expect_sum_comm]
  simp_rw [Finset.expect_sum_comm]
  rw [Finset.sum_comm]
  calc
    (∑ F ∈ H, ∑ v ∈ edge,
        𝔼 colour : V → Bool,
          if PotentialThreat H colour edge target v F then
            (d : ℝ) / F.card else 0) ≤
        ∑ F ∈ H,
          (1 / (2 : ℝ) ^ (F.card - 1)) * ((d : ℝ) / F.card) := by
      apply Finset.sum_le_sum
      intro F hF
      by_cases hex : ∃ v ∈ edge, F ∩ edge = {v}
      · obtain ⟨v, hvEdge, hv⟩ := hex
        rw [Finset.sum_eq_single v]
        · exact (expect_single_threat_term H edge F target d v hF hv).le
        · intro w hwEdge hwv
          have hn : ∀ colour : V → Bool,
              ¬PotentialThreat H colour edge target w F := by
            intro colour hw
            apply hwv
            have hs : ({w} : Finset V) = {v} := hw.2.1.symm.trans hv
            simpa using hs
          simp only [hn, if_false]
          simp
        · exact fun hvnot ↦ (hvnot hvEdge).elim
      · have hz : ∀ v ∈ edge, ∀ colour : V → Bool,
            ¬PotentialThreat H colour edge target v F := by
          intro v hvEdge colour ht
          exact hex ⟨v, hvEdge, ht.2.1⟩
        have hzero :
            (∑ v ∈ edge,
              𝔼 colour : V → Bool,
                if PotentialThreat H colour edge target v F then
                  (d : ℝ) / F.card else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro v hvEdge
          simp [hz v hvEdge]
        rw [hzero]
        positivity
    _ ≤ ∑ F ∈ H,
          (1 / (2 : ℝ) ^ (F.card - 1)) * ((d : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro F hF
      have hFR : (0 : ℝ) < F.card :=
        hrR.trans_le (by exact_mod_cast hmin F hF)
      have hdiv : (d : ℝ) / F.card ≤ (d : ℝ) / r :=
        div_le_div_of_nonneg_left (by positivity) hrR
          (by exact_mod_cast hmin F hF)
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = DGKWeight.qWeightR H * (d : ℝ) / r := by
      rw [← Finset.sum_mul,
        ← qWeightR_eq_sum_invTwoPow_sub_one H
          (fun F hF ↦ lt_of_lt_of_le hr (hmin F hF))]
      ring

lemma expect_outsideThreatLoad_eq_expect_globalThreatLoad
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool) (d : ℕ) :
    (𝔼 outside : OutsideColouring edge,
        outsideThreatLoad H edge target outside d) =
      𝔼 colour : V → Bool,
        globalThreatLoad H colour edge target d := by
  rw [FiniteExposure.expect_eq_expect_outside_inside edge
    (fun colour : V → Bool ↦ globalThreatLoad H colour edge target d)]
  apply Finset.expect_congr rfl
  intro outside _
  calc
    outsideThreatLoad H edge target outside d =
        𝔼 _inside : FiniteExposure.InsideAssignment (A := Bool) edge,
          outsideThreatLoad H edge target outside d := by simp
    _ = 𝔼 inside : FiniteExposure.InsideAssignment (A := Bool) edge,
          globalThreatLoad H (FiniteExposure.glue edge outside inside)
            edge target d := by
      apply Finset.expect_congr rfl
      intro inside _
      exact (globalThreatLoad_glue_eq_outsideThreatLoad
        H edge target outside inside d).symm

/-- The required outside-exposure severity estimate. -/
theorem expect_penaltySum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool) (d r : ℕ)
    (hr : 0 < r) (hmin : ∀ F ∈ H, r ≤ F.card) :
    (𝔼 outside : OutsideColouring edge,
        ∑ v ∈ edge, penalty H edge target outside d v) ≤
      DGKWeight.qWeightR H * (d : ℝ) / r := by
  calc
    (𝔼 outside : OutsideColouring edge,
        ∑ v ∈ edge, penalty H edge target outside d v) ≤
        𝔼 outside : OutsideColouring edge,
          outsideThreatLoad H edge target outside d := by
      apply Finset.expect_le_expect
      intro outside _
      exact penaltySum_le_outsideThreatLoad H edge target outside d
    _ = 𝔼 colour : V → Bool,
          globalThreatLoad H colour edge target d :=
      expect_outsideThreatLoad_eq_expect_globalThreatLoad H edge target d
    _ ≤ DGKWeight.qWeightR H * (d : ℝ) / r :=
      expect_globalThreatLoad_le H edge target d r hr hmin

/-! ## Outside colour-priority labels

The conditional fixed-edge count exposes labels `Bool × Fin N`, rather than
colours alone.  The penalty ignores the priority coordinate.  The following
equivalence and wrappers record that averaging a colour-only statistic over
the label space gives exactly the same answer as averaging it over colours.
-/

/-- Exposed outside colour-priority labels. -/
abbrev OutsideLabels {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (N : ℕ) :=
  FiniteExposure.OutsideAssignment (A := Bool × Fin N) edge

/-- The irrelevant outside-priority coordinates. -/
abbrev OutsidePriorities {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (N : ℕ) :=
  (v : ↥((Finset.univ : Finset V) \ edge)) → Fin N

/-- Forget the priority coordinate of an exposed label assignment. -/
def outsideLabelColours {V : Type*} [Fintype V] [DecidableEq V]
    {edge : Finset V} {N : ℕ} (labels : OutsideLabels edge N) :
    OutsideColouring edge :=
  fun v ↦ (labels v).1

/-- Split an exposed label assignment into its colour and priority
coordinates. -/
def outsideLabelsEquiv {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (N : ℕ) :
    OutsideLabels edge N ≃ OutsideColouring edge × OutsidePriorities edge N where
  toFun labels := (fun v ↦ (labels v).1, fun v ↦ (labels v).2)
  invFun p v := (p.1 v, p.2 v)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma outsideLabelColours_equiv_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (N : ℕ)
    (p : OutsideColouring edge × OutsidePriorities edge N) :
    outsideLabelColours ((outsideLabelsEquiv edge N).symm p) = p.1 := by
  rfl

/-- A colour-only statistic has unchanged expectation after adjoining an
independent, nonempty finite priority coordinate. -/
lemma expect_comp_outsideLabelColours
    {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) (N : ℕ) (hN : 0 < N)
    (statistic : OutsideColouring edge → ℝ) :
    (𝔼 labels : OutsideLabels edge N,
        statistic (outsideLabelColours labels)) =
      𝔼 outside : OutsideColouring edge, statistic outside := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  calc
    (𝔼 labels : OutsideLabels edge N,
        statistic (outsideLabelColours labels)) =
        𝔼 p : OutsideColouring edge × OutsidePriorities edge N,
          statistic
            (outsideLabelColours ((outsideLabelsEquiv edge N).symm p)) := by
      exact Fintype.expect_equiv (outsideLabelsEquiv edge N)
        (fun labels ↦ statistic (outsideLabelColours labels))
        (fun p ↦ statistic
          (outsideLabelColours ((outsideLabelsEquiv edge N).symm p)))
        (fun labels ↦ by simp)
    _ = 𝔼 p : OutsideColouring edge × OutsidePriorities edge N,
          statistic p.1 := by
      apply Finset.expect_congr rfl
      intro p _
      simp
    _ = 𝔼 outside : OutsideColouring edge,
          𝔼 _priority : OutsidePriorities edge N,
            statistic outside := by
      change
        (𝔼 p ∈ (Finset.univ : Finset
            (OutsideColouring edge × OutsidePriorities edge N)),
          statistic p.1) =
          𝔼 outside ∈ (Finset.univ : Finset (OutsideColouring edge)),
            𝔼 _priority ∈
                (Finset.univ : Finset (OutsidePriorities edge N)),
              statistic outside
      rw [show (Finset.univ : Finset
          (OutsideColouring edge × OutsidePriorities edge N)) =
            (Finset.univ : Finset (OutsideColouring edge)) ×ˢ
              (Finset.univ : Finset (OutsidePriorities edge N)) by
        ext p
        simp]
      exact Finset.expect_product _ _ _
    _ = 𝔼 outside : OutsideColouring edge, statistic outside := by
      apply Finset.expect_congr rfl
      intro outside _
      simp

/-- Severity viewed as a function of exposed colour-priority labels. -/
noncomputable def labelSeverity
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool) {N : ℕ}
    (labels : OutsideLabels edge N) (v : V) : ℕ :=
  severity H edge target (outsideLabelColours labels) v

/-- Penalty viewed as a function of exposed colour-priority labels. -/
noncomputable def labelPenalty
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool) {N : ℕ}
    (labels : OutsideLabels edge N) (d : ℕ) (v : V) : ℝ :=
  penalty H edge target (outsideLabelColours labels) d v

lemma labelPenalty_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool) {N : ℕ}
    (labels : OutsideLabels edge N) (d : ℕ) (v : V) :
    0 ≤ labelPenalty H edge target labels d v :=
  penalty_nonneg H edge target (outsideLabelColours labels) d v

/-- The pointwise cap, now in the exact colour-priority label space used by
the conditional product count. -/
theorem labelPenaltySum_le_mul_targetAlmostMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool) {N : ℕ}
    (outside : OutsideLabels edge N)
    (inside : FiniteExposure.InsideAssignment (A := Bool × Fin N) edge)
    (d : ℕ) :
    (∑ v ∈ edge, labelPenalty H edge target outside d v) ≤
      d * targetAlmostMass H
        (fun x ↦ (FiniteExposure.glue edge outside inside x).1) target := by
  let insideColours : FiniteExposure.InsideAssignment (A := Bool) edge :=
    fun v ↦ (inside v).1
  have hcolour :
      (fun x ↦ (FiniteExposure.glue edge outside inside x).1) =
        FiniteExposure.glue edge (outsideLabelColours outside) insideColours := by
    funext x
    by_cases hx : x ∈ edge
    · simp [FiniteExposure.glue_apply_of_mem, hx, insideColours]
    · simp [FiniteExposure.glue_apply_of_not_mem, hx,
        outsideLabelColours]
  simpa only [labelPenalty, hcolour] using
    penaltySum_le_mul_targetAlmostMass H edge target
      (outsideLabelColours outside) insideColours d

/-- The outside-label expectation bound used directly by the fixed-edge
fiber estimate. -/
theorem expect_labelPenaltySum_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (edge : Finset V) (target : Bool)
    (N d r : ℕ) (hN : 0 < N) (hr : 0 < r)
    (hmin : ∀ F ∈ H, r ≤ F.card) :
    (𝔼 labels : OutsideLabels edge N,
        ∑ v ∈ edge, labelPenalty H edge target labels d v) ≤
      DGKWeight.qWeightR H * (d : ℝ) / r := by
  change
    (𝔼 labels : OutsideLabels edge N,
        ∑ v ∈ edge,
          penalty H edge target (outsideLabelColours labels) d v) ≤
      DGKWeight.qWeightR H * (d : ℝ) / r
  rw [expect_comp_outsideLabelColours edge N hN
    (fun outside ↦ ∑ v ∈ edge, penalty H edge target outside d v)]
  exact expect_penaltySum_le H edge target d r hr hmin

end Erdos1027.DGKThreatLoad
