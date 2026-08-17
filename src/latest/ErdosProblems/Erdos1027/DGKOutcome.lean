/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1027.GreedyCore
import ErdosProblems.Erdos1027.DGKPriorities

/-!
# Deterministic outcomes for the finite DGK experiment

This file joins the finite colour--priority outcomes of `DGKPriorities` to
the abstract greedy kernel of `GreedyCore`.  For a hypergraph with no empty
edge, every outcome determines a (noncomputably chosen) flip set.  The
certificate returned by `GreedyCore.exists_flipSet` records both that every
initially monochromatic edge is hit and that every flipped vertex has a
private reason edge on which it has maximum lexicographic priority.

The last theorem is the structural input to the fixed-edge estimate.  If an
edge finishes in colour `b`, then each vertex whose initial colour is
opposite to `b` has a reason edge meeting the final edge only at that vertex.
On the event that there is no light initially monochromatic edge, the reason
vertex lies in the high priority interval belonging to the size of its
reason edge.
-/

namespace Erdos1027.DGKOutcome

open scoped BigOperators
open Finset

abbrev Hypergraph (V : Type*) [DecidableEq V] := Finset (Finset V)

/-! ## The common finite sample space -/

/-- One independently chosen colour--priority label. -/
abbrev Label (N : ℕ) := Bool × Fin N

/-- A label at every vertex. -/
abbrev Outcome (V : Type*) (N : ℕ) := V → Label N

/-- The initial colour coordinate of an outcome. -/
abbrev initial {V : Type*} {N : ℕ} (w : Outcome V N) : V → Bool :=
  DGKPriorities.colour w

/-- The finite priority coordinate, regarded as a natural number for the
lexicographic order used by `GreedyCore`. -/
def priorityNat {V : Type*} {N : ℕ} (w : Outcome V N) (v : V) : ℕ :=
  (DGKPriorities.priority w v).val

/-- The product of all edge sizes is a common denominator for the priority
windows `d / |E|`. -/
def commonDenominator {V : Type*} [DecidableEq V] (H : Hypergraph V) : ℕ :=
  ∏ E ∈ H, E.card

/-- The particular common-denominator outcome space attached to a
hypergraph. -/
abbrev ExperimentOutcome {V : Type*} [DecidableEq V] (H : Hypergraph V) :=
  Outcome V (commonDenominator H)

lemma commonDenominator_pos {V : Type*} [DecidableEq V]
    {H : Hypergraph V} (hne : ∀ E ∈ H, E.Nonempty) :
    0 < commonDenominator H := by
  unfold commonDenominator
  apply Finset.prod_pos
  intro E hE
  exact Finset.card_pos.mpr (hne E hE)

lemma card_dvd_commonDenominator {V : Type*} [DecidableEq V]
    {H : Hypergraph V} {E : Finset V} (hE : E ∈ H) :
    E.card ∣ commonDenominator H := by
  unfold commonDenominator
  exact Finset.dvd_prod_of_mem (fun F : Finset V ↦ F.card) hE

/-! ## Matching the two formulations of initial monochromaticity -/

lemma initiallyMonochromatic_iff_greedy {V : Type*} [DecidableEq V]
    {N : ℕ} (w : Outcome V N) (E : Finset V) :
    DGKPriorities.InitiallyMonochromatic w E ↔
      GreedyCore.InitiallyMonochromatic (initial w) E := by
  constructor
  · rintro ⟨b, hb⟩ x hx y hy
    exact (hb x hx).trans (hb y hy).symm
  · intro h
    by_cases hE : E.Nonempty
    · obtain ⟨v, hv⟩ := hE
      exact ⟨initial w v, fun x hx ↦ h x hx v hv⟩
    · refine ⟨false, ?_⟩
      intro x hx
      exact (hE ⟨x, hx⟩).elim

/-! ## The chosen greedy flip set -/

/-- The certificate supplied by the abstract greedy kernel. -/
def Certificate {V : Type*} [LinearOrder V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N) (S : Finset V) : Prop :=
  (∀ v ∈ S, ∃ E ∈ H,
      GreedyCore.InitiallyMonochromatic (initial w) E ∧
      GreedyCore.IsKeyMaximum (priorityNat w) E v ∧
      E ∩ S = {v}) ∧
    (∀ E ∈ H, GreedyCore.InitiallyMonochromatic (initial w) E →
      (E ∩ S).Nonempty)

private theorem exists_certifiedFlipSet
    {V : Type*} [LinearOrder V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N)
    (hne : ∀ E ∈ H, E.Nonempty) :
    ∃ S : Finset V, Certificate H w S := by
  simpa only [Certificate] using
    (GreedyCore.exists_flipSet H (initial w) (priorityNat w)
      (fun E hEH _hmono ↦ hne E hEH))

/-- The flip set attached to an outcome.  Only the existence and certificate
matter; choosing a canonical implementation is unnecessary for the counting
argument. -/
noncomputable def flipSet {V : Type*} [LinearOrder V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N)
    (hne : ∀ E ∈ H, E.Nonempty) : Finset V :=
  Classical.choose (exists_certifiedFlipSet H w hne)

theorem flipSet_certificate {V : Type*} [LinearOrder V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N)
    (hne : ∀ E ∈ H, E.Nonempty) :
    Certificate H w (flipSet H w hne) :=
  Classical.choose_spec (exists_certifiedFlipSet H w hne)

/-- Flip precisely the vertices in the chosen set. -/
noncomputable def finalColour {V : Type*} [LinearOrder V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N)
    (hne : ∀ E ∈ H, E.Nonempty) (v : V) : Bool :=
  if v ∈ flipSet H w hne then !(initial w v) else initial w v

@[simp] lemma finalColour_eq_not_initial_of_mem
    {V : Type*} [LinearOrder V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N)
    (hne : ∀ E ∈ H, E.Nonempty) {v : V}
    (hv : v ∈ flipSet H w hne) :
    finalColour H w hne v = !(initial w v) := by
  simp [finalColour, hv]

@[simp] lemma finalColour_eq_initial_of_not_mem
    {V : Type*} [LinearOrder V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N)
    (hne : ∀ E ∈ H, E.Nonempty) {v : V}
    (hv : v ∉ flipSet H w hne) :
    finalColour H w hne v = initial w v := by
  simp [finalColour, hv]

theorem initiallyMonochromatic_inter_flipSet_nonempty
    {V : Type*} [LinearOrder V] {N : ℕ}
    {H : Hypergraph V} {w : Outcome V N}
    (hne : ∀ E ∈ H, E.Nonempty) {E : Finset V}
    (hEH : E ∈ H) (hmono : DGKPriorities.InitiallyMonochromatic w E) :
    (E ∩ flipSet H w hne).Nonempty := by
  exact (flipSet_certificate H w hne).2 E hEH
    ((initiallyMonochromatic_iff_greedy w E).mp hmono)

theorem reasonEdge_of_mem_flipSet
    {V : Type*} [LinearOrder V] {N : ℕ}
    {H : Hypergraph V} {w : Outcome V N}
    (hne : ∀ E ∈ H, E.Nonempty) {v : V}
    (hv : v ∈ flipSet H w hne) :
    ∃ F ∈ H,
      DGKPriorities.InitiallyMonochromatic w F ∧
      GreedyCore.IsKeyMaximum (priorityNat w) F v ∧
      F ∩ flipSet H w hne = {v} := by
  obtain ⟨F, hFH, hFmono, hmax, hsingle⟩ :=
    (flipSet_certificate H w hne).1 v hv
  exact ⟨F, hFH, (initiallyMonochromatic_iff_greedy w F).mpr hFmono,
    hmax, hsingle⟩

/-- An initially monochromatic edge does not finish in the same colour in
which it started.  It may finish monochromatic in the opposite colour; those
are exactly the bad final edges controlled by the fixed-edge estimate. -/
theorem initiallyMonochromatic_not_finish_initialColour
    {V : Type*} [LinearOrder V] {N : ℕ}
    {H : Hypergraph V} {w : Outcome V N}
    (hne : ∀ E ∈ H, E.Nonempty) {E : Finset V} {b : Bool}
    (hEH : E ∈ H) (hinitial : ∀ v ∈ E, initial w v = b) :
    ¬(∀ v ∈ E, finalColour H w hne v = b) := by
  intro hfinal
  have hmono : DGKPriorities.InitiallyMonochromatic w E := ⟨b, hinitial⟩
  obtain ⟨v, hv⟩ :=
    initiallyMonochromatic_inter_flipSet_nonempty hne hEH hmono
  have hvE : v ∈ E := (Finset.mem_inter.mp hv).1
  have hvS : v ∈ flipSet H w hne := (Finset.mem_inter.mp hv).2
  apply Bool.not_ne_self b
  calc
    (!b) = (!(initial w v)) :=
      congrArg (fun c : Bool ↦ !c) (hinitial v hvE).symm
    _ = finalColour H w hne v :=
      (finalColour_eq_not_initial_of_mem H w hne hvS).symm
    _ = b := hfinal v hvE

/-! ## Threat edges on the no-light event -/

/-- No initially monochromatic edge is entirely below its high priority
window. -/
def NoLight {V : Type*} [DecidableEq V] {N : ℕ}
    (H : Hypergraph V) (w : Outcome V N) (d : ℕ) : Prop :=
  ∀ E ∈ H, DGKPriorities.InitiallyMonochromatic w E →
    ∃ v ∈ E,
      DGKPriorities.IsHigh N d E.card (DGKPriorities.priority w v)

lemma noLight_iff_no_allLow {V : Type*} [DecidableEq V] {N d : ℕ}
    (H : Hypergraph V) (w : Outcome V N) :
    NoLight H w d ↔
      ∀ E ∈ H, ¬(DGKPriorities.InitiallyMonochromatic w E ∧
        DGKPriorities.AllLow d E.card w E) := by
  constructor
  · intro h E hEH hbad
    obtain ⟨v, hvE, hvHigh⟩ := h E hEH hbad.1
    have hvLow := hbad.2 v hvE
    exact
      ((DGKPriorities.not_low_iff_high (DGKPriorities.priority w v)).mpr hvHigh)
        hvLow
  · intro h E hEH hmono
    by_contra hex
    apply h E hEH
    refine ⟨hmono, ?_⟩
    intro v hvE
    have hvNotHigh :
        ¬DGKPriorities.IsHigh N d E.card (DGKPriorities.priority w v) := by
      intro hvHigh
      exact hex ⟨v, hvE, hvHigh⟩
    rcases DGKPriorities.low_or_high (DGKPriorities.priority w v) with
      hvLow | hvHigh
    · exact hvLow
    · exact (hvNotHigh hvHigh).elim

lemma high_of_priority_le {N d j : ℕ} {p q : Fin N}
    (hpq : p.val ≤ q.val) (hp : DGKPriorities.IsHigh N d j p) :
    DGKPriorities.IsHigh N d j q := by
  unfold DGKPriorities.IsHigh at *
  omega

lemma keyMaximum_priorityNat
    {V : Type*} [LinearOrder V] {N : ℕ} {w : Outcome V N}
    {E : Finset V} {v u : V}
    (hmax : GreedyCore.IsKeyMaximum (priorityNat w) E v)
    (huE : u ∈ E) :
    (DGKPriorities.priority w u).val ≤
      (DGKPriorities.priority w v).val := by
  have hkey := hmax.2 u huE
  have hfst := Prod.Lex.monotone_fst _ _ hkey
  simpa [GreedyCore.key, priorityNat] using hfst

lemma keyMaximum_isHigh_of_noLight
    {V : Type*} [LinearOrder V] {N d : ℕ}
    {H : Hypergraph V} {w : Outcome V N} (hNoLight : NoLight H w d)
    {F : Finset V} {v : V} (hFH : F ∈ H)
    (hFmono : DGKPriorities.InitiallyMonochromatic w F)
    (hmax : GreedyCore.IsKeyMaximum (priorityNat w) F v) :
    DGKPriorities.IsHigh N d F.card (DGKPriorities.priority w v) := by
  obtain ⟨u, huF, huHigh⟩ := hNoLight F hFH hFmono
  exact high_of_priority_le (keyMaximum_priorityNat hmax huF) huHigh

lemma reasonEdge_inter_finalMono_eq_singleton
    {V : Type*} [LinearOrder V] {N : ℕ}
    {H : Hypergraph V} {w : Outcome V N}
    (hne : ∀ E ∈ H, E.Nonempty)
    {E F : Finset V} {v : V} {b : Bool}
    (hfinal : ∀ x ∈ E, finalColour H w hne x = b)
    (hvE : v ∈ E) (hvopp : initial w v ≠ b)
    (hFmono : GreedyCore.InitiallyMonochromatic (initial w) F)
    (hmax : GreedyCore.IsKeyMaximum (priorityNat w) F v)
    (hFflip : F ∩ flipSet H w hne = {v}) :
    F ∩ E = {v} := by
  apply Finset.Subset.antisymm
  · intro u hu
    have huF : u ∈ F := (Finset.mem_inter.mp hu).1
    have huE : u ∈ E := (Finset.mem_inter.mp hu).2
    by_contra huv
    have huS : u ∉ flipSet H w hne := by
      intro huS
      have : u ∈ ({v} : Finset V) := by
        rw [← hFflip]
        exact Finset.mem_inter.mpr ⟨huF, huS⟩
      exact huv (by simpa using this)
    have huvcolour : initial w u = initial w v :=
      hFmono u huF v hmax.1
    have huinitial : initial w u = b :=
      (finalColour_eq_initial_of_not_mem H w hne huS).symm.trans
        (hfinal u huE)
    exact hvopp (huvcolour.symm.trans huinitial)
  · intro u hu
    have huv : u = v := by simpa using hu
    subst u
    exact Finset.mem_inter.mpr ⟨hmax.1, hvE⟩

/-- Every opposite-initial vertex of a final monochromatic edge has a private
high-priority threat edge. -/
theorem opposite_vertex_has_high_threat
    {V : Type*} [LinearOrder V] {N d : ℕ}
    {H : Hypergraph V} {w : Outcome V N}
    (hne : ∀ E ∈ H, E.Nonempty) (hNoLight : NoLight H w d)
    {E : Finset V} {b : Bool} {v : V}
    (hfinal : ∀ x ∈ E, finalColour H w hne x = b)
    (hvE : v ∈ E) (hvopp : initial w v ≠ b) :
    v ∈ flipSet H w hne ∧
      ∃ F ∈ H,
        DGKPriorities.InitiallyMonochromatic w F ∧
        (∀ x ∈ F, initial w x = !b) ∧
        GreedyCore.IsKeyMaximum (priorityNat w) F v ∧
        F ∩ flipSet H w hne = {v} ∧
        F ∩ E = {v} ∧
        DGKPriorities.IsHigh N d F.card (DGKPriorities.priority w v) := by
  have hvS : v ∈ flipSet H w hne := by
    by_contra hvS
    exact hvopp ((finalColour_eq_initial_of_not_mem H w hne hvS).symm.trans
      (hfinal v hvE))
  refine ⟨hvS, ?_⟩
  obtain ⟨F, hFH, hFmono, hmax, hFflip⟩ :=
    (flipSet_certificate H w hne).1 v hvS
  have hFmono' : DGKPriorities.InitiallyMonochromatic w F :=
    (initiallyMonochromatic_iff_greedy w F).mpr hFmono
  have hvnot : initial w v = !b := Bool.eq_not_of_ne hvopp
  have hFopp : ∀ x ∈ F, initial w x = !b := by
    intro x hx
    exact (hFmono x hx v hmax.1).trans hvnot
  have hFE : F ∩ E = {v} :=
    reasonEdge_inter_finalMono_eq_singleton hne hfinal hvE hvopp
      hFmono hmax hFflip
  have hvHigh :
      DGKPriorities.IsHigh N d F.card (DGKPriorities.priority w v) :=
    keyMaximum_isHigh_of_noLight hNoLight hFH hFmono' hmax
  exact ⟨F, hFH, hFmono', hFopp, hmax, hFflip, hFE, hvHigh⟩

end Erdos1027.DGKOutcome
