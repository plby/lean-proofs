/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.Cylinder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic

/-!
# The random upper-bound construction for Erdős Problem 1024

This file represents triples as coordinates of a finite product space.  It
sets up the overlap and hole bad events, proves their exact probabilities and
support independence, and extracts a linear triple system hitting every
`t`-set from any assignment avoiding all bad events.
-/

open scoped BigOperators

namespace Erdos1024
namespace Upper

open Cylinder LocalLemma

/-- A three-element subset of `Fin n`, used as a product coordinate. -/
abbrev Triple (n : ℕ) := {e : Finset (Fin n) // e.card = 3}

/-- Ordered pairs of distinct triples meeting in at least two vertices. -/
abbrev OverlapIndex (n : ℕ) :=
  {p : Triple n × Triple n // p.1 ≠ p.2 ∧ 2 ≤ (p.1.1 ∩ p.2.1).card}

/-- Vertex `t`-sets which must not be independent. -/
abbrev HoleIndex (n t : ℕ) :=
  {S : Finset (Fin n) // S.card = t}

/-- The two families of bad events. -/
abbrev BadIndex (n t : ℕ) := OverlapIndex n ⊕ HoleIndex n t

/-- Triple coordinates inspected by a bad event. -/
def support {n t : ℕ} : BadIndex n t → Finset (Triple n)
  | Sum.inl a => {a.1.1, a.1.2}
  | Sum.inr S => Finset.univ.filter fun e ↦ e.1 ⊆ S.1

@[simp] lemma support_overlap {n t : ℕ} (a : OverlapIndex n) :
    support (t := t) (Sum.inl a) = {a.1.1, a.1.2} := by
  simp [support]

@[simp] lemma support_hole {n t : ℕ} (S : HoleIndex n t) :
    support (Sum.inr S) = Finset.univ.filter fun e ↦ e.1 ⊆ S.1 := by
  simp [support]

lemma support_overlap_card {n t : ℕ} (a : OverlapIndex n) :
    (support (t := t) (Sum.inl a)).card = 2 := by
  simp [a.2.1]

lemma support_hole_card {n t : ℕ} (S : HoleIndex n t) :
    (support (Sum.inr S)).card = t.choose 3 := by
  classical
  have hcard : (support (Sum.inr S)).card = (S.1.powersetCard 3).card := by
    refine Finset.card_bij (fun e _ ↦ e.1) ?_ ?_ ?_
    · intro e he
      simp only [support_hole, Finset.mem_filter, Finset.mem_univ, true_and] at he
      exact Finset.mem_powersetCard.mpr ⟨he, e.2⟩
    · intro e₁ he₁ e₂ he₂ h
      exact Subtype.ext h
    · intro e he
      have he' := Finset.mem_powersetCard.mp he
      exact ⟨⟨e, he'.2⟩, by simp [support, he'.1], rfl⟩
  rw [hcard, Finset.card_powersetCard, S.2]

/-- Uniform product assignments; the distinguished value means "selected". -/
abbrev Outcome (n K : ℕ) := Triple n → Fin K

/-- A bad event as a cylinder in the finite product space. -/
def badEvent {n t K : ℕ} (selected : Fin K) (i : BadIndex n t) :
    Finset (Outcome n K) :=
  match i with
  | Sum.inl _ => constraintEvent (support i) {selected}
  | Sum.inr _ => constraintEvent (support i) (Finset.univ.erase selected)

lemma badEvent_dependsOn {n t K : ℕ} [NeZero K]
    (selected : Fin K) (i : BadIndex n t) :
    Cylinder.DependsOn (badEvent selected i) (support i) := by
  cases i with
  | inl a => exact constraintEvent_dependsOn _ _
  | inr S => exact constraintEvent_dependsOn _ _

/-- Dependency means that the two cylinder supports overlap. -/
def Dependent {n t : ℕ} (i j : BadIndex n t) : Prop :=
  ¬ Disjoint (support i) (support j)

instance dependentDecidable {n t : ℕ} : DecidableRel (@Dependent n t) :=
  fun _ _ ↦ by
    unfold Dependent
    infer_instance

/-- The exact probability of either kind of bad event. -/
noncomputable def badProbability (K : ℕ) {n t : ℕ} : BadIndex n t → ℝ
  | Sum.inl _ => ((1 : ℝ) / K) ^ 2
  | Sum.inr _ => (((K - 1 : ℕ) : ℝ) / K) ^ (t.choose 3)

lemma uniformProbability_badEvent {n t K : ℕ} [NeZero K]
    (selected : Fin K) (i : BadIndex n t) :
    uniformProbability (badEvent selected i) = badProbability K i := by
  cases i with
  | inl a =>
      rw [badEvent, uniformProbability_constraintEvent, support_overlap_card]
      simp [badProbability]
  | inr S =>
      rw [badEvent, uniformProbability_constraintEvent, support_hole_card]
      have hmem : selected ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ _
      rw [Finset.card_erase_of_mem hmem, Finset.card_univ, Fintype.card_fin]
      rfl

lemma badEvent_independent_of_nonNeighbors {n t K : ℕ} [NeZero K]
    (selected : Fin K) (i : BadIndex n t) (J : Finset (BadIndex n t))
    (hJ : ∀ j ∈ J, ¬ Dependent i j) :
    uniformProbability (badEvent selected i ∩ avoiding (badEvent selected) J) =
      uniformProbability (badEvent selected i) *
        uniformProbability (avoiding (badEvent selected) J) := by
  exact uniformProbability_event_inter_avoiding
    (badEvent selected) support (badEvent_dependsOn selected) i J fun j hj ↦
      Classical.not_not.mp (hJ j hj)

/-- The finite asymmetric local lemma specialized to the two bad-event
families. -/
theorem exists_assignment_avoiding_badEvents
    {n t K : ℕ} [NeZero K] (selected : Fin K)
    (charge : BadIndex n t → ℝ)
    (hcharge0 : ∀ i, 0 ≤ charge i) (hcharge1 : ∀ i, charge i < 1)
    (hcriterion : ∀ i (J : Finset (BadIndex n t)), i ∉ J →
      badProbability K i ≤
        charge i * ∏ j ∈ J.filter (Dependent i), (1 - charge j)) :
    ∃ omega : Outcome n K, ∀ i : BadIndex n t, omega ∉ badEvent selected i := by
  exact exists_avoiding_of_asymmetric
    (badEvent selected) Dependent charge hcharge0 hcharge1
    (fun i J hiJ ↦ by
      rw [uniformProbability_badEvent]
      exact hcriterion i J hiJ)
    (badEvent_independent_of_nonNeighbors selected)

/-- The triple system selected by an assignment. -/
def chosenSystem {n K : ℕ} (selected : Fin K) (omega : Outcome n K) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.filter fun e : Triple n ↦ omega e = selected).image Subtype.val

lemma mem_chosenSystem_iff {n K : ℕ} {selected : Fin K} {omega : Outcome n K}
    {e : Finset (Fin n)} :
    e ∈ chosenSystem selected omega ↔
      ∃ he : e.card = 3, omega ⟨e, he⟩ = selected := by
  classical
  simp only [chosenSystem, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨he, hselected⟩
    exact ⟨⟨e, he⟩, hselected, rfl⟩

lemma chosenSystem_threeUniform {n K : ℕ} (selected : Fin K) (omega : Outcome n K) :
    ∀ e ∈ chosenSystem selected omega, e.card = 3 := by
  intro e he
  exact (mem_chosenSystem_iff.mp he).choose

lemma chosenSystem_linear_of_avoids {n t K : ℕ}
    (selected : Fin K) (omega : Outcome n K)
    (havoid : ∀ i : BadIndex n t, omega ∉ badEvent selected i) :
    ∀ ⦃e⦄, e ∈ chosenSystem selected omega →
      ∀ ⦃f⦄, f ∈ chosenSystem selected omega →
        e ≠ f → (e ∩ f).card ≤ 1 := by
  classical
  intro e he f hf hef
  obtain ⟨he3, heSelected⟩ := mem_chosenSystem_iff.mp he
  obtain ⟨hf3, hfSelected⟩ := mem_chosenSystem_iff.mp hf
  by_contra hinter
  have htwo : 2 ≤ (e ∩ f).card := by omega
  have hneTriple : (⟨e, he3⟩ : Triple n) ≠ ⟨f, hf3⟩ := by
    intro h
    exact hef (congrArg Subtype.val h)
  let a : OverlapIndex n :=
    ⟨(⟨e, he3⟩, ⟨f, hf3⟩), hneTriple, htwo⟩
  exact (havoid (Sum.inl a)) (by
    simp [badEvent, support, constraintEvent, a, heSelected, hfSelected])

lemma chosenSystem_hits_tsets_of_avoids {n t K : ℕ}
    (selected : Fin K) (omega : Outcome n K)
    (havoid : ∀ i : BadIndex n t, omega ∉ badEvent selected i) :
    ∀ S : Finset (Fin n), S.card = t →
      ∃ e ∈ chosenSystem selected omega, e ⊆ S := by
  classical
  intro S hS
  let hole : HoleIndex n t := ⟨S, hS⟩
  have hnot := havoid (Sum.inr hole)
  change omega ∉ constraintEvent
    (Finset.univ.filter fun e : Triple n ↦ e.1 ⊆ S)
    (Finset.univ.erase selected) at hnot
  simp only [constraintEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, not_and, not_forall] at hnot
  obtain ⟨e, heSupport, heSelected⟩ := hnot
  have heSub : e.1 ⊆ S := heSupport
  have heSelected' : omega e = selected := by
    by_contra hne
    exact (heSelected hne) trivial
  have heMem : e.1 ∈ chosenSystem selected omega :=
    mem_chosenSystem_iff.mpr ⟨e.2, heSelected'⟩
  exact ⟨e.1, heMem, heSub⟩

/-- Local-lemma charges satisfying the exact product criterion yield a
linear triple system in which every `t` vertices span an edge. -/
theorem exists_linear_hitting_system_of_charges
    {n t K : ℕ} [NeZero K] (selected : Fin K)
    (charge : BadIndex n t → ℝ)
    (hcharge0 : ∀ i, 0 ≤ charge i) (hcharge1 : ∀ i, charge i < 1)
    (hcriterion : ∀ i (J : Finset (BadIndex n t)), i ∉ J →
      badProbability K i ≤
        charge i * ∏ j ∈ J.filter (Dependent i), (1 - charge j)) :
    ∃ H : Finset (Finset (Fin n)),
      (∀ e ∈ H, e.card = 3) ∧
      (∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1) ∧
      (∀ S : Finset (Fin n), S.card = t → ∃ e ∈ H, e ⊆ S) := by
  obtain ⟨omega, homega⟩ := exists_assignment_avoiding_badEvents
    selected charge hcharge0 hcharge1 hcriterion
  exact ⟨chosenSystem selected omega, chosenSystem_threeUniform selected omega,
    chosenSystem_linear_of_avoids selected omega homega,
    chosenSystem_hits_tsets_of_avoids selected omega homega⟩

end Upper
end Erdos1024

#print axioms Erdos1024.Upper.exists_linear_hitting_system_of_charges
