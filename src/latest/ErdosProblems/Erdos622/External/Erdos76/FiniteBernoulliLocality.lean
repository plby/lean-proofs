/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.External.Erdos76.FiniteLocalLemma
import ErdosProblems.Erdos622.External.Erdos76.Kahn

/-!
# Local events in a finite Bernoulli product space

This file supplies the product-space bridge for `FiniteLocalLemma`.  An event
on finite subsets depends on a coordinate set when changing all other
coordinates preserves the event.  Events on disjoint coordinate sets have
exactly factorising Bernoulli mass.  Consequently, a graph containing every
overlap of coordinate supports is a dependency graph in the sense required by
the finite local lemma.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace FiniteNibble

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E I : Type*} [Fintype E] [DecidableEq E]

/-- Two outcomes agree on `R` when they select the same coordinates of `R`. -/
def AgreesOn (R S T : Finset E) : Prop := S ∩ R = T ∩ R

/-- An event depends only on the coordinates in `R`. -/
def EventDependsOn (R : Finset E) (event : Finset E → Prop) : Prop :=
  ∀ S T, AgreesOn R S T → (event S ↔ event T)

lemma agreesOn_refl (R S : Finset E) : AgreesOn R S S := rfl

lemma agreesOn_symm {R S T : Finset E} (h : AgreesOn R S T) : AgreesOn R T S := h.symm

lemma agreesOn_trans {R S T V : Finset E}
    (hST : AgreesOn R S T) (hTV : AgreesOn R T V) : AgreesOn R S V :=
  hST.trans hTV

lemma agreesOn_mono {R R' S T : Finset E} (hRR' : R ⊆ R')
    (h : AgreesOn R' S T) : AgreesOn R S T := by
  unfold AgreesOn at h ⊢
  ext e
  have hmem : e ∈ S ∩ R' ↔ e ∈ T ∩ R' := by rw [h]
  simp only [mem_inter] at hmem ⊢
  constructor
  · rintro ⟨heS, heR⟩
    exact ⟨(hmem.mp ⟨heS, hRR' heR⟩).1, heR⟩
  · rintro ⟨heT, heR⟩
    exact ⟨(hmem.mpr ⟨heT, hRR' heR⟩).1, heR⟩

lemma eventDependsOn_mono {R R' : Finset E} {event : Finset E → Prop}
    (hRR' : R ⊆ R') (h : EventDependsOn R event) : EventDependsOn R' event := by
  intro S T hST
  exact h S T (agreesOn_mono hRR' hST)

lemma eventDependsOn_true (R : Finset E) : EventDependsOn R (fun _ ↦ True) := by
  intro S T hST
  simp

lemma eventDependsOn_and {R T : Finset E} {A B : Finset E → Prop}
    (hA : EventDependsOn R A) (hB : EventDependsOn T B) :
    EventDependsOn (R ∪ T) (fun S ↦ A S ∧ B S) := by
  intro S V hSV
  have hR : AgreesOn R S V := agreesOn_mono subset_union_left hSV
  have hT : AgreesOn T S V := agreesOn_mono subset_union_right hSV
  exact and_congr (hA S V hR) (hB S V hT)

/-- The finite type of subsets of `U`. -/
abbrev Subsets (U : Finset E) := {S : Finset E // S ⊆ U}

/-- Identify subsets of `U` with the attached elements of `U.powerset`. -/
def subsetsEquivPowersetAttach (U : Finset E) :
    Subsets U ≃ ↥U.powerset :=
  Equiv.subtypeEquivRight (by intro S; simp)

/-- A subset of the full coordinate set is just an arbitrary finite subset. -/
def subsetsUnivEquiv : Subsets (Finset.univ : Finset E) ≃ Finset E where
  toFun S := S.1
  invFun S := ⟨S, subset_univ S⟩
  left_inv S := Subtype.ext rfl
  right_inv S := rfl

/-- Splitting a subset of a disjoint union into its two coordinate blocks. -/
def disjointSubsetsEquiv {U V : Finset E} (hUV : Disjoint U V) :
    Subsets (U ∪ V) ≃ Subsets U × Subsets V where
  toFun S :=
    (⟨S.1 ∩ U, inter_subset_right⟩, ⟨S.1 ∩ V, inter_subset_right⟩)
  invFun P := ⟨P.1.1 ∪ P.2.1, union_subset_union P.1.2 P.2.2⟩
  left_inv S := by
    apply Subtype.ext
    ext e
    simp only [mem_union, mem_inter]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro heS
      have hsplit : e ∈ U ∨ e ∈ V := by
        simpa only [mem_union] using S.2 heS
      rcases hsplit with heU | heV
      · exact Or.inl ⟨heS, heU⟩
      · exact Or.inr ⟨heS, heV⟩
  right_inv P := by
    rcases P with ⟨A, B⟩
    apply Prod.ext
    · apply Subtype.ext
      ext e
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨heA | heB, heU⟩
        · exact heA
        · exact False.elim ((Finset.disjoint_left.mp hUV) heU (B.2 heB))
      · intro heA
        exact ⟨Or.inl heA, A.2 heA⟩
    · apply Subtype.ext
      ext e
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨heA | heB, heV⟩
        · exact False.elim ((Finset.disjoint_left.mp hUV) (A.2 heA) heV)
        · exact heB
      · intro heB
        exact ⟨Or.inr heB, B.2 heB⟩

/-- Bernoulli mass of an event restricted to coordinates in `U`. -/
def restrictedEventMass (U : Finset E) (p : E → ℝ) (event : Finset E → Prop) : ℝ :=
  ∑ S : Subsets U, if event S.1 then bernoulliMass U p S.1 else 0

lemma sum_restricted_bernoulliMass (U : Finset E) (p : E → ℝ) :
    ∑ S : Subsets U, bernoulliMass U p S.1 = 1 := by
  calc
    (∑ S : Subsets U, bernoulliMass U p S.1) =
        ∑ S : ↥U.powerset, bernoulliMass U p S.1 := by
      apply Fintype.sum_equiv (subsetsEquivPowersetAttach U)
      intro S
      rfl
    _ = ∑ S ∈ U.powerset, bernoulliMass U p S := by
      simpa using
        (Finset.sum_attach U.powerset
          (fun S : Finset E ↦ bernoulliMass U p S))
    _ = 1 := sum_bernoulliMass U p

lemma restrictedEventMass_true (U : Finset E) (p : E → ℝ) :
    restrictedEventMass U p (fun _ ↦ True) = 1 := by
  unfold restrictedEventMass
  simpa using sum_restricted_bernoulliMass U p

/-- The `eventMass` sample space of all finite subsets agrees with the
restricted construction on the full coordinate set. -/
lemma eventMass_eq_restrictedEventMass_univ (p : E → ℝ)
    (event : Finset E → Prop) :
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S) event =
      restrictedEventMass Finset.univ p event := by
  unfold FiniteLocalLemma.eventMass restrictedEventMass
  symm
  apply Fintype.sum_equiv subsetsUnivEquiv
  intro S
  by_cases h : event S.1 <;> simp [h, subsetsUnivEquiv]

lemma bernoulliMass_union_of_disjoint {U V A B : Finset E} {p : E → ℝ}
    (hUV : Disjoint U V) (hA : A ⊆ U) (hB : B ⊆ V) :
    bernoulliMass (U ∪ V) p (A ∪ B) =
      bernoulliMass U p A * bernoulliMass V p B := by
  have hAB : Disjoint A B := hUV.mono hA hB
  have hdiff : (U ∪ V) \ (A ∪ B) = (U \ A) ∪ (V \ B) := by
    ext e
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨heU | heV, hnot⟩
      · exact Or.inl ⟨heU, fun heA ↦ hnot (Or.inl heA)⟩
      · exact Or.inr ⟨heV, fun heB ↦ hnot (Or.inr heB)⟩
    · rintro (⟨heU, heA⟩ | ⟨heV, heB⟩)
      · refine ⟨Or.inl heU, ?_⟩
        rintro (hAe | hBe)
        · exact heA hAe
        · exact (Finset.disjoint_left.mp hUV) heU (hB hBe)
      · refine ⟨Or.inr heV, ?_⟩
        rintro (hAe | hBe)
        · exact (Finset.disjoint_left.mp hUV) (hA hAe) heV
        · exact heB hBe
  have hdiffDisj : Disjoint (U \ A) (V \ B) :=
    hUV.mono sdiff_subset sdiff_subset
  simp only [bernoulliMass, prod_union hAB, hdiff, prod_union hdiffDisj]
  ring

/-- Exact product factorisation for two local events on disjoint restricted
coordinate spaces. -/
lemma restrictedEventMass_and_of_disjoint {U V : Finset E} {p : E → ℝ}
    {A B : Finset E → Prop} (hUV : Disjoint U V)
    (hA : EventDependsOn U A) (hB : EventDependsOn V B) :
    restrictedEventMass (U ∪ V) p (fun S ↦ A S ∧ B S) =
      restrictedEventMass U p A * restrictedEventMass V p B := by
  let split : Subsets (U ∪ V) ≃ Subsets U × Subsets V :=
    disjointSubsetsEquiv hUV
  let summand : Subsets (U ∪ V) → ℝ := fun S ↦
    if A S.1 ∧ B S.1 then bernoulliMass (U ∪ V) p S.1 else 0
  calc
    restrictedEventMass (U ∪ V) p (fun S ↦ A S ∧ B S) =
        ∑ S : Subsets (U ∪ V), summand S := by
      unfold restrictedEventMass
      apply sum_congr rfl
      intro S _
      by_cases h : A S.1 ∧ B S.1 <;> simp [summand, h]
    _ = ∑ P : Subsets U × Subsets V, summand (split.symm P) := by
      apply Fintype.sum_equiv split
      intro S
      simp only [Equiv.symm_apply_apply]
    _ = ∑ X : Subsets U, ∑ Y : Subsets V, summand (split.symm (X, Y)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ X : Subsets U, ∑ Y : Subsets V,
        (if A X.1 then bernoulliMass U p X.1 else 0) *
          (if B Y.1 then bernoulliMass V p Y.1 else 0) := by
      apply sum_congr rfl
      intro X _
      apply sum_congr rfl
      intro Y _
      have hsplit : (split.symm (X, Y)).1 = X.1 ∪ Y.1 := rfl
      have hAgreeA : AgreesOn U (X.1 ∪ Y.1) X.1 := by
        unfold AgreesOn
        ext e
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨heX | heY, heU⟩
          · exact ⟨heX, X.2 heX⟩
          · exact False.elim ((Finset.disjoint_left.mp hUV) heU (Y.2 heY))
        · rintro ⟨heX, heU⟩
          exact ⟨Or.inl heX, heU⟩
      have hAgreeB : AgreesOn V (X.1 ∪ Y.1) Y.1 := by
        unfold AgreesOn
        ext e
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨heX | heY, heV⟩
          · exact False.elim ((Finset.disjoint_left.mp hUV) (X.2 heX) heV)
          · exact ⟨heY, Y.2 heY⟩
        · rintro ⟨heY, heV⟩
          exact ⟨Or.inr heY, heV⟩
      have hAE : A (X.1 ∪ Y.1) ↔ A X.1 := hA _ _ hAgreeA
      have hBE : B (X.1 ∪ Y.1) ↔ B Y.1 := hB _ _ hAgreeB
      rw [show summand (split.symm (X, Y)) =
          if A (X.1 ∪ Y.1) ∧ B (X.1 ∪ Y.1) then
            bernoulliMass (U ∪ V) p (X.1 ∪ Y.1) else 0 by
              change (if A (split.symm (X, Y)).1 ∧ B (split.symm (X, Y)).1 then
                bernoulliMass (U ∪ V) p (split.symm (X, Y)).1 else 0) = _
              rw [hsplit]]
      rw [bernoulliMass_union_of_disjoint hUV X.2 Y.2]
      by_cases hAX : A X.1 <;> by_cases hBY : B Y.1 <;>
        simp_all
    _ = (∑ X : Subsets U, if A X.1 then bernoulliMass U p X.1 else 0) *
        ∑ Y : Subsets V, if B Y.1 then bernoulliMass V p Y.1 else 0 := by
      rw [sum_mul]
      apply sum_congr rfl
      intro X _
      rw [mul_sum]
    _ = restrictedEventMass U p A * restrictedEventMass V p B := by
      rfl

/-- Marginalising all coordinates outside a local event's support does not
change its Bernoulli mass. -/
lemma eventMass_eq_restrictedEventMass {R : Finset E} {p : E → ℝ}
    {event : Finset E → Prop} (hlocal : EventDependsOn R event) :
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S) event =
      restrictedEventMass R p event := by
  calc
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S) event =
        restrictedEventMass Finset.univ p event :=
      eventMass_eq_restrictedEventMass_univ p event
    _ = restrictedEventMass R p event := by
      have hfactor := restrictedEventMass_and_of_disjoint
        (p := p) (U := R) (V := Finset.univ \ R)
        (A := event) (B := fun _ ↦ True) Finset.disjoint_sdiff hlocal
        (eventDependsOn_true (Finset.univ \ R))
      have hcover : R ∪ (Finset.univ \ R) = (Finset.univ : Finset E) :=
        union_sdiff_of_subset (subset_univ R)
      rw [hcover] at hfactor
      simpa [restrictedEventMass_true] using hfactor

/-- Events supported on disjoint coordinate sets have exactly factorising
mass in the full finite Bernoulli product space. -/
theorem eventMass_and_of_disjoint {R T : Finset E} {p : E → ℝ}
    {A B : Finset E → Prop} (hRT : Disjoint R T)
    (hA : EventDependsOn R A) (hB : EventDependsOn T B) :
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S)
        (fun S ↦ A S ∧ B S) =
      FiniteLocalLemma.eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) A *
        FiniteLocalLemma.eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) B := by
  calc
    FiniteLocalLemma.eventMass
        (fun S : Finset E ↦ bernoulliMass Finset.univ p S)
        (fun S ↦ A S ∧ B S) =
        restrictedEventMass (R ∪ T) p (fun S ↦ A S ∧ B S) :=
      eventMass_eq_restrictedEventMass (eventDependsOn_and hA hB)
    _ = restrictedEventMass R p A * restrictedEventMass T p B :=
      restrictedEventMass_and_of_disjoint hRT hA hB
    _ = FiniteLocalLemma.eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) A *
        FiniteLocalLemma.eventMass
          (fun S : Finset E ↦ bernoulliMass Finset.univ p S) B := by
      rw [eventMass_eq_restrictedEventMass hA,
        eventMass_eq_restrictedEventMass hB]

variable [Fintype I] [DecidableEq I]

/-- Avoiding a finite family of local events depends only on the union of
their coordinate supports. -/
lemma eventDependsOn_avoid {R : I → Finset E} {bad : I → Finset E → Prop}
    (hlocal : ∀ i, EventDependsOn (R i) (bad i)) (J : Finset I) :
    EventDependsOn (J.biUnion R) (FiniteLocalLemma.Avoid bad J) := by
  intro S T hST
  constructor
  · intro hAvoid j hj hbadT
    have hjAgree : AgreesOn (R j) S T :=
      agreesOn_mono (subset_biUnion_of_mem R hj) hST
    exact hAvoid j hj ((hlocal j S T hjAgree).mpr hbadT)
  · intro hAvoid j hj hbadS
    have hjAgree : AgreesOn (R j) S T :=
      agreesOn_mono (subset_biUnion_of_mem R hj) hST
    exact hAvoid j hj ((hlocal j S T hjAgree).mp hbadS)

/-- `dependency` contains the overlap graph of the coordinate supports.  The
diagonal is deliberately excluded, matching the local lemma's use of sets not
containing the distinguished event. -/
def ContainsSupportOverlaps (R : I → Finset E)
    (dependency : I → Finset I) : Prop :=
  ∀ i j, i ≠ j → ¬ Disjoint (R i) (R j) → j ∈ dependency i

lemma support_disjoint_biUnion_outside {R : I → Finset E}
    {dependency : I → Finset I} (hoverlap : ContainsSupportOverlaps R dependency)
    {i : I} {J : Finset I} (hiJ : i ∉ J) (houtside : Disjoint J (dependency i)) :
    Disjoint (R i) (J.biUnion R) := by
  rw [Finset.disjoint_left]
  intro e hei heJ
  obtain ⟨j, hjJ, hej⟩ := mem_biUnion.mp heJ
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hiJ hjJ
  have hjOutside : j ∉ dependency i := by
    intro hjDep
    exact (Finset.disjoint_left.mp houtside) hjJ hjDep
  have hijDisjoint : Disjoint (R i) (R j) := by
    by_contra hnot
    exact hjOutside (hoverlap i j hij hnot)
  exact (Finset.disjoint_left.mp hijDisjoint) hei hej

/-- A dependency graph containing every overlap of supports gives exact
independence outside each dependency neighbourhood. -/
theorem independentOutside_of_eventDependsOn
    (p : E → ℝ) (R : I → Finset E) (bad : I → Finset E → Prop)
    (dependency : I → Finset I)
    (hlocal : ∀ i, EventDependsOn (R i) (bad i))
    (hoverlap : ContainsSupportOverlaps R dependency) :
    FiniteLocalLemma.IndependentOutside
      (fun S : Finset E ↦ bernoulliMass Finset.univ p S) bad dependency := by
  intro i J hiJ houtside
  exact eventMass_and_of_disjoint
    (support_disjoint_biUnion_outside hoverlap hiJ houtside)
    (hlocal i) (eventDependsOn_avoid hlocal J)

/-- The local-bound interface needed by the finite local lemma follows from
local coordinate supports, an overlap dependency graph, and marginal event
bounds. -/
theorem hasLocalBound_of_eventDependsOn
    (p : E → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (R : I → Finset E) (bad : I → Finset E → Prop)
    (dependency : I → Finset I) {bound : ℝ}
    (hlocal : ∀ i, EventDependsOn (R i) (bad i))
    (hoverlap : ContainsSupportOverlaps R dependency)
    (hmarginal : ∀ i, FiniteLocalLemma.eventMass
      (fun S : Finset E ↦ bernoulliMass Finset.univ p S) (bad i) ≤ bound) :
    FiniteLocalLemma.HasLocalBound
      (fun S : Finset E ↦ bernoulliMass Finset.univ p S) bad dependency bound := by
  apply FiniteLocalLemma.hasLocalBound_of_independentOutside
    (fun S : Finset E ↦ bernoulliMass Finset.univ p S)
  · intro S
    exact bernoulliMass_nonneg (subset_univ S)
      (fun e _ ↦ hp0 e) (fun e _ ↦ hp1 e)
  · exact independentOutside_of_eventDependsOn p R bad dependency hlocal hoverlap
  · exact hmarginal

end

end FiniteNibble
end Erdos76
