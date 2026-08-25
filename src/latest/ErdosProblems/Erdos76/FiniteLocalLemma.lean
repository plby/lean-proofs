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
import Mathlib

/-!
# A finite symmetric Lovasz local lemma

This file gives a measure-theory-free local lemma for an explicitly finite
probability space.  It is intended for finite product experiments in nibble
arguments, where independence outside a dependency neighbourhood is most
conveniently expressed as a factorisation of finite sums.
-/

open Finset
open scoped BigOperators

namespace Erdos76
namespace FiniteLocalLemma

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Omega I : Type*} [Fintype Omega] [Fintype I] [DecidableEq I]

/-- The mass of an event in an explicitly finite weighted sample space. -/
def eventMass (mass : Omega → ℝ) (event : Omega → Prop) : ℝ :=
  ∑ omega, if event omega then mass omega else 0

/-- No event with an index in `S` occurs at `omega`. -/
def Avoid (bad : I → Omega → Prop) (S : Finset I) (omega : Omega) : Prop :=
  ∀ i ∈ S, ¬ bad i omega

lemma eventMass_nonneg (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (event : Omega → Prop) :
    0 ≤ eventMass mass event := by
  unfold eventMass
  exact sum_nonneg fun omega _ ↦ by
    split
    · exact hmass omega
    · exact le_rfl

lemma eventMass_mono (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    {event event' : Omega → Prop} (h : ∀ omega, event omega → event' omega) :
    eventMass mass event ≤ eventMass mass event' := by
  unfold eventMass
  apply sum_le_sum
  intro omega _
  by_cases he : event omega
  · simp [he, h omega he]
  · by_cases he' : event' omega <;> simp [he, he', hmass omega]

lemma avoid_anti {bad : I → Omega → Prop} {S T : Finset I} (hTS : T ⊆ S)
    {omega : Omega} (h : Avoid bad S omega) :
    Avoid bad T omega := by
  intro i hiT
  exact h i (hTS hiT)

lemma eventMass_avoid_insert_add (mass : Omega → ℝ) (bad : I → Omega → Prop)
    (i : I) (S : Finset I) :
    eventMass mass (Avoid bad (insert i S)) +
        eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) =
      eventMass mass (Avoid bad S) := by
  unfold eventMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro omega _
  simp only [Avoid, forall_mem_insert]
  by_cases hi : bad i omega <;>
    by_cases hS : ∀ a ∈ S, ¬ bad a omega <;>
      simp [hi, hS] <;> congr

/-- The local hypothesis used by the finite local lemma.  It says that after
conditioning on avoiding any family outside `i`'s dependency neighbourhood,
the unnormalised conditional mass of bad event `i` is at most `p` times the
conditioning mass.  Ordinary independence from all those events, together
with the marginal bound `P(bad i) ≤ p`, implies this hypothesis. -/
def HasLocalBound (mass : Omega → ℝ) (bad : I → Omega → Prop)
    (dependency : I → Finset I) (p : ℝ) : Prop :=
  ∀ (i : I) (S : Finset I), i ∉ S → Disjoint S (dependency i) →
    eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
      p * eventMass mass (Avoid bad S)

/-- Factorisation outside dependency neighbourhoods. -/
def IndependentOutside (mass : Omega → ℝ) (bad : I → Omega → Prop)
    (dependency : I → Finset I) : Prop :=
  ∀ (i : I) (S : Finset I), i ∉ S → Disjoint S (dependency i) →
    eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) =
      eventMass mass (bad i) * eventMass mass (Avoid bad S)

lemma hasLocalBound_of_independentOutside
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (bad : I → Omega → Prop) (dependency : I → Finset I) {p : ℝ}
    (hindep : IndependentOutside mass bad dependency)
    (hmarginal : ∀ i, eventMass mass (bad i) ≤ p) :
    HasLocalBound mass bad dependency p := by
  intro i S hiS hdisj
  rw [hindep i S hiS hdisj]
  exact mul_le_mul_of_nonneg_right (hmarginal i)
    (eventMass_nonneg mass hmass (Avoid bad S))

private lemma conditional_event_le
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    {p x : ℝ} {d : ℕ}
    (hp : 0 ≤ p) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hparameter : p ≤ x * (1 - x) ^ d)
    (hdegree : ∀ i, (dependency i).card ≤ d)
    (hlocal : HasLocalBound mass bad dependency p)
    (S : Finset I) (i : I) (hiS : i ∉ S) :
    eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
      x * eventMass mass (Avoid bad S) := by
  induction hcard : S.card using Nat.strong_induction_on generalizing S i with
  | h n ih =>
      let T := S \ dependency i
      let R := S ∩ dependency i
      have hTS : T ⊆ S := sdiff_subset
      have hRS : R ⊆ S := inter_subset_left
      have hTR : T ∪ R = S := by
        ext j
        simp only [T, R, mem_union, mem_sdiff, mem_inter]
        tauto
      have hiT : i ∉ T := fun hi ↦ hiS (hTS hi)
      have hTdisj : Disjoint T (dependency i) := by
        rw [Finset.disjoint_iff_inter_eq_empty]
        ext j
        simp [T]
      have hnum_mono :
          eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
            eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad T omega) := by
        apply eventMass_mono mass hmass
        intro omega homega
        exact ⟨homega.1, avoid_anti hTS homega.2⟩
      have hnum_local :
          eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad T omega) ≤
            p * eventMass mass (Avoid bad T) :=
        hlocal i T hiT hTdisj
      have hxbase0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1.le
      have hxbase1 : 1 - x ≤ 1 := by linarith
      have hRcard : R.card ≤ d :=
        (card_le_card inter_subset_right).trans (hdegree i)
      have hlower_aux : ∀ U : Finset I, U ⊆ R →
          (1 - x) ^ U.card * eventMass mass (Avoid bad T) ≤
            eventMass mass (Avoid bad (T ∪ U)) := by
        intro U
        induction U using Finset.induction_on with
        | empty =>
            intro _
            simp
        | @insert j U hj ihU =>
            intro hsub
            have hjR : j ∈ R := hsub (mem_insert_self j U)
            have hUR : U ⊆ R := fun a ha ↦ hsub (mem_insert_of_mem ha)
            have hjS : j ∈ S := hRS hjR
            have hjdep : j ∈ dependency i := (mem_inter.mp hjR).2
            have hjT : j ∉ T := by simp [T, hjdep]
            have hjTU : j ∉ T ∪ U := by simp [hjT, hj]
            have hTUS : T ∪ U ⊆ S := by
              intro a ha
              rcases mem_union.mp ha with haT | haU
              · exact hTS haT
              · exact hRS (hUR haU)
            have hcard_lt : (T ∪ U).card < n := by
              rw [← hcard]
              exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTUS, by
                intro heq
                have : j ∈ T ∪ U := heq.symm ▸ hjS
                exact hjTU this⟩)
            have hcond := ih (T ∪ U).card hcard_lt (T ∪ U) j hjTU rfl
            have hstep :
                (1 - x) * eventMass mass (Avoid bad (T ∪ U)) ≤
                  eventMass mass (Avoid bad (insert j (T ∪ U))) := by
              have hid := eventMass_avoid_insert_add mass bad j (T ∪ U)
              linarith
            calc
              (1 - x) ^ (insert j U).card * eventMass mass (Avoid bad T) =
                  (1 - x) *
                    ((1 - x) ^ U.card * eventMass mass (Avoid bad T)) := by
                    rw [card_insert_of_notMem hj, pow_succ]
                    ring
              _ ≤ (1 - x) * eventMass mass (Avoid bad (T ∪ U)) :=
                mul_le_mul_of_nonneg_left (ihU hUR) hxbase0
              _ ≤ eventMass mass (Avoid bad (insert j (T ∪ U))) := hstep
              _ = eventMass mass (Avoid bad (T ∪ insert j U)) := by
                congr 2
                ext a
                simp [or_left_comm, or_assoc]
      have hlower :
          (1 - x) ^ R.card * eventMass mass (Avoid bad T) ≤
            eventMass mass (Avoid bad S) := by
        simpa only [hTR] using hlower_aux R Subset.rfl
      have hmassT : 0 ≤ eventMass mass (Avoid bad T) :=
        eventMass_nonneg mass hmass _
      calc
        eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
            p * eventMass mass (Avoid bad T) := hnum_mono.trans hnum_local
        _ ≤ (x * (1 - x) ^ d) * eventMass mass (Avoid bad T) :=
          mul_le_mul_of_nonneg_right hparameter hmassT
        _ ≤ (x * (1 - x) ^ R.card) * eventMass mass (Avoid bad T) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one hxbase0 hxbase1 hRcard) hx0)
            hmassT
        _ = x * ((1 - x) ^ R.card * eventMass mass (Avoid bad T)) := by ring
        _ ≤ x * eventMass mass (Avoid bad S) :=
          mul_le_mul_of_nonneg_left hlower hx0

/-- **Finite symmetric Lovasz local lemma**, in the standard
`p ≤ x(1-x)^d` form.

The dependency neighbourhoods need not be symmetric; only their cardinality
and the stated local conditional bound are used.  The conclusion supplies an
actual point of the finite sample space at which no bad event occurs. -/
theorem exists_avoiding_all
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_total : ∑ omega, mass omega = 1)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    {p x : ℝ} {d : ℕ}
    (hp : 0 ≤ p) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hparameter : p ≤ x * (1 - x) ^ d)
    (hdegree : ∀ i, (dependency i).card ≤ d)
    (hlocal : HasLocalBound mass bad dependency p) :
    ∃ omega, ∀ i, ¬ bad i omega := by
  have hcond : ∀ (S : Finset I) (i : I), i ∉ S →
      eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
        x * eventMass mass (Avoid bad S) :=
    conditional_event_le mass hmass bad dependency hp hx0 hx1 hparameter
      hdegree hlocal
  have hAvoidLower : ∀ S : Finset I,
      (1 - x) ^ S.card ≤ eventMass mass (Avoid bad S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa [eventMass, Avoid] using hmass_total.ge
    | @insert i S hiS ihS =>
        have hstep :
            (1 - x) * eventMass mass (Avoid bad S) ≤
              eventMass mass (Avoid bad (insert i S)) := by
          have hc := hcond S i hiS
          have hid := eventMass_avoid_insert_add mass bad i S
          linarith
        calc
          (1 - x) ^ (insert i S).card = (1 - x) * (1 - x) ^ S.card := by
            rw [card_insert_of_notMem hiS, pow_succ]
            ring
          _ ≤ (1 - x) * eventMass mass (Avoid bad S) :=
            mul_le_mul_of_nonneg_left ihS (sub_nonneg.mpr hx1.le)
          _ ≤ eventMass mass (Avoid bad (insert i S)) := hstep
  by_contra hnone
  push_neg at hnone
  have hzero : eventMass mass (Avoid bad (univ : Finset I)) = 0 := by
    unfold eventMass
    apply sum_eq_zero
    intro omega _
    have hnot : ¬ Avoid bad (univ : Finset I) omega := by
      intro hAvoid
      obtain ⟨i, hi⟩ := hnone omega
      exact hAvoid i (mem_univ i) hi
    simp [hnot]
  have hpos : 0 < (1 - x) ^ (univ : Finset I).card :=
    pow_pos (sub_pos.mpr hx1) _
  have := hAvoidLower (univ : Finset I)
  rw [hzero] at this
  linarith

/-- Convenient wrapper using ordinary factorisation outside dependency
neighbourhoods and a uniform marginal bound. -/
theorem exists_avoiding_all_of_independentOutside
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_total : ∑ omega, mass omega = 1)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    {p x : ℝ} {d : ℕ}
    (hp : 0 ≤ p) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hparameter : p ≤ x * (1 - x) ^ d)
    (hdegree : ∀ i, (dependency i).card ≤ d)
    (hindep : IndependentOutside mass bad dependency)
    (hmarginal : ∀ i, eventMass mass (bad i) ≤ p) :
    ∃ omega, ∀ i, ¬ bad i omega := by
  exact exists_avoiding_all mass hmass hmass_total bad dependency hp hx0 hx1
    hparameter hdegree
    (hasLocalBound_of_independentOutside mass hmass bad dependency hindep hmarginal)

end

end FiniteLocalLemma
end Erdos76
