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
import ErdosProblems.Erdos622.External.Erdos76.FiniteBernoulliLocality

/-!
# A finite asymmetric local lemma for Alon's linear-arboricity argument

Alon's independent-transversal proposition uses two kinds of bad event, with
different marginal bounds and different local-lemma parameters.  The symmetric
finite local lemma in `Erdos76` therefore does not directly express the
argument.  This file proves the fully asymmetric finite version over the same
explicit weighted sample spaces.

The dependency neighbourhoods need not be symmetric.  The only probabilistic
hypothesis is the unnormalised conditional inequality in
`HasAsymmetricLocalBound`; the Bernoulli-coordinate layer can discharge it by
exact factorisation outside the declared supports.
-/

open Finset
open scoped BigOperators
open Erdos76.FiniteLocalLemma

namespace Erdos622
namespace AlonLLL

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Omega I : Type*} [Fintype Omega] [Fintype I] [DecidableEq I]

/-- The asymmetric local-bound hypothesis: bad event `i` has its own bound
`p i`, rather than sharing one uniform marginal bound with every event. -/
def HasAsymmetricLocalBound (mass : Omega → ℝ) (bad : I → Omega → Prop)
    (dependency : I → Finset I) (p : I → ℝ) : Prop :=
  ∀ (i : I) (S : Finset I), i ∉ S → Disjoint S (dependency i) →
    eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
      p i * eventMass mass (Avoid bad S)

/-- Exact factorisation outside the dependency neighbourhood, plus individual
marginal bounds, supplies the asymmetric local-bound interface. -/
lemma hasAsymmetricLocalBound_of_independentOutside
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (bad : I → Omega → Prop) (dependency : I → Finset I) (p : I → ℝ)
    (hindep : IndependentOutside mass bad dependency)
    (hmarginal : ∀ i, eventMass mass (bad i) ≤ p i) :
    HasAsymmetricLocalBound mass bad dependency p := by
  intro i S hiS hdisj
  rw [hindep i S hiS hdisj]
  exact mul_le_mul_of_nonneg_right (hmarginal i)
    (Erdos76.FiniteLocalLemma.eventMass_nonneg mass hmass (Avoid bad S))

private lemma conditional_event_le
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    (p x : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hparameter : ∀ i,
      p i ≤ x i * ∏ j ∈ dependency i, (1 - x j))
    (hlocal : HasAsymmetricLocalBound mass bad dependency p)
    (S : Finset I) (i : I) (hiS : i ∉ S) :
    eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
      x i * eventMass mass (Avoid bad S) := by
  induction hcard : S.card using Nat.strong_induction_on generalizing S i with
  | h n ih =>
      let T := S \ dependency i
      let R := S ∩ dependency i
      have hTS : T ⊆ S := sdiff_subset
      have hRS : R ⊆ S := inter_subset_left
      have hRdep : R ⊆ dependency i := inter_subset_right
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
        apply Erdos76.FiniteLocalLemma.eventMass_mono mass hmass
        intro omega homega
        exact ⟨homega.1,
          Erdos76.FiniteLocalLemma.avoid_anti hTS homega.2⟩
      have hnum_local :
          eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad T omega) ≤
            p i * eventMass mass (Avoid bad T) :=
        hlocal i T hiT hTdisj
      have hfactor0 : ∀ j, 0 ≤ 1 - x j := fun j ↦ sub_nonneg.mpr (hx1 j).le
      have hfactor1 : ∀ j, 1 - x j ≤ 1 := fun j ↦ by linarith [hx0 j]
      have hprod_mono :
          (∏ j ∈ dependency i, (1 - x j)) ≤
            ∏ j ∈ R, (1 - x j) := by
        exact Finset.prod_le_prod_of_subset_of_le_one hRdep
          (fun j _ ↦ hfactor0 j) (fun j _ _ ↦ hfactor1 j)
      have hlower_aux : ∀ U : Finset I, U ⊆ R →
          (∏ j ∈ U, (1 - x j)) * eventMass mass (Avoid bad T) ≤
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
            have hjdep : j ∈ dependency i := hRdep hjR
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
                (1 - x j) * eventMass mass (Avoid bad (T ∪ U)) ≤
                  eventMass mass (Avoid bad (insert j (T ∪ U))) := by
              have hid := Erdos76.FiniteLocalLemma.eventMass_avoid_insert_add
                mass bad j (T ∪ U)
              linarith
            calc
              (∏ a ∈ insert j U, (1 - x a)) *
                    eventMass mass (Avoid bad T) =
                  (1 - x j) *
                    ((∏ a ∈ U, (1 - x a)) *
                      eventMass mass (Avoid bad T)) := by
                    rw [prod_insert hj]
                    ring
              _ ≤ (1 - x j) * eventMass mass (Avoid bad (T ∪ U)) :=
                mul_le_mul_of_nonneg_left (ihU hUR) (hfactor0 j)
              _ ≤ eventMass mass (Avoid bad (insert j (T ∪ U))) := hstep
              _ = eventMass mass (Avoid bad (T ∪ insert j U)) := by
                congr 2
                ext a
                simp [or_left_comm, or_assoc]
      have hlower :
          (∏ j ∈ R, (1 - x j)) * eventMass mass (Avoid bad T) ≤
            eventMass mass (Avoid bad S) := by
        simpa only [hTR] using hlower_aux R Subset.rfl
      have hmassT : 0 ≤ eventMass mass (Avoid bad T) :=
        Erdos76.FiniteLocalLemma.eventMass_nonneg mass hmass _
      calc
        eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
            p i * eventMass mass (Avoid bad T) := hnum_mono.trans hnum_local
        _ ≤ (x i * ∏ j ∈ dependency i, (1 - x j)) *
              eventMass mass (Avoid bad T) :=
          mul_le_mul_of_nonneg_right (hparameter i) hmassT
        _ ≤ (x i * ∏ j ∈ R, (1 - x j)) *
              eventMass mass (Avoid bad T) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprod_mono (hx0 i)) hmassT
        _ = x i * ((∏ j ∈ R, (1 - x j)) *
              eventMass mass (Avoid bad T)) := by ring
        _ ≤ x i * eventMass mass (Avoid bad S) :=
          mul_le_mul_of_nonneg_left hlower (hx0 i)

/-- **Finite asymmetric Lovasz local lemma.**

If each event has conditional mass at most `p i` away from its dependency
neighbourhood and `p i ≤ x i * ∏ j ∈ dependency i, (1 - x j)`, then some
point avoids all bad events. -/
theorem exists_avoiding_all
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_total : ∑ omega, mass omega = 1)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    (p x : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hparameter : ∀ i,
      p i ≤ x i * ∏ j ∈ dependency i, (1 - x j))
    (hlocal : HasAsymmetricLocalBound mass bad dependency p) :
    ∃ omega, ∀ i, ¬ bad i omega := by
  have hcond : ∀ (S : Finset I) (i : I), i ∉ S →
      eventMass mass (fun omega ↦ bad i omega ∧ Avoid bad S omega) ≤
        x i * eventMass mass (Avoid bad S) :=
    conditional_event_le mass hmass bad dependency p x hp hx0 hx1
      hparameter hlocal
  have hAvoidLower : ∀ S : Finset I,
      (∏ i ∈ S, (1 - x i)) ≤ eventMass mass (Avoid bad S) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        simpa [eventMass, Avoid] using hmass_total.ge
    | @insert i S hiS ihS =>
        have hstep :
            (1 - x i) * eventMass mass (Avoid bad S) ≤
              eventMass mass (Avoid bad (insert i S)) := by
          have hc := hcond S i hiS
          have hid := Erdos76.FiniteLocalLemma.eventMass_avoid_insert_add
            mass bad i S
          linarith
        calc
          (∏ j ∈ insert i S, (1 - x j)) =
              (1 - x i) * ∏ j ∈ S, (1 - x j) := by rw [prod_insert hiS]
          _ ≤ (1 - x i) * eventMass mass (Avoid bad S) :=
            mul_le_mul_of_nonneg_left ihS (sub_nonneg.mpr (hx1 i).le)
          _ ≤ eventMass mass (Avoid bad (insert i S)) := hstep
  by_contra hnone
  push_neg at hnone
  have hzero : eventMass mass (Avoid bad (univ : Finset I)) = 0 := by
    unfold Erdos76.FiniteLocalLemma.eventMass
    apply sum_eq_zero
    intro omega _
    have hnot : ¬ Avoid bad (univ : Finset I) omega := by
      intro hAvoid
      obtain ⟨i, hi⟩ := hnone omega
      exact hAvoid i (mem_univ i) hi
    simp [hnot]
  have hpos : 0 < ∏ i : I, (1 - x i) :=
    prod_pos fun i _ ↦ sub_pos.mpr (hx1 i)
  have h := hAvoidLower (univ : Finset I)
  rw [hzero] at h
  simpa using (not_lt_of_ge h hpos)

/-- Convenient asymmetric wrapper using exact independence outside dependency
neighbourhoods and individual marginal bounds. -/
theorem exists_avoiding_all_of_independentOutside
    (mass : Omega → ℝ) (hmass : ∀ omega, 0 ≤ mass omega)
    (hmass_total : ∑ omega, mass omega = 1)
    (bad : I → Omega → Prop) (dependency : I → Finset I)
    (p x : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hparameter : ∀ i,
      p i ≤ x i * ∏ j ∈ dependency i, (1 - x j))
    (hindep : IndependentOutside mass bad dependency)
    (hmarginal : ∀ i, eventMass mass (bad i) ≤ p i) :
    ∃ omega, ∀ i, ¬ bad i omega := by
  exact exists_avoiding_all mass hmass hmass_total bad dependency p x hp hx0 hx1
    hparameter
    (hasAsymmetricLocalBound_of_independentOutside mass hmass bad dependency p
      hindep hmarginal)

/-! ## Bernoulli-coordinate specialization -/

/-- Asymmetric local lemma for events supported on finite Bernoulli
coordinates.  This is the direct two-parameter engine in Alon's proof. -/
theorem exists_avoiding_bernoulli_localEvents
    {E J : Type*} [Fintype E] [DecidableEq E]
    [Fintype J] [DecidableEq J]
    (prob : E → ℝ) (hprob0 : ∀ e, 0 ≤ prob e)
    (hprob1 : ∀ e, prob e ≤ 1)
    (support : J → Finset E) (bad : J → Finset E → Prop)
    (dependency : J → Finset J) (p x : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hparameter : ∀ i,
      p i ≤ x i * ∏ j ∈ dependency i, (1 - x j))
    (hlocal : ∀ i,
      Erdos76.FiniteNibble.EventDependsOn (support i) (bad i))
    (hoverlap :
      Erdos76.FiniteNibble.ContainsSupportOverlaps support dependency)
    (hmarginal : ∀ i,
      eventMass
        (fun S : Finset E ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
        (bad i) ≤ p i) :
    ∃ S : Finset E, ∀ i, ¬ bad i S := by
  let mass : Finset E → ℝ := fun S ↦
    Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S
  refine exists_avoiding_all_of_independentOutside
    mass ?_ ?_ bad dependency p x hp hx0 hx1 hparameter ?_ hmarginal
  · intro S
    exact Erdos76.FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun e _ ↦ hprob0 e) (fun e _ ↦ hprob1 e)
  · simpa [mass] using
      Erdos76.FiniteNibble.sum_bernoulliMass
        (Finset.univ : Finset E) prob
  · exact Erdos76.FiniteNibble.independentOutside_of_eventDependsOn
      prob support bad dependency hlocal hoverlap

/-! ## Elementary local events and their exact marginals -/

lemma eventDependsOn_disjoint_self {E : Type*} [DecidableEq E]
    (R : Finset E) :
    Erdos76.FiniteNibble.EventDependsOn R (fun S ↦ Disjoint S R) := by
  intro S T hST
  change Disjoint S R ↔ Disjoint T R
  rw [Finset.disjoint_iff_inter_eq_empty,
    Finset.disjoint_iff_inter_eq_empty]
  unfold Erdos76.FiniteNibble.AgreesOn at hST
  rw [hST]

lemma eventDependsOn_subset {E : Type*} [DecidableEq E]
    (R : Finset E) :
    Erdos76.FiniteNibble.EventDependsOn R (fun S ↦ R ⊆ S) := by
  intro S T hST
  constructor
  · intro hRS e heR
    have he : e ∈ S ∩ R := Finset.mem_inter.mpr ⟨hRS heR, heR⟩
    rw [hST] at he
    exact (Finset.mem_inter.mp he).1
  · intro hRT e heR
    have he : e ∈ T ∩ R := Finset.mem_inter.mpr ⟨hRT heR, heR⟩
    rw [← hST] at he
    exact (Finset.mem_inter.mp he).1

/-- In a finite Bernoulli product, the probability that no coordinate of `R`
is selected is the product of the failure probabilities on `R`. -/
lemma eventMass_disjoint_eq_prod
    {E : Type*} [Fintype E] [DecidableEq E]
    (prob : E → ℝ) (R : Finset E) :
    eventMass
        (fun S : Finset E ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
        (fun S ↦ Disjoint S R) =
      ∏ e ∈ R, (1 - prob e) := by
  rw [Erdos76.FiniteNibble.eventMass_eq_restrictedEventMass
    (eventDependsOn_disjoint_self R)]
  unfold Erdos76.FiniteNibble.restrictedEventMass
  rw [Fintype.sum_eq_single (⟨∅, empty_subset R⟩ :
    Erdos76.FiniteNibble.Subsets R)]
  · simp [Erdos76.FiniteNibble.bernoulliMass]
  · intro S hSne
    have hnonempty : S.1.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hS
      apply hSne
      exact Subtype.ext hS
    have hnDisjoint : ¬ Disjoint S.1 R := by
      obtain ⟨e, heS⟩ := hnonempty
      exact fun h ↦ (Finset.disjoint_left.mp h) heS (S.2 heS)
    simp [hnDisjoint]

/-- In a finite Bernoulli product, the probability that every coordinate of
`R` is selected is the product of the success probabilities on `R`. -/
lemma eventMass_subset_eq_prod
    {E : Type*} [Fintype E] [DecidableEq E]
    (prob : E → ℝ) (R : Finset E) :
    eventMass
        (fun S : Finset E ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
        (fun S ↦ R ⊆ S) =
      ∏ e ∈ R, prob e := by
  rw [Erdos76.FiniteNibble.eventMass_eq_restrictedEventMass
    (eventDependsOn_subset R)]
  unfold Erdos76.FiniteNibble.restrictedEventMass
  rw [Fintype.sum_eq_single (⟨R, Subset.rfl⟩ :
    Erdos76.FiniteNibble.Subsets R)]
  · simp [Erdos76.FiniteNibble.bernoulliMass]
  · intro S hSne
    have hnsubset : ¬ R ⊆ S.1 := by
      intro hRS
      apply hSne
      apply Subtype.ext
      exact Subset.antisymm S.2 hRS
    simp [hnsubset]

/-! ## The two numerical estimates in Proposition 2.4 -/

private def cubicBinomialLower (n : ℕ) (t : ℝ) : ℝ :=
  1 + (n : ℝ) * t +
    (n : ℝ) * ((n : ℝ) - 1) / 2 * t ^ 2 +
    (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 * t ^ 3

private lemma cubicBinomialLower_le_pow {n : ℕ} (hn : 3 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) :
    cubicBinomialLower n t ≤ (1 + t) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [cubicBinomialLower]
      ring_nf
      exact le_rfl
  | succ n hn ih =>
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
      have hcoefficient :
          0 ≤ (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
        positivity
      have hfour : 0 ≤
          ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6) * t ^ 4 :=
        mul_nonneg hcoefficient (pow_nonneg ht 4)
      have hid :
          (1 + t) * cubicBinomialLower n t =
            cubicBinomialLower (n + 1) t +
              ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6) * t ^ 4 := by
        simp only [cubicBinomialLower, Nat.cast_add, Nat.cast_one]
        ring
      calc
        cubicBinomialLower (n + 1) t ≤
            (1 + t) * cubicBinomialLower n t := by linarith
        _ ≤ (1 + t) * (1 + t) ^ n :=
          mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 + t) ^ (n + 1) := by rw [pow_succ']

private lemma one_sub_inv_pow_lt_three_eighths (n : ℕ) (hn : 25 ≤ n) :
    ((1 : ℝ) - 1 / (n : ℝ)) ^ n < 3 / 8 := by
  have hnR : (25 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  let t : ℝ := 1 / ((n : ℝ) - 1)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcubic := cubicBinomialLower_le_pow (show 3 ≤ n by omega) ht
  have hcubicLarge : (8 : ℝ) / 3 < cubicBinomialLower n t := by
    dsimp [cubicBinomialLower, t]
    field_simp
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hpowLarge : (8 : ℝ) / 3 < (1 + t) ^ n :=
    hcubicLarge.trans_le hcubic
  have hqnonneg : 0 ≤ ((1 : ℝ) - 1 / (n : ℝ)) ^ n := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one hnpos]
    linarith
  have hrecipnonneg : 0 ≤ (1 + t) ^ n := by positivity
  have hmul :
      ((1 : ℝ) - 1 / (n : ℝ)) ^ n * (1 + t) ^ n = 1 := by
    rw [← mul_pow]
    have hbase : ((1 : ℝ) - 1 / (n : ℝ)) * (1 + t) = 1 := by
      dsimp [t]
      field_simp
      ring
    rw [hbase, one_pow]
  nlinarith

private lemma one_sub_small_pow_lower_three_quarters (d : ℕ) (hd : 0 < d) :
    (3 : ℝ) / 4 ≤
      (1 - 1 / (100 * (d : ℝ) ^ 2)) ^ (25 * d ^ 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hy : (0 : ℝ) ≤ 1 / (100 * (d : ℝ) ^ 2) := by positivity
  have hy_le : 1 / (100 * (d : ℝ) ^ 2) ≤ 1 := by
    have : (1 : ℝ) ≤ 100 * (d : ℝ) ^ 2 := by nlinarith [sq_nonneg ((d : ℝ) - 1)]
    exact (div_le_one (by positivity)).2 this
  have hBernoulli := one_add_mul_le_pow
    (a := -(1 / (100 * (d : ℝ) ^ 2))) (by linarith) (25 * d ^ 2)
  have hcast : ((25 * d ^ 2 : ℕ) : ℝ) = 25 * (d : ℝ) ^ 2 := by norm_num
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hBernoulli
  have heq :
      (1 : ℝ) + (25 * (d : ℝ) ^ 2) *
          (-(1 / (100 * (d : ℝ) ^ 2))) = 3 / 4 := by
    field_simp
    ring
  calc
    (3 : ℝ) / 4 =
        1 + (25 * (d : ℝ) ^ 2) *
          (-(1 / (100 * (d : ℝ) ^ 2))) := heq.symm
    _ ≤ (1 + -(1 / (100 * (d : ℝ) ^ 2))) ^ (25 * d ^ 2) :=
      hBernoulli
    _ = (1 - 1 / (100 * (d : ℝ) ^ 2)) ^ (25 * d ^ 2) := by ring

private lemma edge_parameter_inequality (d : ℕ) (hd : 0 < d) :
    (1 / (25 * (d : ℝ))) ^ 2 ≤
      (1 / (100 * (d : ℝ) ^ 2)) *
        (1 - 1 / (100 * (d : ℝ) ^ 2)) ^ (2 * d) *
        ((1 : ℝ) / 2) ^ 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hBernoulli := one_add_mul_le_pow
    (a := -(1 / (100 * (d : ℝ) ^ 2))) (by
      have : 1 / (100 * (d : ℝ) ^ 2) ≤ 1 := by
        apply (div_le_one (by positivity)).2
        nlinarith [sq_nonneg ((d : ℝ) - 1)]
      linarith) (2 * d)
  rw [Nat.cast_mul, Nat.cast_ofNat] at hBernoulli
  have hlower : (49 : ℝ) / 50 ≤
      (1 - 1 / (100 * (d : ℝ) ^ 2)) ^ (2 * d) := by
    calc
      (49 : ℝ) / 50 ≤
          1 - (2 * (d : ℝ)) / (100 * (d : ℝ) ^ 2) := by
        field_simp
        ring_nf
        nlinarith
      _ = 1 + (2 * (d : ℝ)) *
          (-(1 / (100 * (d : ℝ) ^ 2))) := by ring
      _ ≤ _ := hBernoulli
  have hpos : 0 < 1 / (100 * (d : ℝ) ^ 2) := by positivity
  calc
    (1 / (25 * (d : ℝ))) ^ 2 ≤
        (1 / (100 * (d : ℝ) ^ 2)) * ((49 : ℝ) / 50) *
          ((1 : ℝ) / 2) ^ 2 := by
      field_simp
      ring_nf
      nlinarith
    _ ≤ (1 / (100 * (d : ℝ) ^ 2)) *
          (1 - 1 / (100 * (d : ℝ) ^ 2)) ^ (2 * d) *
          ((1 : ℝ) / 2) ^ 2 := by
      gcongr

/-! ## Dependency counts for graph-edge events -/

/-- The graph edges meeting a vertex set are covered by the union of the
incidence finsets of its vertices. -/
private lemma card_edges_meeting_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (d : ℕ) (hdegree : ∀ v, G.degree v ≤ d) :
    (G.edgeFinset.filter fun e ↦ ¬ Disjoint R e.toFinset).card ≤ R.card * d := by
  have hsub :
      G.edgeFinset.filter (fun e ↦ ¬ Disjoint R e.toFinset) ⊆
        R.biUnion (fun v ↦ G.incidenceFinset v) := by
    intro e he
    have hoverlap : ¬ Disjoint R e.toFinset := (mem_filter.mp he).2
    rw [Finset.not_disjoint_iff] at hoverlap
    obtain ⟨v, hvR, hve⟩ := hoverlap
    rw [mem_biUnion]
    refine ⟨v, hvR, ?_⟩
    rw [G.mem_incidenceFinset]
    let e' : G.edgeSet := ⟨e, G.mem_edgeFinset.mp (mem_filter.mp he).1⟩
    have hv : v ∈ (e' : Sym2 V) := Sym2.mem_toFinset.mp hve
    exact G.edge_mem_incidenceSet_iff.mpr hv
  calc
    (G.edgeFinset.filter fun e ↦ ¬ Disjoint R e.toFinset).card ≤
        (R.biUnion (fun v ↦ G.incidenceFinset v)).card := card_le_card hsub
    _ ≤ ∑ v ∈ R, (G.incidenceFinset v).card := card_biUnion_le
    _ = ∑ v ∈ R, G.degree v := by simp
    _ ≤ ∑ _v ∈ R, d := sum_le_sum fun v _ ↦ hdegree v
    _ = R.card * d := by simp

/-- Pairwise-disjoint parts meeting `R` inject into the vertices of `R`. -/
private lemma card_parts_meeting_le
    {V J : Type*} [Fintype J] [DecidableEq J] [DecidableEq V]
    (parts : J → Finset V)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (R : Finset V) :
    ((univ : Finset J).filter fun i ↦ ¬ Disjoint (parts i) R).card ≤ R.card := by
  let s := (univ : Finset J).filter fun i ↦ ¬ Disjoint (parts i) R
  let pick : (i : s) → V := fun i ↦
    Classical.choose (Finset.not_disjoint_iff.mp (mem_filter.mp i.2).2)
  have pick_mem_part (i : s) : pick i ∈ parts i := by
    exact (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (mem_filter.mp i.2).2)).1
  have pick_mem_R (i : s) : pick i ∈ R := by
    exact (Classical.choose_spec
      (Finset.not_disjoint_iff.mp (mem_filter.mp i.2).2)).2
  let f : s → R := fun i ↦ ⟨pick i, pick_mem_R i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have hd := hdisjoint i j hne
    have hpick : pick i = pick j := congrArg Subtype.val hij
    exact (Finset.disjoint_left.mp hd) (pick_mem_part i)
      (hpick ▸ pick_mem_part j)
  simpa [s] using Finset.card_le_card_of_injective hf

/-- The two families of bad events in Alon's proof: a missed part, or a
selected graph edge. -/
inductive TransversalBad (J E : Type*)
  | missed (i : J)
  | edge (e : E)
  deriving DecidableEq, Fintype

private def transversalSupport
    {V J : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (parts : J → Finset V) :
    TransversalBad J G.edgeFinset → Finset V
  | .missed i => parts i
  | .edge e => (e : Sym2 V).toFinset

private def transversalEvent
    {V J : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (parts : J → Finset V) :
    TransversalBad J G.edgeFinset → Finset V → Prop
  | .missed i, S => Disjoint S (parts i)
  | .edge e, S => (e : Sym2 V).toFinset ⊆ S

private def transversalDependency
    {V J : Type*} [Fintype V] [DecidableEq V]
    [Fintype J] [DecidableEq J]
    {G : SimpleGraph V} (parts : J → Finset V)
    (a : TransversalBad J G.edgeFinset) :
    Finset (TransversalBad J G.edgeFinset) :=
  univ.filter fun b ↦ b ≠ a ∧
    ¬ Disjoint (transversalSupport parts a) (transversalSupport parts b)

private def transversalBound (d : ℕ) {J E : Type*} :
    TransversalBad J E → ℝ
  | .missed _ => (1 - 1 / (25 * (d : ℝ))) ^ (25 * d)
  | .edge _ => (1 / (25 * (d : ℝ))) ^ 2

private def transversalParameter (d : ℕ) {J E : Type*} :
    TransversalBad J E → ℝ
  | .missed _ => 1 / 2
  | .edge _ => 1 / (100 * (d : ℝ) ^ 2)

private def isMissed {J E : Type*} : TransversalBad J E → Prop
  | .missed _ => True
  | .edge _ => False

private def isEdge {J E : Type*} : TransversalBad J E → Prop
  | .missed _ => False
  | .edge _ => True

private lemma dependency_missed_card_le
    {V J : Type*} [Fintype V] [DecidableEq V]
    [Fintype J] [DecidableEq J]
    (G : SimpleGraph V)
    (parts : J → Finset V) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (hcard : ∀ i, (parts i).card = 25 * d) (i : J) :
    (transversalDependency (G := G) parts (.missed i)).card ≤ 25 * d ^ 2 := by
  let dep := transversalDependency (G := G) parts (.missed i)
  have hno : ∀ j : J, TransversalBad.missed j ∉ dep := by
    intro j hj
    have hj' := (mem_filter.mp hj).2
    by_cases hji : j = i
    · subst j
      exact hj'.1 rfl
    · exact hj'.2 (hdisjoint i j (Ne.symm hji))
  have hedge : ∀ a ∈ dep, ∃ e : G.edgeFinset, a = .edge e := by
    intro a ha
    cases a with
    | missed j => exact False.elim (hno j ha)
    | edge e => exact ⟨e, rfl⟩
  let f : dep → G.edgeFinset := fun a ↦ Classical.choose (hedge a a.2)
  have hf_eq (a : dep) : a.1 = .edge (f a) :=
    Classical.choose_spec (hedge a a.2)
  let target : Finset G.edgeFinset := (univ : Finset G.edgeFinset).filter fun e ↦
    ¬ Disjoint (parts i) ((e : Sym2 V).toFinset)
  have hfmem (a : dep) : f a ∈ target := by
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have ha := (mem_filter.mp a.2).2.2
    simpa [transversalSupport, hf_eq a] using ha
  let f' : dep → target := fun a ↦ ⟨f a, hfmem a⟩
  have hfinj : Function.Injective f' := by
    intro a b hab
    apply Subtype.ext
    have hab' : f a = f b := congrArg Subtype.val hab
    rw [hf_eq a, hf_eq b, hab']
  have hleTarget : dep.card ≤ target.card :=
    Finset.card_le_card_of_injective hfinj
  have htarget : target.card =
      (G.edgeFinset.filter fun e ↦
        ¬ Disjoint (parts i) e.toFinset).card := by
    have h := congrArg Finset.card
      (Finset.filter_attach
        (fun e : Sym2 V ↦ ¬ Disjoint (parts i) e.toFinset) G.edgeFinset)
    simpa [target] using h
  rw [htarget] at hleTarget
  calc
    dep.card ≤ (parts i).card * d :=
      hleTarget.trans (card_edges_meeting_le G (parts i) d hdegree)
    _ = 25 * d ^ 2 := by rw [hcard i]; ring

private lemma dependency_edge_type_cards
    {V J : Type*} [Fintype V] [DecidableEq V]
    [Fintype J] [DecidableEq J]
    (G : SimpleGraph V)
    (parts : J → Finset V) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (e : G.edgeFinset) :
    ((transversalDependency (G := G) parts (.edge e)).filter isMissed).card ≤ 2 ∧
    ((transversalDependency (G := G) parts (.edge e)).filter isEdge).card ≤ 2 * d := by
  let dep := transversalDependency (G := G) parts (.edge e)
  let left := dep.filter isMissed
  let right := dep.filter isEdge
  have hleftWitness : ∀ a ∈ left, ∃ i : J, a = .missed i := by
    intro a ha
    have ht := (mem_filter.mp ha).2
    cases a with
    | missed i => exact ⟨i, rfl⟩
    | edge e => simp [isMissed] at ht
  let fl : left → J := fun a ↦ Classical.choose (hleftWitness a a.2)
  have hfl_eq (a : left) : a.1 = .missed (fl a) :=
    Classical.choose_spec (hleftWitness a a.2)
  let targetLeft : Finset J := (univ : Finset J).filter fun i ↦
    ¬ Disjoint (parts i) ((e : Sym2 V).toFinset)
  have hflMem (a : left) : fl a ∈ targetLeft := by
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have haDep := (mem_filter.mp (mem_filter.mp a.2).1).2.2
    have haDep0 : ¬ Disjoint ((e : Sym2 V).toFinset) (parts (fl a)) := by
      simpa [transversalSupport, hfl_eq a] using haDep
    have haDep' : ¬ Disjoint (parts (fl a)) ((e : Sym2 V).toFinset) :=
      fun h ↦ haDep0 h.symm
    exact haDep'
  let fl' : left → targetLeft := fun a ↦ ⟨fl a, hflMem a⟩
  have hflInj : Function.Injective fl' := by
    intro a b hab
    apply Subtype.ext
    have hab' : fl a = fl b := congrArg Subtype.val hab
    rw [hfl_eq a, hfl_eq b, hab']
  have hleftLe : left.card ≤ targetLeft.card :=
    Finset.card_le_card_of_injective hflInj
  have htargetLeft : targetLeft.card ≤ 2 := by
    exact (card_parts_meeting_le parts hdisjoint
      ((e : Sym2 V).toFinset)).trans_eq (G.card_toFinset_mem_edgeFinset e)
  have hrightWitness : ∀ a ∈ right, ∃ f : G.edgeFinset, a = .edge f := by
    intro a ha
    have ht := (mem_filter.mp ha).2
    cases a with
    | missed i => simp [isEdge] at ht
    | edge f => exact ⟨f, rfl⟩
  let fr : right → G.edgeFinset := fun a ↦ Classical.choose (hrightWitness a a.2)
  have hfr_eq (a : right) : a.1 = .edge (fr a) :=
    Classical.choose_spec (hrightWitness a a.2)
  let targetRight : Finset G.edgeFinset := (univ : Finset G.edgeFinset).filter fun f ↦
    ¬ Disjoint ((e : Sym2 V).toFinset) ((f : Sym2 V).toFinset)
  have hfrMem (a : right) : fr a ∈ targetRight := by
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have haDep := (mem_filter.mp (mem_filter.mp a.2).1).2.2
    simpa [transversalSupport, hfr_eq a] using haDep
  let fr' : right → targetRight := fun a ↦ ⟨fr a, hfrMem a⟩
  have hfrInj : Function.Injective fr' := by
    intro a b hab
    apply Subtype.ext
    have hab' : fr a = fr b := congrArg Subtype.val hab
    rw [hfr_eq a, hfr_eq b, hab']
  have hrightLe : right.card ≤ targetRight.card :=
    Finset.card_le_card_of_injective hfrInj
  have htargetRight : targetRight.card =
      (G.edgeFinset.filter fun f ↦
        ¬ Disjoint ((e : Sym2 V).toFinset) f.toFinset).card := by
    have h := congrArg Finset.card
      (Finset.filter_attach
        (fun f : Sym2 V ↦
          ¬ Disjoint ((e : Sym2 V).toFinset) f.toFinset) G.edgeFinset)
    simpa [targetRight] using h
  have hmeeting := card_edges_meeting_le G ((e : Sym2 V).toFinset) d hdegree
  rw [← htargetRight, G.card_toFinset_mem_edgeFinset e] at hmeeting
  exact ⟨hleftLe.trans htargetLeft, hrightLe.trans hmeeting⟩

private lemma transversal_parameter_bound
    {V J : Type*} [Fintype V] [DecidableEq V]
    [Fintype J] [DecidableEq J]
    (G : SimpleGraph V)
    (parts : J → Finset V) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ v, G.degree v ≤ d)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (hcard : ∀ i, (parts i).card = 25 * d) :
    ∀ a : TransversalBad J G.edgeFinset,
      transversalBound d a ≤ transversalParameter d a *
        ∏ b ∈ transversalDependency (G := G) parts a,
          (1 - transversalParameter d b) := by
  intro a
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let y : ℝ := 1 / (100 * (d : ℝ) ^ 2)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hy1 : y ≤ 1 := by
    dsimp [y]
    apply (div_le_one (by positivity)).2
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  cases a with
  | missed i =>
      let dep := transversalDependency (G := G) parts (.missed i)
      have hno : ∀ j : J, TransversalBad.missed j ∉ dep := by
        intro j hj
        have hj' := (mem_filter.mp hj).2
        by_cases hji : j = i
        · subst j
          exact hj'.1 rfl
        · exact hj'.2 (hdisjoint i j (Ne.symm hji))
      have hfactor : ∀ b ∈ dep,
          1 - transversalParameter d b = 1 - y := by
        intro b hb
        cases b with
        | missed j => exact False.elim (hno j hb)
        | edge e => rfl
      have hprod :
          (∏ b ∈ dep, (1 - transversalParameter d b)) =
            (1 - y) ^ dep.card := by
        calc
          (∏ b ∈ dep, (1 - transversalParameter d b)) =
              ∏ _b ∈ dep, (1 - y) :=
            prod_congr rfl hfactor
          _ = (1 - y) ^ dep.card := by simp
      have hdepCard : dep.card ≤ 25 * d ^ 2 :=
        dependency_missed_card_le G parts d hdegree hdisjoint hcard i
      have hpow : (1 - y) ^ (25 * d ^ 2) ≤ (1 - y) ^ dep.card :=
        pow_le_pow_of_le_one (sub_nonneg.mpr hy1) (by linarith) hdepCard
      have hsmall :
          (1 - 1 / (25 * (d : ℝ))) ^ (25 * d) ≤ (3 : ℝ) / 8 := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (one_sub_inv_pow_lt_three_eighths (25 * d) (by omega)).le
      have hlarge := one_sub_small_pow_lower_three_quarters d hd
      rw [hprod]
      change (1 - 1 / (25 * (d : ℝ))) ^ (25 * d) ≤
        (1 / 2 : ℝ) * (1 - y) ^ dep.card
      calc
        (1 - 1 / (25 * (d : ℝ))) ^ (25 * d) ≤ (3 : ℝ) / 8 := hsmall
        _ = (1 / 2 : ℝ) * (3 / 4) := by norm_num
        _ ≤ (1 / 2 : ℝ) * (1 - y) ^ (25 * d ^ 2) := by
          exact mul_le_mul_of_nonneg_left (by simpa [y] using hlarge) (by norm_num)
        _ ≤ (1 / 2 : ℝ) * (1 - y) ^ dep.card := by gcongr
  | edge e =>
      let dep := transversalDependency (G := G) parts (.edge e)
      let left := dep.filter isMissed
      let right := dep.filter isEdge
      have hcards := dependency_edge_type_cards G parts d hdegree hdisjoint e
      have hleftCard : left.card ≤ 2 := hcards.1
      have hrightCard : right.card ≤ 2 * d := hcards.2
      have hcover : left ∪ right = dep := by
        ext b
        cases b <;> simp [left, right, isMissed, isEdge]
      have hlr : Disjoint left right := by
        rw [Finset.disjoint_left]
        intro b hbl hbr
        have hl := (mem_filter.mp hbl).2
        have hr := (mem_filter.mp hbr).2
        cases b <;> simp [isMissed, isEdge] at hl hr
      have hleftProd :
          (∏ b ∈ left, (1 - transversalParameter d b)) =
            ((1 : ℝ) / 2) ^ left.card := by
        calc
          (∏ b ∈ left, (1 - transversalParameter d b)) =
              ∏ _b ∈ left, ((1 : ℝ) / 2) := by
            apply prod_congr rfl
            intro b hb
            have ht := (mem_filter.mp hb).2
            cases b with
            | missed i => norm_num [transversalParameter]
            | edge e => simp [isMissed] at ht
          _ = ((1 : ℝ) / 2) ^ left.card := by simp
      have hrightProd :
          (∏ b ∈ right, (1 - transversalParameter d b)) =
            (1 - y) ^ right.card := by
        calc
          (∏ b ∈ right, (1 - transversalParameter d b)) =
              ∏ _b ∈ right, (1 - y) := by
            apply prod_congr rfl
            intro b hb
            have ht := (mem_filter.mp hb).2
            cases b <;> simp [isEdge, transversalParameter, y] at ht ⊢
          _ = (1 - y) ^ right.card := by simp
      have hprod :
          (∏ b ∈ dep, (1 - transversalParameter d b)) =
            ((1 : ℝ) / 2) ^ left.card * (1 - y) ^ right.card := by
        rw [← hcover, prod_union hlr, hleftProd, hrightProd]
      have hhalfPow : ((1 : ℝ) / 2) ^ 2 ≤ ((1 : ℝ) / 2) ^ left.card :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hleftCard
      have hyPow : (1 - y) ^ (2 * d) ≤ (1 - y) ^ right.card :=
        pow_le_pow_of_le_one (sub_nonneg.mpr hy1) (by linarith) hrightCard
      have hbase := edge_parameter_inequality d hd
      rw [hprod]
      change (1 / (25 * (d : ℝ))) ^ 2 ≤
        y * (((1 : ℝ) / 2) ^ left.card * (1 - y) ^ right.card)
      calc
        (1 / (25 * (d : ℝ))) ^ 2 ≤
            y * (1 - y) ^ (2 * d) * ((1 : ℝ) / 2) ^ 2 := by
          simpa [y] using hbase
        _ ≤ y * ((1 : ℝ) / 2) ^ left.card * (1 - y) ^ right.card := by
          have hmul : ((1 : ℝ) / 2) ^ 2 * (1 - y) ^ (2 * d) ≤
              ((1 : ℝ) / 2) ^ left.card * (1 - y) ^ right.card :=
            mul_le_mul hhalfPow hyPow
              (pow_nonneg (sub_nonneg.mpr hy1) _)
              (pow_nonneg (by norm_num) _)
          calc
            y * (1 - y) ^ (2 * d) * ((1 : ℝ) / 2) ^ 2 =
                y * (((1 : ℝ) / 2) ^ 2 * (1 - y) ^ (2 * d)) := by ring
            _ ≤ y * (((1 : ℝ) / 2) ^ left.card * (1 - y) ^ right.card) :=
              mul_le_mul_of_nonneg_left hmul hy0
            _ = y * ((1 : ℝ) / 2) ^ left.card * (1 - y) ^ right.card := by ring
        _ = y * (((1 : ℝ) / 2) ^ left.card * (1 - y) ^ right.card) := by ring

/-! ## Alon's Proposition 2.4 -/

/-- Exact-size form of Alon's independent-transversal proposition. -/
private theorem exists_independent_transversal_exact
    {V J : Type*} [Fintype V] [DecidableEq V]
    [Fintype J] [DecidableEq J]
    (G : SimpleGraph V)
    (parts : J → Finset V) (d : ℕ) (hd : 0 < d)
    (hdegree : ∀ v, G.degree v ≤ d)
    (hcard : ∀ i, (parts i).card = 25 * d)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j)) :
    ∃ W : Finset V,
      G.IsIndepSet (W : Set V) ∧ ∀ i, (W ∩ parts i).Nonempty := by
  let prob : V → ℝ := fun _ ↦ 1 / (25 * (d : ℝ))
  let support := transversalSupport (G := G) parts
  let bad := transversalEvent (G := G) parts
  let dependency := transversalDependency (G := G) parts
  let p : TransversalBad J G.edgeFinset → ℝ := transversalBound d
  let x : TransversalBad J G.edgeFinset → ℝ := transversalParameter d
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hprob0 : ∀ v, 0 ≤ prob v := fun _ ↦ by dsimp [prob]; positivity
  have hprob1 : ∀ v, prob v ≤ 1 := by
    intro v
    dsimp [prob]
    apply (div_le_one (by positivity)).2
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hp0 : ∀ a : TransversalBad J G.edgeFinset, 0 ≤ p a := by
    intro a
    cases a with
    | missed i =>
        dsimp [p, transversalBound]
        apply pow_nonneg
        rw [sub_nonneg]
        apply (div_le_one (by positivity)).2
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith
    | edge e => dsimp [p, transversalBound]; positivity
  have hx0 : ∀ a : TransversalBad J G.edgeFinset, 0 ≤ x a := by
    intro a
    cases a <;> dsimp [x, transversalParameter] <;> positivity
  have hx1 : ∀ a : TransversalBad J G.edgeFinset, x a < 1 := by
    intro a
    cases a with
    | missed i => norm_num [x, transversalParameter]
    | edge e =>
        dsimp [x, transversalParameter]
        rw [div_lt_one (by positivity)]
        have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
        nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hparameter : ∀ a : TransversalBad J G.edgeFinset,
      p a ≤ x a * ∏ b ∈ dependency a, (1 - x b) := by
    simpa [p, x, dependency] using
      transversal_parameter_bound G parts d hd hdegree hdisjoint hcard
  have hlocal : ∀ a : TransversalBad J G.edgeFinset,
      Erdos76.FiniteNibble.EventDependsOn (support a) (bad a) := by
    intro a
    cases a with
    | missed i => exact eventDependsOn_disjoint_self (parts i)
    | edge e => exact eventDependsOn_subset ((e : Sym2 V).toFinset)
  have hoverlap :
      Erdos76.FiniteNibble.ContainsSupportOverlaps support dependency := by
    intro a b hab hover
    simp only [dependency, transversalDependency, mem_filter, mem_univ, true_and]
    exact ⟨Ne.symm hab, hover⟩
  have hmarginal : ∀ a : TransversalBad J G.edgeFinset,
      eventMass
          (fun S : Finset V ↦
            Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
          (bad a) ≤ p a := by
    intro a
    cases a with
    | missed i =>
        have hmass := eventMass_disjoint_eq_prod prob (parts i)
        change eventMass
            (fun S : Finset V ↦
              Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
            (fun S ↦ Disjoint S (parts i)) ≤
          (1 - 1 / (25 * (d : ℝ))) ^ (25 * d)
        rw [hmass]
        simp [prob, hcard i]
    | edge e =>
        have hmass := eventMass_subset_eq_prod prob ((e : Sym2 V).toFinset)
        change eventMass
            (fun S : Finset V ↦
              Erdos76.FiniteNibble.bernoulliMass Finset.univ prob S)
            (fun S ↦ (e : Sym2 V).toFinset ⊆ S) ≤
          (1 / (25 * (d : ℝ))) ^ 2
        rw [hmass]
        simp [prob, G.card_toFinset_mem_edgeFinset e]
  obtain ⟨W, hW⟩ := exists_avoiding_bernoulli_localEvents
    prob hprob0 hprob1 support bad dependency p x hp0 hx0 hx1 hparameter
      hlocal hoverlap hmarginal
  refine ⟨W, ?_, ?_⟩
  · rw [G.isIndepSet_iff]
    intro v hv w hw hvw hadj
    let e : G.edgeFinset := ⟨s(v, w), by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj⟩
    have havoid := hW (TransversalBad.edge e)
    apply havoid
    change s(v, w).toFinset ⊆ W
    rw [Sym2.toFinset_mk_eq]
    simp [hv, hw]
  · intro i
    have havoid := hW (TransversalBad.missed i)
    change ¬ Disjoint W (parts i) at havoid
    rw [Finset.not_disjoint_iff] at havoid
    obtain ⟨v, hvW, hvpart⟩ := havoid
    exact ⟨v, mem_inter.mpr ⟨hvW, hvpart⟩⟩

end

end AlonLLL
end Erdos622
