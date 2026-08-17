/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.KeyConditional
import ErdosProblems.Erdos182.KeyBuckets
import ErdosProblems.Erdos182.KeyPruning
import ErdosProblems.Erdos182.WeightedSubsets

/-!
# The core Janzer--Sudakov random restriction

This file integrates the dyadic bucketing, independent finite sampling,
conditional first-moment estimate, and deterministic pruning used in
Janzer--Sudakov Lemma 4.1.  Exponents in the public interface are natural
numbers.  Consequently the case in which the displayed exponent is negative
is handled separately (the power is then `2 ^ 0 = 1`).
-/

open Finset Fintype
open scoped BigOperators

namespace Erdos182

section Sampling

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Right vertices all of whose neighbours survived the left sampling. -/
def sampledRight (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (S : Finset A) : Finset B :=
  B₀.filter fun v ↦ bipNeighborsB R v ⊆ S

@[simp] theorem mem_sampledRight {R : A → B → Prop} [DecidableRel R]
    {B₀ : Finset B} {S : Finset A} {v : B} :
    v ∈ sampledRight R B₀ S ↔ v ∈ B₀ ∧ bipNeighborsB R v ⊆ S := by
  simp [sampledRight]

theorem sampledRight_closed (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (S : Finset A) :
    ∀ v ∈ sampledRight R B₀ S, ∀ u, R u v → u ∈ S := by
  intro v hv u huv
  exact (mem_sampledRight.mp hv).2 (mem_bipNeighborsB.mpr huv)

theorem sampledRight_restricted_degree
    (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (S : Finset A) {v : B}
    (hv : v ∈ sampledRight R B₀ S) :
    (S.filter fun u ↦ R u v).card = bipDegreeB R v := by
  unfold bipDegreeB
  congr 1
  ext u
  simp only [Finset.mem_filter, mem_bipNeighborsB]
  constructor
  · exact fun hu ↦ hu.2
  · intro huv
    exact ⟨(mem_sampledRight.mp hv).2 (mem_bipNeighborsB.mpr huv), huv⟩

private theorem prod_union_eq_prod_mul_prod_sdiff (p : A → ℝ)
    (s t : Finset A) :
    (∏ x ∈ s ∪ t, p x) = (∏ x ∈ s, p x) * ∏ x ∈ (t \ s), p x := by
  have hdis : Disjoint s (t \ s) := by
    exact Finset.disjoint_left.mpr fun a ha hat ↦ (Finset.mem_sdiff.mp hat).2 ha
  rw [← Finset.prod_union hdis]
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- The unnormalised conditional first moment.  The event that `v` survives
is left as an indicator; expanding the restricted degree and using
independence gives exactly `q(v)` times the conditional product sum. -/
theorem subsetExpectation_survival_mul_degree
    (R : A → B → Prop) [DecidableRel R]
    (p : A → ℝ) (B₀ : Finset B) (u : A) (v : B) :
    subsetExpectation p (fun S ↦
        if bipNeighborsB R v ⊆ S then
          (bipRestrictedDegreeA R (sampledRight R B₀ S) u : ℝ)
        else 0) =
      rightSurvivalProbability R p v *
        conditionalDegreeFactor R p B₀ u v := by
  classical
  let W : Finset B := B₀.filter (R u)
  have hdegree (S : Finset A) :
      (bipRestrictedDegreeA R (sampledRight R B₀ S) u : ℝ) =
        ∑ w ∈ W, if bipNeighborsB R w ⊆ S then 1 else 0 := by
    have heq : (sampledRight R B₀ S).filter (R u) =
        W.filter fun w ↦ bipNeighborsB R w ⊆ S := by
      ext w
      simp only [sampledRight, Finset.mem_filter, W]
      tauto
    rw [bipRestrictedDegreeA, heq]
    calc
      ((W.filter fun w ↦ bipNeighborsB R w ⊆ S).card : ℝ) =
          ∑ _w ∈ W.filter (fun w ↦ bipNeighborsB R w ⊆ S), (1 : ℝ) := by simp
      _ = ∑ w ∈ W, if bipNeighborsB R w ⊆ S then (1 : ℝ) else 0 := by
        rw [Finset.sum_filter]
  calc
    subsetExpectation p (fun S ↦
        if bipNeighborsB R v ⊆ S then
          (bipRestrictedDegreeA R (sampledRight R B₀ S) u : ℝ)
        else 0) =
        subsetExpectation p (fun S ↦ ∑ w ∈ W,
          if bipNeighborsB R v ∪ bipNeighborsB R w ⊆ S then (1 : ℝ) else 0) := by
      congr 1
      funext S
      rw [hdegree]
      by_cases hv : bipNeighborsB R v ⊆ S
      · simp only [hv, if_true]
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hwS : bipNeighborsB R w ⊆ S
        · simp [hwS, Finset.union_subset hv hwS]
        · have hu : ¬ (bipNeighborsB R v ∪ bipNeighborsB R w ⊆ S) := by
            intro h
            exact hwS (Finset.Subset.trans Finset.subset_union_right h)
          simp [hwS, hu]
      · simp only [hv, if_false]
        symm
        apply Finset.sum_eq_zero
        intro w hw
        have hu : ¬ (bipNeighborsB R v ∪ bipNeighborsB R w ⊆ S) := by
          intro h
          exact hv (Finset.Subset.trans Finset.subset_union_left h)
        simp [hu]
    _ = ∑ w ∈ W, ∏ x ∈ bipNeighborsB R v ∪ bipNeighborsB R w, p x := by
      rw [subsetExpectation_sum]
      apply Finset.sum_congr rfl
      intro w hw
      exact subsetExpectation_indicator_superset p _
    _ = rightSurvivalProbability R p v *
        conditionalDegreeFactor R p B₀ u v := by
      unfold rightSurvivalProbability conditionalDegreeFactor
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [prod_union_eq_prod_mul_prod_sdiff]

/-- The expectation of the cardinality of an independently sampled set. -/
theorem subsetExpectation_card (p : A → ℝ) :
    subsetExpectation p (fun S ↦ (S.card : ℝ)) = ∑ u, p u := by
  simpa using subsetExpectation_sum_mem p (fun _ ↦ (1 : ℝ))

/-- Pointwise right-side double counting for the sampled relation. -/
theorem bipRestrictedEdgeCount_sampledRight
    (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (S : Finset A) :
    bipRestrictedEdgeCount R S (sampledRight R B₀ S) =
      ∑ v ∈ B₀, if bipNeighborsB R v ⊆ S then bipDegreeB R v else 0 := by
  rw [bipRestrictedEdgeCount_eq_sum_right, sampledRight, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hvs : bipNeighborsB R v ⊆ S
  · simp only [hvs, if_true]
    exact sampledRight_restricted_degree R B₀ S (mem_sampledRight.mpr ⟨hv, hvs⟩)
  · simp [hvs]

/-- First moment of the number of sampled incidences. -/
theorem subsetExpectation_sampled_edgeCount
    (R : A → B → Prop) [DecidableRel R]
    (p : A → ℝ) (B₀ : Finset B) :
    subsetExpectation p (fun S ↦
        (bipRestrictedEdgeCount R S (sampledRight R B₀ S) : ℝ)) =
      ∑ v ∈ B₀, (bipDegreeB R v : ℝ) *
        rightSurvivalProbability R p v := by
  calc
    subsetExpectation p (fun S ↦
        (bipRestrictedEdgeCount R S (sampledRight R B₀ S) : ℝ)) =
        subsetExpectation p (fun S ↦ ∑ v ∈ B₀,
          if bipNeighborsB R v ⊆ S then (bipDegreeB R v : ℝ) else 0) := by
      congr 1
      funext S
      exact_mod_cast bipRestrictedEdgeCount_sampledRight R B₀ S
    _ = ∑ v ∈ B₀, subsetExpectation p (fun S ↦
          if bipNeighborsB R v ⊆ S then (bipDegreeB R v : ℝ) else 0) :=
      subsetExpectation_sum p B₀ _
    _ = ∑ v ∈ B₀, (bipDegreeB R v : ℝ) *
        rightSurvivalProbability R p v := by
      apply Finset.sum_congr rfl
      intro v hv
      calc
        subsetExpectation p (fun S ↦
            if bipNeighborsB R v ⊆ S then (bipDegreeB R v : ℝ) else 0) =
            subsetExpectation p (fun S ↦ (bipDegreeB R v : ℝ) *
              (if bipNeighborsB R v ⊆ S then (1 : ℝ) else 0)) := by
                congr 1
                funext S
                by_cases h : bipNeighborsB R v ⊆ S <;> simp [h]
        _ = (bipDegreeB R v : ℝ) *
            subsetExpectation p (fun S ↦
              if bipNeighborsB R v ⊆ S then (1 : ℝ) else 0) :=
          subsetExpectation_const_mul p _ _
        _ = (bipDegreeB R v : ℝ) * rightSurvivalProbability R p v := by
          rw [subsetExpectation_indicator_superset]
          rfl

/-- Monotonicity of the finite weighted expectation. -/
theorem subsetExpectation_mono (p : A → ℝ)
    (hp : ∀ u, 0 ≤ p u ∧ p u ≤ 1) {f g : Finset A → ℝ}
    (hfg : ∀ S, f S ≤ g S) :
    subsetExpectation p f ≤ subsetExpectation p g := by
  unfold subsetExpectation
  exact Finset.sum_le_sum fun S hS ↦
    mul_le_mul_of_nonneg_left (hfg S) (subsetWeight_nonneg p hp S)

/-- Event mass in the variable-probability product law. -/
noncomputable def subsetEventMass (p : A → ℝ) (E : Finset A → Prop)
    [DecidablePred E] : ℝ :=
  subsetExpectation p fun S ↦ if E S then 1 else 0

/-- Unnormalised Markov inequality for the bad-incidence event. -/
theorem scale_mul_badIncidenceMass_le
    (R : A → B → Prop) [DecidableRel R]
    (p : A → ℝ) (hp : ∀ u, 0 ≤ p u ∧ p u ≤ 1)
    (B₀ : Finset B) (u : A) (v : B) (z : ℝ) (cutoff : ℕ)
    (hz : 0 ≤ z) (hcutoff : cutoff = ⌊z⌋₊) :
    z * subsetEventMass p (fun S ↦ bipNeighborsB R v ⊆ S ∧
        cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u) ≤
      rightSurvivalProbability R p v *
        conditionalDegreeFactor R p B₀ u v := by
  classical
  rw [subsetEventMass, ← subsetExpectation_const_mul]
  calc
    subsetExpectation p (fun S ↦ z *
        (if bipNeighborsB R v ⊆ S ∧
            cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u
          then 1 else 0)) ≤
        subsetExpectation p (fun S ↦
          if bipNeighborsB R v ⊆ S then
            (bipRestrictedDegreeA R (sampledRight R B₀ S) u : ℝ)
          else 0) := by
      apply subsetExpectation_mono p hp
      intro S
      by_cases hsurv : bipNeighborsB R v ⊆ S
      · by_cases hbad : cutoff <
            bipRestrictedDegreeA R (sampledRight R B₀ S) u
        · simp only [hsurv, hbad, and_self, if_true, mul_one]
          have hzlt : z <
              (bipRestrictedDegreeA R (sampledRight R B₀ S) u : ℝ) := by
            apply Nat.lt_of_floor_lt
            simpa [hcutoff] using hbad
          exact hzlt.le
        · simp [hsurv, hbad, hz]
      · simp [hsurv, hz]
    _ = _ := subsetExpectation_survival_mul_degree R p B₀ u v

/-- Pointwise expansion of the bad-edge count into bad incidences. -/
theorem pruningBadEdgeCount_sampledRight
    (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (S : Finset A) (cutoff : ℕ) :
    pruningBadEdgeCount R S (sampledRight R B₀ S) cutoff =
      ∑ v ∈ B₀, ∑ u ∈ bipNeighborsB R v,
        if bipNeighborsB R v ⊆ S ∧
            cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u
          then 1 else 0 := by
  unfold pruningBadEdgeCount
  rw [bipRestrictedEdgeCount_eq_sum_right, sampledRight, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hvB
  by_cases hv : bipNeighborsB R v ⊆ S
  · simp only [hv, true_and, if_true]
    have heq :
        (pruningBadA R S (sampledRight R B₀ S) cutoff).filter (fun u ↦ R u v) =
          (bipNeighborsB R v).filter fun u ↦
            cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u := by
      ext u
      simp only [Finset.mem_filter, mem_pruningBadA, mem_bipNeighborsB]
      constructor
      · rintro ⟨⟨huS, hbad⟩, huv⟩
        exact ⟨huv, hbad⟩
      · rintro ⟨huv, hbad⟩
        exact ⟨⟨hv (mem_bipNeighborsB.mpr huv), hbad⟩, huv⟩
    change
      ((pruningBadA R S (sampledRight R B₀ S) cutoff).filter (fun u ↦ R u v)).card = _
    rw [heq]
    calc
      ((bipNeighborsB R v).filter (fun u ↦
          cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u)).card =
          ∑ _u ∈ (bipNeighborsB R v).filter (fun u ↦
            cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u), 1 := by simp
      _ = ∑ u ∈ bipNeighborsB R v,
          if cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u
            then 1 else 0 := by rw [Finset.sum_filter]
  · simp only [hv, false_and, if_false]
    simp

/-- First moment of the bad-edge count, expanded as event masses. -/
theorem subsetExpectation_pruningBadEdgeCount
    (R : A → B → Prop) [DecidableRel R]
    (p : A → ℝ) (B₀ : Finset B) (cutoff : ℕ) :
    subsetExpectation p (fun S ↦
        (pruningBadEdgeCount R S (sampledRight R B₀ S) cutoff : ℝ)) =
      ∑ v ∈ B₀, ∑ u ∈ bipNeighborsB R v,
        subsetEventMass p (fun S ↦ bipNeighborsB R v ⊆ S ∧
          cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u) := by
  calc
    subsetExpectation p (fun S ↦
        (pruningBadEdgeCount R S (sampledRight R B₀ S) cutoff : ℝ)) =
        subsetExpectation p (fun S ↦ ∑ v ∈ B₀, ∑ u ∈ bipNeighborsB R v,
          if bipNeighborsB R v ⊆ S ∧
              cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u
            then (1 : ℝ) else 0) := by
      congr 1
      funext S
      exact_mod_cast pruningBadEdgeCount_sampledRight R B₀ S cutoff
    _ = ∑ v ∈ B₀, ∑ u ∈ bipNeighborsB R v,
        subsetExpectation p (fun S ↦
          if bipNeighborsB R v ⊆ S ∧
              cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u
            then (1 : ℝ) else 0) := by
      rw [subsetExpectation_sum]
      apply Finset.sum_congr rfl
      intro v hv
      exact subsetExpectation_sum p (bipNeighborsB R v) _
    _ = _ := by rfl

end Sampling

section ScaleScore

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The score used in the paper is written with the (possibly larger)
dyadic scale `M`, while the public density conclusion is written with the
codegree bound `Q`. -/
theorem isKeyRestriction_pruning_of_scale_score
    {R : A → B → Prop} [DecidableRel R]
    {x r Q cutoff : ℕ} {S : Finset A} {T : Finset B} {M : ℝ}
    (hx : 0 < x) (hr : 0 < r) (hM : (Q : ℝ) ≤ M)
    (hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S)
    (hscore : 0 <
      (bipRestrictedEdgeCount R (pruningSurvivingA R S T cutoff)
          (pruningSurvivingB R S T cutoff) : ℝ) -
        M / (10 * (x : ℝ) * (r : ℝ)) *
          (pruningSurvivingA R S T cutoff).card)
    (hcutoff : (cutoff : ℝ) ≤ 4 * (r : ℝ) * M) :
    IsKeyRestriction R r x Q (pruningSurvivingA R S T cutoff)
      (pruningSurvivingB R S T cutoff) := by
  let A' := pruningSurvivingA R S T cutoff
  let B' := pruningSurvivingB R S T cutoff
  have hdenom : 0 < 10 * (x : ℝ) * (r : ℝ) := by positivity
  have hscale :
      M * (A'.card : ℝ) <
        (10 * (x : ℝ) * (r : ℝ)) *
          (bipRestrictedEdgeCount R A' B' : ℝ) := by
    have hs : M / (10 * (x : ℝ) * (r : ℝ)) * (A'.card : ℝ) <
        (bipRestrictedEdgeCount R A' B' : ℝ) := by
      simpa [A', B'] using (sub_pos.mp hscore)
    calc
      M * (A'.card : ℝ) =
          (10 * (x : ℝ) * (r : ℝ)) *
            (M / (10 * (x : ℝ) * (r : ℝ)) * A'.card) := by
              field_simp
      _ < _ := mul_lt_mul_of_pos_left hs hdenom
  have hnonempty : A'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hA
    have hcardzero : A'.card = 0 := by rw [hA]; simp
    have he : bipRestrictedEdgeCount R A' B' = 0 := by
      rw [hA]
      simp [bipRestrictedEdgeCount]
    have : ¬ (0 : ℝ) < 0 := lt_irrefl 0
    apply this
    simpa [A', B', he, hcardzero] using hscore
  refine ⟨hnonempty, pruning_closed R S T cutoff hclosed, ?_, ?_⟩
  · have hlt :
        (Q : ℝ) * (A'.card : ℝ) <
          (10 * (x : ℝ) * (r : ℝ)) *
            (bipRestrictedEdgeCount R A' B' : ℝ) :=
      (mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)).trans_lt hscale
    exact_mod_cast hlt.le
  · intro u hu
    have hdegNat : bipRestrictedDegreeA R B' u ≤ cutoff :=
      pruning_max_degree R S T cutoff u hu
    have hdegCast : (bipRestrictedDegreeA R B' u : ℝ) ≤ (cutoff : ℝ) := by
      exact_mod_cast hdegNat
    have hdeg : (bipRestrictedDegreeA R B' u : ℝ) ≤ 4 * (r : ℝ) * M :=
      hdegCast.trans hcutoff
    have hlt :
        (bipRestrictedDegreeA R B' u : ℝ) * (A'.card : ℝ) <
          (40 * (x : ℝ) * (r : ℝ) ^ 2) *
            (bipRestrictedEdgeCount R A' B' : ℝ) := by
      calc
        (bipRestrictedDegreeA R B' u : ℝ) * (A'.card : ℝ) ≤
            (4 * (r : ℝ) * M) * A'.card :=
          mul_le_mul_of_nonneg_right hdeg (Nat.cast_nonneg _)
        _ = 4 * (r : ℝ) * (M * A'.card) := by ring
        _ < 4 * (r : ℝ) *
            ((10 * (x : ℝ) * (r : ℝ)) *
              (bipRestrictedEdgeCount R A' B' : ℝ)) :=
          mul_lt_mul_of_pos_left hscale (by positivity)
        _ = (40 * (x : ℝ) * (r : ℝ) ^ 2) *
            (bipRestrictedEdgeCount R A' B' : ℝ) := by ring
    exact_mod_cast hlt.le

end ScaleScore

section SingletonRestriction

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A single positive-degree right vertex already gives a key restriction
when the requested density numerator is at most `10 x r`. -/
theorem exists_keyRestriction_singleton
    (R : A → B → Prop) [DecidableRel R]
    (x r Q : ℕ) (hx : 0 < x) (hr : 0 < r)
    (hregular : ∀ v, bipDegreeB R v = r)
    (hB : Nonempty B) (hQ : Q ≤ 10 * x * r) :
    ∃ A' B', IsKeyRestriction R r x Q A' B' := by
  classical
  let v : B := Classical.choice hB
  let A' : Finset A := bipNeighborsB R v
  let B' : Finset B := {v}
  have hcardA : A'.card = r := hregular v
  have hnonempty : A'.Nonempty := Finset.card_pos.mp (hcardA.trans_gt hr)
  have hedge : bipRestrictedEdgeCount R A' B' = r := by
    calc
      bipRestrictedEdgeCount R A' B' = r * B'.card :=
        bipRestrictedEdgeCount_eq_mul_card R A' B' r (by
          intro w hw
          simp only [B', Finset.mem_singleton] at hw
          subst w
          have heq : A'.filter (fun u ↦ R u v) = A' := by
            apply Finset.filter_eq_self.mpr
            intro u hu
            exact mem_bipNeighborsB.mp hu
          rw [heq, hcardA])
      _ = r := by simp [B']
  refine ⟨A', B', hnonempty, ?_, ?_, ?_⟩
  · rintro ⟨w, hw⟩ u huw
    simp only [B', Finset.mem_singleton] at hw
    subst w
    exact mem_bipNeighborsB.mpr huw
  · rw [hcardA, hedge]
    exact Nat.mul_le_mul_right r hQ
  · intro u hu
    have hdegree : bipRestrictedDegreeA R B' u ≤ 1 := by
      unfold bipRestrictedDegreeA
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [B'])
    rw [hcardA, hedge]
    calc
      bipRestrictedDegreeA R B' u * r ≤ 1 * r :=
        Nat.mul_le_mul_right r hdegree
      _ ≤ 40 * x * r ^ 2 * r := by
        have hpos : 0 < 40 * x * r ^ 2 := by positivity
        have : 1 ≤ 40 * x * r ^ 2 := hpos
        nlinarith

end SingletonRestriction

section Main

variable {A B : Type*} [Fintype A] [Fintype B]

/-- **Janzer--Sudakov Lemma 4.1, relation form.** -/
theorem exists_keyRestriction_core
    (R : A → B → Prop) [DecidableRel R]
    (r s t : ℕ) (hr : 0 < r) (hs : 0 < s) (hst : s < t)
    (hA : Nonempty A)
    (hregular : ∀ v, bipDegreeB R v = r)
    (hmax : ∀ u, bipDegreeA R u ≤ 2 ^ t)
    (hcodeg : ∀ u w, u ≠ w →
      bipCodegree R u w ≤ 2 ^ (r * s - (r - 1) * t))
    (hdensity : 2 ^ s * Fintype.card A ≤ bipEdgeCount R) :
    ∃ A' B',
      IsKeyRestriction R r (t - s) (2 ^ (r * s - (r - 1) * t)) A' B' := by
  classical
  let x := t - s
  let Q := 2 ^ (r * s - (r - 1) * t)
  have hx : 0 < x := by simp [x, Nat.sub_pos_iff_lt, hst]
  have hAcard : 0 < Fintype.card A := Fintype.card_pos_iff.mpr hA
  have hedgepos : 0 < bipEdgeCount R := by
    exact (Nat.mul_pos (by positivity) hAcard).trans_le hdensity
  have hB : Nonempty B := by
    rcases isEmpty_or_nonempty B with h | h
    · have hz : bipEdgeCount R = 0 := by
        simp [bipEdgeCount, bipDegreeA, bipNeighborsA]
      exact False.elim (by omega)
    · exact h
  by_cases hexp : (r - 1) * t ≤ r * s
  · let alpha : A → ℕ := bucketIndex R s
    obtain ⟨gamma, hgammaLower, hgammaUpper, hlarge, hbeta⟩ :=
      exists_large_bucketFiber R hr hst hregular hmax
    let B₀ : Finset B := bucketFiber R s gamma
    let p : A → ℝ := dyadicProbability alpha t
    let M : ℝ := dyadicConditionalScale gamma r t
    let q : ℝ := (2 : ℝ) ^ gamma / (2 : ℝ) ^ (t * r)
    let cutoff : ℕ := ⌊4 * (r : ℝ) * M⌋₊
    have halphaUpper : ∀ u, alpha u ≤ t :=
      fun u ↦ bucketIndex_upper R hst hmax u
    have halphaLower : ∀ u, s + 1 ≤ alpha u :=
      fun u ↦ bucketIndex_lower R s u
    have hdegreeAlpha : ∀ u, bipDegreeA R u ≤ 2 ^ alpha u :=
      fun u ↦ degree_le_two_pow_bucketIndex R s u
    have hp : ∀ u, 0 ≤ p u ∧ p u ≤ 1 :=
      fun u ↦ dyadicProbability_mem_unitInterval alpha t halphaUpper u
    have hbeta' : ∀ v ∈ B₀,
        ∑ u ∈ bipNeighborsB R v, alpha u = gamma := by
      intro v hv
      exact hbeta v hv
    have hMpos : 0 < M := by
      dsimp [M, dyadicConditionalScale]
      positivity
    have hqpos : 0 < q := by
      dsimp [q]
      positivity
    have hsurvival : ∀ v ∈ B₀,
        rightSurvivalProbability R p v = q := by
      intro v hv
      unfold rightSurvivalProbability
      simp only [p, q]
      rw [prod_dyadicProbability, hbeta' v hv]
      have hcard : (bipNeighborsB R v).card = r := hregular v
      rw [hcard]
    have hMgeQ : (Q : ℝ) ≤ M := by
      have hQr : Q ≤ r * Q := by
        have := Nat.mul_le_mul_left Q (show 1 ≤ r by omega)
        simpa [Nat.mul_comm] using this
      calc
        (Q : ℝ) ≤ (r * Q : ℕ) := by exact_mod_cast hQr
        _ ≤ M := by
          simpa [Q, M] using
            dyadic_codegree_term_le r s t gamma hexp hgammaLower
    have hbadMass : ∀ v ∈ B₀, ∀ u, R u v →
        2 * (r : ℝ) * subsetEventMass p
          (fun S ↦ bipNeighborsB R v ⊆ S ∧
            cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u) ≤ q := by
      intro v hv u huv
      let mass := subsetEventMass p
        (fun S ↦ bipNeighborsB R v ⊆ S ∧
          cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u)
      have hmarkov := scale_mul_badIncidenceMass_le R p hp B₀ u v
        (4 * (r : ℝ) * M) cutoff (by positivity) rfl
      have hcond := (js_conditional_product_bound R B₀ alpha r s t gamma u v hv huv
        halphaUpper halphaLower hdegreeAlpha
        (fun w hw ↦ hregular w) hbeta' hexp
        (fun x hxu ↦ hcodeg u x (Ne.symm hxu))).2
      rw [hsurvival v hv] at hmarkov hcond
      have hcancel : 2 * (r : ℝ) * mass ≤ q := by
        have hmul : (2 * M) * (2 * (r : ℝ) * mass) ≤ (2 * M) * q := by
          calc
          (2 * M) * (2 * (r : ℝ) * mass) =
              (4 * (r : ℝ) * M) * mass := by ring
          _ ≤ q * conditionalDegreeFactor R p B₀ u v := hmarkov
          _ ≤ q * (2 * M) := hcond
          _ = (2 * M) * q := by ring
        exact le_of_mul_le_mul_left hmul (by positivity)
      exact hcancel
    let EX := subsetExpectation p (fun S ↦
      (bipRestrictedEdgeCount R S (sampledRight R B₀ S) : ℝ))
    let EY := subsetExpectation p (fun S ↦
      (pruningBadEdgeCount R S (sampledRight R B₀ S) cutoff : ℝ))
    let ES := subsetExpectation p (fun S ↦ (S.card : ℝ))
    have hEX : EX = (r : ℝ) * (B₀.card : ℝ) * q := by
      dsimp [EX]
      rw [subsetExpectation_sampled_edgeCount]
      calc
        (∑ v ∈ B₀, (bipDegreeB R v : ℝ) *
            rightSurvivalProbability R p v) =
            ∑ _v ∈ B₀, (r : ℝ) * q := by
              apply Finset.sum_congr rfl
              intro v hv
              rw [hregular v, hsurvival v hv]
        _ = (r : ℝ) * (B₀.card : ℝ) * q := by
          simp
          ring
    have htwoEY : 2 * (r : ℝ) * EY ≤ EX := by
      dsimp [EY]
      rw [subsetExpectation_pruningBadEdgeCount, hEX]
      calc
        2 * (r : ℝ) *
            (∑ v ∈ B₀, ∑ u ∈ bipNeighborsB R v,
              subsetEventMass p (fun S ↦ bipNeighborsB R v ⊆ S ∧
                cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u)) =
            ∑ v ∈ B₀, ∑ u ∈ bipNeighborsB R v,
              2 * (r : ℝ) * subsetEventMass p
                (fun S ↦ bipNeighborsB R v ⊆ S ∧
                  cutoff < bipRestrictedDegreeA R (sampledRight R B₀ S) u) := by
            simp_rw [Finset.mul_sum]
        _ ≤ ∑ v ∈ B₀, ∑ _u ∈ bipNeighborsB R v, q := by
          apply Finset.sum_le_sum
          intro v hv
          apply Finset.sum_le_sum
          intro u hu
          exact hbadMass v hv u (mem_bipNeighborsB.mp hu)
        _ = (r : ℝ) * (B₀.card : ℝ) * q := by
          have hcard : ∀ v : B, (bipNeighborsB R v).card = r := hregular
          simp_rw [Finset.sum_const, nsmul_eq_mul, hcard]
          simp
          ring
    have hedgeEq : bipEdgeCount R = r * Fintype.card B := by
      rw [bipEdgeCount_eq_sum_degreeB]
      simp [hregular, Nat.mul_comm]
    have hratioNat : bipEdgeCount R ≤ x * r * (r * B₀.card) := by
      calc
        bipEdgeCount R = r * Fintype.card B := hedgeEq
        _ ≤ r * (r * (t - s) * B₀.card) := Nat.mul_le_mul_left r hlarge
        _ = x * r * (r * B₀.card) := by
          simp only [x]
          ring
    have hEXlower :
        (bipEdgeCount R : ℝ) * q / ((x : ℝ) * (r : ℝ)) ≤ EX := by
      rw [hEX]
      rw [div_le_iff₀ (show 0 < (x : ℝ) * (r : ℝ) by positivity)]
      have hc : (bipEdgeCount R : ℝ) ≤
          (x : ℝ) * (r : ℝ) * ((r : ℝ) * B₀.card) := by
        exact_mod_cast hratioNat
      calc
        (bipEdgeCount R : ℝ) * q ≤
            ((x : ℝ) * (r : ℝ) * ((r : ℝ) * B₀.card)) * q :=
          mul_le_mul_of_nonneg_right hc hqpos.le
        _ = ((r : ℝ) * B₀.card * q) * ((x : ℝ) * r) := by ring
    have hsumPow : ∑ u : A, 2 ^ alpha u ≤ 4 * bipEdgeCount R := by
      calc
        ∑ u : A, 2 ^ alpha u ≤
            ∑ u : A, (2 ^ (s + 1) + 2 * bipDegreeA R u) :=
          Finset.sum_le_sum fun u hu ↦ two_pow_bucketIndex_le R s u
        _ = 2 ^ (s + 1) * Fintype.card A + 2 * bipEdgeCount R := by
          simp [bipEdgeCount, Finset.sum_add_distrib, Finset.mul_sum,
            Nat.mul_comm]
        _ ≤ 4 * bipEdgeCount R := by
          calc
            2 ^ (s + 1) * Fintype.card A + 2 * bipEdgeCount R =
                2 * (2 ^ s * Fintype.card A) + 2 * bipEdgeCount R := by
              rw [pow_succ]
              ring
            _ ≤ 2 * bipEdgeCount R + 2 * bipEdgeCount R :=
              Nat.add_le_add_right (Nat.mul_le_mul_left 2 hdensity) _
            _ = 4 * bipEdgeCount R := by ring
    have hES : ES ≤ 4 * (bipEdgeCount R : ℝ) / (2 : ℝ) ^ t := by
      dsimp [ES]
      rw [subsetExpectation_card]
      have hden : 0 < (2 : ℝ) ^ t := by positivity
      calc
        (∑ u : A, p u) = (∑ u : A, (2 ^ alpha u : ℕ) : ℝ) /
            (2 : ℝ) ^ t := by
          simp only [p, dyadicProbability, Finset.sum_div, Nat.cast_pow,
            Nat.cast_ofNat, Nat.cast_sum]
        _ ≤ (4 * (bipEdgeCount R : ℝ)) / (2 : ℝ) ^ t := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hsumPow) hden.le
    have hMq : M / (2 : ℝ) ^ t = q := by
      have htr : t * r = t + (r - 1) * t := by
        conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ r by omega)]
        simp [Nat.mul_add, Nat.add_comm, Nat.mul_comm]
      dsimp [M, q, dyadicConditionalScale]
      rw [htr, pow_add]
      field_simp
    let c : ℝ := M / (10 * (x : ℝ) * (r : ℝ))
    have hcnonneg : 0 ≤ c := by dsimp [c]; positivity
    have hcost : c * ES ≤
        (2 / 5 : ℝ) *
          ((bipEdgeCount R : ℝ) * q / ((x : ℝ) * (r : ℝ))) := by
      calc
        c * ES ≤ c * (4 * (bipEdgeCount R : ℝ) / (2 : ℝ) ^ t) :=
          mul_le_mul_of_nonneg_left hES hcnonneg
        _ = (2 / 5 : ℝ) *
            ((bipEdgeCount R : ℝ) * q / ((x : ℝ) * (r : ℝ))) := by
          dsimp [c]
          rw [← hMq]
          field_simp
          ring
    let score : Finset A → ℝ := fun S ↦
      (bipRestrictedEdgeCount R S (sampledRight R B₀ S) : ℝ) -
        (r : ℝ) * pruningBadEdgeCount R S (sampledRight R B₀ S) cutoff -
        c * S.card
    have hEscore : subsetExpectation p score = EX - (r : ℝ) * EY - c * ES := by
      have hsub (f g : Finset A → ℝ) :
          subsetExpectation p (fun S ↦ f S - g S) =
            subsetExpectation p f - subsetExpectation p g := by
        unfold subsetExpectation
        simp only [mul_sub, Finset.sum_sub_distrib]
      dsimp [score, EX, EY, ES]
      rw [hsub, hsub, subsetExpectation_const_mul, subsetExpectation_const_mul]
    have hscorePos : 0 < subsetExpectation p score := by
      rw [hEscore]
      let L := (bipEdgeCount R : ℝ) * q / ((x : ℝ) * (r : ℝ))
      have hLpos : 0 < L := by dsimp [L]; positivity
      have hhalf : EX / 2 ≤ EX - (r : ℝ) * EY := by linarith
      have hLhalf : L / 2 ≤ EX / 2 := by
        exact div_le_div_of_nonneg_right hEXlower (by norm_num)
      have hcost' : c * ES ≤ (2 / 5 : ℝ) * L := by simpa [L] using hcost
      linarith
    obtain ⟨S, hSsub, hscoreS⟩ := exists_pos_of_subsetExpectation_pos p hp score hscorePos
    let T := sampledRight R B₀ S
    let A' := pruningSurvivingA R S T cutoff
    let B' := pruningSurvivingB R S T cutoff
    have hclosed : ∀ v ∈ T, ∀ u, R u v → u ∈ S :=
      sampledRight_closed R B₀ S
    have hregT : ∀ v ∈ T, (S.filter fun u ↦ R u v).card = r := by
      intro v hv
      rw [sampledRight_restricted_degree R B₀ S hv]
      exact hregular v
    have hprune := pruning_edgeCount_le_add R S T cutoff r hclosed hregT
    have hpruneReal :
        (bipRestrictedEdgeCount R S T : ℝ) -
            (r : ℝ) * pruningBadEdgeCount R S T cutoff ≤
          (bipRestrictedEdgeCount R A' B' : ℝ) := by
      have hcast : (bipRestrictedEdgeCount R S T : ℝ) ≤
          (bipRestrictedEdgeCount R A' B' : ℝ) +
            (r : ℝ) * pruningBadEdgeCount R S T cutoff := by
        exact_mod_cast hprune
      linarith
    have hcardA' : A'.card ≤ S.card :=
      Finset.card_le_card (pruningSurvivingA_subset R S T cutoff)
    have hactualScore : 0 <
        (bipRestrictedEdgeCount R A' B' : ℝ) - c * A'.card := by
      have hcardReal : (A'.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcardA'
      have hcostmono := mul_le_mul_of_nonneg_left hcardReal hcnonneg
      dsimp [score, T] at hscoreS
      linarith
    refine ⟨A', B', ?_⟩
    apply isKeyRestriction_pruning_of_scale_score hx hr hMgeQ hclosed
    · simpa [A', B', c] using hactualScore
    · dsimp [cutoff]
      exact Nat.floor_le (by positivity)
  · have hzero : r * s - (r - 1) * t = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_lt (lt_of_not_ge hexp))
    have hQone : Q = 1 := by simp [Q, hzero]
    apply exists_keyRestriction_singleton R x r Q hx hr hregular hB
    rw [hQone]
    have : 0 < 10 * x * r := by positivity
    omega

#print axioms exists_keyRestriction_core

end Main

end Erdos182
