import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Uniform probability on a finite type

This file records the elementary counting facts needed for the exact
finite random-graph model.  We deliberately define probability as a real
cardinality ratio.  Consequently all events are available without any
measurability hypotheses, and every result below is a finite counting
identity or inequality.
-/

open scoped BigOperators
open Filter

namespace Erdos746.FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Uniform probability of a predicate on a finite type.  On the empty type
this is zero, by the field convention `0 / 0 = 0`. -/
def prob (event : Omega -> Prop) : Real := by
  exact ({omega : Omega | event omega}.ncard : Real) / Nat.card Omega

/-- The defining cardinal-ratio formula, exposed for rewriting. -/
theorem prob_eq_filter_card_div (event : Omega -> Prop) [DecidablePred event] :
    prob event =
      ((Finset.univ.filter event).card : Real) / Fintype.card Omega := by
  classical
  rw [prob, Set.ncard_eq_toFinset_card, Nat.card_eq_fintype_card]
  congr 1
  norm_cast
  apply congrArg Finset.card
  ext omega
  simp

/-- Equivalent cardinal-ratio formula using the subtype of successful
outcomes. -/
theorem prob_eq_subtype_card_div (event : Omega -> Prop) :
    prob event =
      (Nat.card {omega : Omega // event omega} : Real) / Nat.card Omega := by
  rw [prob]
  congr 1

@[simp]
theorem prob_false : prob (fun _ : Omega => False) = 0 := by
  simp [prob]

@[simp]
theorem prob_true [Nonempty Omega] : prob (fun _ : Omega => True) = 1 := by
  have hcard : (Nat.card Omega : Real) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  simp [prob, hcard]

theorem prob_nonneg (event : Omega -> Prop) : 0 <= prob event := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem prob_le_one (event : Omega -> Prop) : prob event <= 1 := by
  cases isEmpty_or_nonempty Omega with
  | inl h => simp [prob]
  | inr h =>
      rw [prob, div_le_one (by
        rw [Nat.card_eq_fintype_card]
        exact_mod_cast Fintype.card_pos)]
      exact_mod_cast Set.ncard_le_card {omega : Omega | event omega}

theorem prob_mem_Icc (event : Omega -> Prop) : prob event ∈ Set.Icc (0 : Real) 1 :=
  ⟨prob_nonneg event, prob_le_one event⟩

/-- Monotonicity under pointwise implication of events. -/
theorem prob_mono {event₁ event₂ : Omega -> Prop}
    (h : forall omega, event₁ omega -> event₂ omega) :
    prob event₁ <= prob event₂ := by
  rw [prob, prob]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard (by
    intro omega homega
    exact h omega homega)

/-- The complement rule on a nonempty finite sample space. -/
theorem prob_compl [Nonempty Omega] (event : Omega -> Prop) :
    prob (fun omega => ¬ event omega) = 1 - prob event := by
  classical
  rw [prob, prob]
  have hcard : (Nat.card Omega : Real) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  let successful : Set Omega := {omega | event omega}
  have heq : {omega : Omega | ¬ event omega} = successfulᶜ := by
    ext omega
    simp [successful]
  rw [heq, Set.ncard_compl successful]
  rw [Nat.cast_sub (Set.ncard_le_card successful)]
  simp only [successful]
  field_simp

/-- The union bound for two events. -/
theorem prob_or_le (event₁ event₂ : Omega -> Prop) :
    prob (fun omega => event₁ omega ∨ event₂ omega) <=
      prob event₁ + prob event₂ := by
  classical
  rw [prob, prob, prob]
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_union_le {omega : Omega | event₁ omega}
    {omega : Omega | event₂ omega}

/-- Finite union bound, indexed by a `Finset`. -/
theorem prob_exists_mem_le_sum {I : Type*} (s : Finset I)
    (event : I -> Omega -> Prop) :
    prob (fun omega => ∃ i ∈ s, event i omega) <=
      ∑ i ∈ s, prob (event i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      calc
        prob (fun omega => ∃ j ∈ insert i s, event j omega) =
            prob (fun omega => event i omega ∨ ∃ j ∈ s, event j omega) := by
              congr 1
              funext omega
              simp
        _ <= prob (event i) + prob (fun omega => ∃ j ∈ s, event j omega) :=
          prob_or_le _ _
        _ <= prob (event i) + ∑ j ∈ s, prob (event j) := add_le_add_right ih _
        _ = ∑ j ∈ insert i s, prob (event j) := by simp [hi]

/-- Exact probability formula when the sample space itself is a filtered
finite set.  This is the form used for uniform fixed-size graph layers. -/
theorem prob_subtype_finset {Alpha : Type*} [DecidableEq Alpha]
    (sample : Finset Alpha) (event : Alpha -> Prop) [DecidablePred event] :
    @prob {x : Alpha // x ∈ sample}
        (fun x => event x.1) =
      ((sample.filter event).card : Real) / sample.card := by
  classical
  rw [prob_eq_filter_card_div]
  simp only [Fintype.card_coe, Set.ncard_coe_finset]
  congr 1
  norm_cast
  simpa using congrArg Finset.card (Finset.filter_attach event sample)

/-- A real sequence converges to one exactly when its complementary failure
sequence converges to zero. -/
theorem tendsto_one_iff_tendsto_one_sub_zero {I : Type*} {l : Filter I}
    (p : I -> Real) :
    Tendsto p l (nhds 1) <->
      Tendsto (fun i => 1 - p i) l (nhds 0) := by
  constructor
  · intro hp
    have hone : Tendsto (fun _ : I => (1 : Real)) l (nhds 1) := tendsto_const_nhds
    simpa using hone.sub hp
  · intro hfail
    have hone : Tendsto (fun _ : I => (1 : Real)) l (nhds 1) := tendsto_const_nhds
    have h := hone.sub hfail
    convert h using 1 <;> ring

/-- Event version of the preceding limit equivalence on a fixed nonempty
sample space. -/
theorem tendsto_prob_one_iff_tendsto_compl_zero [Nonempty Omega]
    {I : Type*} {l : Filter I} (event : I -> Omega -> Prop) :
    Tendsto (fun i => prob (event i)) l (nhds 1) <->
      Tendsto (fun i => prob (fun omega => ¬ event i omega)) l (nhds 0) := by
  rw [tendsto_one_iff_tendsto_one_sub_zero]
  apply tendsto_congr'
  exact Filter.Eventually.of_forall fun i => (prob_compl (event i)).symm

end

end Erdos746.FiniteProbability
