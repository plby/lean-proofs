import ErdosProblems.Erdos556.Bernoulli

/-!
# Finite sampling bounds

Union bounds, Markov's inequality, and independent containment events are
proved as finite real sums. These are the probabilistic inputs to the
connecting-reservoir construction.
-/

namespace Erdos556.Bernoulli

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

theorem eventMass_nonneg {Ω : Type*} [Fintype Ω] (mass : Ω → ℝ)
    (hmass : ∀ x, 0 ≤ mass x) (A : Ω → Prop) : 0 ≤ eventMass mass A := by
  apply sum_nonneg
  intro x _
  split_ifs <;> simp_all

theorem eventMass_mono {Ω : Type*} [Fintype Ω] (mass : Ω → ℝ)
    (hmass : ∀ x, 0 ≤ mass x) {A B : Ω → Prop} (hAB : ∀ x, A x → B x) :
    eventMass mass A ≤ eventMass mass B := by
  apply sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp_all

theorem eventMass_not {Ω : Type*} [Fintype Ω] (mass : Ω → ℝ)
    (hsum : ∑ x, mass x = 1) (A : Ω → Prop) :
    eventMass mass (fun x => ¬ A x) = 1 - eventMass mass A := by
  have hsplit : eventMass mass A + eventMass mass (fun x => ¬ A x) = 1 := by
    unfold eventMass
    rw [← sum_add_distrib, ← hsum]
    apply sum_congr rfl
    intro x _
    by_cases ha : A x <;> simp [ha]
  linarith

theorem eventMass_or_le {Ω : Type*} [Fintype Ω] (mass : Ω → ℝ)
    (hmass : ∀ x, 0 ≤ mass x) (A B : Ω → Prop) :
    eventMass mass (fun x => A x ∨ B x) ≤ eventMass mass A + eventMass mass B := by
  unfold eventMass
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb, hmass x]

theorem eventMass_exists_le {Ω I : Type*} [Fintype Ω] [Fintype I]
    (mass : Ω → ℝ) (hmass : ∀ x, 0 ≤ mass x) (A : I → Ω → Prop) :
    eventMass mass (fun x => ∃ i, A i x) ≤ ∑ i, eventMass mass (A i) := by
  unfold eventMass
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases h : ∃ i, A i x
  · obtain ⟨i, hi⟩ := h
    rw [if_pos ⟨i, hi⟩]
    have hle := single_le_sum (s := (univ : Finset I))
      (f := fun j => if A j x then mass x else 0)
      (fun j _ => by split_ifs <;> simp_all) (mem_univ i)
    simpa only [if_pos hi] using hle
  · rw [if_neg h]
    apply sum_nonneg
    intro i _
    split_ifs <;> simp_all

theorem eventMass_markov {Ω : Type*} [Fintype Ω]
    (mass X : Ω → ℝ) (hmass : ∀ x, 0 ≤ mass x) (hX : ∀ x, 0 ≤ X x) (t : ℝ) :
    t * eventMass mass (fun x => t < X x) ≤ ∑ x, mass x * X x := by
  unfold eventMass
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  by_cases hx : t < X x
  · rw [if_pos hx, mul_comm t]
    exact mul_le_mul_of_nonneg_left hx.le (hmass x)
  · rw [if_neg hx, mul_zero]
    exact mul_nonneg (hmass x) (hX x)

theorem exists_avoiding_of_eventMass_lt_one {Ω : Type*} [Fintype Ω]
    (mass : Ω → ℝ) (hsum : ∑ x, mass x = 1) (A : Ω → Prop)
    (hA : eventMass mass A < 1) : ∃ x, ¬ A x := by
  by_contra h
  push Not at h
  have heq : eventMass mass A = 1 := by simp [eventMass, h, hsum]
  linarith

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem sum_full_bernoulliMass (p : E → ℝ) :
    ∑ S : Finset E, bernoulliMass univ p S = 1 := by
  have h := eventMass_eq_restrictedEventMass_univ p (fun _ => True)
  simpa only [eventMass, if_true, restrictedEventMass_true] using h

theorem contains_dependsOn (L : Finset E) : EventDependsOn L (fun X => L ⊆ X) := by
  intro X Y hXY
  unfold AgreesOn at hXY
  constructor
  · intro hLX x hxL
    have hx : x ∈ X ∩ L := mem_inter.mpr ⟨hLX hxL, hxL⟩
    rw [hXY] at hx
    exact (mem_inter.mp hx).1
  · intro hLY x hxL
    have hx : x ∈ Y ∩ L := mem_inter.mpr ⟨hLY hxL, hxL⟩
    rw [← hXY] at hx
    exact (mem_inter.mp hx).1

theorem eventDependsOn_not {L : Finset E} {A : Finset E → Prop}
    (hA : EventDependsOn L A) : EventDependsOn L (fun X => ¬ A X) := by
  intro X Y hXY
  exact not_congr (hA X Y hXY)

theorem eventMass_contains (p : E → ℝ) (L : Finset E) :
    eventMass (bernoulliMass univ p) (fun X => L ⊆ X) = ∏ e ∈ L, p e := by
  rw [eventMass_eq_restrictedEventMass (contains_dependsOn L)]
  unfold restrictedEventMass
  rw [sum_eq_single (⟨L, subset_rfl⟩ : Subsets L)]
  · simp [bernoulliMass]
  · intro X _ hX
    have hn : ¬ L ⊆ X.val := by
      intro h
      exact hX (Subtype.ext (Subset.antisymm X.property h))
    simp [hn]
  · simp

#print axioms eventMass_contains

theorem eventDependsOn_forall_mem {I : Type*} [DecidableEq I]
    (R : I → Finset E) (A : I → Finset E → Prop)
    (hA : ∀ i, EventDependsOn (R i) (A i)) (J : Finset I) :
    EventDependsOn (J.biUnion R) (fun S => ∀ i ∈ J, A i S) := by
  intro S T hST
  constructor
  · intro h i hi
    have hsub : R i ⊆ J.biUnion R := subset_biUnion_of_mem R hi
    exact (hA i S T (agreesOn_mono hsub hST)).mp (h i hi)
  · intro h i hi
    have hsub : R i ⊆ J.biUnion R := subset_biUnion_of_mem R hi
    exact (hA i S T (agreesOn_mono hsub hST)).mpr (h i hi)

theorem eventMass_forall_eq_prod {I : Type*} [DecidableEq I]
    (p : E → ℝ) (R : I → Finset E) (A : I → Finset E → Prop)
    (hA : ∀ i, EventDependsOn (R i) (A i)) (J : Finset I)
    (hdisj : (J : Set I).Pairwise fun i j => Disjoint (R i) (R j)) :
    eventMass (bernoulliMass univ p) (fun S => ∀ i ∈ J, A i S) =
      ∏ i ∈ J, eventMass (bernoulliMass univ p) (A i) := by
  revert hdisj
  induction J using Finset.induction_on with
  | empty =>
      intro _
      simp [eventMass, sum_full_bernoulliMass]
  | @insert i J hi ih =>
      intro hdisj
      have hD : Disjoint (R i) (J.biUnion R) := by
        rw [disjoint_biUnion_right]
        intro j hj
        exact hdisj (mem_insert_self i J) (mem_insert_of_mem hj)
          (by intro h; subst j; exact hi hj)
      have hDJ : (J : Set I).Pairwise fun i j => Disjoint (R i) (R j) :=
        hdisj.mono (subset_insert i J)
      simp only [forall_mem_insert, prod_insert hi]
      rw [eventMass_and_of_disjoint hD (hA i)
        (eventDependsOn_forall_mem R A hA J), ih hDJ]

/-- The probability that none of a disjoint family of sets is fully sampled. -/
theorem eventMass_missing_all {I : Type*} [DecidableEq I]
    (q : ℝ) (R : I → Finset E) (J : Finset I)
    (hdisj : (J : Set I).Pairwise fun i j => Disjoint (R i) (R j)) :
    eventMass (bernoulliMass univ (fun _ : E => q))
      (fun S => ∀ i ∈ J, ¬ R i ⊆ S) = ∏ i ∈ J, (1 - q ^ (R i).card) := by
  rw [eventMass_forall_eq_prod (fun _ => q) R (fun i S => ¬ R i ⊆ S)
    (fun i => eventDependsOn_not (contains_dependsOn (R i))) J hdisj]
  apply prod_congr rfl
  intro i _
  rw [eventMass_not _ (sum_full_bernoulliMass _) (fun S => R i ⊆ S),
    eventMass_contains]
  simp

theorem eventMass_missing_all_le {I : Type*} [DecidableEq I]
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (R : I → Finset E) (J : Finset I)
    (hdisj : (J : Set I).Pairwise fun i j => Disjoint (R i) (R j)) (L : ℕ)
    (hsize : ∀ i ∈ J, (R i).card ≤ L) :
    eventMass (bernoulliMass univ (fun _ : E => q))
      (fun S => ∀ i ∈ J, ¬ R i ⊆ S) ≤ (1 - q ^ L) ^ J.card := by
  rw [eventMass_missing_all q R J hdisj]
  calc
    ∏ i ∈ J, (1 - q ^ (R i).card) ≤ ∏ _i ∈ J, (1 - q ^ L) := by
      apply prod_le_prod
      · intro i _
        exact sub_nonneg.mpr (pow_le_one₀ hq0 hq1)
      · intro i hi
        exact sub_le_sub_left (pow_le_pow_of_le_one hq0 hq1 (hsize i hi)) 1
    _ = (1 - q ^ L) ^ J.card := by simp

#print axioms eventMass_missing_all_le

/-- A small sample contains a member of every prescribed disjoint family.
The explicit failure bound is what will later be checked for the graph
families; no independence between distinct families is needed. -/
theorem exists_small_set_hitting_families {I : Type*} [Fintype I]
    (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) (L m : ℕ)
    (R : I → Fin m → Finset E)
    (hdisj : ∀ i, (Set.univ : Set (Fin m)).Pairwise
      fun j k => Disjoint (R i j) (R i k))
    (hsize : ∀ i j, (R i j).card ≤ L)
    (hfail : (Fintype.card I : ℝ) * (1 - q ^ L) ^ m < 1 / 2)
    (hE : 0 < Fintype.card E) :
    ∃ S : Finset E, (S.card : ℝ) ≤ 2 * q * Fintype.card E ∧
      ∀ i, ∃ j, R i j ⊆ S := by
  let mass : Finset E → ℝ := bernoulliMass univ (fun _ => q)
  have hmass (S : Finset E) : 0 ≤ mass S :=
    bernoulliMass_nonneg (subset_univ S) (fun _ _ => hq0.le) (fun _ _ => hq1)
  have hsum : ∑ S, mass S = 1 := sum_full_bernoulliMass _
  have hmean : ∑ S : Finset E, mass S * (S.card : ℝ) =
      q * Fintype.card E := by
    simpa [mass, mul_comm] using
      sum_bernoulliMass_mul_card (univ : Finset E) (fun _ => q)
  let t : ℝ := 2 * q * Fintype.card E
  have ht : 0 < t := by
    dsimp [t]
    exact mul_pos (mul_pos (by norm_num) hq0) (by exact_mod_cast hE)
  have hlarge : eventMass mass (fun S => t < (S.card : ℝ)) ≤ 1 / 2 := by
    apply (mul_le_mul_iff_right₀ ht).mp
    calc
      t * eventMass mass (fun S => t < (S.card : ℝ)) ≤
          ∑ S : Finset E, mass S * (S.card : ℝ) :=
        eventMass_markov mass (fun S => S.card) hmass (fun S => by positivity) t
      _ = t * (1 / 2) := by rw [hmean]; dsimp [t]; ring
  let bad : I → Finset E → Prop := fun i S => ∀ j, ¬ R i j ⊆ S
  have hbad (i : I) : eventMass mass (bad i) ≤ (1 - q ^ L) ^ m := by
    simpa only [mass, bad, mem_univ, forall_true_left, card_univ, Fintype.card_fin]
      using eventMass_missing_all_le q hq0.le hq1 (R i) univ
        (by simpa only [coe_univ] using hdisj i) L (fun j _ => hsize i j)
  have hsome : eventMass mass (fun S => ∃ i, bad i S) < 1 / 2 := by
    calc
      eventMass mass (fun S => ∃ i, bad i S) ≤ ∑ i, eventMass mass (bad i) :=
        eventMass_exists_le mass hmass bad
      _ ≤ ∑ _i : I, (1 - q ^ L) ^ m := sum_le_sum (fun i _ => hbad i)
      _ = (Fintype.card I : ℝ) * (1 - q ^ L) ^ m := by simp
      _ < 1 / 2 := hfail
  have hall : eventMass mass (fun S => t < (S.card : ℝ) ∨ ∃ i, bad i S) < 1 := by
    have h := eventMass_or_le mass hmass
      (fun S => t < (S.card : ℝ)) (fun S => ∃ i, bad i S)
    linarith
  obtain ⟨S, hS⟩ := exists_avoiding_of_eventMass_lt_one mass hsum _ hall
  refine ⟨S, le_of_not_gt (fun h => hS (Or.inl h)), ?_⟩
  intro i
  by_contra hi
  push Not at hi
  exact hS (Or.inr ⟨i, hi⟩)

#print axioms exists_small_set_hitting_families

end

end Erdos556.Bernoulli
