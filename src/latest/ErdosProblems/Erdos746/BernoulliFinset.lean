import ErdosProblems.Erdos746.BinomialBounds

/-!
# Bernoulli product probability on a finite powerset

This file develops the elementary finite probability space in which every
element of a finite set `U` is selected independently with probability `p`.
All probabilities are explicit finite sums, so no measurability hypotheses
are needed.
-/

open scoped BigOperators

namespace Erdos746.BernoulliFinset

noncomputable section

variable {α : Type*} [DecidableEq α]

/-- Bernoulli weight of `A` relative to the finite universe `U`.  The intended
sample space is `U.powerset`; outside that sample space the value is merely a
convenient total extension. -/
def weight (U : Finset α) (p : ℝ) (A : Finset α) : ℝ :=
  p ^ A.card * (1 - p) ^ (U.card - A.card)

/-- Mass of an event in the finite Bernoulli subset space. -/
def eventMass (U : Finset α) (p : ℝ) (event : Finset α → Prop) : ℝ := by
  classical
  exact ∑ A ∈ U.powerset.filter event, weight U p A

/-- On subsets of `U`, the power formula for `weight` agrees with the usual
coordinatewise Bernoulli product. -/
theorem weight_eq_prod {U A : Finset α} (hA : A ⊆ U) (p : ℝ) :
    weight U p A =
      (∏ _i ∈ A, p) * ∏ _i ∈ U \ A, (1 - p) := by
  rw [weight, Finset.prod_const, Finset.prod_const]
  congr 2
  rw [Finset.card_sdiff]
  simpa [Finset.inter_eq_left.mpr hA]

/-- The Bernoulli weights have total mass one. -/
@[simp] theorem sum_weight_powerset (U : Finset α) (p : ℝ) :
    (∑ A ∈ U.powerset, weight U p A) = 1 := by
  calc
    (∑ A ∈ U.powerset, weight U p A) =
        ∑ A ∈ U.powerset,
          (∏ _i ∈ A, p) * ∏ _i ∈ U \ A, (1 - p) := by
            apply Finset.sum_congr rfl
            intro A hA
            exact weight_eq_prod (Finset.mem_powerset.mp hA) p
    _ = ∏ _i ∈ U, (p + (1 - p)) := by
      rw [Finset.prod_add]
    _ = 1 := by simp

@[simp] theorem eventMass_true (U : Finset α) (p : ℝ) :
    eventMass U p (fun _ => True) = 1 := by
  simp [eventMass]

@[simp] theorem eventMass_false (U : Finset α) (p : ℝ) :
    eventMass U p (fun _ => False) = 0 := by
  simp [eventMass]

/-- Every atom has nonnegative mass when `p ∈ [0,1]`. -/
theorem weight_nonneg {U A : Finset α} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ weight U p A := by
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- Every event has nonnegative mass when `p ∈ [0,1]`. -/
theorem eventMass_nonneg (U : Finset α) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (event : Finset α → Prop) :
    0 ≤ eventMass U p event := by
  classical
  exact Finset.sum_nonneg fun A _ => weight_nonneg hp0 hp1

/-- Monotonicity of finite Bernoulli event mass. -/
theorem eventMass_mono (U : Finset α) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (event₁ event₂ : Finset α → Prop)
    (h : ∀ A, event₁ A → event₂ A) :
    eventMass U p event₁ ≤ eventMass U p event₂ := by
  classical
  unfold eventMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro A hA
    rw [Finset.mem_filter] at hA ⊢
    exact ⟨hA.1, h A hA.2⟩
  · intro A _ _
    exact weight_nonneg hp0 hp1

/-- Every event has mass at most one. -/
theorem eventMass_le_one (U : Finset α) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (event : Finset α → Prop) :
    eventMass U p event ≤ 1 := by
  rw [← eventMass_true U p]
  exact eventMass_mono U hp0 hp1 event (fun _ => True) (fun _ _ => trivial)

/-- The union bound for two events. -/
theorem eventMass_or_le (U : Finset α) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (event₁ event₂ : Finset α → Prop) :
    eventMass U p (fun A => event₁ A ∨ event₂ A) ≤
      eventMass U p event₁ + eventMass U p event₂ := by
  classical
  unfold eventMass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro A hAU
  by_cases h₁ : event₁ A <;> by_cases h₂ : event₂ A
  · simp [h₁, h₂, weight_nonneg hp0 hp1]
  · simp [h₁, h₂]
  · simp [h₁, h₂]
  · simp only [h₁, h₂, false_or, if_false]
    norm_num

/-- An event and its complement partition the finite sample space. -/
theorem eventMass_add_not (U : Finset α) (p : ℝ)
    (event : Finset α → Prop) :
    eventMass U p event + eventMass U p (fun A => ¬ event A) = 1 := by
  classical
  unfold eventMass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  trans ∑ A ∈ U.powerset, weight U p A
  · apply Finset.sum_congr rfl
    intro A hA
    by_cases hE : event A <;> simp [hE]
  · exact sum_weight_powerset U p

/-- Complement rule. -/
theorem eventMass_not (U : Finset α) (p : ℝ)
    (event : Finset α → Prop) :
    eventMass U p (fun A => ¬ event A) = 1 - eventMass U p event := by
  linarith [eventMass_add_not U p event]

/-- Exact mass of the empty selected subset. -/
@[simp] theorem eventMass_eq_empty (U : Finset α) (p : ℝ) :
    eventMass U p (fun A => A = ∅) = (1 - p) ^ U.card := by
  classical
  unfold eventMass
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single ∅]
  · simp [weight]
  · intro A hA hAne
    simp [hAne]
  · simp

/-- Exact mass that at least one coordinate is selected. -/
theorem eventMass_nonempty (U : Finset α) (p : ℝ) :
    eventMass U p Finset.Nonempty = 1 - (1 - p) ^ U.card := by
  rw [show Finset.Nonempty = (fun A : Finset α => ¬ A = ∅) by
    funext A
    apply propext
    exact Finset.nonempty_iff_ne_empty]
  rw [eventMass_not, eventMass_eq_empty]

private theorem cylinder_summand {U S T A : Finset α} (hAU : A ⊆ U)
    (hSU : S ⊆ U) (p : ℝ) :
    ((∏ i ∈ A, if i ∈ T then 0 else p) *
        ∏ i ∈ U \ A, if i ∈ S then 0 else (1 - p)) =
      if S ⊆ A ∧ Disjoint T A then weight U p A else 0 := by
  classical
  by_cases hC : S ⊆ A ∧ Disjoint T A
  · rw [if_pos hC]
    have hleft : (∏ i ∈ A, if i ∈ T then 0 else p) = ∏ _i ∈ A, p := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_neg]
      exact fun hiT => Finset.disjoint_left.mp hC.2 hiT hi
    have hright :
        (∏ i ∈ U \ A, if i ∈ S then 0 else (1 - p)) =
          ∏ _i ∈ U \ A, (1 - p) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [if_neg]
      exact fun hiS => (Finset.mem_sdiff.mp hi).2 (hC.1 hiS)
    rw [hleft, hright, ← weight_eq_prod hAU p]
  · rw [if_neg hC]
    by_cases hSA : S ⊆ A
    · have hnotD : ¬ Disjoint T A := fun hD => hC ⟨hSA, hD⟩
      obtain ⟨i, hiT, hiA⟩ := Finset.not_disjoint_iff.mp hnotD
      have hprod : (∏ j ∈ A, if j ∈ T then (0 : ℝ) else p) = 0 := by
        apply Finset.prod_eq_zero hiA
        exact if_pos hiT
      rw [hprod, zero_mul]
    · obtain ⟨i, hiS, hiA⟩ := Finset.not_subset.mp hSA
      have hiUA : i ∈ U \ A := Finset.mem_sdiff.mpr ⟨hSU hiS, hiA⟩
      have hprod :
          (∏ j ∈ U \ A, if j ∈ S then (0 : ℝ) else (1 - p)) = 0 := by
        apply Finset.prod_eq_zero hiUA
        exact if_pos hiS
      rw [hprod, mul_zero]

/-- The coordinate product whose `prod_add` expansion selects exactly the
subsets containing `S` and avoiding `T`. -/
private theorem cylinder_coordinate_product {U S T : Finset α}
    (hSU : S ⊆ U) (hTU : T ⊆ U) (hST : Disjoint S T) (p : ℝ) :
    (∏ i ∈ U,
        ((if i ∈ T then 0 else p) +
          if i ∈ S then 0 else (1 - p))) =
      p ^ S.card * (1 - p) ^ T.card := by
  classical
  have hpoint : ∀ i ∈ U,
      ((if i ∈ T then 0 else p) +
          if i ∈ S then 0 else (1 - p)) =
        if i ∈ S then p else if i ∈ T then (1 - p) else 1 := by
    intro i hi
    by_cases hiS : i ∈ S
    · have hiT : i ∉ T := fun hiT => Finset.disjoint_left.mp hST hiS hiT
      simp [hiS, hiT]
    · by_cases hiT : i ∈ T <;> simp [hiS, hiT]
  have hrepl :
      (∏ i ∈ U,
          ((if i ∈ T then 0 else p) +
            if i ∈ S then 0 else (1 - p))) =
        ∏ i ∈ U, if i ∈ S then p else if i ∈ T then (1 - p) else 1 := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hpoint i hi
  rw [hrepl]
  rw [Finset.prod_ite]
  have hfilterS : U.filter (fun i => i ∈ S) = S := by
    ext i
    simp [hSU]
  rw [hfilterS, Finset.prod_const]
  have hfilterT : U.filter (fun i => i ∉ S ∧ i ∈ T) = T := by
    ext i
    constructor
    · simp only [Finset.mem_filter]
      exact fun hi => hi.2.2
    · intro hiT
      simp only [Finset.mem_filter]
      exact ⟨hTU hiT, fun hiS => Finset.disjoint_left.mp hST hiS hiT, hiT⟩
  rw [Finset.prod_ite]
  simp only [Finset.filter_filter]
  rw [hfilterT, Finset.prod_const]
  simp

/-- Exact cylinder probability: every coordinate of `S` is selected, every
coordinate of the disjoint set `T` is absent, and all other coordinates are
free. -/
theorem eventMass_contains_disjoint {U S T : Finset α}
    (hSU : S ⊆ U) (hTU : T ⊆ U) (hST : Disjoint S T) (p : ℝ) :
    eventMass U p (fun A => S ⊆ A ∧ Disjoint T A) =
      p ^ S.card * (1 - p) ^ T.card := by
  classical
  unfold eventMass
  rw [Finset.sum_filter]
  rw [← cylinder_coordinate_product hSU hTU hST p]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hC : S ⊆ A ∧ Disjoint T A
  · simpa [hC] using
      (cylinder_summand (T := T) (Finset.mem_powerset.mp hA) hSU p).symm
  · simpa [hC] using
      (cylinder_summand (T := T) (Finset.mem_powerset.mp hA) hSU p).symm

/-- Exact probability that every member of `S` is selected. -/
theorem eventMass_contains {U S : Finset α} (hSU : S ⊆ U) (p : ℝ) :
    eventMass U p (fun A => S ⊆ A) = p ^ S.card := by
  simpa using eventMass_contains_disjoint hSU (Finset.empty_subset U)
    (by simp : Disjoint S ∅) p

/-- Exact probability that every member of `T` is absent. -/
theorem eventMass_avoids {U T : Finset α} (hTU : T ⊆ U) (p : ℝ) :
    eventMass U p (fun A => Disjoint T A) = (1 - p) ^ T.card := by
  simpa using eventMass_contains_disjoint (Finset.empty_subset U) hTU
    (by simp : Disjoint ∅ T) p

/-- Finite union bound. -/
theorem eventMass_exists_mem_le_sum {ι : Type*} (U : Finset α) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Finset ι)
    (event : ι → Finset α → Prop) :
    eventMass U p (fun A => ∃ i ∈ s, event i A) ≤
      ∑ i ∈ s, eventMass U p (event i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      calc
        eventMass U p (fun A => ∃ j ∈ insert i s, event j A) =
            eventMass U p (fun A => event i A ∨ ∃ j ∈ s, event j A) := by
              congr 1
              funext A
              simp
        _ ≤ eventMass U p (event i) +
              eventMass U p (fun A => ∃ j ∈ s, event j A) :=
            eventMass_or_le U hp0 hp1 _ _
        _ ≤ eventMass U p (event i) + ∑ j ∈ s, eventMass U p (event j) :=
            add_le_add (le_refl _) ih
        _ = ∑ j ∈ insert i s, eventMass U p (event j) := by simp [hi]

/-- Bernoulli atom weights factor over two disjoint coordinate blocks. -/
theorem weight_union_of_disjoint {U V A B : Finset α} (hUV : Disjoint U V)
    (hAU : A ⊆ U) (hBV : B ⊆ V) (p : ℝ) :
    weight (U ∪ V) p (A ∪ B) = weight U p A * weight V p B := by
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact Finset.disjoint_left.mp hUV (hAU hiA) (hBV hiB)
  have hAc : A.card ≤ U.card := Finset.card_le_card hAU
  have hBc : B.card ≤ V.card := Finset.card_le_card hBV
  have hsub :
      U.card + V.card - (A.card + B.card) =
        (U.card - A.card) + (V.card - B.card) := by omega
  simp only [weight, Finset.card_union_of_disjoint hUV,
    Finset.card_union_of_disjoint hAB, hsub, pow_add]
  ring

/-- Cylinder events on disjoint coordinate blocks are independent.  This is
the finite factorization statement used when a random edge set is decomposed
into disjoint bundles. -/
theorem eventMass_cylinder_union_factor {U₁ U₂ S₁ S₂ T₁ T₂ : Finset α}
    (hU : Disjoint U₁ U₂)
    (hS₁ : S₁ ⊆ U₁) (hS₂ : S₂ ⊆ U₂)
    (hT₁ : T₁ ⊆ U₁) (hT₂ : T₂ ⊆ U₂)
    (hST₁ : Disjoint S₁ T₁) (hST₂ : Disjoint S₂ T₂) (p : ℝ) :
    eventMass (U₁ ∪ U₂) p
        (fun A => S₁ ∪ S₂ ⊆ A ∧ Disjoint (T₁ ∪ T₂) A) =
      eventMass U₁ p (fun A => S₁ ⊆ A ∧ Disjoint T₁ A) *
        eventMass U₂ p (fun A => S₂ ⊆ A ∧ Disjoint T₂ A) := by
  have hSU : S₁ ∪ S₂ ⊆ U₁ ∪ U₂ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (hS₁ hi)
    · exact Finset.mem_union_right _ (hS₂ hi)
  have hTU : T₁ ∪ T₂ ⊆ U₁ ∪ U₂ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (hT₁ hi)
    · exact Finset.mem_union_right _ (hT₂ hi)
  have hS12 : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    exact Finset.disjoint_left.mp hU (hS₁ hi₁) (hS₂ hi₂)
  have hT12 : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    exact Finset.disjoint_left.mp hU (hT₁ hi₁) (hT₂ hi₂)
  have hST : Disjoint (S₁ ∪ S₂) (T₁ ∪ T₂) := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    rcases Finset.mem_union.mp hiS with hiS₁ | hiS₂
    · rcases Finset.mem_union.mp hiT with hiT₁ | hiT₂
      · exact Finset.disjoint_left.mp hST₁ hiS₁ hiT₁
      · exact Finset.disjoint_left.mp hU (hS₁ hiS₁) (hT₂ hiT₂)
    · rcases Finset.mem_union.mp hiT with hiT₁ | hiT₂
      · exact Finset.disjoint_left.mp hU (hT₁ hiT₁) (hS₂ hiS₂)
      · exact Finset.disjoint_left.mp hST₂ hiS₂ hiT₂
  rw [eventMass_contains_disjoint hSU hTU hST,
    eventMass_contains_disjoint hS₁ hT₁ hST₁,
    eventMass_contains_disjoint hS₂ hT₂ hST₂,
    Finset.card_union_of_disjoint hS12,
    Finset.card_union_of_disjoint hT12, pow_add, pow_add]
  ring

private theorem subset_eq_inter_union_inter {U V C : Finset α}
    (hC : C ⊆ U ∪ V) : C ∩ U ∪ C ∩ V = C := by
  ext i
  constructor
  · simp only [Finset.mem_union, Finset.mem_inter]
    exact fun h => h.elim And.left And.left
  · intro hiC
    have hiUV := hC hiC
    simp only [Finset.mem_union, Finset.mem_inter] at hiUV ⊢
    exact hiUV.elim (fun hiU => Or.inl ⟨hiC, hiU⟩)
      (fun hiV => Or.inr ⟨hiC, hiV⟩)

/-- Reindexing a powerset of a disjoint union by the pair of its blockwise
intersections. -/
theorem sum_powerset_union_of_disjoint {M : Type*} [AddCommMonoid M]
    {U V : Finset α} (hUV : Disjoint U V) (f : Finset α → Finset α → M) :
    (∑ C ∈ (U ∪ V).powerset, f (C ∩ U) (C ∩ V)) =
      ∑ A ∈ U.powerset, ∑ B ∈ V.powerset, f A B := by
  classical
  suffices hsum :
      (∑ C ∈ (U ∪ V).powerset, f (C ∩ U) (C ∩ V)) =
        ∑ z ∈ U.powerset ×ˢ V.powerset, f z.1 z.2 by
    rw [Finset.sum_product] at hsum
    exact hsum
  apply Finset.sum_bij
      (fun C _ => (C ∩ U, C ∩ V))
  · intro C hC
    have hsub := Finset.mem_powerset.mp hC
    simp only [Finset.mem_product, Finset.mem_powerset]
    constructor
    · intro i hi
      exact (Finset.mem_inter.mp hi).2
    · intro i hi
      exact (Finset.mem_inter.mp hi).2
  · intro C₁ hC₁ C₂ hC₂ heq
    apply Finset.ext
    intro i
    have hrec₁ := subset_eq_inter_union_inter (Finset.mem_powerset.mp hC₁)
    have hrec₂ := subset_eq_inter_union_inter (Finset.mem_powerset.mp hC₂)
    have hfst : C₁ ∩ U = C₂ ∩ U := congrArg Prod.fst heq
    have hsnd : C₁ ∩ V = C₂ ∩ V := congrArg Prod.snd heq
    rw [← hrec₁, ← hrec₂, hfst, hsnd]
  · rintro ⟨A, B⟩ hAB
    simp only [Finset.mem_product, Finset.mem_powerset] at hAB
    refine ⟨A ∪ B, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro i hi
      rcases Finset.mem_union.mp hi with hiA | hiB
      · exact Finset.mem_union_left _ (hAB.1 hiA)
      · exact Finset.mem_union_right _ (hAB.2 hiB)
    · apply Prod.ext
      · ext i
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hiA | hiB, hiU⟩
          · exact hiA
          · exact False.elim (Finset.disjoint_left.mp hUV hiU (hAB.2 hiB))
        · exact fun hiA => ⟨Or.inl hiA, hAB.1 hiA⟩
      · ext i
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hiA | hiB, hiV⟩
          · exact False.elim (Finset.disjoint_left.mp hUV (hAB.1 hiA) hiV)
          · exact hiB
        · exact fun hiB => ⟨Or.inr hiB, hAB.2 hiB⟩
  · intro C hC
    rfl

/-- Restricting an atom to two disjoint coordinate blocks factors its
weight. -/
theorem weight_inter_factor {U V C : Finset α} (hUV : Disjoint U V)
    (hC : C ⊆ U ∪ V) (p : ℝ) :
    weight (U ∪ V) p C =
      weight U p (C ∩ U) * weight V p (C ∩ V) := by
  calc
    weight (U ∪ V) p C =
        weight (U ∪ V) p (C ∩ U ∪ C ∩ V) := by
          rw [subset_eq_inter_union_inter hC]
    _ = weight U p (C ∩ U) * weight V p (C ∩ V) :=
      weight_union_of_disjoint hUV
        (fun _ hi => (Finset.mem_inter.mp hi).2)
        (fun _ hi => (Finset.mem_inter.mp hi).2) p

/-- Arbitrary events depending separately on two disjoint coordinate blocks
are independent. -/
theorem eventMass_inter_factor {U V : Finset α} (hUV : Disjoint U V)
    (p : ℝ) (eventU eventV : Finset α → Prop) :
    eventMass (U ∪ V) p
        (fun C => eventU (C ∩ U) ∧ eventV (C ∩ V)) =
      eventMass U p eventU * eventMass V p eventV := by
  classical
  unfold eventMass
  simp_rw [Finset.sum_filter]
  trans ∑ C ∈ (U ∪ V).powerset,
        (if eventU (C ∩ U) then weight U p (C ∩ U) else 0) *
          (if eventV (C ∩ V) then weight V p (C ∩ V) else 0)
  · apply Finset.sum_congr rfl
    intro C hC
    have hweight := weight_inter_factor hUV (Finset.mem_powerset.mp hC) p
    by_cases hEU : eventU (C ∩ U) <;>
      by_cases hEV : eventV (C ∩ V) <;> simp [hEU, hEV, hweight]
  · trans ∑ A ∈ U.powerset, ∑ B ∈ V.powerset,
        (if eventU A then weight U p A else 0) *
          (if eventV B then weight V p B else 0)
    · exact sum_powerset_union_of_disjoint (M := ℝ) hUV
        (fun A B =>
          (if eventU A then weight U p A else 0) *
            (if eventV B then weight V p B else 0))
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.mul_sum]

/-- Partition an event according to the value of a finite-valued
classifier.  This is the finite-sum analogue of summing a probability over
the fibers of a random variable. -/
theorem eventMass_classifier_mem {β : Type*} [DecidableEq β]
    (U : Finset α) (p : ℝ) (f : Finset α → β) (s : Finset β) :
    eventMass U p (fun A => f A ∈ s) =
      ∑ b ∈ s, eventMass U p (fun A => f A = b) := by
  classical
  unfold eventMass
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hAU
  by_cases hf : f A ∈ s
  · rw [if_pos hf]
    rw [Finset.sum_eq_single (f A)]
    · simp
    · intro b hb hne
      simp [hne.symm]
    · exact fun hnot => (hnot hf).elim
  · rw [if_neg hf]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hne : f A ≠ b := fun hab => hf (hab ▸ hb)
    simp [hne]

/-- An event depending only on the coordinates in `V` has the same mass in
any larger Bernoulli universe `U`.  This is the main adapter from local
coordinate calculations to graph events with many irrelevant edges. -/
theorem eventMass_restrict {U V : Finset α} (hVU : V ⊆ U) (p : ℝ)
    (event : Finset α → Prop) :
    eventMass U p (fun A => event (A ∩ V)) = eventMass V p event := by
  classical
  have hdis : Disjoint V (U \ V) := by
    rw [Finset.disjoint_left]
    intro x hxV hxUV
    exact (Finset.mem_sdiff.mp hxUV).2 hxV
  calc
    eventMass U p (fun A => event (A ∩ V)) =
        eventMass (V ∪ (U \ V)) p (fun A => event (A ∩ V)) := by
          rw [Finset.union_sdiff_of_subset hVU]
    _ = eventMass (V ∪ (U \ V)) p
          (fun A => event (A ∩ V) ∧ True) := by simp
    _ = eventMass V p event * eventMass (U \ V) p (fun _ => True) :=
      eventMass_inter_factor hdis p event (fun _ => True)
    _ = eventMass V p event := by simp

section Bundles

variable {β : Type*} [DecidableEq β]

/-- Union of a finite indexed family of coordinate bundles. -/
def bundleUnion (I : Finset β) (B : β → Finset α) : Finset α :=
  I.biUnion B

/-- The bundles indexed by `I` are pairwise disjoint. -/
def PairwiseDisjointBundles (I : Finset β) (B : β → Finset α) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j)

/-- Indices of bundles containing at least one selected coordinate. -/
def occupiedBundles (I : Finset β) (B : β → Finset α)
    (A : Finset α) : Finset β :=
  I.filter fun i => (A ∩ B i).Nonempty

/-- Only indices belonging to `I` can be occupied. -/
theorem occupiedBundles_subset (I : Finset β) (B : β → Finset α)
    (A : Finset α) : occupiedBundles I B A ⊆ I := by
  exact Finset.filter_subset _ _

private theorem bundle_mem_union {I : Finset β} (B : β → Finset α)
    {i : β} (hi : i ∈ I) : B i ⊆ bundleUnion I B := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩

/-- Events local to every bundle factor as a finite product. -/
theorem eventMass_bundle_all (I : Finset β) (B : β → Finset α)
    (hpair : PairwiseDisjointBundles I B) (p : ℝ)
    (event : β → Finset α → Prop) :
    eventMass (bundleUnion I B) p
        (fun A => ∀ i ∈ I, event i (A ∩ B i)) =
      ∏ i ∈ I, eventMass (B i) p (event i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [bundleUnion]
  | @insert a I ha ih =>
      have hpairI : PairwiseDisjointBundles I B := by
        intro i hi j hj hij
        exact hpair i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      have hdis : Disjoint (B a) (bundleUnion I B) := by
        rw [Finset.disjoint_left]
        intro x hxa hxU
        obtain ⟨j, hjI, hxj⟩ := Finset.mem_biUnion.mp hxU
        have haj : a ≠ j := fun haj => ha (haj ▸ hjI)
        exact Finset.disjoint_left.mp
          (hpair a (Finset.mem_insert_self a I) j
            (Finset.mem_insert_of_mem hjI) haj) hxa hxj
      have hinter : ∀ (C : Finset α) (i : β), i ∈ I →
          (C ∩ bundleUnion I B) ∩ B i = C ∩ B i := by
        intro C i hi
        ext x
        constructor
        · intro hx
          have hx' := Finset.mem_inter.mp hx
          exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx'.1).1, hx'.2⟩
        · intro hx
          have hx' := Finset.mem_inter.mp hx
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_inter.mpr ⟨hx'.1, bundle_mem_union B hi hx'.2⟩, hx'.2⟩
      have hpred :
          (fun C : Finset α => ∀ i ∈ insert a I, event i (C ∩ B i)) =
            (fun C => event a (C ∩ B a) ∧
              ∀ i ∈ I, event i ((C ∩ bundleUnion I B) ∩ B i)) := by
        funext C
        apply propext
        constructor
        · intro hall
          refine ⟨hall a (Finset.mem_insert_self a I), ?_⟩
          intro i hi
          rw [hinter C i hi]
          exact hall i (Finset.mem_insert_of_mem hi)
        · rintro ⟨haE, hrest⟩ i hi
          rcases Finset.mem_insert.mp hi with rfl | hiI
          · exact haE
          · rw [← hinter C i hiI]
            exact hrest i hiI
      rw [show bundleUnion (insert a I) B = B a ∪ bundleUnion I B by
        simp [bundleUnion, ha]]
      rw [hpred, eventMass_inter_factor hdis p (event a)
        (fun D => ∀ i ∈ I, event i (D ∩ B i))]
      rw [ih hpairI]
      simp [ha]

private theorem occupiedBundles_eq_iff {I K : Finset β} {B : β → Finset α}
    {A : Finset α} (hKI : K ⊆ I) :
    occupiedBundles I B A = K ↔
      ∀ i ∈ I,
        if i ∈ K then (A ∩ B i).Nonempty else A ∩ B i = ∅ := by
  classical
  constructor
  · intro hocc i hiI
    by_cases hiK : i ∈ K
    · rw [if_pos hiK]
      have : i ∈ occupiedBundles I B A := hocc.symm ▸ hiK
      exact (Finset.mem_filter.mp this).2
    · rw [if_neg hiK]
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      have : i ∈ occupiedBundles I B A :=
        Finset.mem_filter.mpr ⟨hiI, hne⟩
      exact hiK (hocc ▸ this)
  · intro hall
    ext i
    constructor
    · intro hi
      have hi' := Finset.mem_filter.mp hi
      by_contra hiK
      have hempty := hall i hi'.1
      rw [if_neg hiK] at hempty
      exact (Finset.not_nonempty_iff_eq_empty.mpr hempty) hi'.2
    · intro hiK
      have hiI := hKI hiK
      have hne := hall i hiI
      rw [if_pos hiK] at hne
      exact Finset.mem_filter.mpr ⟨hiI, hne⟩

/-- Exact mass of any prescribed occupied-bundle pattern. -/
theorem eventMass_occupiedBundles_eq (I K : Finset β) (B : β → Finset α)
    (hpair : PairwiseDisjointBundles I B) {s : ℕ}
    (hcard : ∀ i ∈ I, (B i).card = s) (hKI : K ⊆ I) (p : ℝ) :
    eventMass (bundleUnion I B) p (fun A => occupiedBundles I B A = K) =
      (1 - (1 - p) ^ s) ^ K.card *
        ((1 - p) ^ s) ^ (I.card - K.card) := by
  classical
  rw [show (fun A => occupiedBundles I B A = K) =
      (fun A => ∀ i ∈ I,
        if i ∈ K then (A ∩ B i).Nonempty else A ∩ B i = ∅) by
    funext A
    apply propext
    exact occupiedBundles_eq_iff hKI]
  rw [eventMass_bundle_all I B hpair p
    (fun i C => if i ∈ K then C.Nonempty else C = ∅)]
  have hfactor : ∀ i ∈ I,
      eventMass (B i) p
          (fun C => if i ∈ K then C.Nonempty else C = ∅) =
        if i ∈ K then 1 - (1 - p) ^ s else (1 - p) ^ s := by
    intro i hiI
    by_cases hiK : i ∈ K
    · simp only [hiK, if_pos]
      rw [eventMass_nonempty, hcard i hiI]
    · simp only [hiK, if_false]
      rw [eventMass_eq_empty, hcard i hiI]
  apply Eq.trans (Finset.prod_congr rfl hfactor)
  rw [Finset.prod_ite]
  have hfilterK : I.filter (fun i => i ∈ K) = K := by
    ext i
    simp [hKI]
  have hfilterNotK : I.filter (fun i => i ∉ K) = I \ K := by
    ext i
    simp
  have hcardDiff : (I \ K).card = I.card - K.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hKI]
  rw [hfilterK, hfilterNotK, Finset.prod_const, Finset.prod_const, hcardDiff]

/-- The exact mass that precisely `r` equal-size, pairwise-disjoint bundles
are occupied is the corresponding binomial mass. -/
theorem eventMass_occupiedBundles_card_eq (I : Finset β) (B : β → Finset α)
    (hpair : PairwiseDisjointBundles I B) {s : ℕ}
    (hcard : ∀ i ∈ I, (B i).card = s) (p : ℝ) (r : ℕ) :
    eventMass (bundleUnion I B) p
        (fun A => (occupiedBundles I B A).card = r) =
      binomialTerm I.card (1 - (1 - p) ^ s) r := by
  classical
  rw [show (fun A => (occupiedBundles I B A).card = r) =
      (fun A => occupiedBundles I B A ∈ I.powersetCard r) by
    funext A
    apply propext
    simp only [Finset.mem_powersetCard]
    exact ⟨fun h => ⟨occupiedBundles_subset I B A, h⟩, And.right⟩]
  rw [eventMass_classifier_mem]
  calc
    (∑ K ∈ I.powersetCard r,
        eventMass (bundleUnion I B) p (fun A => occupiedBundles I B A = K)) =
        ∑ _K ∈ I.powersetCard r,
          (1 - (1 - p) ^ s) ^ r *
            ((1 - p) ^ s) ^ (I.card - r) := by
      apply Finset.sum_congr rfl
      intro K hK
      rw [eventMass_occupiedBundles_eq I K B hpair hcard
        (Finset.mem_powersetCard.mp hK).1 p,
        (Finset.mem_powersetCard.mp hK).2]
    _ = binomialTerm I.card (1 - (1 - p) ^ s) r := by
      rw [Finset.sum_const, Finset.card_powersetCard]
      simp [binomialTerm, nsmul_eq_mul]
      ring

/-- Exact lower tail for the number of occupied equal-size, pairwise
disjoint bundles. -/
theorem eventMass_occupiedBundles_card_lt (I : Finset β) (B : β → Finset α)
    (hpair : PairwiseDisjointBundles I B) {s : ℕ}
    (hcard : ∀ i ∈ I, (B i).card = s) (p : ℝ) (K : ℕ) :
    eventMass (bundleUnion I B) p
        (fun A => (occupiedBundles I B A).card < K) =
      binomialLowerTail I.card K (1 - (1 - p) ^ s) := by
  rw [show (fun A => (occupiedBundles I B A).card < K) =
      (fun A => (occupiedBundles I B A).card ∈ Finset.range K) by
    funext A
    apply propext
    exact Finset.mem_range.symm]
  rw [eventMass_classifier_mem]
  exact Finset.sum_congr rfl fun r _ =>
    eventMass_occupiedBundles_card_eq I B hpair hcard p r

/-- Restricting the selected set to the union of all bundles does not change
which bundles are occupied. -/
theorem occupiedBundles_inter_bundleUnion (I : Finset β) (B : β → Finset α)
    (A : Finset α) :
    occupiedBundles I B (A ∩ bundleUnion I B) = occupiedBundles I B A := by
  classical
  ext i
  simp only [occupiedBundles, Finset.mem_filter]
  constructor
  · rintro ⟨hiI, hne⟩
    refine ⟨hiI, ?_⟩
    apply hne.mono
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx'.1).1, hx'.2⟩
  · rintro ⟨hiI, hne⟩
    refine ⟨hiI, ?_⟩
    apply hne.mono
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨hx'.1, bundle_mem_union B hiI hx'.2⟩, hx'.2⟩

/-- Ambient-universe form of the exact occupied-count law.  Coordinates
outside the bundle union are integrated out. -/
theorem eventMass_occupiedBundles_card_eq_of_subset
    (U : Finset α) (I : Finset β) (B : β → Finset α)
    (hBU : bundleUnion I B ⊆ U)
    (hpair : PairwiseDisjointBundles I B) {s : ℕ}
    (hcard : ∀ i ∈ I, (B i).card = s) (p : ℝ) (r : ℕ) :
    eventMass U p (fun A => (occupiedBundles I B A).card = r) =
      binomialTerm I.card (1 - (1 - p) ^ s) r := by
  rw [show (fun A => (occupiedBundles I B A).card = r) =
      (fun A =>
        (occupiedBundles I B (A ∩ bundleUnion I B)).card = r) by
    funext A
    rw [occupiedBundles_inter_bundleUnion]]
  calc
    eventMass U p
        (fun A => (occupiedBundles I B (A ∩ bundleUnion I B)).card = r) =
      eventMass (bundleUnion I B) p
        (fun A => (occupiedBundles I B A).card = r) :=
      eventMass_restrict hBU p
        (fun A => (occupiedBundles I B A).card = r)
    _ = binomialTerm I.card (1 - (1 - p) ^ s) r :=
      eventMass_occupiedBundles_card_eq I B hpair hcard p r

/-- Ambient-universe form of the exact occupied-bundle lower tail. -/
theorem eventMass_occupiedBundles_card_lt_of_subset
    (U : Finset α) (I : Finset β) (B : β → Finset α)
    (hBU : bundleUnion I B ⊆ U)
    (hpair : PairwiseDisjointBundles I B) {s : ℕ}
    (hcard : ∀ i ∈ I, (B i).card = s) (p : ℝ) (K : ℕ) :
    eventMass U p (fun A => (occupiedBundles I B A).card < K) =
      binomialLowerTail I.card K (1 - (1 - p) ^ s) := by
  rw [show (fun A => (occupiedBundles I B A).card < K) =
      (fun A =>
        (occupiedBundles I B (A ∩ bundleUnion I B)).card < K) by
    funext A
    rw [occupiedBundles_inter_bundleUnion]]
  calc
    eventMass U p
        (fun A => (occupiedBundles I B (A ∩ bundleUnion I B)).card < K) =
      eventMass (bundleUnion I B) p
        (fun A => (occupiedBundles I B A).card < K) :=
      eventMass_restrict hBU p
        (fun A => (occupiedBundles I B A).card < K)
    _ = binomialLowerTail I.card K (1 - (1 - p) ^ s) :=
      eventMass_occupiedBundles_card_lt I B hpair hcard p K

end Bundles

end

end Erdos746.BernoulliFinset
