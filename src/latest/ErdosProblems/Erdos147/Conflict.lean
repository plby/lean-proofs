import ErdosProblems.Erdos147.Core

open Filter
open Asymptotics
open scoped SimpleGraph Topology

namespace Erdos147

set_option autoImplicit false

/-! ## Janzer's threshold split, specialized to twelve-cycles -/

structure LeftCycleSplit {L R : Type*} (B : L → R → Prop) where
  x₁ : L
  x₂ : R
  x₈ : R
  bridge : B x₁ x₂
  middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈)
  tail : WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)

instance LeftCycleSplit.instFinite
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    Finite (LeftCycleSplit B) := by
  let e : LeftCycleSplit B →
      Σ x₁ : L, Σ x₂ x₈ : R,
        WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈) ×
          WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁) :=
    fun c ↦ ⟨c.x₁, c.x₂, c.x₈, c.middle, c.tail⟩
  exact Finite.of_injective e (by
    intro c d h
    cases c
    cases d
    cases h
    rfl)

noncomputable def CycleSplit.toLeftCycleSplit
    {L R : Type*} (B : L → R → Prop)
    (c : CycleSplit (bipartiteRelGraph B)) (l : L) (hl : c.x₁ = Sum.inl l) :
    LeftCycleSplit B := by
  rcases c with ⟨x₁, x₂, x₈, bridge, middle, tail⟩
  dsimp at hl
  subst x₁
  cases x₂ with
  | inl l₂ => simp [bipartiteRelGraph] at bridge
  | inr r₂ =>
      cases x₈ with
      | inl l₈ =>
          have hn := bipartiteWalk_length_five_side_ne tail.1 tail.2
          simp [bipartiteSide] at hn
      | inr r₈ => exact ⟨l, r₂, r₈, bridge, middle, tail⟩

def LeftCycleSplit.toCycleSplit
    {L R : Type*} {B : L → R → Prop} (c : LeftCycleSplit B) :
    CycleSplit (bipartiteRelGraph B) :=
  { x₁ := Sum.inl c.x₁
    x₂ := Sum.inr c.x₂
    x₈ := Sum.inr c.x₈
    bridge := c.bridge
    middle := c.middle
    tail := c.tail }

lemma CycleSplit.toCycleSplit_toLeftCycleSplit
    {L R : Type*} (B : L → R → Prop)
    (c : CycleSplit (bipartiteRelGraph B)) (l : L) (hl : c.x₁ = Sum.inl l) :
    (c.toLeftCycleSplit B l hl).toCycleSplit = c := by
  rcases c with ⟨x₁, x₂, x₈, bridge, middle, tail⟩
  dsimp at hl
  subst x₁
  cases x₂ with
  | inl l₂ => simp [bipartiteRelGraph] at bridge
  | inr r₂ =>
      cases x₈ with
      | inl l₈ =>
          have hn := bipartiteWalk_length_five_side_ne tail.1 tail.2
          simp [bipartiteSide] at hn
      | inr r₈ => rfl

lemma CycleSplit.toLeftCycleSplit_conflict
    {L R : Type*} (B : L → R → Prop)
    (C : (L ⊕ R) → (L ⊕ R) → Prop)
    (c : CycleSplit (bipartiteRelGraph B)) (l : L) (hl : c.x₁ = Sum.inl l)
    (i : Fin 6) (hC : C c.x₁ (c.middle.1.getVert i.1)) :
    C (Sum.inl (c.toLeftCycleSplit B l hl).x₁)
      ((c.toLeftCycleSplit B l hl).middle.1.getVert i.1) := by
  rcases c with ⟨x₁, x₂, x₈, bridge, middle, tail⟩
  dsimp at hl
  subst x₁
  cases x₂ with
  | inl l₂ => simp [bipartiteRelGraph] at bridge
  | inr r₂ =>
      cases x₈ with
      | inl l₈ =>
          have hn := bipartiteWalk_length_five_side_ne tail.1 tail.2
          simp [bipartiteSide] at hn
      | inr r₈ => exact hC

def bipartiteRelGraphSwapIso {L R : Type*} (B : L → R → Prop) :
    bipartiteRelGraph (fun r l ↦ B l r) ≃g bipartiteRelGraph B :=
  ⟨Equiv.sumComm R L, by
    rintro (r | l) (r' | l') <;> simp [bipartiteRelGraph]⟩

def ClosedWalk.mapIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (w : ClosedWalk G 12) : ClosedWalk H 12 :=
  ⟨e w.1, ⟨w.2.1.map e.toHom, by simpa using w.2.2⟩⟩

lemma ClosedWalk.cycleSupport_mapIso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (w : ClosedWalk G 12) :
    (w.mapIso e).cycleSupport = w.cycleSupport.map e := by
  simp [ClosedWalk.mapIso, ClosedWalk.cycleSupport, SimpleGraph.Walk.support_map,
    List.map_dropLast]

lemma ClosedWalk.mapIso_injective {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) :
    Function.Injective (ClosedWalk.mapIso e : ClosedWalk G 12 → ClosedWalk H 12) := by
  intro w z h
  apply ClosedWalk.cycleSupport_injective
  apply (List.map_injective_iff.mpr e.injective)
  rw [← w.cycleSupport_mapIso e, ← z.cycleSupport_mapIso e,
    congrArg ClosedWalk.cycleSupport h]

def swapConflict {L R : Type*} (C : (L ⊕ R) → (L ⊕ R) → Prop) :
    (R ⊕ L) → (R ⊕ L) → Prop :=
  fun x y ↦ C (Equiv.sumComm R L x) (Equiv.sumComm R L y)

instance swapConflict.instDecidableRel {L R : Type*}
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :
    DecidableRel (swapConflict C) := by
  intro x y
  exact inferInstanceAs (Decidable (C (Equiv.sumComm R L x) (Equiv.sumComm R L y)))

noncomputable def leftTailMultiplicity
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (x₁ : L) (x₈ : R) : ℝ :=
  walkCount (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)

noncomputable def leftMiddleMultiplicity
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (x₂ x₈ : R) : ℝ :=
  walkCount (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈)

abbrev LeftLowCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (q : ℝ) :=
  Σ x₁ : L, Σ x₂ x₈ : R,
    {p : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈) ×
        WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁) //
      B x₁ x₂ ∧
        leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈}

lemma card_leftLowCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (q : ℝ) :
    (Nat.card (LeftLowCode B q) : ℝ) =
      ∑ x₁ : L, ∑ x₂ : R, ∑ x₈ : R,
        if B x₁ x₂ ∧
            leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈ then
          leftMiddleMultiplicity B x₂ x₈ * leftTailMultiplicity B x₁ x₈ else 0 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp only [LeftLowCode, Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  apply Finset.sum_congr rfl
  intro x₂ hx₂
  apply Finset.sum_congr rfl
  intro x₈ hx₈
  by_cases h : B x₁ x₂ ∧
      leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈
  · let A :=
      WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈) ×
        WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)
    have hsubcard : Fintype.card {p : A // B x₁ x₂ ∧
        leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈} =
        Fintype.card A := by
      let e : {p : A // B x₁ x₂ ∧
          leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈} ≃ A :=
        { toFun := fun z ↦ z.1
          invFun := fun p ↦ ⟨p, h⟩
          left_inv := fun z ↦ Subtype.ext rfl
          right_inv := fun _ ↦ rfl }
      exact Fintype.card_congr e
    rw [if_pos h, hsubcard]
    simp [A, Fintype.card_prod, leftMiddleMultiplicity, leftTailMultiplicity,
      walkCount_eq_card]
  · simp [h]

noncomputable def relLeftDegreeReal
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (l : L) : ℝ :=
  ∑ r : R, if B l r then 1 else 0

lemma leftTailSquareSum_le_homCycleCount_ten
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    (∑ x₁ : L, ∑ x₈ : R, leftTailMultiplicity B x₁ x₈ ^ 2) ≤
      homCycleCount (bipartiteRelGraph B) 10 := by
  rw [show 10 = 2 * 5 by norm_num, homCycleCount_even_eq_sum_sq]
  simp only [Fintype.sum_sum_type]
  have hcomm : (∑ x₁ : L, ∑ x₈ : R, leftTailMultiplicity B x₁ x₈ ^ 2) =
      ∑ x₁ : L, ∑ x₈ : R,
        walkCount (bipartiteRelGraph B) 5 (Sum.inl x₁) (Sum.inr x₈) ^ 2 := by
    apply Finset.sum_congr rfl
    intro x₁ hx₁
    apply Finset.sum_congr rfl
    intro x₈ hx₈
    rw [leftTailMultiplicity, walkCount_comm]
  rw [hcomm]
  simp_rw [Finset.sum_add_distrib]
  have hll : 0 ≤ ∑ x : L, ∑ y : L,
      walkCount (bipartiteRelGraph B) 5 (Sum.inl x) (Sum.inl y) ^ 2 := by
    positivity
  have hrl : 0 ≤ ∑ x : R, ∑ y : L,
      walkCount (bipartiteRelGraph B) 5 (Sum.inr x) (Sum.inl y) ^ 2 := by
    positivity
  have hrr : 0 ≤ ∑ x : R, ∑ y : R,
      walkCount (bipartiteRelGraph B) 5 (Sum.inr x) (Sum.inr y) ^ 2 := by
    positivity
  nlinarith

lemma card_leftLowCode_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (q D : ℝ) (hq : 0 ≤ q) (hD : 0 ≤ D)
    (hdeg : ∀ l, relLeftDegreeReal B l ≤ D) :
    (Nat.card (LeftLowCode B q) : ℝ) ≤
      q * D * homCycleCount (bipartiteRelGraph B) 10 := by
  rw [card_leftLowCode]
  calc
    (∑ x₁ : L, ∑ x₂ : R, ∑ x₈ : R,
        if B x₁ x₂ ∧
            leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈ then
          leftMiddleMultiplicity B x₂ x₈ * leftTailMultiplicity B x₁ x₈ else 0) ≤
        ∑ x₁ : L, ∑ x₂ : R, ∑ x₈ : R,
          if B x₁ x₂ then q * leftTailMultiplicity B x₁ x₈ ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro x₁ hx₁
      apply Finset.sum_le_sum
      intro x₂ hx₂
      apply Finset.sum_le_sum
      intro x₈ hx₈
      by_cases hlow : B x₁ x₂ ∧
          leftMiddleMultiplicity B x₂ x₈ < q * leftTailMultiplicity B x₁ x₈
      · rw [if_pos hlow, if_pos hlow.1]
        have ha := walkCount_nonneg (bipartiteRelGraph B) 5
          (Sum.inr x₈) (Sum.inl x₁)
        have hmul := mul_le_mul_of_nonneg_right (le_of_lt hlow.2) ha
        simpa [leftTailMultiplicity, pow_two, mul_assoc] using hmul
      · rw [if_neg hlow]
        positivity
    _ = ∑ x₁ : L, ∑ x₈ : R,
          q * leftTailMultiplicity B x₁ x₈ ^ 2 * relLeftDegreeReal B x₁ := by
      apply Finset.sum_congr rfl
      intro x₁ hx₁
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      rw [relLeftDegreeReal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      by_cases he : B x₁ x₂ <;> simp [he]
    _ ≤ ∑ x₁ : L, ∑ x₈ : R,
          q * leftTailMultiplicity B x₁ x₈ ^ 2 * D := by
      apply Finset.sum_le_sum
      intro x₁ hx₁
      apply Finset.sum_le_sum
      intro x₈ hx₈
      exact mul_le_mul_of_nonneg_left (hdeg x₁)
        (mul_nonneg hq (sq_nonneg _))
    _ = q * D * (∑ x₁ : L, ∑ x₈ : R,
          leftTailMultiplicity B x₁ x₈ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₁ hx₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      ring
    _ ≤ q * D * homCycleCount (bipartiteRelGraph B) 10 := by
      exact mul_le_mul_of_nonneg_left (leftTailSquareSum_le_homCycleCount_ten B)
        (mul_nonneg hq hD)

noncomputable def leftConflictDegreeReal
    {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (u : L ⊕ R) (x₂ : R) : ℝ :=
  ∑ x₁ : L, if B x₁ x₂ ∧ C (Sum.inl x₁) u then 1 else 0

abbrev LeftHighCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] (q : ℝ) :=
  Σ x₂ x₈ : R,
    Σ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
      Σ i : Fin 6, Σ x₁ : L,
        {tail : WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁) //
          B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
            q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈}

lemma card_leftHighCode
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] (q : ℝ) :
    (Nat.card (LeftHighCode B C q) : ℝ) =
      ∑ x₂ : R, ∑ x₈ : R,
        ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
          ∑ i : Fin 6, ∑ x₁ : L,
            if B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
                q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈ then
              leftTailMultiplicity B x₁ x₈ else 0 := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp only [LeftHighCode, Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x₂ hx₂
  apply Finset.sum_congr rfl
  intro x₈ hx₈
  apply Finset.sum_congr rfl
  intro middle hmiddle
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro x₁ hx₁
  let A := WalkOfLength (bipartiteRelGraph B) 5 (Sum.inr x₈) (Sum.inl x₁)
  let P : Prop := B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
    q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈
  by_cases h : P
  · have hsubcard : Fintype.card {tail : A // P} = Fintype.card A := by
      let e : {tail : A // P} ≃ A :=
        { toFun := fun z ↦ z.1
          invFun := fun tail ↦ ⟨tail, h⟩
          left_inv := fun z ↦ Subtype.ext rfl
          right_inv := fun _ ↦ rfl }
      exact Fintype.card_congr e
    rw [if_pos h, hsubcard]
    simp [A, P, leftTailMultiplicity, walkCount_eq_card]
  · simp [P, h]

lemma leftMiddleSquareSum_le_homCycleCount_twelve
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] :
    (∑ x₂ : R, ∑ x₈ : R, leftMiddleMultiplicity B x₂ x₈ ^ 2) ≤
      homCycleCount (bipartiteRelGraph B) 12 := by
  rw [show 12 = 2 * 6 by norm_num, homCycleCount_even_eq_sum_sq]
  simp only [Fintype.sum_sum_type]
  simp_rw [Finset.sum_add_distrib]
  have hll : 0 ≤ ∑ x : L, ∑ y : L,
      walkCount (bipartiteRelGraph B) 6 (Sum.inl x) (Sum.inl y) ^ 2 := by
    positivity
  have hlr : 0 ≤ ∑ x : L, ∑ y : R,
      walkCount (bipartiteRelGraph B) 6 (Sum.inl x) (Sum.inr y) ^ 2 := by
    positivity
  have hrl : 0 ≤ ∑ x : R, ∑ y : L,
      walkCount (bipartiteRelGraph B) 6 (Sum.inr x) (Sum.inl y) ^ 2 := by
    positivity
  simp only [leftMiddleMultiplicity]
  nlinarith

lemma card_leftHighCode_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (q s : ℝ) (hq : 0 < q) (hs : 0 ≤ s)
    (hconf : ∀ u x₂, leftConflictDegreeReal B C u x₂ ≤ s) :
    (Nat.card (LeftHighCode B C q) : ℝ) ≤
      (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 := by
  rw [card_leftHighCode]
  calc
    (∑ x₂ : R, ∑ x₈ : R,
        ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
          ∑ i : Fin 6, ∑ x₁ : L,
            if B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
                q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈ then
              leftTailMultiplicity B x₁ x₈ else 0) ≤
        ∑ x₂ : R, ∑ x₈ : R,
          ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
            ∑ i : Fin 6, ∑ x₁ : L,
              if B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) then
                leftMiddleMultiplicity B x₂ x₈ / q else 0 := by
      apply Finset.sum_le_sum
      intro x₂ hx₂
      apply Finset.sum_le_sum
      intro x₈ hx₈
      apply Finset.sum_le_sum
      intro middle hmiddle
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro x₁ hx₁
      by_cases hall : B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) ∧
          q * leftTailMultiplicity B x₁ x₈ ≤ leftMiddleMultiplicity B x₂ x₈
      · rw [if_pos hall, if_pos ⟨hall.1, hall.2.1⟩]
        apply (le_div_iff₀ hq).2
        simpa [mul_comm] using hall.2.2
      · rw [if_neg hall]
        by_cases hc : B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1)
        · rw [if_pos hc]
          exact div_nonneg (walkCount_nonneg (bipartiteRelGraph B) 6 _ _) hq.le
        · simp [hc]
    _ = ∑ x₂ : R, ∑ x₈ : R,
          ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
            ∑ i : Fin 6,
              (leftMiddleMultiplicity B x₂ x₈ / q) *
                leftConflictDegreeReal B C (middle.1.getVert i.1) x₂ := by
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      apply Finset.sum_congr rfl
      intro middle hmiddle
      apply Finset.sum_congr rfl
      intro i hi
      rw [leftConflictDegreeReal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₁ hx₁
      by_cases hc : B x₁ x₂ ∧ C (Sum.inl x₁) (middle.1.getVert i.1) <;>
        simp [hc]
    _ ≤ ∑ x₂ : R, ∑ x₈ : R,
          ∑ middle : WalkOfLength (bipartiteRelGraph B) 6 (Sum.inr x₂) (Sum.inr x₈),
            ∑ _i : Fin 6, (leftMiddleMultiplicity B x₂ x₈ / q) * s := by
      apply Finset.sum_le_sum
      intro x₂ hx₂
      apply Finset.sum_le_sum
      intro x₈ hx₈
      apply Finset.sum_le_sum
      intro middle hmiddle
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hconf (middle.1.getVert i.1) x₂)
        (div_nonneg (walkCount_nonneg (bipartiteRelGraph B) 6 _ _) hq.le)
    _ = ∑ x₂ : R, ∑ x₈ : R,
          (6 * s / q) * leftMiddleMultiplicity B x₂ x₈ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      apply Finset.sum_congr rfl
      intro x₈ hx₈
      simp [leftMiddleMultiplicity, walkCount_eq_card]
      ring
    _ = (6 * s / q) * (∑ x₂ : R, ∑ x₈ : R,
          leftMiddleMultiplicity B x₂ x₈ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x₂ hx₂
      rw [Finset.mul_sum]
    _ ≤ (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 := by
      exact mul_le_mul_of_nonneg_left (leftMiddleSquareSum_le_homCycleCount_twelve B)
        (div_nonneg (mul_nonneg (show (0 : ℝ) ≤ 6 by norm_num) hs) hq.le)

abbrev LeftBadSplit
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :=
  {c : LeftCycleSplit B // ∃ i : Fin 6,
    C (Sum.inl c.x₁) (c.middle.1.getVert i.1)}

noncomputable def leftBadSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (l : L) (hl : w.1 = Sum.inl l) : LeftBadSplit B C := by
  let c := CycleSplit.ofClosedWalk w
  let d := c.toLeftCycleSplit B l hl
  refine ⟨d, k, ?_⟩
  apply c.toLeftCycleSplit_conflict B C l hl k
  change C w.1 ((CycleSplit.ofClosedWalk w).middle.1.getVert k.1)
  rw [CycleSplit.ofClosedWalk_middle_getVert]
  exact hC

noncomputable def rightBadSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (r : R) (hr : w.1 = Sum.inr r) :
    LeftBadSplit (fun r l ↦ B l r) (swapConflict C) := by
  let e := (bipartiteRelGraphSwapIso B).symm
  let w' := w.mapIso e
  have hr' : w'.1 = Sum.inl r := by
    change e w.1 = Sum.inl r
    rw [hr]
    rfl
  have hC' : swapConflict C w'.1 (w'.2.1.getVert (k.1 + 1)) := by
    dsimp only [w', ClosedWalk.mapIso]
    have hswap (x : L ⊕ R) : Equiv.sumComm R L (e x) = x := by
      cases x <;> rfl
    have hswapHom (x : L ⊕ R) : Equiv.sumComm R L (e.toHom x) = x := by
      cases x <;> rfl
    simpa only [swapConflict, SimpleGraph.Walk.getVert_map, hswap, hswapHom] using hC
  exact leftBadSplitOfClosedWalk (fun r l ↦ B l r) (swapConflict C) w' k hC' r hr'

lemma ClosedWalk.mapIso_symm_mapIso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) (w : ClosedWalk G 12) :
    (w.mapIso e).mapIso e.symm = w := by
  apply ClosedWalk.cycleSupport_injective
  rw [(w.mapIso e).cycleSupport_mapIso e.symm, w.cycleSupport_mapIso e]
  simp

lemma leftBadSplitOfClosedWalk_toCycleSplit
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (l : L) (hl : w.1 = Sum.inl l) :
    (leftBadSplitOfClosedWalk B C w k hC l hl).1.toCycleSplit =
      CycleSplit.ofClosedWalk w := by
  apply CycleSplit.toCycleSplit_toLeftCycleSplit B

lemma rightBadSplitOfClosedWalk_toClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1)))
    (r : R) (hr : w.1 = Sum.inr r) :
    (((rightBadSplitOfClosedWalk B C w k hC r hr).1.toCycleSplit.toClosedWalk).mapIso
        (bipartiteRelGraphSwapIso B)) = w := by
  let e := (bipartiteRelGraphSwapIso B).symm
  let w' := w.mapIso e
  have hr' : w'.1 = Sum.inl r := by
    change e w.1 = Sum.inl r
    rw [hr]
    rfl
  have hC' : swapConflict C w'.1 (w'.2.1.getVert (k.1 + 1)) := by
    dsimp only [w', ClosedWalk.mapIso]
    have hswap (x : L ⊕ R) : Equiv.sumComm R L (e x) = x := by
      cases x <;> rfl
    have hswapHom (x : L ⊕ R) : Equiv.sumComm R L (e.toHom x) = x := by
      cases x <;> rfl
    simpa only [swapConflict, SimpleGraph.Walk.getVert_map, hswap, hswapHom] using hC
  rw [show rightBadSplitOfClosedWalk B C w k hC r hr =
      leftBadSplitOfClosedWalk (fun r l ↦ B l r) (swapConflict C) w' k hC' r hr' by rfl]
  rw [leftBadSplitOfClosedWalk_toCycleSplit, CycleSplit.toClosedWalk_ofClosedWalk]
  exact ClosedWalk.mapIso_symm_mapIso e w

def cycleForwardDistance (i j : Fin 12) : ℕ := (j.1 + 12 - i.1) % 12

def cycleConflictStart (i j : Fin 12) : Fin 12 :=
  if cycleForwardDistance i j ≤ 6 then i else j

def cycleConflictOffset (i j : Fin 12) : Fin 6 := by
  let d := cycleForwardDistance i j
  by_cases h : d ≤ 6
  · exact ⟨d - 1, by
      omega⟩
  · exact ⟨12 - d - 1, by
      have hdlt : d < 12 := Nat.mod_lt _ (by norm_num)
      omega⟩

lemma cycleConflictStart_offset (i j : Fin 12) (hij : i ≠ j) :
    (cycleConflictStart i j = i ∧
        ((cycleConflictOffset i j).1 + 1 + (cycleConflictStart i j).1) % 12 = j.1) ∨
      (cycleConflictStart i j = j ∧
        ((cycleConflictOffset i j).1 + 1 + (cycleConflictStart i j).1) % 12 = i.1) := by
  decide +revert

lemma ClosedWalk.rotate12_has_oriented_conflict
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) (w : ClosedWalk (bipartiteRelGraph B) 12)
    (i j : Fin 12) (hij : i ≠ j)
    (hC : C (w.2.1.getVert i.1) (w.2.1.getVert j.1)) :
    let w' := w.rotate12 (cycleConflictStart i j)
    C w'.1 (w'.2.1.getVert ((cycleConflictOffset i j).1 + 1)) := by
  dsimp only
  have hs := cycleConflictStart_offset i j hij
  let k : Fin 12 := ⟨(cycleConflictOffset i j).1 + 1, by
    have := (cycleConflictOffset i j).2
    omega⟩
  change C (w.2.1.getVert (cycleConflictStart i j).1)
    ((w.rotate12 (cycleConflictStart i j)).2.1.getVert k.1)
  rw [w.rotate12_getVert (cycleConflictStart i j) k]
  rcases hs with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hs]
    have ht' : (k.1 + i.1) % 12 = j.1 := by
      simpa [k, hs, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
    rw [ht']
    exact hC
  · rw [hs]
    have ht' : (k.1 + j.1) % 12 = i.1 := by
      simpa [k, hs, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using ht
    rw [ht']
    exact hCsymm hC

abbrev ConflictClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :=
  {w : ClosedWalk (bipartiteRelGraph B) 12 //
    ∃ i j : Fin 12, i ≠ j ∧ C (w.2.1.getVert i.1) (w.2.1.getVert j.1)}

noncomputable def conflictFirstIndex
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {B : L → R → Prop} [∀ l r, Decidable (B l r)]
    {C : (L ⊕ R) → (L ⊕ R) → Prop} [DecidableRel C]
    (z : ConflictClosedWalk B C) : Fin 12 := Classical.choose z.2

noncomputable def conflictSecondIndex
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {B : L → R → Prop} [∀ l r, Decidable (B l r)]
    {C : (L ⊕ R) → (L ⊕ R) → Prop} [DecidableRel C]
    (z : ConflictClosedWalk B C) : Fin 12 := Classical.choose (Classical.choose_spec z.2)

lemma conflictIndex_spec
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {B : L → R → Prop} [∀ l r, Decidable (B l r)]
    {C : (L ⊕ R) → (L ⊕ R) → Prop} [DecidableRel C]
    (z : ConflictClosedWalk B C) :
    conflictFirstIndex z ≠ conflictSecondIndex z ∧
      C (z.1.2.1.getVert (conflictFirstIndex z).1)
        (z.1.2.1.getVert (conflictSecondIndex z).1) :=
  Classical.choose_spec (Classical.choose_spec z.2)

noncomputable def badSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1))) :
    LeftBadSplit B C ⊕ LeftBadSplit (fun r l ↦ B l r) (swapConflict C) :=
  match h : w.1 with
  | Sum.inl l => Sum.inl (leftBadSplitOfClosedWalk B C w k hC l h)
  | Sum.inr r => Sum.inr (rightBadSplitOfClosedWalk B C w k hC r h)

noncomputable def badSplitRotatedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] :
    LeftBadSplit B C ⊕ LeftBadSplit (fun r l ↦ B l r) (swapConflict C) →
      ClosedWalk (bipartiteRelGraph B) 12
  | Sum.inl z => z.1.toCycleSplit.toClosedWalk
  | Sum.inr z => z.1.toCycleSplit.toClosedWalk.mapIso (bipartiteRelGraphSwapIso B)

lemma badSplitRotatedWalk_badSplitOfClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (w : ClosedWalk (bipartiteRelGraph B) 12) (k : Fin 6)
    (hC : C w.1 (w.2.1.getVert (k.1 + 1))) :
    badSplitRotatedWalk B C (badSplitOfClosedWalk B C w k hC) = w := by
  unfold badSplitOfClosedWalk
  split
  · simp only [badSplitRotatedWalk]
    rw [leftBadSplitOfClosedWalk_toCycleSplit, CycleSplit.toClosedWalk_ofClosedWalk]
  · simp only [badSplitRotatedWalk]
    apply rightBadSplitOfClosedWalk_toClosedWalk

noncomputable def encodeConflictClosedWalk
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) (z : ConflictClosedWalk B C) :
    (Fin 12 × Fin 12) ×
      (LeftBadSplit B C ⊕ LeftBadSplit (fun r l ↦ B l r) (swapConflict C)) := by
  let i := conflictFirstIndex z
  let j := conflictSecondIndex z
  let w := z.1.rotate12 (cycleConflictStart i j)
  let k := cycleConflictOffset i j
  have hC : C w.1 (w.2.1.getVert (k.1 + 1)) :=
    z.1.rotate12_has_oriented_conflict B C hCsymm i j
      (conflictIndex_spec z).1 (conflictIndex_spec z).2
  exact ((i, j), badSplitOfClosedWalk B C w k hC)

lemma encodeConflictClosedWalk_injective
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) : Function.Injective (encodeConflictClosedWalk B C hCsymm) := by
  intro z z' hzz'
  let i := conflictFirstIndex z
  let j := conflictSecondIndex z
  let i' := conflictFirstIndex z'
  let j' := conflictSecondIndex z'
  have htag : (i, j) = (i', j') := congrArg Prod.fst hzz'
  have hi : i = i' := congrArg Prod.fst htag
  have hj : j = j' := congrArg Prod.snd htag
  have hcode : (encodeConflictClosedWalk B C hCsymm z).2 =
      (encodeConflictClosedWalk B C hCsymm z').2 := congrArg Prod.snd hzz'
  have hrot : z.1.rotate12 (cycleConflictStart i j) =
      z'.1.rotate12 (cycleConflictStart i j) := by
    calc
      z.1.rotate12 (cycleConflictStart i j) =
          badSplitRotatedWalk B C (encodeConflictClosedWalk B C hCsymm z).2 := by
            symm
            apply badSplitRotatedWalk_badSplitOfClosedWalk
      _ = badSplitRotatedWalk B C (encodeConflictClosedWalk B C hCsymm z').2 := by
            rw [hcode]
      _ = z'.1.rotate12 (cycleConflictStart i' j') := by
            apply badSplitRotatedWalk_badSplitOfClosedWalk
      _ = z'.1.rotate12 (cycleConflictStart i j) := by rw [hi, hj]
  apply Subtype.ext
  exact ClosedWalk.rotate12_injective (cycleConflictStart i j) hrot

lemma card_conflictClosedWalk_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) :
    (Nat.card (ConflictClosedWalk B C) : ℝ) ≤ 144 *
      (Nat.card (LeftBadSplit B C) +
        Nat.card (LeftBadSplit (fun r l ↦ B l r) (swapConflict C))) := by
  let : Fintype (LeftBadSplit B C) := Fintype.ofFinite _
  let : Fintype (LeftBadSplit (fun r l ↦ B l r) (swapConflict C)) := Fintype.ofFinite _
  have hcard := Nat.card_le_card_of_injective (encodeConflictClosedWalk B C hCsymm)
    (encodeConflictClosedWalk_injective B C hCsymm)
  have hcard' : Nat.card (ConflictClosedWalk B C) ≤ 144 *
      (Nat.card (LeftBadSplit B C) +
        Nat.card (LeftBadSplit (fun r l ↦ B l r) (swapConflict C))) := by
    simpa only [Nat.card_prod, Nat.card_fin, Nat.card_sum] using hcard
  exact_mod_cast hcard'

def ClosedWalk.mapIsoN {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {j : ℕ} (e : G ≃g H) (w : ClosedWalk G j) : ClosedWalk H j :=
  ⟨e w.1, ⟨w.2.1.map e.toHom, by simpa using w.2.2⟩⟩

def ClosedWalk.supportCode {V : Type*} {G : SimpleGraph V} {j : ℕ}
    (w : ClosedWalk G j) : List V := w.2.1.support

lemma ClosedWalk.supportCode_injective {V : Type*} {G : SimpleGraph V} {j : ℕ} :
    Function.Injective (ClosedWalk.supportCode : ClosedWalk G j → List V) := by
  intro w z h
  rcases w with ⟨v, p, hp⟩
  rcases z with ⟨v', q, hq⟩
  have hv : v = v' := by
    have hh := congrArg List.head? h
    simp only [ClosedWalk.supportCode] at hh
    rw [← p.cons_tail_support, ← q.cons_tail_support] at hh
    simpa only [List.head?_cons, Option.some.injEq] using hh
  subst v'
  have hpq : p = q := SimpleGraph.Walk.ext_support h
  subst q
  rfl

lemma ClosedWalk.supportCode_mapIsoN {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {j : ℕ} (e : G ≃g H) (w : ClosedWalk G j) :
    (w.mapIsoN e).supportCode = w.supportCode.map e := by
  simp [ClosedWalk.mapIsoN, ClosedWalk.supportCode, SimpleGraph.Walk.support_map]

lemma ClosedWalk.mapIsoN_injective {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {j : ℕ} (e : G ≃g H) :
    Function.Injective (ClosedWalk.mapIsoN e : ClosedWalk G j → ClosedWalk H j) := by
  intro w z h
  apply ClosedWalk.supportCode_injective
  apply (List.map_injective_iff.mpr e.injective)
  rw [← w.supportCode_mapIsoN e, ← z.supportCode_mapIsoN e,
    congrArg ClosedWalk.supportCode h]

lemma homCycleCount_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (j : ℕ) :
    homCycleCount G j = homCycleCount H j := by
  rw [homCycleCount_eq_card_closedWalk, homCycleCount_eq_card_closedWalk]
  congr 1
  apply le_antisymm
  · exact Nat.card_le_card_of_injective (ClosedWalk.mapIsoN e)
      (ClosedWalk.mapIsoN_injective e)
  · exact Nat.card_le_card_of_injective (ClosedWalk.mapIsoN e.symm)
      (ClosedWalk.mapIsoN_injective e.symm)

lemma card_leftBadSplit_le_low_add_high
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C] (q : ℝ) :
    (Nat.card (LeftBadSplit B C) : ℝ) ≤
      Nat.card (LeftLowCode B q) + Nat.card (LeftHighCode B C q) := by
  classical
  let encode : LeftBadSplit B C → LeftLowCode B q ⊕ LeftHighCode B C q := fun z ↦
    if hlow : leftMiddleMultiplicity B z.1.x₂ z.1.x₈ <
        q * leftTailMultiplicity B z.1.x₁ z.1.x₈ then
      Sum.inl ⟨z.1.x₁, z.1.x₂, z.1.x₈,
        ⟨(z.1.middle, z.1.tail), z.1.bridge, hlow⟩⟩
    else
      let i := Classical.choose z.2
      Sum.inr ⟨z.1.x₂, z.1.x₈, z.1.middle, i, z.1.x₁,
        ⟨z.1.tail, z.1.bridge, Classical.choose_spec z.2, le_of_not_gt hlow⟩⟩
  let decode : LeftLowCode B q ⊕ LeftHighCode B C q → LeftCycleSplit B
    | Sum.inl z =>
        { x₁ := z.1
          x₂ := z.2.1
          x₈ := z.2.2.1
          bridge := z.2.2.2.2.1
          middle := z.2.2.2.1.1
          tail := z.2.2.2.1.2 }
    | Sum.inr z =>
        { x₁ := z.2.2.2.2.1
          x₂ := z.1
          x₈ := z.2.1
          bridge := z.2.2.2.2.2.2.1
          middle := z.2.2.1
          tail := z.2.2.2.2.2.1 }
  have hdecode : ∀ z : LeftBadSplit B C, decode (encode z) = z.1 := by
    intro z
    by_cases hlow : leftMiddleMultiplicity B z.1.x₂ z.1.x₈ <
        q * leftTailMultiplicity B z.1.x₁ z.1.x₈
    · simp [encode, decode, hlow]
    · simp [encode, decode, hlow]
  have hinj : Function.Injective encode := by
    intro z w hzw
    apply Subtype.ext
    rw [← hdecode z, ← hdecode w, hzw]
  let : Fintype (LeftLowCode B q) := inferInstance
  let : Fintype (LeftHighCode B C q) := inferInstance
  have hcard := Nat.card_le_card_of_injective encode hinj
  have hcard' : Nat.card (LeftBadSplit B C) ≤
      Nat.card (LeftLowCode B q) + Nat.card (LeftHighCode B C q) := by
    simpa only [Nat.card_sum] using hcard
  exact_mod_cast hcard'

lemma card_leftBadSplit_le
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (q D s : ℝ) (hq : 0 < q) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hdeg : ∀ l, relLeftDegreeReal B l ≤ D)
    (hconf : ∀ u x₂, leftConflictDegreeReal B C u x₂ ≤ s) :
    (Nat.card (LeftBadSplit B C) : ℝ) ≤
      q * D * homCycleCount (bipartiteRelGraph B) 10 +
        (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 := by
  calc
    (Nat.card (LeftBadSplit B C) : ℝ) ≤
        Nat.card (LeftLowCode B q) + Nat.card (LeftHighCode B C q) :=
      card_leftBadSplit_le_low_add_high B C q
    _ ≤ q * D * homCycleCount (bipartiteRelGraph B) 10 +
        (6 * s / q) * homCycleCount (bipartiteRelGraph B) 12 :=
      add_le_add (card_leftLowCode_le B q D hq.le hD hdeg)
        (card_leftHighCode_le B C q s hq hs hconf)

lemma threshold_balance
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    let q := Real.sqrt (B / A)
    q * A + B / q = 2 * Real.sqrt (A * B) := by
  dsimp only
  let q := Real.sqrt (B / A)
  have hBA : 0 < B / A := div_pos hB hA
  have hq : 0 < q := Real.sqrt_pos.2 hBA
  have hq2 : q ^ 2 = B / A := Real.sq_sqrt hBA.le
  have hBq : B / q = q * A := by
    rw [div_eq_iff hq.ne']
    have hBA' : B = q ^ 2 * A := by
      rw [hq2]
      field_simp
    nlinarith
  have hqA : q * A = Real.sqrt (A * B) := by
    have hnonneg : 0 ≤ q * A := mul_nonneg hq.le hA.le
    have hsnonneg : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
    have hsquare : (q * A) ^ 2 = (Real.sqrt (A * B)) ^ 2 := by
      rw [Real.sq_sqrt (mul_nonneg hA.le hB.le)]
      have hBA' : B = q ^ 2 * A := by
        rw [hq2]
        field_simp
      nlinarith
    nlinarith
  rw [hBq, hqA]
  ring

lemma homCycleCount_twelve_le_of_all_conflicting
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (C : (L ⊕ R) → (L ⊕ R) → Prop) [DecidableRel C]
    (hCsymm : Symmetric C) (D₁ D₂ s₁ s₂ : ℝ)
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hDord : D₁ ≤ D₂)
    (hdeg₁ : ∀ l, relLeftDegreeReal B l ≤ D₁)
    (hdeg₂ : ∀ r, relLeftDegreeReal (fun r l ↦ B l r) r ≤ D₂)
    (hconf₁ : ∀ u r, leftConflictDegreeReal B C u r ≤ s₁)
    (hconf₂ : ∀ u l, leftConflictDegreeReal (fun r l ↦ B l r)
      (swapConflict C) u l ≤ s₂)
    (hs₁bound : s₁ ≤ 8 * Real.sqrt D₂)
    (hs₂bound : s₂ ≤ 8 * Real.sqrt D₁)
    (hall : ∀ w : ClosedWalk (bipartiteRelGraph B) 12,
      ∃ i j : Fin 12, i ≠ j ∧
        C (w.2.1.getVert i.1) (w.2.1.getVert j.1)) :
    homCycleCount (bipartiteRelGraph B) 12 ≤
      16000000 * (D₂ * Real.sqrt D₁) *
        homCycleCount (bipartiteRelGraph B) 10 := by
  let Q := bipartiteRelGraph B
  let x := homCycleCount Q 10
  let y := homCycleCount Q 12
  have hx0 : 0 ≤ x := by simpa [x, Q] using homCycleCount_even_nonneg Q 5
  have hy0 : 0 ≤ y := by simpa [y, Q] using homCycleCount_even_nonneg Q 6
  have hrhs0 : 0 ≤ 16000000 * (D₂ * Real.sqrt D₁) * x :=
    mul_nonneg (mul_nonneg (by positivity)
      (mul_nonneg hD₂.le (Real.sqrt_nonneg _))) hx0
  by_cases hy : y = 0
  · change y ≤ 16000000 * (D₂ * Real.sqrt D₁) * x
    exact hy.le.trans hrhs0
  have hyp : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hxp : 0 < x := by
    have hycard : Nat.card (ClosedWalk Q 12) ≠ 0 := by
      intro hz
      apply hy
      rw [show y = homCycleCount Q 12 by rfl, homCycleCount_eq_card_closedWalk]
      exact_mod_cast hz
    obtain ⟨⟨w⟩, _⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hycard)
    let p : ClosedWalk Q 10 :=
      ⟨w.1, ⟨(w.2.1.take 5).append (w.2.1.take 5).reverse, by simp [w.2.2]⟩⟩
    rw [show x = homCycleCount Q 10 by rfl, homCycleCount_eq_card_closedWalk]
    exact_mod_cast Nat.card_pos_iff.mpr ⟨⟨p⟩, inferInstance⟩
  let q₁ := Real.sqrt ((6 * s₁ * y) / (D₁ * x))
  let q₂ := Real.sqrt ((6 * s₂ * y) / (D₂ * x))
  have hq₁ : 0 < q₁ := Real.sqrt_pos.2 (div_pos
    (mul_pos (mul_pos (by norm_num) hs₁) hyp) (mul_pos hD₁ hxp))
  have hq₂ : 0 < q₂ := Real.sqrt_pos.2 (div_pos
    (mul_pos (mul_pos (by norm_num) hs₂) hyp) (mul_pos hD₂ hxp))
  have hcount : y = Nat.card (ConflictClosedWalk B C) := by
    rw [show y = homCycleCount Q 12 by rfl, homCycleCount_eq_card_closedWalk]
    congr 1
    apply le_antisymm
    · exact Nat.card_le_card_of_injective
        (fun w : ClosedWalk Q 12 ↦ ⟨w, hall w⟩) (fun _ _ h ↦ Subtype.ext_iff.mp h)
    · exact Nat.card_le_card_of_injective (fun w : ConflictClosedWalk B C ↦ w.1)
        (fun _ _ h ↦ Subtype.ext h)
  have hleft := card_leftBadSplit_le B C q₁ D₁ s₁ hq₁ hD₁.le hs₁.le hdeg₁ hconf₁
  change (Nat.card (LeftBadSplit B C) : ℝ) ≤
    q₁ * D₁ * x + (6 * s₁ / q₁) * y at hleft
  have hright := card_leftBadSplit_le (fun r l ↦ B l r) (swapConflict C)
    q₂ D₂ s₂ hq₂ hD₂.le hs₂.le hdeg₂ hconf₂
  have hiso10 : homCycleCount (bipartiteRelGraph (fun r l ↦ B l r)) 10 = x := by
    simpa [Q, x] using homCycleCount_eq_of_iso
      (bipartiteRelGraph (fun r l ↦ B l r)) Q (bipartiteRelGraphSwapIso B) 10
  have hiso12 : homCycleCount (bipartiteRelGraph (fun r l ↦ B l r)) 12 = y := by
    simpa [Q, y] using homCycleCount_eq_of_iso
      (bipartiteRelGraph (fun r l ↦ B l r)) Q (bipartiteRelGraphSwapIso B) 12
  rw [hiso10, hiso12] at hright
  have hcard := card_conflictClosedWalk_le B C hCsymm
  rw [← hcount] at hcard
  have hbal₁ : q₁ * (D₁ * x) + (6 * s₁ * y) / q₁ =
      2 * Real.sqrt ((D₁ * x) * (6 * s₁ * y)) := by
    simpa [q₁] using threshold_balance (mul_pos hD₁ hxp)
      (mul_pos (mul_pos (by norm_num) hs₁) hyp)
  have hbal₂ : q₂ * (D₂ * x) + (6 * s₂ * y) / q₂ =
      2 * Real.sqrt ((D₂ * x) * (6 * s₂ * y)) := by
    simpa [q₂] using threshold_balance (mul_pos hD₂ hxp)
      (mul_pos (mul_pos (by norm_num) hs₂) hyp)
  have hrough : y ≤ 576 * Real.sqrt
      (48 * (D₂ * Real.sqrt D₁) * x * y) := by
    have hsqrtord : Real.sqrt D₁ ≤ Real.sqrt D₂ := Real.sqrt_le_sqrt hDord
    have hmix : D₁ * Real.sqrt D₂ ≤ D₂ * Real.sqrt D₁ := by
      have hsq₁ : (Real.sqrt D₁) ^ 2 = D₁ := Real.sq_sqrt hD₁.le
      have hsq₂ : (Real.sqrt D₂) ^ 2 = D₂ := Real.sq_sqrt hD₂.le
      calc
        D₁ * Real.sqrt D₂ = (Real.sqrt D₁) ^ 2 * Real.sqrt D₂ := by rw [hsq₁]
        _ = Real.sqrt D₁ * (Real.sqrt D₁ * Real.sqrt D₂) := by ring
        _ ≤ Real.sqrt D₂ * (Real.sqrt D₁ * Real.sqrt D₂) :=
          mul_le_mul_of_nonneg_right hsqrtord
            (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        _ = (Real.sqrt D₂) ^ 2 * Real.sqrt D₁ := by ring
        _ = D₂ * Real.sqrt D₁ := by rw [hsq₂]
    have hprod₁ : (D₁ * x) * (6 * s₁ * y) ≤
        48 * (D₂ * Real.sqrt D₁) * x * y := by
      calc
        (D₁ * x) * (6 * s₁ * y) = 6 * (D₁ * s₁) * (x * y) := by ring
        _ ≤ 6 * (8 * (D₁ * Real.sqrt D₂)) * (x * y) := by
          have hDs := mul_le_mul_of_nonneg_left hs₁bound hD₁.le
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by nlinarith [hDs]) (by norm_num))
            (mul_nonneg hx0 hy0)
        _ ≤ 6 * (8 * (D₂ * Real.sqrt D₁)) * (x * y) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hmix (by norm_num)) (by norm_num))
            (mul_nonneg hx0 hy0)
        _ = 48 * (D₂ * Real.sqrt D₁) * x * y := by ring
    have hprod₂ : (D₂ * x) * (6 * s₂ * y) ≤
        48 * (D₂ * Real.sqrt D₁) * x * y := by
      calc
        (D₂ * x) * (6 * s₂ * y) = 6 * (D₂ * s₂) * (x * y) := by ring
        _ ≤ 6 * (D₂ * (8 * Real.sqrt D₁)) * (x * y) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hs₂bound hD₂.le) (by norm_num))
            (mul_nonneg hx0 hy0)
        _ = 48 * (D₂ * Real.sqrt D₁) * x * y := by ring
    have hroot₁ : Real.sqrt ((D₁ * x) * (6 * s₁ * y)) ≤
        Real.sqrt (48 * (D₂ * Real.sqrt D₁) * x * y) := by
      exact Real.sqrt_le_sqrt hprod₁
    have hroot₂ : Real.sqrt ((D₂ * x) * (6 * s₂ * y)) ≤
        Real.sqrt (48 * (D₂ * Real.sqrt D₁) * x * y) := by
      exact Real.sqrt_le_sqrt hprod₂
    have hsum := add_le_add hleft hright
    have hscaled := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 144 by norm_num)
    calc
      y ≤ 144 * (Nat.card (LeftBadSplit B C) +
          Nat.card (LeftBadSplit (fun r l ↦ B l r) (swapConflict C))) := hcard
      _ ≤ 144 * ((q₁ * D₁ * x + (6 * s₁ / q₁) * y) +
          (q₂ * D₂ * x + (6 * s₂ / q₂) * y)) := hscaled
      _ = 144 * (2 * Real.sqrt ((D₁ * x) * (6 * s₁ * y)) +
          2 * Real.sqrt ((D₂ * x) * (6 * s₂ * y))) := by
            rw [← hbal₁, ← hbal₂]
            ring
      _ ≤ 576 * Real.sqrt (48 * (D₂ * Real.sqrt D₁) * x * y) := by
            nlinarith
  have hM0 : 0 ≤ D₂ * Real.sqrt D₁ :=
    mul_nonneg hD₂.le (Real.sqrt_nonneg _)
  have hZ : 0 ≤ 48 * (D₂ * Real.sqrt D₁) * x * y :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hx0) hy0
  have hsquare := Real.sq_sqrt hZ
  have hy2 : y ^ 2 ≤ 576 ^ 2 *
      (48 * (D₂ * Real.sqrt D₁) * x * y) := by nlinarith [sq_nonneg y]
  have hcancel : y ≤ (576 ^ 2 * 48) * (D₂ * Real.sqrt D₁) * x := by
    by_contra hn
    have hlt : (576 ^ 2 * 48) * (D₂ * Real.sqrt D₁) * x < y :=
      lt_of_not_ge hn
    have hmul := mul_lt_mul_of_pos_right hlt hyp
    nlinarith
  change y ≤ 16000000 * (D₂ * Real.sqrt D₁) * x
  calc
    y ≤ 15925248 * (D₂ * Real.sqrt D₁) * x := by norm_num at hcancel ⊢; exact hcancel
    _ ≤ 16000000 * (D₂ * Real.sqrt D₁) * x := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (by norm_num) hM0) hx0

lemma homCycleCount_twelve_le_two_of_ten_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (K : ℝ) (hK : 0 ≤ K)
    (hbound : homCycleCount G 12 ≤ K * homCycleCount G 10) :
    homCycleCount G 12 ≤ K ^ 5 * homCycleCount G 2 := by
  let a := homCycleCount G 2
  let x := homCycleCount G 10
  let y := homCycleCount G 12
  have ha0 : 0 ≤ a := by simpa [a] using homCycleCount_even_nonneg G 1
  have hx0 : 0 ≤ x := by simpa [x] using homCycleCount_even_nonneg G 5
  have hy0 : 0 ≤ y := by simpa [y] using homCycleCount_even_nonneg G 6
  change y ≤ K ^ 5 * a
  change y ≤ K * x at hbound
  by_cases hy : y = 0
  · exact hy.le.trans (mul_nonneg (pow_nonneg hK 5) ha0)
  have hyp : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
  have hpow : y ^ 5 ≤ (K * x) ^ 5 := pow_le_pow_left₀ hy0 hbound 5
  have hinterp : x ^ 5 ≤ a * y ^ 4 := by
    simpa [a, x, y] using homCycleCount_ten_pow_five_le G
  have hfive : y ^ 5 ≤ K ^ 5 * a * y ^ 4 := by
    calc
      y ^ 5 ≤ (K * x) ^ 5 := hpow
      _ = K ^ 5 * x ^ 5 := by ring
      _ ≤ K ^ 5 * (a * y ^ 4) :=
        mul_le_mul_of_nonneg_left hinterp (pow_nonneg hK 5)
      _ = K ^ 5 * a * y ^ 4 := by ring
  have hy4 : 0 < y ^ 4 := pow_pos hyp 4
  by_contra hn
  have hlt : K ^ 5 * a < y := lt_of_not_ge hn
  have hstrict := mul_lt_mul_of_pos_right hlt hy4
  apply (not_lt_of_ge hfive)
  simpa [pow_succ'] using hstrict

end Erdos147
