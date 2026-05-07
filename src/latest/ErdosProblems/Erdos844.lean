/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Aristotle (Harmonic)
-/

import Mathlib

namespace Erdos844

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.refine false

/-!
# Erdős Problem 844: The Erdős–Sárközy Problem

## Problem Statement

Let `A ⊆ {1, …, N}` be such that for all `a, b ∈ A`, the product `a * b` is not squarefree.
The maximum size of such an `A` is achieved by taking `A` to be the set of
even numbers together with odd non-squarefree numbers in `{1, …, N}`.

## Proof

The proof follows Weisenberg's reduction to a theorem of Chvátal on intersecting families
in hereditary hypergraphs.

**Key idea (Weisenberg):**
1. Any valid `A` must contain all non-squarefree numbers in `{1, …, N}`, since if `a` is
   non-squarefree then `a * b` is non-squarefree for every `b`.
2. It suffices to find the largest subset `B` of squarefree numbers in `{1, …, N}` such
   that any two elements share a common prime factor.
3. By Chvátal's theorem, this maximum is achieved by the set of even squarefree numbers.

## References

- Chvátal, V., "Intersecting families of edges in hypergraphs having the hereditary property"
-/

open Finset Nat

/-! ### Definitions -/

/-- The dominance order on finsets of natural numbers: `Dominated Y X` means there exists
an injection `f : Y → X` with `y ≤ f(y)` for all `y ∈ Y`.
This is written `Y ◁ X` in Chvátal's paper. -/
def Dominated (Y X : Finset ℕ) : Prop :=
  ∃ f : ℕ → ℕ, Set.InjOn f (Y : Set ℕ) ∧
    (∀ y ∈ Y, f y ∈ X) ∧ (∀ y ∈ Y, y ≤ f y)

/-- The proposed optimal set for the Erdős–Sárközy problem: all numbers in `{1, …, N}`
that are even or non-squarefree. -/
noncomputable def erdosSarkozySet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun k => 2 ∣ k ∨ ¬ Squarefree k)

/-! ### Chvátal's Theorem (Ground Set Version) -/

/-!
# Case B helpers for Chvátal's theorem

This section provides the two key lemmas needed for Case B of Chvátal's theorem:
1. Complement reversal of the dominance order
2. The shifting/exchange property for weight-minimizing intersecting families
-/

/-! ## Complement reversal of dominance -/

/-- The tail count of a finset above k. -/
private def tailCount (A : Finset ℕ) (k : ℕ) : ℕ := (A.filter (· ≥ k)).card

/-
Dominated implies tail inequality: if Y ◁ X, then for all k,
|{y ∈ Y : y ≥ k}| ≤ |{x ∈ X : x ≥ k}|.
-/
private lemma dominated_tail_ineq (Y X : Finset ℕ)
    (h : Dominated Y X) :
    ∀ k, tailCount Y k ≤ tailCount X k := by
  unfold tailCount
  obtain ⟨f, hf_inj, hf_mem, hf_le⟩ := h
  intro k
  have h_sub : (↑(Y.filter (· ≥ k)) : Set ℕ) ⊆ ↑Y :=
    Finset.coe_subset.mpr (Finset.filter_subset _ _)
  have h_image :
      Finset.image f (Y.filter (· ≥ k)) ⊆
      X.filter (· ≥ k) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr
      ⟨hf_mem y (Finset.mem_filter.mp hy).1,
       le_trans (Finset.mem_filter.mp hy).2
         (hf_le y (Finset.mem_filter.mp hy).1)⟩
  calc (Y.filter (· ≥ k)).card
      = (Finset.image f (Y.filter (· ≥ k))).card := by
        rw [Finset.card_image_of_injOn
          (hf_inj.mono h_sub)]
    _ ≤ (X.filter (· ≥ k)).card :=
        Finset.card_mono h_image

/-
From tail inequalities, construct a dominance injection (greedy algorithm).
This is proved by strong induction on the size of A.
-/
private lemma dominated_of_tail_ineq (N : ℕ) (A B : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hB : B ⊆ Finset.Icc 1 N)
    (h_tail : ∀ k, tailCount A k ≤ tailCount B k) :
    Dominated A B := by
  -- By strong induction on the size of A.
  induction' hA : A.card using Nat.strong_induction_on with n ih generalizing A B;
  by_cases hA_empty : A = ∅;
  · exact ⟨fun _ => 0,
      fun _ h => absurd (hA_empty ▸ h) (by simp),
      fun _ h => absurd (hA_empty ▸ h) (by simp),
      fun _ h => absurd (hA_empty ▸ h) (by simp)⟩;
  · -- Let a_max be the maximum element in A.
    obtain ⟨a_max, ha_max⟩ : ∃ a_max ∈ A, ∀ a ∈ A, a ≤ a_max := by
      exact ⟨A.max' (Finset.nonempty_of_ne_empty hA_empty),
        Finset.max'_mem _ _, fun a ha => Finset.le_max' _ _ ha⟩;
    -- Let b_max be the maximum element in B that is greater than or equal to a_max.
    obtain ⟨b_max, hb_max⟩ :
        ∃ b_max ∈ B, a_max ≤ b_max ∧ ∀ b ∈ B, a_max ≤ b → b ≤ b_max := by
      obtain ⟨b_max, hb_max⟩ : ∃ b_max ∈ B, a_max ≤ b_max := by
        specialize h_tail a_max; contrapose! h_tail
        exact lt_of_le_of_lt
          (Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
            fun x hx => not_le_of_gt (h_tail x hx)) |> le_of_eq)
          (Finset.card_pos.mpr
            ⟨a_max, Finset.mem_filter.mpr ⟨ha_max.1, le_rfl⟩⟩)
      set Bf := B.filter fun b => a_max ≤ b
      have hBf_ne : Bf.Nonempty :=
        ⟨b_max, Finset.mem_filter.mpr hb_max⟩
      exact ⟨Bf.max' hBf_ne,
        (Finset.mem_filter.mp (Bf.max'_mem hBf_ne)).1,
        (Finset.mem_filter.mp (Bf.max'_mem hBf_ne)).2,
        fun b hb hb' =>
          Finset.le_max' _ _
            (Finset.mem_filter.mpr ⟨hb, hb'⟩)⟩;
    -- Let A' = A.erase a_max and B' = B.erase b_max.
    set A' := A.erase a_max
    set B' := B.erase b_max;
    -- By the induction hypothesis, there exists a dominance injection $f' : A' \to B'$.
    obtain ⟨f', hf'⟩ : ∃ f' : ℕ → ℕ,
        Set.InjOn f' (A' : Set ℕ) ∧
        (∀ y ∈ A', f' y ∈ B') ∧ (∀ y ∈ A', y ≤ f' y) := by
      have h_tail_A'B' : ∀ k, tailCount A' k ≤ tailCount B' k := by
        intro k; specialize h_tail k; by_cases hk : k ≤ a_max <;> simp_all +decide [ tailCount ] ;
        · rw [show { x ∈ A' | k ≤ x } = { x ∈ A | k ≤ x } \ {a_max}
              from ?_,
            show { x ∈ B' | k ≤ x } = { x ∈ B | k ≤ x } \ {b_max}
              from ?_];
          · grind;
          · grind;
          · grind;
        · rw [ Finset.card_eq_zero.mpr ];
          · exact Nat.zero_le _;
          · exact Finset.eq_empty_of_forall_notMem fun x hx => by
              linarith [Finset.mem_filter.mp hx,
                ha_max.2 x (Finset.mem_of_mem_erase
                  (Finset.mem_filter.mp hx |>.1))];
      exact ih _
        (by rw [Finset.card_erase_of_mem ha_max.1, hA]
            exact Nat.pred_lt (by
              rw [← hA]
              exact Finset.card_ne_zero.mpr
                (Finset.nonempty_of_ne_empty
                  hA_empty)))
        _ _
        (Finset.Subset.trans (Finset.erase_subset _ _) ‹A ⊆ Icc 1 N›)
        (Finset.Subset.trans (Finset.erase_subset _ _) ‹B ⊆ Icc 1 N›)
        h_tail_A'B' rfl;
    use fun x => if x = a_max then b_max else f' x;
    simp_all +decide [ Set.InjOn ];
    grind

/-
Complement reversal of dominance: if Y ◁ X within {1,...,N},
then {1,...,N}\X ◁ {1,...,N}\Y.
-/
lemma dominated_compl (N : ℕ) (X Y : Finset ℕ)
    (hX : X ⊆ Finset.Icc 1 N) (hY : Y ⊆ Finset.Icc 1 N)
    (h : Dominated Y X) :
    Dominated (Finset.Icc 1 N \ X) (Finset.Icc 1 N \ Y) := by
  apply dominated_of_tail_ineq N (Finset.Icc 1 N \ X) (Finset.Icc 1 N \ Y);
  · exact sdiff_subset
  · exact sdiff_subset
  · -- By definition of tail count, we have:
    have h_tail_count_def : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        ∀ k, tailCount A k + tailCount (Finset.Icc 1 N \ A) k =
        tailCount (Finset.Icc 1 N) k := by
      intros A hA k;
      unfold tailCount;
      rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
      rw [ add_comm, Finset.sum_sdiff hA ];
    exact fun k => by
      linarith [h_tail_count_def X hX k,
        h_tail_count_def Y hY k, dominated_tail_ineq Y X h k]

/-! ## Weight function and shifting property -/

/-- Weight of a family of sets, using powers of 2 to ensure strict decrease under shifts. -/
noncomputable def familyWeight (G : Finset (Finset ℕ)) : ℕ :=
  G.sum (fun X => X.sum (fun k => 2 ^ k))

/-
The shifting property at element N: if G has minimum weight among intersecting
subfamilies of F of the same cardinality, then for all X ∈ G with N ∈ X,
and k ∈ {1,...,N-1} \ X, the set (X \ {N}) ∪ {k} is also in G.

This is the key exchange argument from Chvátal's proof.
-/
set_option maxHeartbeats 800000 in
lemma min_weight_shiftN (N : ℕ)
    (F G : Finset (Finset ℕ))
    (hF_sub : ∀ X ∈ F, X ⊆ Finset.Icc 1 N)
    (hF_hered : ∀ X ∈ F, ∀ Y, Y ⊆ Finset.Icc 1 N → Dominated Y X → Y ∈ F)
    (hG_sub : G ⊆ F)
    (hG_int : ∀ X ∈ G, ∀ Y ∈ G, (X ∩ Y).Nonempty)
    (hG_min : ∀ G' : Finset (Finset ℕ), G' ⊆ F → G'.card = G.card →
      (∀ X ∈ G', ∀ Y ∈ G', (X ∩ Y).Nonempty) → familyWeight G ≤ familyWeight G') :
    ∀ X ∈ G, N ∈ X → ∀ k, 1 ≤ k → k < N → k ∉ X →
    (X.erase N ∪ {k}) ∈ G := by
  intro X hX hXN k hk1 hkN hkX
  by_contra h_contra
  set bad := Finset.filter
    (fun Y => N ∈ Y ∧ k ∉ Y ∧ (Y.erase N ∪ {k}) ∉ G) G
    with hbad_def
  set H := (G \ bad) ∪
    (Finset.image (fun Y => Y.erase N ∪ {k}) bad)
    with hH_def
  have hH_card : H.card = G.card := by
    rw [ Finset.card_union_of_disjoint ] <;> norm_num [ Finset.disjoint_right ];
    · rw [ Finset.card_image_of_injOn, Finset.card_sdiff ];
      · rw [Finset.inter_eq_left.mpr fun x hx => by aesop]
        rw [tsub_add_cancel_of_le]
        exact Finset.card_le_card fun x hx => by aesop;
      · simp +contextual [ Finset.ext_iff, Set.InjOn ];
        grind +extAll;
    · aesop;
  -- By minimality, H cannot be intersecting.
  have hH_not_int : ¬∀ X ∈ H, ∀ Y ∈ H, (X ∩ Y).Nonempty := by
    contrapose! hG_min;
    refine' ⟨ H, _, hH_card, hG_min, _ ⟩;
    · intro Y hy; simp_all +decide [ Finset.subset_iff ] ;
      rcases hy with ( ⟨ hy₁, hy₂ ⟩ | ⟨ a, ⟨ ha₁, ha₂, ha₃, ha₄ ⟩, rfl ⟩ );
      · exact hG_sub hy₁;
      · refine' hF_hered _ ( hG_sub ha₁ ) _ _ _;
        · simp +zetaDelta at *;
          exact ⟨ ⟨ hk1, hkN.le ⟩, fun x hx₁ hx₂ => hF_sub _ ( hG_sub ha₁ ) hx₂ ⟩;
        · use fun x => if x = k then N else x;
          simp +decide [ Set.InjOn ];
          lia;
    · -- Weight strictly decreases when replacing N with k.
      have h_weight_decr :
          ∀ Y ∈ bad,
          (Y.erase N ∪ {k}).sum (2 ^ ·) < Y.sum (2 ^ ·) := by
        intro Y hy
        rw [Finset.sum_union] <;> simp_all +decide
        rw [← Finset.sum_erase_add _ _ hy.2.1]
        linarith [pow_lt_pow_right₀ (by decide : 1 < 2) hkN]
      have h_weight_decr :
          (bad.image (fun Y => Y.erase N ∪ {k})).sum
            (fun Y => Y.sum (2 ^ ·)) <
          bad.sum (fun Y => Y.sum (2 ^ ·)) := by
        rw [ Finset.sum_image ];
        · exact Finset.sum_lt_sum_of_nonempty ⟨ X, by aesop ⟩ h_weight_decr;
        · intros Y hy Z hz h_eq; simp_all +decide [ Finset.ext_iff ] ;
          grind +suggestions;
      unfold familyWeight; rw [Finset.sum_union]; simp_all +decide
      · rw [← Finset.sum_sdiff
            (Finset.filter_subset
              (fun Y => N ∈ Y ∧ k ∉ Y ∧
                insert k (Y.erase N) ∉ G) G)]
        linarith;
      · simp +contextual [ Finset.disjoint_left ];
        grind +ring;
  simp_all +decide [ Finset.Nonempty ];
  grind +ring


/-- The self-complementary part of F: sets whose complement is also in F. -/
private noncomputable def selfComp (F : Finset (Finset ℕ)) (N : ℕ) : Finset (Finset ℕ) :=
  F.filter (fun X => Finset.Icc 1 N \ X ∈ F)

/-
F \\ selfComp is hereditary: if X ∈ F \\ selfComp and Y ◁ X, then Y ∈ F \\ selfComp.
-/
private lemma F_nonsc_hered (N : ℕ)
    (F : Finset (Finset ℕ))
    (hF_sub : ∀ X ∈ F, X ⊆ Finset.Icc 1 N)
    (hF_hered : ∀ X ∈ F, ∀ Y, Y ⊆ Finset.Icc 1 N → Dominated Y X → Y ∈ F)
    (X : Finset ℕ) (hXF : X ∈ F) (hXsc : Finset.Icc 1 N \ X ∉ F)
    (Y : Finset ℕ) (hYsub : Y ⊆ Finset.Icc 1 N) (hYX : Dominated Y X) :
    Y ∈ F ∧ Finset.Icc 1 N \ Y ∉ F := by
  refine' ⟨ hF_hered X hXF Y hYsub hYX, _ ⟩;
  contrapose! hXsc;
  convert hF_hered _ hXsc _ _ _;
  · exact sdiff_subset
  · convert dominated_compl N X Y ( hF_sub X hXF ) hYsub _;
    exact hYX

/-
Complement pair bound: in an intersecting family, at most half of each
self-complementary pair can appear.
-/
private lemma compl_pair_bound (N : ℕ) (hN : 2 ≤ N)
    (F : Finset (Finset ℕ))
    (hF_sub : ∀ X ∈ F, X ⊆ Finset.Icc 1 N)
    (G : Finset (Finset ℕ)) (hG_sub : G ⊆ F)
    (hG_int : ∀ X ∈ G, ∀ Y ∈ G, (X ∩ Y).Nonempty) :
    (G.filter (fun X => Finset.Icc 1 N \ X ∈ F)).card ≤
    (F.filter (fun X => (1 : ℕ) ∈ X ∧ Finset.Icc 1 N \ X ∈ F)).card := by
  refine' le_trans _ ( Finset.card_le_card _ );
  nontriviality;
  convert Finset.card_le_card_of_injOn _ _ _;
  use fun X => if 1 ∈ X then X else Icc 1 N \ X;
  rotate_left;
  intro X hX Y hy hxy;
  grind;
  exact Finset.coe_subset.mp fun ⦃a⦄ a_1 ↦ a_1
  intro X hX;
  by_cases h1 : 1 ∈ X <;> simp_all +decide;
  · exact hG_sub hX.1;
  · have h := hF_sub _ (hG_sub hX.1)
    exact ⟨by linarith,
      by simpa [Finset.inter_eq_right.mpr h]
        using hG_sub hX.1⟩

/-
Non-self-complementary elements containing N have intersecting link
when G has the shiftN property.
-/
private lemma nonsc_link_int (N : ℕ)
    (F : Finset (Finset ℕ))
    (hF_sub : ∀ X ∈ F, X ⊆ Finset.Icc 1 N)
    (hF_hered : ∀ X ∈ F, ∀ Y, Y ⊆ Finset.Icc 1 N → Dominated Y X → Y ∈ F)
    (G : Finset (Finset ℕ)) (hG_sub : G ⊆ F)
    (hG_int : ∀ X ∈ G, ∀ Y ∈ G, (X ∩ Y).Nonempty)
    (hG_shift : ∀ X ∈ G, N ∈ X → ∀ k, 1 ≤ k → k < N →
      k ∉ X → (X.erase N ∪ {k}) ∈ G)
    (Y : Finset ℕ) (hY : Y ∈ G) (hYN : N ∈ Y)
    (hYsc : Finset.Icc 1 N \ Y ∉ F)
    (Z : Finset ℕ) (hZ : Z ∈ G) (hZN : N ∈ Z)
    :
    ((Y.erase N) ∩ (Z.erase N)).Nonempty := by
  contrapose! hG_shift;
  obtain ⟨k, hk⟩ : ∃ k, k ∈ Finset.Icc 1 N ∧ k ∉ Y ∧ k ∉ Z := by
    by_cases h_union : Y ∪ Z = Finset.Icc 1 N;
    · have h_compl : Finset.Icc 1 N \ Y ⊆ Z := by
        grind;
      have h_compl : Dominated (Finset.Icc 1 N \ Y) Z := by
        use fun x => x;
        aesop;
      exact False.elim <| hYsc <| hF_hered _ ( hG_sub hZ ) _ ( by aesop ) h_compl;
    · grind +qlia;
  refine' ⟨ Y, hY, hYN, k, _, _, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
  · grind;
  · grind +splitIndPred

/-
Case B of Chvátal's theorem: when the link of G₂ at N is NOT intersecting.
  Uses the weight-minimization trick from Chvátal's original proof:
  replace G by a minimum-weight intersecting subfamily of same size,
  which has the shifting property, then apply the three-way split.
-/
set_option maxHeartbeats 1600000 in
private lemma chvatal_case_B (N : ℕ) (hN : 2 ≤ N)
    (F : Finset (Finset ℕ))
    (hF_sub : ∀ X ∈ F, X ⊆ Finset.Icc 1 N)
    (hF_hered : ∀ X ∈ F, ∀ Y, Y ⊆ Finset.Icc 1 N → Dominated Y X → Y ∈ F)
    (G : Finset (Finset ℕ)) (hG_sub : G ⊆ F)
    (hG_int : ∀ X ∈ G, ∀ Y ∈ G, (X ∩ Y).Nonempty)
    (G2 : Finset (Finset ℕ)) (hG2 : G2 = G.filter (fun X => N ∈ X))
    (hB : ∃ X ∈ G2, ∃ Y ∈ G2, ¬((X.erase N) ∩ (Y.erase N)).Nonempty)
    (ih : ∀ (N' : ℕ), N' < N → ∀ (F' : Finset (Finset ℕ)),
      (∀ X ∈ F', X ⊆ Finset.Icc 1 N') →
      (∀ X ∈ F', ∀ Y, Y ⊆ Finset.Icc 1 N' → Dominated Y X → Y ∈ F') →
      ∀ (G' : Finset (Finset ℕ)), G' ⊆ F' →
      (∀ X ∈ G', ∀ Y ∈ G', (X ∩ Y).Nonempty) →
      G'.card ≤ (F'.filter (1 ∈ ·)).card) :
    G.card ≤ (F.filter (1 ∈ ·)).card := by
  -- Step 1: Find G' ⊆ F with |G'| = |G|, intersecting, and minimum weight
  have hF_hered' : ∀ X ∈ F, ∀ Y, Y ⊆ Finset.Icc 1 N → Dominated Y X → Y ∈ F :=
    fun X hX Y hY hD => hF_hered X hX Y hY hD
  set candidates := F.powerset.filter (fun G' => G'.card = G.card ∧
    ∀ X ∈ G', ∀ Y ∈ G', (X ∩ Y).Nonempty) with hcand_def
  have hG_cand : G ∈ candidates := by
    simp only [hcand_def, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hG_sub, trivial, hG_int⟩
  obtain ⟨G', hG'_cand, hG'_min⟩ :=
    Finset.exists_min_image candidates familyWeight ⟨G, hG_cand⟩
  have hG'_mem : G' ∈ candidates := hG'_cand
  simp only [hcand_def, Finset.mem_filter, Finset.mem_powerset] at hG'_cand
  obtain ⟨hG'_sub, hG'_card, hG'_int⟩ := hG'_cand
  -- Step 2: G' has shiftN property
  have hG'_shift := min_weight_shiftN N F G' hF_sub hF_hered' hG'_sub hG'_int
    (fun G'' hG''_sub hG''_card hG''_int => hG'_min G''
      (by simp only [hcand_def, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hG''_sub, hG''_card.trans hG'_card, hG''_int⟩))
  -- Step 3: Three-way split of G'
  -- G'_sc: self-complementary part, G'_0: non-sc without N, G'_2: non-sc with N
  set G'_sc := G'.filter (fun X => Finset.Icc 1 N \ X ∈ F) with hG'_sc_def
  set G'_ns := G'.filter (fun X => Finset.Icc 1 N \ X ∉ F) with hG'_ns_def
  set G'_0 := G'_ns.filter (fun X => N ∉ X) with hG'_0_def
  set G'_2 := G'_ns.filter (fun X => N ∈ X) with hG'_2_def
  -- Step 4: Split H = F.filter(1 ∈ ·) similarly
  set H := F.filter (fun X => (1 : ℕ) ∈ X) with hH_def
  set H_sc := H.filter (fun X => Finset.Icc 1 N \ X ∈ F) with hH_sc_def
  set H_0 := (H.filter (fun X => Finset.Icc 1 N \ X ∉ F)).filter (fun X => N ∉ X)
  set H_2 := (H.filter (fun X => Finset.Icc 1 N \ X ∉ F)).filter (fun X => N ∈ X)
  -- Step 5: G' = G'_sc ∪ G'_0 ∪ G'_2, H = H_sc ∪ H_0 ∪ H_2
  have hG'_split : G'.card = G'_sc.card + G'_0.card + G'_2.card := by
    rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
    · congr;
      grind;
    · simp +contextual [ Finset.disjoint_left ];
      grind;
    · exact Finset.disjoint_left.mpr fun x hx hx' => by aesop;
  have hH_split : H.card = H_sc.card + H_0.card + H_2.card := by
    rw [ ← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint ];
    · congr with x
      by_cases hx : Finset.Icc 1 N \ x ∈ F <;>
        by_cases hx' : N ∈ x <;> simp +decide;
      · grind +extAll;
      · grind;
      · grind;
      · grind;
    · simp +contextual [ Finset.disjoint_left ];
      grind +splitIndPred;
    · exact Finset.disjoint_left.mpr fun x hx hx' => by aesop;
  -- Step 6: Bound |G'_sc| ≤ |H_sc|
  have hsc_bound : G'_sc.card ≤ H_sc.card := by
    have := compl_pair_bound N hN F hF_sub G' hG'_sub hG'_int
    convert this using 2
    ext X; simp [hH_sc_def, hH_def]
    tauto
  -- Step 7: Bound |G'_0| ≤ |H_0| by induction on F_0
  have h0_bound : G'_0.card ≤ H_0.card := by
    convert ih (N - 1) (Nat.sub_lt (by linarith) zero_lt_one)
      (F.filter (fun X =>
        X ⊆ Icc 1 (N - 1) ∧ Icc 1 N \ X ∉ F))
      _ _ G'_0 _ _ using 1;
    · refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +contextual;
      · grind;
      · grind;
    · grind +qlia;
    · simp +zetaDelta at *;
      intros X hX hX_sub hX_not_in_F Y hY_sub hY_dom
      apply And.intro;
      · exact hF_hered X hX Y
          (hY_sub.trans
            (Finset.Icc_subset_Icc_right (Nat.pred_le _)))
          hY_dom;
      · apply And.intro hY_sub;
        apply F_nonsc_hered N F hF_sub hF_hered X hX
          hX_not_in_F Y (by
          exact Finset.Subset.trans hY_sub
            (Finset.Icc_subset_Icc_right
              (Nat.pred_le _))) hY_dom |>.2;
    · grind;
    · exact fun X hX Y hY =>
        hG'_int X
          (Finset.mem_filter.mp hX |>.1 |>
            Finset.mem_filter.mp |>.1)
          Y
          (Finset.mem_filter.mp hY |>.1 |>
            Finset.mem_filter.mp |>.1)
  -- Step 8: Bound |G'_2| ≤ |H_2| by link argument + induction
  have h2_bound : G'_2.card ≤ H_2.card := by
    -- By the problem statement, the link of $G'_2$ at $N$ is intersecting.
    have h_link_int : ∀ Y ∈ G'_2, ∀ Z ∈ G'_2, ((Y.erase N) ∩ (Z.erase N)).Nonempty := by
      intros Y hy Z hz
      have hyG := Finset.mem_filter.mp hy |>.1 |>
        Finset.mem_filter.mp
      have hzG := Finset.mem_filter.mp hz |>.1 |>
        Finset.mem_filter.mp
      exact nonsc_link_int N F hF_sub hF_hered G'
        hG'_sub hG'_int hG'_shift Y hyG.1
        (Finset.mem_filter.mp hy |>.2) hyG.2 Z hzG.1
        (Finset.mem_filter.mp hz |>.2);
    -- Define K := (F.filter(fun X => N ∈ X ∧ Icc 1 N \ X ∉ F)).image(fun X => X.erase N).
    set K := (F.filter (fun X =>
        N ∈ X ∧ Finset.Icc 1 N \ X ∉ F)).image
      (fun X => X.erase N) with hK_def;
    -- K is hereditary on Icc 1 (N-1).
    have hK_hered : ∀ X ∈ K, ∀ Y ⊆ Finset.Icc 1 (N - 1), Dominated Y X → Y ∈ K := by
      intros X hX Y hY_sub hY_dom;
      obtain ⟨ Z, hZ, rfl ⟩ := Finset.mem_image.mp hX;
      -- Since $Y$ is dominated by $Z.erase N$, we have $Y ∪ {N}$ is dominated by $Z$.
      have hY_union_N_dom : Dominated (Y ∪ {N}) Z := by
        obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := hY_dom;
        use fun x => if x = N then N else f x;
        simp +zetaDelta at *;
        refine' ⟨ _, _, _ ⟩;
        · intro x hx y hy; simp +decide [ Set.InjOn ] at *;
          grind;
        · grind;
        · grind +locals;
      have hY_union_N_in_F : Y ∪ {N} ∈ F := by
        apply hF_hered' Z (Finset.mem_filter.mp hZ).left (Y ∪ {N});
        · exact Finset.union_subset
            (hY_sub.trans
              (Finset.Icc_subset_Icc_right
                (Nat.pred_le _)))
            (by norm_num; linarith);
        · exact hY_union_N_dom;
      have hY_union_N_compl_not_in_F : Finset.Icc 1 N \ (Y ∪ {N}) ∉ F := by
        have hY_union_N_compl_not_in_F :
            Dominated (Finset.Icc 1 N \ Z)
              (Finset.Icc 1 N \ (Y ∪ {N})) := by
          convert dominated_compl N _ _ _ _ hY_union_N_dom using 1;
          · exact hF_sub _ ( Finset.mem_filter.mp hZ |>.1 );
          · exact Finset.union_subset
              (Finset.Subset.trans hY_sub
                (Finset.Icc_subset_Icc_right
                  (Nat.pred_le _)))
              (by norm_num; linarith);
        grind;
      simp +zetaDelta at *;
      use insert N Y;
      simp [hY_union_N_in_F, hY_union_N_compl_not_in_F];
      exact fun h => by have := hY_sub h; norm_num at this; omega;
    -- Apply the induction hypothesis to K.
    have h_ind : (G'_2.image (fun X => X.erase N)).card ≤ (K.filter (fun X => 1 ∈ X)).card := by
      apply ih (N - 1) (Nat.sub_lt (by linarith) (by linarith)) K;
      · simp +zetaDelta at *;
        intros X x hx hxN hx_not_in_F hx_erase_N
        have hx_subset : x ⊆ Finset.Icc 1 N := by
          exact hF_sub x hx;
        exact hx_erase_N ▸ fun y hy =>
          Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp
                (hx_subset (Finset.mem_of_mem_erase hy))).1,
              Nat.le_sub_one_of_lt
                ((Finset.mem_Icc.mp
                    (hx_subset
                      (Finset.mem_of_mem_erase hy))).2.lt_of_ne
                  (by aesop))⟩;
      · assumption;
      · simp +zetaDelta at *;
        simp +contextual [ Finset.subset_iff ];
        exact fun x y hy hy' hy'' hx => ⟨ y, ⟨ hG'_mem.1 hy, hy'', hy' ⟩, hx ⟩;
      · simp +zetaDelta at *;
        rintro X x hx hx' hx'' rfl Y y hy hy' hy'' rfl;
        exact h_link_int x hx hx' hx'' y hy hy' hy'' |> fun ⟨ z, hz ⟩ => ⟨ z, by aesop ⟩;
    convert h_ind using 1;
    · rw [ Finset.card_image_of_injOn ];
      intro X hX Y hy hXY; simp_all +decide [ Finset.ext_iff ] ;
      grind;
    · refine' Finset.card_bij ( fun X hX => X.erase N ) _ _ _ <;> simp +contextual [ hK_def ];
      · grind +locals;
      · simp +contextual [ Finset.ext_iff ];
        grind;
      · grind +qlia
  -- Step 9: Sum
  linarith [hG'_card.symm]

set_option maxHeartbeats 800000 in
theorem chvatal_theorem_ground_set (N : ℕ) (hN : 0 < N)
    (F : Finset (Finset ℕ))
    (hF_sub : ∀ X ∈ F, X ⊆ Finset.Icc 1 N)
    (hF_hered : ∀ X ∈ F, ∀ Y, Y ⊆ Finset.Icc 1 N → Dominated Y X → Y ∈ F)
    (G : Finset (Finset ℕ)) (hG_sub : G ⊆ F)
    (hG_int : ∀ X ∈ G, ∀ Y ∈ G, (X ∩ Y).Nonempty) :
    G.card ≤ (F.filter (1 ∈ ·)).card := by
  induction' N using Nat.strong_induction_on with N ih generalizing F G;
  by_cases hG2 :
      ∀ X ∈ G.filter (fun X => N ∈ X),
      ∀ Y ∈ G.filter (fun X => N ∈ X),
      (X.erase N ∩ Y.erase N).Nonempty;
  · -- Let $G_1 = G.filter (fun X => N ∉ X)$ and $G_2 = G.filter (fun X => N ∈ X)$.
    set G1 := G.filter (fun X => N ∉ X)
    set G2 := G.filter (fun X => N ∈ X);
    have hG1 : G1.card ≤
        (Finset.filter (1 ∈ ·) (F.filter (N ∉ ·))).card := by
      by_cases hN1 : N = 1;
      · simp +zetaDelta at *;
        rw [ Finset.card_eq_zero.mpr ];
        · exact Nat.zero_le _;
        · grind;
      · convert ih (N - 1) (Nat.pred_lt hN.ne')
          (Nat.sub_pos_of_lt
            (lt_of_le_of_ne hN (Ne.symm hN1)))
          (F.filter (fun X => N ∉ X))
          _ _ G1 _ _ using 1;
        · intro X hX x hx
          have hm := hF_sub X (Finset.mem_filter.mp hX |>.1) hx
          exact Finset.mem_Icc.mpr
            ⟨(Finset.mem_Icc.mp hm).1,
              Nat.le_pred_of_lt
                ((Finset.mem_Icc.mp hm).2.lt_of_ne
                  (by aesop))⟩
        · simp +zetaDelta at *;
          exact fun X hX hNX Y hY hYX =>
            ⟨hF_hered X hX Y
              (Finset.Subset.trans hY
                (Finset.Icc_subset_Icc_right
                  (Nat.pred_le _))) hYX,
            fun hNY => by
              have := hY hNY
              exact absurd this (by norm_num; omega)⟩
        · exact fun x hx =>
            Finset.mem_filter.mpr
              ⟨hG_sub <| Finset.mem_filter.mp hx |>.1,
                Finset.mem_filter.mp hx |>.2⟩
        · exact fun X hX Y hY =>
            hG_int X (Finset.filter_subset _ _ hX)
              Y (Finset.filter_subset _ _ hY)
    have hG2 : G2.card ≤
        (Finset.filter (1 ∈ ·)
          ((F.filter (N ∈ ·)).image (fun X =>
            X.erase N))).card := by
      by_cases hN1 : N = 1;
      · simp_all +decide [ Finset.subset_iff ];
        contrapose! hG2;
        obtain ⟨ X, hX ⟩ := Finset.card_pos.mp ( pos_of_gt hG2 ) ; use X; aesop;
      · convert ih (N - 1) (Nat.sub_lt hN zero_lt_one)
          (Nat.sub_pos_of_lt
            (lt_of_le_of_ne hN (Ne.symm hN1)))
          (Finset.image (fun X => X.erase N)
            (F.filter (fun X => N ∈ X)))
          _ _
          (Finset.image (fun X => X.erase N) G2)
          _ _ using 1;
        · rw [ Finset.card_image_of_injOn ];
          intro X hX Y hy; simp_all +decide [ Finset.ext_iff ] ;
          grind +locals;
        · grind +qlia;
        · simp +zetaDelta at *;
          rintro X x hx hxN rfl Y hy hY;
          use Insert.insert N Y;
          simp +zetaDelta at *;
          refine' ⟨ hF_hered _ hx _ _ _, _ ⟩;
          · exact Finset.insert_subset_iff.mpr
              ⟨Finset.mem_Icc.mpr ⟨hN, le_rfl⟩,
                hy.trans
                  (Finset.Icc_subset_Icc_right
                    (Nat.pred_le _))⟩;
          · obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := hY;
            use fun y => if y = N then N else f y;
            simp_all +decide [ Set.InjOn ];
            grind;
          · exact fun h => by have := hy h; have := Finset.mem_Icc.mp this; omega;
        · exact Finset.image_subset_image <| Finset.filter_subset_filter _ hG_sub;
        · grind;
    have hG2_card :
        (Finset.filter (1 ∈ ·)
          ((F.filter (N ∈ ·)).image (fun X =>
            X.erase N))).card ≤
        (Finset.filter (fun X => 1 ∈ X ∧ N ∈ X) F).card := by
      rw [ Finset.card_filter, Finset.card_filter ];
      rw [ Finset.sum_image ];
      · rw [ Finset.sum_filter ];
        gcongr ; aesop;
      · intro X hX Y hy; simp_all +decide [ Finset.ext_iff ] ;
        grind +revert;
    have hG_card : G.card = G1.card + G2.card := by
      rw [ Finset.card_filter, Finset.card_filter ];
      simpa only [← Finset.sum_add_distrib] using
        Finset.card_eq_sum_ones G ▸ by
          congr; ext; split_ifs <;> tauto;
    convert Nat.add_le_add hG1 ( hG2.trans hG2_card ) using 1;
    rw [ ← Finset.card_union_of_disjoint ];
    · congr with X ; by_cases hX : N ∈ X <;> aesop;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by aesop;
  · by_cases hN2 : 2 ≤ N;
    · apply chvatal_case_B N hN2 F hF_sub hF_hered G
        hG_sub hG_int (G.filter (fun X => N ∈ X)) rfl;
      · grind;
      · grind +locals;
    · interval_cases N ; simp_all +decide;
      rw [ show G = { { 1 } } from _ ];
      · exact Finset.card_pos.mpr ⟨{1}, by
          obtain ⟨x, hx, hx', y, hy, hy', hxy⟩ := hG2
          specialize hF_sub x (hG_sub hx); aesop⟩;
      · grind

/-! ### Relabeling: reducing to the ground set {1, …, N} -/

/-- The rank function: maps elements of `S` to `{1, …, |S|}` preserving order.
For elements not in `S`, returns 0. -/
noncomputable def rankFun (S : Finset ℕ) (x : ℕ) : ℕ :=
  if hx : x ∈ S then ((S.orderIsoOfFin rfl).symm ⟨x, hx⟩).val + 1 else 0

/-- The inverse of rankFun: maps `k ∈ {1, …, |S|}` to the `k`-th smallest element of `S`. -/
noncomputable def unrankFun (S : Finset ℕ) (k : ℕ) : ℕ :=
  if h : 1 ≤ k ∧ k ≤ S.card then (S.orderIsoOfFin rfl ⟨k - 1, by omega⟩ : ℕ) else 0

private lemma rankFun_mem_Icc {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) :
    rankFun S x ∈ Finset.Icc 1 S.card := by
  -- Since x is in S, the rank of x is in the range {1, ..., |S|}.
  simp only [rankFun, hx, ↓reduceDIte, mem_Icc,
    le_add_iff_nonneg_left, _root_.zero_le,
    Order.add_one_le_iff, Fin.is_lt, and_self]

private lemma rankFun_strictMonoOn (S : Finset ℕ) :
    StrictMonoOn (rankFun S) (S : Set ℕ) := by
  intros x hx y hy hxy
  have h_order :
      (S.orderIsoOfFin rfl).symm ⟨x, hx⟩ <
      (S.orderIsoOfFin rfl).symm ⟨y, hy⟩ := by
    simp_all only [OrderIso.lt_iff_lt, Subtype.mk_lt_mk]
  unfold rankFun
  simp_all only [OrderIso.lt_iff_lt, Subtype.mk_lt_mk,
    gt_iff_lt]
  simp_all only [SetLike.mem_coe, ↓reduceDIte,
    Order.lt_add_one_iff, Order.add_one_le_iff,
    Fin.val_fin_lt, OrderIso.lt_iff_lt,
    Subtype.mk_lt_mk]

private lemma rankFun_image (S : Finset ℕ) :
    S.image (rankFun S) = Finset.Icc 1 S.card := by
  refine' Finset.eq_of_subset_of_card_le _ _;
  · exact Finset.image_subset_iff.mpr fun x hx => rankFun_mem_Icc hx;
  · rw [ Finset.card_image_of_injOn ];
    · norm_num;
    · exact rankFun_strictMonoOn S |> StrictMonoOn.injOn

private lemma rankFun_min' {S : Finset ℕ} (hS : S.Nonempty) :
    rankFun S (S.min' hS) = 1 := by
  unfold rankFun
  have hm := Finset.min'_mem S hS
  simp only [hm, ↓reduceDIte]
  suffices h : (S.orderIsoOfFin rfl).symm
      ⟨S.min' hS, hm⟩ =
      ⟨0, Finset.card_pos.mpr hS⟩ by
    simp only [h, Fin.val_mk]
  rw [OrderIso.symm_apply_eq]
  ext
  exact (Finset.orderEmbOfFin_zero rfl
    (Finset.card_pos.mpr hS)).symm

private lemma unrankFun_mem {S : Finset ℕ} {k : ℕ} (hk : 1 ≤ k ∧ k ≤ S.card) :
    unrankFun S k ∈ S := by
  unfold unrankFun
  simp_all only [and_self, ↓reduceDIte,
    coe_orderIsoOfFin_apply, orderEmbOfFin_mem]

private lemma unrankFun_rankFun {S : Finset ℕ} {x : ℕ} (hx : x ∈ S) :
    unrankFun S (rankFun S x) = x := by
  unfold unrankFun rankFun
  simp_all only [↓reduceDIte, le_add_iff_nonneg_left,
    _root_.zero_le, Order.add_one_le_iff, Fin.is_lt,
    and_self, add_tsub_cancel_right, Fin.eta,
    OrderIso.apply_symm_apply]

private lemma rankFun_unrankFun {S : Finset ℕ} {k : ℕ} (hk : 1 ≤ k ∧ k ≤ S.card) :
    rankFun S (unrankFun S k) = k := by
  unfold rankFun unrankFun
  split_ifs <;>
    simp_all +decide only [coe_orderIsoOfFin_apply,
      orderEmbOfFin_mem, not_true_eq_false]
  erw [OrderIso.symm_apply_apply]
  simp_all only [coe_orderIsoOfFin_apply,
    orderEmbOfFin_mem, Nat.sub_add_cancel]

private lemma unrankFun_monotone {S : Finset ℕ} {a b : ℕ}
    (ha : 1 ≤ a ∧ a ≤ S.card) (hb : 1 ≤ b ∧ b ≤ S.card) (hab : a ≤ b) :
    unrankFun S a ≤ unrankFun S b := by
  unfold unrankFun;
  simp +decide only [ha, and_self, ↓reduceDIte,
    coe_orderIsoOfFin_apply, hb,
    OrderEmbedding.le_iff_le, Fin.mk_le_mk,
    tsub_le_iff_right, Nat.sub_add_cancel, hab]

private lemma dominated_image_rankFun {S Y X : Finset ℕ} (hY : Y ⊆ S) (hX : X ⊆ S)
    (h : Dominated Y X) :
    Dominated (Y.image (rankFun S)) (X.image (rankFun S)) := by
  cases' h with f hf;
  use fun k => rankFun S ( f ( unrankFun S k ) );
  refine' ⟨ _, _, _ ⟩;
  · intro k hk l hl hkl;
    obtain ⟨y, hyY, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨z, hzY, rfl⟩ := Finset.mem_image.mp hl
    change rankFun S (f (unrankFun S (rankFun S y))) =
      rankFun S (f (unrankFun S (rankFun S z))) at hkl
    rw [unrankFun_rankFun (hY hyY), unrankFun_rankFun (hY hzY)] at hkl
    have hf_eq : f y = f z :=
      (rankFun_strictMonoOn S).injOn
        (hX (hf.2.1 y hyY)) (hX (hf.2.1 z hzY)) hkl
    exact congrArg (rankFun S) (hf.1 hyY hzY hf_eq)
  · simp +zetaDelta at *;
    intro y hy;
    rw [ unrankFun_rankFun ] ; aesop;
    exact hY hy;
  · simp_all +decide [ Set.InjOn ];
    intro y hy; rw [ unrankFun_rankFun ( hY hy ) ] ;
    exact (rankFun_strictMonoOn S).le_iff_le
      (hY hy) (hX (hf.2.1 y hy)) |>.2 (hf.2.2 y hy)

private lemma dominated_image_unrankFun {S : Finset ℕ} {Y' X' : Finset ℕ}
    (hY' : Y' ⊆ Finset.Icc 1 S.card) (hX' : X' ⊆ Finset.Icc 1 S.card)
    (h : Dominated Y' X') :
    Dominated (Y'.image (unrankFun S)) (X'.image (unrankFun S)) := by
  obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := h;
  refine' ⟨fun x =>
    unrankFun S (f (rankFun S x)), _, _, _⟩ <;>
    simp_all +decide [Set.InjOn];
  · intro x hx y hy hxy
    have h_eq : f (rankFun S (unrankFun S x)) = f (rankFun S (unrankFun S y)) := by
      apply_fun rankFun S at hxy;
      convert hxy using 1;
      · rw [ rankFun_unrankFun ];
        · rw [ rankFun_unrankFun ];
          constructor
          · linarith [hf₃ x hx, Finset.mem_Icc.mp (hY' hx)]
          · have := Finset.mem_Icc.mp (hX' (hf₂ x hx))
            linarith
        · exact Finset.mem_Icc.mp ( hY' hx );
      · rw [ rankFun_unrankFun ];
        · rw [ rankFun_unrankFun ];
          exact ⟨hf₃ y hy |> le_trans
            (Finset.mem_Icc.mp (hY' hy) |>.1),
            (Finset.mem_Icc.mp (hX' (hf₂ y hy))).2⟩;
        · exact Finset.mem_Icc.mp ( hY' hy );
    have h_eq : rankFun S (unrankFun S x) = rankFun S (unrankFun S y) := by
      apply hf₁;
      · convert hx using 1;
        exact rankFun_unrankFun ( Finset.mem_Icc.mp ( hY' hx ) );
      · convert hy using 1;
        exact rankFun_unrankFun ( Finset.mem_Icc.mp ( hY' hy ) );
      · exact h_eq;
    have h_eq : ∀ k ∈ Finset.Icc 1 S.card, rankFun S (unrankFun S k) = k := by
      exact fun k hk => rankFun_unrankFun <| Finset.mem_Icc.mp hk;
    have := h_eq x ( hY' hx ) ; have := h_eq y ( hY' hy ) ; aesop;
  · exact fun x hx => ⟨f x, hf₂ x hx, by
      rw [rankFun_unrankFun
        (show 1 ≤ x ∧ x ≤ S.card from
          Finset.mem_Icc.mp (hY' hx))]⟩;
  · intro y hy; rw [ rankFun_unrankFun ] ;
    · exact unrankFun_monotone
        (Finset.mem_Icc.mp (hY' hy))
        (Finset.mem_Icc.mp (hX' (hf₂ y hy)))
        (hf₃ y hy);
    · exact Finset.mem_Icc.mp ( hY' hy )

/-
Finsets that are subsets of S are uniquely determined by their rankFun-images.
-/
private lemma image_rankFun_injOn (S : Finset ℕ) :
    Set.InjOn (fun X => X.image (rankFun S))
      {X : Finset ℕ | X ⊆ S} := by
  intro X hX Y hY heq
  have heq' : X.image (rankFun S) =
      Y.image (rankFun S) := heq
  ext x
  have hinj := (rankFun_strictMonoOn S).injOn
  constructor <;> intro hx
  · have hmem : rankFun S x ∈ Y.image (rankFun S) :=
      heq' ▸ Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hmem
    exact hinj (hX hx) (hY hy) hxy.symm ▸ hy
  · have hmem : rankFun S x ∈ X.image (rankFun S) :=
      heq'.symm ▸ Finset.mem_image_of_mem _ hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hmem
    exact hinj (hY hx) (hX hy) hxy.symm ▸ hy

/-
The filter condition is preserved by rankFun: `S.min' hS ∈ X ↔ 1 ∈ X.image (rankFun S)`
for `X ⊆ S`.
-/
private lemma mem_min_iff_one_mem_image
    {S X : Finset ℕ} (hS : S.Nonempty) (hX : X ⊆ S) :
    S.min' hS ∈ X ↔ 1 ∈ X.image (rankFun S) := by
  constructor
  · exact fun h => Finset.mem_image.mpr
      ⟨_, h, rankFun_min' hS⟩
  · intro h
    obtain ⟨x, hx, hx'⟩ := Finset.mem_image.mp h
    have hinj := (rankFun_strictMonoOn S).injOn
    have : x = S.min' hS := hinj (hX hx)
      (Finset.min'_mem S hS)
      (hx'.trans (rankFun_min' hS).symm)
    exact this ▸ hx

/-! ### Chvátal's Theorem (General Version) -/

/-- **Chvátal's Theorem** (generalized to an arbitrary ground set `S ⊆ ℕ`).

Let `S` be a nonempty finite set of natural numbers. Let `F` be a family of subsets of `S`
satisfying the **hereditary property**: if `X ∈ F` and `Y ⊆ S` is dominated by `X`
(i.e., there is an injection `f : Y → X` with `y ≤ f(y)` for all `y`), then `Y ∈ F`.

If `G ⊆ F` is an **intersecting family** (any two members share a common element), then
`|G| ≤ |{X ∈ F : min(S) ∈ X}|`.

This is the main theorem of Chvátal, "Intersecting families of edges in hypergraphs having
the hereditary property", generalized from the ground set `{1, …, n}` to an arbitrary
finite `S ⊆ ℕ` by the obvious order-preserving relabeling. -/
theorem chvatal_theorem (S : Finset ℕ) (hS : S.Nonempty)
    (F : Finset (Finset ℕ))
    (hF_sub : ∀ X ∈ F, X ⊆ S)
    (hF_hered : ∀ X ∈ F, ∀ Y, Y ⊆ S → Dominated Y X → Y ∈ F)
    (G : Finset (Finset ℕ)) (hG_sub : G ⊆ F)
    (hG_int : ∀ X ∈ G, ∀ Y ∈ G, (X ∩ Y).Nonempty) :
    G.card ≤ (F.filter (S.min' hS ∈ ·)).card := by
  -- Relabel S to {1, …, |S|} via rankFun
  set N := S.card with hN_def
  have hN : 0 < N := Finset.Nonempty.card_pos hS
  set mapSet : Finset ℕ → Finset ℕ := fun X => X.image (rankFun S)
  set F' := F.image mapSet
  set G' := G.image mapSet
  -- mapSet is injective on F (all members are subsets of S)
  have mapSet_injOn_F : Set.InjOn mapSet (F : Set (Finset ℕ)) := by
    intro A hA B hB hAB
    exact image_rankFun_injOn S (hF_sub A hA) (hF_sub B hB) hAB
  -- Verify conditions for chvatal_theorem_ground_set
  have hF'_sub : ∀ X ∈ F', X ⊆ Finset.Icc 1 N := by
    intro X' hX'
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hX'
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact rankFun_mem_Icc (hF_sub X hX hx)
  have hF'_hered : ∀ X ∈ F', ∀ Y, Y ⊆ Finset.Icc 1 N → Dominated Y X → Y ∈ F' := by
    intro X' hX' Y' hY' hdom
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hX'
    -- Un-relabel Y' to get Y ⊆ S
    set Y := Y'.image (unrankFun S)
    have hY_sub : Y ⊆ S := by
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
      exact unrankFun_mem (Finset.mem_Icc.mp (hY' hk))
    -- Show Dominated Y X
    have hX_sub := hF_sub X hX
    have hX'_sub : X.image (rankFun S) ⊆ Finset.Icc 1 S.card := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact rankFun_mem_Icc (hX_sub hx)
    have hunrelabel : (X.image (rankFun S)).image (unrankFun S) = X := by
      ext y; constructor
      · intro hy'
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy'
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
        rwa [unrankFun_rankFun (hX_sub hx)]
      · intro hy'
        exact Finset.mem_image.mpr ⟨rankFun S y,
          Finset.mem_image_of_mem _ hy', unrankFun_rankFun (hX_sub hy')⟩
    have hdom_Y_X : Dominated Y X := hunrelabel ▸
      dominated_image_unrankFun hY' hX'_sub hdom
    have hY_in_F := hF_hered X hX Y hY_sub hdom_Y_X
    -- Show Y' = mapSet Y
    have hY'_eq : Y' = Y.image (rankFun S) := by
      ext k; constructor
      · intro hk
        exact Finset.mem_image.mpr ⟨unrankFun S k,
          Finset.mem_image.mpr ⟨k, hk, rfl⟩,
          rankFun_unrankFun (Finset.mem_Icc.mp (hY' hk))⟩
      · intro hk
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hy
        rwa [rankFun_unrankFun (Finset.mem_Icc.mp (hY' hk'))]
    rw [hY'_eq]
    exact Finset.mem_image_of_mem mapSet hY_in_F
  have hG'_sub : G' ⊆ F' := Finset.image_subset_image hG_sub
  have hG'_int : ∀ X ∈ G', ∀ Y ∈ G', (X ∩ Y).Nonempty := by
    intro X' hX' Y' hY'
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hX'
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hY'
    obtain ⟨z, hz⟩ := hG_int X hX Y hY
    exact ⟨rankFun S z, Finset.mem_inter.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_inter.mp hz).1,
       Finset.mem_image_of_mem _ (Finset.mem_inter.mp hz).2⟩⟩
  -- Apply chvatal_theorem_ground_set
  have step := chvatal_theorem_ground_set N hN F' hF'_sub hF'_hered G' hG'_sub hG'_int
  -- Connect cardinalities: G.card = G'.card
  have hG_card : G.card = G'.card := by
    symm; exact Finset.card_image_of_injOn
      (mapSet_injOn_F.mono (Finset.coe_subset.mpr hG_sub))
  -- Connect cardinalities: filter condition
  have hF_filter_card : (F.filter (S.min' hS ∈ ·)).card = (F'.filter (1 ∈ ·)).card := by
    have : (F.image mapSet).filter (1 ∈ ·) = (F.filter (S.min' hS ∈ ·)).image mapSet := by
      ext X'; simp only [Finset.mem_filter, Finset.mem_image]; constructor
      · rintro ⟨⟨X, hX, rfl⟩, h1⟩
        exact ⟨X, ⟨hX, (mem_min_iff_one_mem_image hS (hF_sub X hX)).mpr h1⟩, rfl⟩
      · rintro ⟨X, ⟨hX, hmin⟩, rfl⟩
        exact ⟨⟨X, hX, rfl⟩, (mem_min_iff_one_mem_image hS (hF_sub X hX)).mp hmin⟩
    rw [show F' = F.image mapSet from rfl, this]
    exact (Finset.card_image_of_injOn
      (mapSet_injOn_F.mono (Finset.coe_subset.mpr
        (Finset.filter_subset (S.min' hS ∈ ·) F)))).symm
  linarith

/-! ### Helper lemmas about squarefree numbers -/

/-
If `a` is not squarefree, then `a * b` is not squarefree for any `b`.
-/
lemma not_squarefree_mul_left {a b : ℕ} (ha : ¬ Squarefree a) : ¬ Squarefree (a * b) := by
  exact fun h => ha <| h.squarefree_of_dvd <| dvd_mul_right _ _

/-
For squarefree `a` and `b`, if `a * b` is not squarefree then `a` and `b` are not
coprime. This is the contrapositive of `Nat.squarefree_mul_iff`.
-/
lemma not_coprime_of_squarefree_not_squarefree_mul {a b : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hab : ¬ Squarefree (a * b)) :
    ¬ Nat.Coprime a b := by
  exact fun h => hab <| Nat.squarefree_mul_iff.mpr ⟨ h, ha, hb ⟩

/-
Two squarefree positive natural numbers with the same prime factors are equal.
-/
lemma eq_of_squarefree_primeFactors_eq {a b : ℕ}
    (ha : Squarefree a) (hb : Squarefree b)
    (h : a.primeFactors = b.primeFactors) : a = b := by
  rw [ ← Nat.prod_primeFactors_of_squarefree ha, ← Nat.prod_primeFactors_of_squarefree hb, h ]

/-
`Nat.primeFactors` is injective on squarefree positive natural numbers.
-/
lemma primeFactors_injOn_squarefree :
    Set.InjOn Nat.primeFactors {m : ℕ | Squarefree m} := by
  intro m hm n hn hmn;
  convert eq_of_squarefree_primeFactors_eq hm hn hmn

/-
The prime factors of a number in `{1, …, N}` are all primes `≤ N`.
-/
lemma primeFactors_subset_primes_Icc {m N : ℕ} (hm : m ∈ Finset.Icc 1 N) :
    m.primeFactors ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
  exact fun x hx => Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_primeFactors hx,
        Nat.le_trans (Nat.le_of_mem_primeFactors hx)
          (Finset.mem_Icc.mp hm |>.2)⟩,
      Nat.prime_of_mem_primeFactors hx⟩

/-
The product of a finset of primes is at least 1.
-/
lemma one_le_prod_primes {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    1 ≤ ∏ p ∈ s, p := by
  exact Finset.prod_pos fun p hp => Nat.Prime.pos ( hs p hp )

/-
The product of a finset of primes is squarefree.
-/
lemma squarefree_prod_primes {s : Finset ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  induction s using Finset.induction with
  | empty => exact squarefree_one
  | @insert a s hna ih =>
    rw [Finset.prod_insert hna]
    have hp := hs _ (Finset.mem_insert_self _ _)
    have hs' : ∀ q ∈ _, Nat.Prime q :=
      fun q hq => hs q (Finset.mem_insert_of_mem hq)
    exact Nat.squarefree_mul_iff.mpr
      ⟨Nat.Coprime.prod_right fun q hq =>
        hp.coprime_iff_not_dvd.mpr fun hdvd =>
          hna ((Nat.prime_dvd_prime_iff_eq hp
            (hs' q hq)).mp hdvd ▸ hq),
        hp.squarefree, ih hs'⟩

/-- For `N ≥ 2`, the minimum element of the primes in `{1, …, N}` is 2. -/
lemma primes_Icc_nonempty {N : ℕ} (hN : 2 ≤ N) :
    ((Finset.Icc 1 N).filter Nat.Prime).Nonempty :=
  ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hN⟩, by decide⟩⟩

lemma min_primes_Icc_eq_two {N : ℕ} (hN : 2 ≤ N) :
    ((Finset.Icc 1 N).filter Nat.Prime).min' (primes_Icc_nonempty hN) = 2 := by
  refine' le_antisymm _ _ <;> norm_num [ Finset.min' ];
  · exact ⟨ 2, ⟨ ⟨ by norm_num, hN ⟩, by norm_num ⟩, by norm_num ⟩;
  · exact fun b hb₁ hb₂ hb₃ => hb₃.two_le

/-
Not coprime iff prime factors are not disjoint (for positive numbers).
-/
lemma not_coprime_iff_primeFactors_not_disjoint {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ¬ Nat.Coprime a b ↔ ¬ Disjoint a.primeFactors b.primeFactors := by
  rw [not_iff_not]
  exact (Nat.disjoint_primeFactors ha hb).symm

/-
Not disjoint finsets iff nonempty intersection.
-/
lemma Finset.not_disjoint_iff_inter_nonempty {α : Type*} [DecidableEq α]
    {s t : Finset α} : ¬ Disjoint s t ↔ (s ∩ t).Nonempty := by
  rw [Finset.disjoint_iff_inter_eq_empty,
    Finset.nonempty_iff_ne_empty]

/-! ### Hereditary property for squarefree prime-factor families -/

/-
The family of prime-factor sets of squarefree numbers in `{1, …, N}` satisfies the
hereditary property under the dominance order, with ground set being the primes in
`{1, …, N}`.
-/
lemma hereditary_squarefree_primeFactors (N : ℕ) :
    let S := (Finset.Icc 1 N).filter Nat.Prime
    let F := ((Finset.Icc 1 N).filter Squarefree).image Nat.primeFactors
    ∀ X ∈ F, ∀ Y, Y ⊆ S → Dominated Y X → Y ∈ F := by
  simp +zetaDelta at *;
  intros X x hx₁ hx₂ hx₃ hx₄ Y hy₁ hy₂;
  use ∏ p ∈ Y, p;
  have hprime : ∀ p, p ∈ Y → Nat.Prime p :=
    fun p hp => (Finset.mem_filter.mp (hy₁ hp)).2
  refine' ⟨⟨⟨one_le_prod_primes hprime, _⟩,
    squarefree_prod_primes hprime⟩, _⟩;
  · obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := hy₂;
    refine' le_trans _ ( show ∏ p ∈ Finset.image f Y, p ≤ N from _ );
    · rw [ Finset.prod_image <| by tauto ];
      exact Finset.prod_le_prod' hf₃;
    · have h_prod_le_N : ∏ p ∈ X, p ≤ N := by
        rw [ ← hx₄, Nat.prod_primeFactors_of_squarefree hx₃ ] ; linarith;
      exact le_trans
        (Finset.prod_le_prod_of_subset_of_one_le'
          (Finset.image_subset_iff.mpr hf₂)
          fun p hp _ =>
            Nat.Prime.pos
              (Nat.prime_of_mem_primeFactors
                (hx₄ ▸ hp)))
        h_prod_le_N;
  · exact Nat.primeFactors_prod fun p hp => ( Finset.mem_filter.mp ( hy₁ hp ) ) |>.2

/-! ### Application of Chvátal to squarefree numbers -/

theorem chvatal_squarefree (N : ℕ) (B : Finset ℕ)
    (hB : B ⊆ (Finset.Icc 1 N).filter Squarefree)
    (hB_int : ∀ a ∈ B, ∀ b ∈ B, ¬ Nat.Coprime a b) :
    B.card ≤ ((Finset.Icc 1 N).filter (fun k => Squarefree k ∧ 2 ∣ k)).card := by
  by_cases hN : 2 ≤ N;
  · set S := (Finset.Icc 1 N).filter Nat.Prime
    set F := ((Finset.Icc 1 N).filter Squarefree).image Nat.primeFactors
    set G := B.image Nat.primeFactors;
    have hG_card : G.card ≤ (F.filter (S.min' (primes_Icc_nonempty hN) ∈ ·)).card := by
      apply chvatal_theorem S (primes_Icc_nonempty hN) F;
      · simp +zetaDelta at *;
        exact fun X x hx₁ hx₂ hx₃ hx₄ =>
          hx₄ ▸ primeFactors_subset_primes_Icc
            (Finset.mem_Icc.mpr ⟨hx₁, hx₂⟩);
      · exact hereditary_squarefree_primeFactors N;
      · exact Finset.image_subset_image hB;
      · simp +zetaDelta at *;
        exact fun a ha b hb => by
          obtain ⟨p, hp⟩ :=
            Nat.Prime.not_coprime_iff_dvd.mp (hB_int a ha b hb)
          exact ⟨p, Finset.mem_inter.mpr
            ⟨Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.1, by
              linarith [Finset.mem_Icc.mp
                (Finset.mem_filter.mp (hB ha) |>.1)]⟩,
            Nat.mem_primeFactors.mpr ⟨hp.1, hp.2.2, by
              linarith [Finset.mem_Icc.mp
                (Finset.mem_filter.mp (hB hb) |>.1)]⟩⟩⟩
    convert hG_card using 1;
    · rw [ Finset.card_image_of_injOn ];
      exact fun x hx y hy hxy =>
        eq_of_squarefree_primeFactors_eq
          (Finset.mem_filter.mp (hB hx) |>.2)
          (Finset.mem_filter.mp (hB hy) |>.2) hxy;
    · rw [ show S.min' ( primes_Icc_nonempty hN ) = 2 from min_primes_Icc_eq_two hN ];
      refine' Finset.card_bij ( fun x hx => Nat.primeFactors x ) _ _ _;
      · simp +zetaDelta at *;
        exact fun a ha₁ ha₂ ha₃ ha₄ =>
          ⟨⟨a, ⟨⟨ha₁, ha₂⟩, ha₃⟩, rfl⟩,
            Nat.prime_two, ha₄, by linarith⟩;
      · intro a₁ ha₁ a₂ ha₂ h
        exact eq_of_squarefree_primeFactors_eq
          (Finset.mem_filter.mp ha₁ |>.2.1)
          (Finset.mem_filter.mp ha₂ |>.2.1) h;
      · grind;
  · interval_cases N <;> simp_all +decide [ Finset.subset_iff ];
    · exact Finset.eq_empty_of_forall_notMem hB;
    · induction B using Finset.induction <;> simp_all +decide

/-! ### Main Theorem -/

theorem erdos_sarkozy (N : ℕ) (A : Finset ℕ)
    (hA_sub : A ⊆ Finset.Icc 1 N)
    (hA_prod : ∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) :
    A.card ≤ (erdosSarkozySet N).card := by
  set B := A.filter Squarefree
  set C := A.filter (fun k => ¬ Squarefree k) with hC;
  have hB_card : B.card ≤ ((Finset.Icc 1 N).filter (fun k => Squarefree k ∧ 2 ∣ k)).card := by
    apply chvatal_squarefree N B;
    · exact Finset.filter_subset_filter _ hA_sub;
    · exact fun a ha b hb =>
        not_coprime_of_squarefree_not_squarefree_mul
          (Finset.mem_filter.mp ha |>.2)
          (Finset.mem_filter.mp hb |>.2)
          (hA_prod a (Finset.mem_filter.mp ha |>.1)
            b (Finset.mem_filter.mp hb |>.1));
  have hC_card : C.card ≤ ((Finset.Icc 1 N).filter (fun k => ¬ Squarefree k)).card := by
    exact Finset.card_le_card fun x hx =>
      Finset.mem_filter.mpr
        ⟨hA_sub <| Finset.mem_filter.mp hx |>.1,
          Finset.mem_filter.mp hx |>.2⟩;
  convert Nat.add_le_add hB_card hC_card using 1;
  · rw [ Finset.card_filter_add_card_filter_not ];
  · unfold erdosSarkozySet
    rw [← Finset.card_union_of_disjoint]; congr
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
    exact Finset.disjoint_filter.mpr (by tauto)

end Erdos844

#print axioms Erdos844.erdos_sarkozy
-- 'Erdos844.erdos_sarkozy' depends on axioms: [propext, Classical.choice, Quot.sound]
