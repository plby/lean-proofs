/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Released under Apache 2.0 license.
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star

namespace Erdos540

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedDecidableInType false
set_option linter.style.maxHeartbeats false
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-!
# Erdős Problem 540

**Problem**: Is it true that if `A ⊆ ℤ/Nℤ` has size `≫ N^{1/2}` then there exists some
non-empty `S ⊆ A` such that `∑_{n ∈ S} n ≡ 0 (mod N)`?

**Answer**: YES.

We prove: there exists an absolute constant `C > 0` such that for every positive
integer `N` and every subset `A` of `ℤ/Nℤ` with `|A| ≥ C · √N`, there is a
non-empty subset `S ⊆ A` whose elements sum to zero in `ℤ/Nℤ`.

The proof proceeds in several steps
[Szemerédi, E., On a conjecture of Erdős and Heilbronn. Acta Arith. (1970), 227-229] :
1. A **matrix/pigeonhole argument** (`matrix_argument`) finds a zero-sum subset
   given enough "compatible" additions and removals with controlled sumset growth.
2. A **monotone transition bound** (`monotone_transition_bound`) shows that the
   weighted count of critical transitions for any monotone predicate is ≤ k!.
3. An **averaging argument** (`exists_good_D`) uses the transition bound to find
   a pivot set `D` with enough good additions and removals.
4. Everything is assembled in `erdos_540_generalized` for general finite abelian
   groups, and then specialized to `ℤ/Nℤ` in `erdos_540`.

**Reference**: We follow the proof in
Szemerédi, E., On a conjecture of Erdős and Heilbronn. Acta Arith. (1970), 227-229.
-/

open Finset BigOperators

noncomputable section

/-! ## Basic definitions -/

/-- The set of all non-empty subset sums of a finite set `A`. -/
def subsetSums {G : Type*} [DecidableEq G] [AddCommMonoid G] (A : Finset G) : Finset G :=
  ((A.powerset.filter Finset.Nonempty).image (fun S => S.sum id))

/-- A set `A` has the zero-sum property if some non-empty subset sums to zero. -/
def hasZeroSum {G : Type*} [DecidableEq G] [AddCommMonoid G] (A : Finset G) : Prop :=
  ∃ S : Finset G, S ⊆ A ∧ S.Nonempty ∧ S.sum id = 0

/-! ## Trivial case -/

/-- If `0 ∈ A`, then `A` trivially has a zero-sum subset. -/
lemma hasZeroSum_of_zero_mem {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {A : Finset G} (h : (0 : G) ∈ A) : hasZeroSum A :=
  ⟨{0}, singleton_subset_iff.mpr h, singleton_nonempty _, sum_singleton _ _⟩

/-- Monotonicity of subset sums. -/
lemma subsetSums_mono {G : Type*} [DecidableEq G] [AddCommMonoid G]
    {A B : Finset G} (h : A ⊆ B) : subsetSums A ⊆ subsetSums B := by
  intro x hx
  simp only [subsetSums, mem_image, mem_filter, mem_powerset] at hx ⊢
  obtain ⟨S, ⟨hSA, hSne⟩, rfl⟩ := hx
  exact ⟨S, ⟨hSA.trans h, hSne⟩, rfl⟩

/-! ## The matrix argument (Claim 1)

The core combinatorial argument: given compatible additions and removals
with controlled sumset growth, we find a zero-sum subset. -/

/-- **Matrix argument**: Given a pivot set `D ⊆ A` with enough compatible additions
(elements that can be added with small sumset growth) and removals (elements that can
be removed with small sumset growth), then `A` has a zero-sum subset. -/
theorem matrix_argument {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]
    {A D : Finset G} {adds removes : Finset G}
    (hDA : D ⊆ A)
    (hAddsA : adds ⊆ A)
    (hRemsD : removes ⊆ D)
    (hAddsDisj : Disjoint adds D)
    (_h0A : (0 : G) ∉ A)
    (hAddGrowth : ∀ a ∈ adds,
      (subsetSums (insert a D) \ subsetSums D).card ≤ Nat.sqrt (Fintype.card G))
    (hRemGrowth : ∀ b ∈ removes,
      (subsetSums D \ subsetSums (D.erase b)).card ≤ Nat.sqrt (Fintype.card G))
    (hAddsCard : 3 * Nat.sqrt (Fintype.card G) < adds.card)
    (hRemsCard : 3 * Nat.sqrt (Fintype.card G) < removes.card) :
    hasZeroSum A := by
  obtain ⟨i₀, hi₀⟩ :
      ∃ i₀ ∈ removes,
      Finset.card (Finset.filter
        (fun a => (D.sum id - i₀ + a ∈ subsetSums D)) adds) >
      Nat.sqrt (Fintype.card G) := by
    have h_row_entries :
        ∑ i ∈ removes, Finset.card (Finset.filter
          (fun a => (D.sum id - i + a ∈ subsetSums D)) adds) ≥
        adds.card * (removes.card - Nat.sqrt (Fintype.card G)) := by
      have h_row_entries :
          ∀ a ∈ adds, Finset.card (Finset.filter
            (fun i => (D.sum id - i + a ∈ subsetSums D)) removes) ≥
          removes.card - Nat.sqrt (Fintype.card G) := by
        intro a ha
        have h_add_entries_a :
            Finset.card (Finset.filter
              (fun i => (D.sum id - i + a ∈
                subsetSums (insert a D) \ subsetSums D)) removes) ≤
            Nat.sqrt (Fintype.card G) := by
          refine le_trans ?_ ( hAddGrowth a ha )
          have h_add_entries_a :
              Finset.image (fun i => D.sum id - i + a)
                (Finset.filter
                  (fun i => (D.sum id - i + a ∈
                    subsetSums (insert a D) \ subsetSums D))
                  removes) ⊆
              subsetSums (insert a D) \ subsetSums D := by
            grind +splitImp
          exact le_trans
            (by rw [Finset.card_image_of_injective _
              fun x y hxy => by simpa using hxy])
            (Finset.card_mono h_add_entries_a)
        have h_add_entries_a :
            Finset.card (Finset.filter
              (fun i => (D.sum id - i + a ∈ subsetSums D)) removes) +
            Finset.card (Finset.filter
              (fun i => (D.sum id - i + a ∈
                subsetSums (insert a D) \ subsetSums D)) removes) ≥
            removes.card := by
          rw [← Finset.card_union_of_disjoint]
          · refine Finset.card_le_card ?_
            intro i hi
            by_cases hi' :
                D.sum id - i + a ∈ subsetSums D <;>
              simp_all +decide [Finset.subset_iff]
            refine Finset.mem_image.mpr
              ⟨Finset.erase (insert a D) i,
                ?_, ?_⟩ <;>
              simp_all +decide [Finset.subset_iff]
            · exact ⟨a, Finset.mem_insert_self _ _, by
                obtain ⟨x, hx⟩ :=
                  Finset.card_pos.mp (by
                    linarith [Nat.sqrt_pos.mpr
                      (Fintype.card_pos_iff.mpr ⟨a⟩)] :
                    0 < Finset.card removes)
                exact ⟨x,
                  Finset.mem_insert_of_mem (hRemsD hx),
                  by rintro rfl
                     exact Finset.disjoint_left.mp
                       hAddsDisj ha (hRemsD hx)⟩⟩
            · rw [Finset.sum_insert
                (Finset.disjoint_left.mp hAddsDisj ha),
                add_comm]
              abel1
          · simp +contextual [Finset.disjoint_left]
        exact Nat.sub_le_of_le_add <| by linarith
      have h_row_entries :
          ∑ a ∈ adds, Finset.card (Finset.filter
            (fun i => (D.sum id - i + a ∈ subsetSums D))
            removes) ≥
          adds.card * (removes.card - Nat.sqrt (Fintype.card G)) := by
        exact le_trans (by simp +decide) (Finset.sum_le_sum h_row_entries)
      convert h_row_entries using 1
      simp +decide only [card_filter]
      exact Finset.sum_comm
    contrapose! h_row_entries
    refine lt_of_le_of_lt (Finset.sum_le_sum h_row_entries) ?_
    norm_num
    nlinarith [Nat.sub_add_cancel
      (show Nat.sqrt (Fintype.card G) ≤ #removes from by linarith)]
  obtain ⟨q, hq⟩ :
      ∃ q ∈ Finset.filter
        (fun a => (D.sum id - i₀ + a ∈ subsetSums D)) adds,
      D.sum id - i₀ + q ∈ subsetSums (D.erase i₀) := by
    contrapose! hi₀
    intro hi₀_mem
    have h_filter :
        Finset.image (fun a => D.sum id - i₀ + a)
          (Finset.filter
            (fun a => D.sum id - i₀ + a ∈ subsetSums D) adds) ⊆
        subsetSums D \ subsetSums (D.erase i₀) := by
      grind
    exact le_trans
      (by rw [Finset.card_image_of_injective _
        (add_right_injective _)])
      (le_trans (Finset.card_mono h_filter)
        (hRemGrowth i₀ hi₀_mem))
  obtain ⟨S, hS₁, hS₂⟩ := Finset.mem_image.mp hq.2
  refine ⟨(D.erase i₀ \ S) ∪ {q}, ?_, ?_, ?_⟩ <;>
    simp_all +decide [Finset.subset_iff]
  rw [Finset.sum_insert] <;>
    simp_all +decide [Finset.subset_iff]
  exact fun _ _ =>
    False.elim (Finset.disjoint_left.mp hAddsDisj hq.1.1 ‹_›)

/-! ## Existence of compatible sets -/

/-! ### Double counting in the subset lattice

We prove `monotone_transition_bound` via a telescoping argument.
Define `Y(j) = |{D ∈ A.powersetCard j | P D}|`. By double counting edges in
the inclusion graph between `j`-subsets and `(j+1)`-subsets, we show:

  `T(j) = (j + 1) · Y(j + 1) − (k − j) · Y(j)`

where `T(j)` is the critical transition count at level `j`. Then the weighted sum
telescopes: `∑ j, T(j) · j! · (k−j−1)! = k! · (Y(k) − Y(0)) ≤ k!`. -/

/-- **Double counting**: the total number of pairs `(D, a)` with `D ∈ A.powersetCard j`,
`a ∈ A \ D`, and `P (insert a D)` equals the sum of `E.card` over all `(j+1)`-subsets
`E ⊆ A` satisfying `P`. The bijection maps `(D, a) ↦ (insert a D, a)`. -/
private lemma sum_filter_insert_card {G : Type*} [DecidableEq G]
    {A : Finset G} {j : ℕ} (P : Finset G → Prop) [DecidablePred P] :
    ∑ D ∈ A.powersetCard j,
      ((A \ D).filter fun a => P (insert a D)).card =
    ∑ E ∈ (A.powersetCard (j + 1)).filter P, E.card := by
  simp only [card_filter]
  rw [Finset.sum_sigma']
  have h_bij :
      ∑ D ∈ A.powersetCard j, ∑ y ∈ A \ D, (if P (insert y D) then 1 else 0) =
      ∑ E ∈ A.powersetCard (j + 1), ∑ x ∈ E, (if P E then 1 else 0) := by
    simp only [sum_sigma']
    refine Finset.sum_bij (fun x _ => ⟨insert x.snd x.fst, x.snd⟩) ?_ ?_ ?_ ?_ <;>
      simp +decide
    · exact fun a ha₁ ha₂ ha₃ ha₄ =>
        ⟨Finset.insert_subset ha₃ ha₁, by rw [Finset.card_insert_of_notMem ha₄, ha₂]⟩
    · intro a₁ ha₁ ha₂ ha₃ ha₄ a₂ ha₅ ha₆ ha₇ ha₈ h₁ h₂
      ext <;> simp_all +decide [Finset.ext_iff]
      specialize h₁ ‹_›
      aesop
    · intro b hb₁ hb₂ hb₃
      exact ⟨b.fst.erase b.snd, b.snd, by simp_all +decide [Finset.subset_iff]⟩
  convert h_bij using 1
  · exact sum_sigma (A.powersetCard j) (sdiff A) fun x =>
      if P (insert x.snd x.fst) then 1 else 0
  · simp [Finset.sum_ite]

/-- For **monotone** `P`, the transition count at level `j` (cast to `ℤ`) equals
`(j + 1) * Y(j + 1) − (A.card − j) * Y(j)`, where `Y(m)` is the number of
`m`-element subsets of `A` on which `P` holds. -/
private lemma transition_count_int {G : Type*} [DecidableEq G]
    {A : Finset G} {j : ℕ} (hj : j < A.card)
    (P : Finset G → Prop) [DecidablePred P]
    (hP_mono : ∀ S T : Finset G, S ⊆ T → T ⊆ A → P S → P T) :
    (∑ D ∈ A.powersetCard j,
        ((A \ D).filter fun a => ¬P D ∧ P (insert a D)).card : ℤ) =
      (j + 1) * ((A.powersetCard (j + 1)).filter P).card -
      (A.card - (j : ℤ)) * ((A.powersetCard j).filter P).card := by
  -- Split: the ¬P(D) ∧ P(insert a D) count = total P(insert a D) count minus the P(D) part.
  have h_split :
      ∑ D ∈ A.powersetCard j, ((A \ D).filter fun a => ¬P D ∧ P (insert a D)).card =
      ∑ D ∈ A.powersetCard j, ((A \ D).filter fun a => P (insert a D)).card -
      ∑ D ∈ (A.powersetCard j).filter P,
        ((A \ D).filter fun a => P (insert a D)).card := by
    refine eq_tsub_of_add_eq ?_
    rw [Finset.sum_filter, add_comm, ← Finset.sum_add_distrib]
    congr with D
    aesop
  -- When P(D) holds, monotonicity gives P(insert a D) for all a, so the filter is full.
  have h_mono_filter :
      ∑ D ∈ (A.powersetCard j).filter P,
        ((A \ D).filter fun a => P (insert a D)).card =
      ∑ D ∈ (A.powersetCard j).filter P, (A.card - j) := by
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [Finset.filter_true_of_mem] <;> grind
  -- By double counting, the total insert-satisfying count = (j+1) * Y(j+1).
  have h_double_count :
      ∑ D ∈ A.powersetCard j, ((A \ D).filter fun a => P (insert a D)).card =
      (j + 1) * ((A.powersetCard (j + 1)).filter P).card := by
    convert sum_filter_insert_card P using 1
    rw [Finset.sum_congr rfl fun x hx =>
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hx |>.1)).2]
    simp [mul_comm]
  simp_all
  rw [← Nat.cast_sum, h_split, Nat.cast_sub]
  · simp [mul_comm, Nat.cast_sub hj.le]
  · rw [← h_double_count, ← h_mono_filter]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Key averaging inequality**: For any monotone decidable predicate on subsets of `A`,
the weighted count of "critical transitions" is at most `k!`.

A critical transition at level `j` is a pair `(D, a)` where `D ⊆ A` has `j` elements,
`a ∈ A \ D`, `¬P(D)`, and `P(D ∪ {a})`. Each such pair is weighted by `j! · (k-j-1)!`.

The proof uses double counting in the subset lattice: the transition count at level `j`
equals `(j+1) · Y(j+1) − (k−j) · Y(j)`, where `Y(m)` counts `m`-subsets satisfying `P`.
Multiplying by `j! · (k−j−1)!` gives a telescoping sum equal to `k! · (Y(k) − Y(0)) ≤ k!`.
-/
lemma monotone_transition_bound {G : Type*} [DecidableEq G]
    {A : Finset G} (P : Finset G → Prop) [DecidablePred P]
    (hP_mono : ∀ S T : Finset G, S ⊆ T → T ⊆ A → P S → P T) :
    ∑ j ∈ Finset.range A.card,
      (∑ D ∈ A.powersetCard j,
        ((A \ D).filter fun a => ¬P D ∧ P (insert a D)).card) *
      j.factorial * (A.card - j - 1).factorial ≤
    A.card.factorial := by
  set Y := fun m : ℕ => ((A.powersetCard m).filter P).card
  -- The weighted sum telescopes via f(m) = Y(m) · m! · (k - m)!.
  have h_telescope :
      ∑ j ∈ Finset.range A.card,
        ((j + 1) * Y (j + 1) - (A.card - j) * Y j : ℤ) *
        j.factorial * (A.card - j - 1).factorial =
      A.card.factorial * (Y A.card - Y 0) := by
    convert Finset.sum_range_sub
      (fun j => (Y j : ℤ) * j.factorial * (A.card - j).factorial) A.card using 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [show A.card - i = (A.card - (i + 1)) + 1 by
        rw [tsub_add_eq_add_tsub (by linarith [Finset.mem_range.mp hi])]; simp]
      push_cast [Nat.factorial_succ]; ring_nf
      rw [Nat.cast_sub (by linarith [Finset.mem_range.mp hi])]
      push_cast; ring
    · simp [mul_comm]; ring
  -- Y(k) ≤ 1 (at most one k-subset of A), so k! · (Y(k) - Y(0)) ≤ k!.
  have hY_le : Y A.card ≤ 1 :=
    le_trans (Finset.card_filter_le _ _)
      (by simp)
  have h_bound : (A.card.factorial : ℤ) * (Y A.card - Y 0) ≤ A.card.factorial := by
    have : (Y A.card : ℤ) ≤ 1 := by exact_mod_cast hY_le
    have : (0 : ℤ) ≤ Y 0 := Nat.cast_nonneg _
    nlinarith [Nat.factorial_pos A.card]
  -- Rewrite each term using transition_count_int.
  have h_eq :
      ∑ j ∈ Finset.range A.card,
        ((j + 1) * Y (j + 1) - (A.card - j) * Y j : ℤ) *
        j.factorial * (A.card - j - 1).factorial =
      ∑ j ∈ Finset.range A.card,
        ((∑ D ∈ A.powersetCard j,
          ((A \ D).filter fun a => ¬P D ∧ P (insert a D)).card : ℕ)) *
        j.factorial * (A.card - j - 1).factorial := by
    push_cast
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← transition_count_int (Finset.mem_range.mp hj) P hP_mono]
  zify at *
  rcases le_total (Y A.card) (Y 0) with h | h <;> simp_all


/-- The weighted sum of growth across all levels is at most `|G| · k!`. -/
lemma weighted_growth_sum_le {G : Type*} [DecidableEq G]
    [AddCommGroup G] [Fintype G] (A : Finset G) :
    ∑ j ∈ Finset.range A.card,
      (∑ D ∈ A.powersetCard j,
        ∑ a ∈ A \ D,
          (subsetSums (insert a D) \ subsetSums D).card
      ) * j.factorial * (A.card - j - 1).factorial
    ≤ Fintype.card G * A.card.factorial := by
  have h_bound : ∀ g : G,
      ∑ j ∈ Finset.range A.card,
        (∑ D ∈ A.powersetCard j,
          ((A \ D).filter fun a =>
            g ∉ subsetSums D ∧ g ∈ subsetSums (insert a D)).card
        ) * j.factorial * (A.card - j - 1).factorial ≤
        A.card.factorial := by
    intros g
    apply monotone_transition_bound
    exact fun S T hST _ hg => subsetSums_mono hST hg
  have h_sum_bound :
      ∑ g : G, ∑ j ∈ Finset.range A.card,
        (∑ D ∈ A.powersetCard j,
          ((A \ D).filter fun a =>
            g ∉ subsetSums D ∧ g ∈ subsetSums (insert a D)).card
        ) * j.factorial * (A.card - j - 1).factorial ≤
        Fintype.card G * A.card.factorial :=
    le_trans (Finset.sum_le_sum fun _ _ => h_bound _) (by simp +decide)
  convert h_sum_bound using 1
  rw [Finset.sum_comm, Finset.sum_congr rfl]
  simp +decide only [card_eq_sum_ones, sum_sigma', sum_mul _ _ _]
  intro j hj
  refine Finset.sum_bij (fun x _ => ⟨x.2.2, x.1, x.2.1⟩) ?_ ?_ ?_ ?_ <;> aesop

/-! ## Helper lemmas for the averaging argument -/

/-- Finset Markov inequality: for a function `f` on a finset, the number of elements
where `f` exceeds a threshold `t` is at most `(∑ f) / (t + 1)`. -/
lemma finset_markov_card_le {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (t : ℕ) :
    (t + 1) * (S.filter fun x => t < f x).card ≤ ∑ x ∈ S, f x := by
  rw [Finset.card_filter, mul_comm]
  rw [Finset.sum_mul _ _ _]
  exact Finset.sum_le_sum fun x _ => by split_ifs <;> linarith

/-- At each level, the Markov bound relates bad additions to total growth. -/
lemma bad_add_le_growth {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]
    (A D : Finset G) :
    (Nat.sqrt (Fintype.card G) + 1) *
      ((A \ D).filter fun a =>
        Nat.sqrt (Fintype.card G) <
          (subsetSums (insert a D) \ subsetSums D).card).card
    ≤ ∑ a ∈ A \ D, (subsetSums (insert a D) \ subsetSums D).card :=
  finset_markov_card_le (A \ D)
    (fun a => (subsetSums (insert a D) \ subsetSums D).card) _

/-- The weighted sum of bad additions is bounded. -/
lemma weighted_bad_markov {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]
    (A : Finset G) :
    (Nat.sqrt (Fintype.card G) + 1) *
      ∑ j ∈ Finset.range A.card,
        (∑ D ∈ A.powersetCard j,
          ((A \ D).filter fun a =>
            Nat.sqrt (Fintype.card G) <
              (subsetSums (insert a D) \ subsetSums D).card).card
        ) * j.factorial * (A.card - j - 1).factorial
    ≤ Fintype.card G * A.card.factorial := by
  have hBad :
      ∀ D ∈ Finset.powerset A,
      (Nat.sqrt (Fintype.card G) + 1) *
        ((A \ D).filter fun a =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums (insert a D) \ subsetSums D).card).card ≤
        ∑ a ∈ A \ D, (subsetSums (insert a D) \ subsetSums D).card :=
    fun D _ => bad_add_le_growth A D
  have hSum :
      (Nat.sqrt (Fintype.card G) + 1) *
        ∑ j ∈ Finset.range A.card,
          (∑ D ∈ A.powersetCard j,
            ((A \ D).filter fun a =>
              Nat.sqrt (Fintype.card G) <
                (subsetSums (insert a D) \ subsetSums D).card).card
          ) * j.factorial * (A.card - j - 1).factorial ≤
        ∑ j ∈ Finset.range A.card,
          (∑ D ∈ A.powersetCard j,
            ∑ a ∈ A \ D,
              (subsetSums (insert a D) \ subsetSums D).card
          ) * j.factorial * (A.card - j - 1).factorial := by
    rw [Finset.mul_sum _ _ _]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul]
        using mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum fun D hD =>
            hBad D <| Finset.mem_powerset.mpr <|
              Finset.mem_powersetCard.mp hD |>.1)
          <| mul_nonneg (Nat.cast_nonneg _) <| Nat.cast_nonneg _
  exact hSum.trans (weighted_growth_sum_le A)

/-- The bijection: total bad removals at level `j+1` equals total bad additions at
level `j`. -/
lemma bad_rem_sum_eq {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]
    (A : Finset G) (j : ℕ) :
    ∑ D ∈ A.powersetCard (j + 1),
      (D.filter fun b =>
        Nat.sqrt (Fintype.card G) <
          (subsetSums D \ subsetSums (D.erase b)).card).card
    = ∑ D ∈ A.powersetCard j,
      ((A \ D).filter fun a =>
        Nat.sqrt (Fintype.card G) <
          (subsetSums (insert a D) \ subsetSums D).card).card := by
  simp +decide only [card_filter]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij (fun x _ => ⟨x.1.erase x.2, x.2⟩)
  · simp +contextual [Finset.mem_powersetCard, Finset.subset_iff]
  · simp +contextual
    grind +suggestions
  · simp +decide [Finset.subset_iff]
    exact fun b hb₁ hb₂ hb₃ hb₄ =>
      ⟨Insert.insert b.snd b.fst, b.snd,
        ⟨⟨fun x hx => by aesop,
          by rw [Finset.card_insert_of_notMem hb₄, hb₂]⟩,
          by aesop⟩,
        by aesop⟩
  · simp +contextual [Finset.subset_iff]

/-- Key arithmetic: `7n ≤ 49 · √n · (√n + 1)`. -/
lemma seven_n_le_49_sqrt (n : ℕ) :
    7 * n ≤ 49 * Nat.sqrt n * (Nat.sqrt n + 1) := by
  nlinarith [Nat.lt_succ_sqrt n]

set_option maxHeartbeats 400000 in
/-- At a good level, the Markov + union bound finds a `D` good for both additions and
removals. -/
lemma exists_D_at_level {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]
    {A : Finset G} {j : ℕ}
    (hjA : j ≤ A.card)
    (hj_low : 7 * Nat.sqrt (Fintype.card G) ≤ j)
    (hkj_low : 7 * Nat.sqrt (Fintype.card G) ≤ A.card - j)
    (h_add_bound :
      ∑ D ∈ A.powersetCard j,
        ((A \ D).filter fun a =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums (insert a D) \ subsetSums D).card).card
      ≤ (A.card - j) * Nat.choose A.card j / 7)
    (h_rem_bound :
      ∑ D ∈ A.powersetCard j,
        (D.filter fun b =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums D \ subsetSums (D.erase b)).card).card
      ≤ j * Nat.choose A.card j / 7) :
    ∃ D ⊆ A,
      (3 * Nat.sqrt (Fintype.card G) <
        ((A \ D).filter fun a =>
          (subsetSums (insert a D) \ subsetSums D).card ≤
            Nat.sqrt (Fintype.card G)).card) ∧
      (3 * Nat.sqrt (Fintype.card G) <
        (D.filter fun b =>
          (subsetSums D \ subsetSums (D.erase b)).card ≤
            Nat.sqrt (Fintype.card G)).card) := by
  by_contra h_contra
  have h_bad_add_rem :
      ∀ D ∈ Finset.powersetCard j A,
      ((A \ D).filter fun a =>
        Nat.sqrt (Fintype.card G) <
          (subsetSums (insert a D) \ subsetSums D).card).card ≥
        #A - j - 3 * Nat.sqrt (Fintype.card G) ∨
      (D.filter fun b =>
        Nat.sqrt (Fintype.card G) <
          (subsetSums D \ subsetSums (D.erase b)).card).card ≥
        j - 3 * Nat.sqrt (Fintype.card G) := by
    intro D hD
    contrapose! h_contra
    refine ⟨D, Finset.mem_powersetCard.mp hD |>.1, ?_, ?_⟩ <;>
      simp_all +decide [Finset.card_sdiff]
    · rw [show (Finset.filter (fun a =>
          #(subsetSums (insert a D)) ≤
            (Fintype.card G).sqrt +
              #(subsetSums D ∩ subsetSums (insert a D)))
          (A \ D)) =
        (A \ D) \ (Finset.filter (fun a =>
          (Fintype.card G).sqrt <
            #(subsetSums (insert a D)) -
              #(subsetSums D ∩ subsetSums (insert a D)))
          (A \ D)) from ?_]
      · grind
      · grind +splitIndPred
    · rw [show (Finset.filter (fun b =>
          #(subsetSums D) ≤
            (Fintype.card G).sqrt +
              #(subsetSums (D.erase b) ∩ subsetSums D)) D) =
        D \ (Finset.filter (fun b =>
          (Fintype.card G).sqrt <
            #(subsetSums D) -
              #(subsetSums (D.erase b) ∩ subsetSums D)) D) from ?_]
      · grind
      · grind
  have h_total_bad :
      (∑ D ∈ Finset.powersetCard j A,
        ((A \ D).filter fun a =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums (insert a D) \ subsetSums D).card).card *
          (j - 3 * Nat.sqrt (Fintype.card G)) +
      ∑ D ∈ Finset.powersetCard j A,
        (D.filter fun b =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums D \ subsetSums (D.erase b)).card).card *
          (#A - j - 3 * Nat.sqrt (Fintype.card G))) ≤
      ((#A - j) * (Nat.choose A.card j) / 7) *
        (j - 3 * Nat.sqrt (Fintype.card G)) +
      (j * (Nat.choose A.card j) / 7) *
        (#A - j - 3 * Nat.sqrt (Fintype.card G)) :=
    add_le_add
      (by simpa only [Finset.sum_mul _ _ _]
        using Nat.mul_le_mul_right _ h_add_bound)
      (by simpa only [Finset.sum_mul _ _ _]
        using Nat.mul_le_mul_right _ h_rem_bound)
  have h_total_bad_ge :
      (∑ D ∈ Finset.powersetCard j A,
        ((A \ D).filter fun a =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums (insert a D) \ subsetSums D).card).card *
          (j - 3 * Nat.sqrt (Fintype.card G)) +
      ∑ D ∈ Finset.powersetCard j A,
        (D.filter fun b =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums D \ subsetSums (D.erase b)).card).card *
          (#A - j - 3 * Nat.sqrt (Fintype.card G))) ≥
      (Nat.choose A.card j) *
        ((j - 3 * Nat.sqrt (Fintype.card G)) *
          (#A - j - 3 * Nat.sqrt (Fintype.card G))) := by
    have h_total_bad_ge :
        ∀ D ∈ Finset.powersetCard j A,
        ((A \ D).filter fun a =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums (insert a D) \ subsetSums D).card).card *
          (j - 3 * Nat.sqrt (Fintype.card G)) +
        (D.filter fun b =>
          Nat.sqrt (Fintype.card G) <
            (subsetSums D \ subsetSums (D.erase b)).card).card *
          (#A - j - 3 * Nat.sqrt (Fintype.card G)) ≥
        (j - 3 * Nat.sqrt (Fintype.card G)) *
          (#A - j - 3 * Nat.sqrt (Fintype.card G)) := by
      intro D hD
      specialize h_bad_add_rem D hD
      rcases h_bad_add_rem with h | h <;>
        nlinarith [
          Nat.zero_le (j - 3 * Nat.sqrt (Fintype.card G)),
          Nat.zero_le (#A - j - 3 * Nat.sqrt (Fintype.card G))]
    simpa [Finset.sum_add_distrib] using Finset.sum_le_sum h_total_bad_ge
  have h_contradiction :
      (j - 3 * Nat.sqrt (Fintype.card G)) *
        (#A - j - 3 * Nat.sqrt (Fintype.card G)) >
      ((#A - j) * (j - 3 * Nat.sqrt (Fintype.card G)) +
        j * (#A - j - 3 * Nat.sqrt (Fintype.card G))) / 7 := by
    rw [gt_iff_lt, Nat.div_lt_iff_lt_mul] <;> norm_num
    zify at *
    rw [Nat.cast_sub, Nat.cast_sub, Nat.cast_sub] <;>
      push_cast <;> repeat linarith
    rw [Nat.cast_sub] at * <;> try linarith
    nlinarith only [hj_low, hkj_low,
      show (Nat.sqrt (Fintype.card G) : ℤ) > 0 from
        Nat.cast_pos.mpr
          (Nat.sqrt_pos.mpr (Fintype.card_pos_iff.mpr ⟨0⟩))]
  contrapose! h_contradiction
  rw [Nat.le_div_iff_mul_le] <;> norm_num
  nlinarith [
    Nat.div_mul_le_self ((#A - j) * Nat.choose #A j) 7,
    Nat.div_mul_le_self (j * Nat.choose #A j) 7,
    Nat.choose_pos hjA]

set_option maxHeartbeats 400000 in
/-- **Existence of good D**: There exists `D ⊆ A` with many good additions
and removals. -/
lemma exists_good_D {G : Type*} [DecidableEq G] [AddCommGroup G] [Fintype G]
    {A : Finset G}
    (hAcard : 100 * Nat.sqrt (Fintype.card G) ≤ A.card)
    (hAlt : A.card < Fintype.card G) :
    ∃ D ⊆ A,
      (3 * Nat.sqrt (Fintype.card G) <
        ((A \ D).filter fun a =>
          (subsetSums (insert a D) \ subsetSums D).card ≤
            Nat.sqrt (Fintype.card G)).card) ∧
      (3 * Nat.sqrt (Fintype.card G) <
        (D.filter fun b =>
          (subsetSums D \ subsetSums (D.erase b)).card ≤
            Nat.sqrt (Fintype.card G)).card) := by
  set s := Nat.sqrt (Fintype.card G)
  set k := A.card
  set n := Fintype.card G
  obtain ⟨j, hj⟩ :
      ∃ j ∈ Finset.Icc (26 * s + 1) (75 * s),
      (∑ D ∈ A.powersetCard j,
        ((A \ D).filter fun a =>
          Nat.sqrt n <
            (subsetSums (insert a D) \ subsetSums D).card).card
      ) * Nat.factorial j * Nat.factorial (k - j - 1) ≤
        Nat.factorial k / 7 ∧
      (∑ D ∈ A.powersetCard (j - 1),
        ((A \ D).filter fun a =>
          Nat.sqrt n <
            (subsetSums (insert a D) \ subsetSums D).card).card
      ) * Nat.factorial (j - 1) *
        Nat.factorial (k - (j - 1) - 1) ≤
        Nat.factorial k / 7 := by
    have h_pigeonhole :
        Finset.card (Finset.filter (fun j =>
          (∑ D ∈ A.powersetCard j,
            ((A \ D).filter fun a =>
              Nat.sqrt n <
                (subsetSums (insert a D) \ subsetSums D).card).card
          ) * Nat.factorial j * Nat.factorial (k - j - 1) >
            Nat.factorial k / 7) (Finset.range k)) ≤
        7 * n / (s + 1) := by
      have h_pigeonhole :
          (∑ j ∈ Finset.range k,
            (∑ D ∈ A.powersetCard j,
              ((A \ D).filter fun a =>
                Nat.sqrt n <
                  (subsetSums (insert a D) \ subsetSums D).card).card
            ) * Nat.factorial j * Nat.factorial (k - j - 1)) ≤
            n * Nat.factorial k / (s + 1) := by
        have := @weighted_bad_markov G
        exact Nat.le_div_iff_mul_le (Nat.succ_pos _) |>.2
          (by linarith [this A])
      have h_pigeonhole :
          (∑ j ∈ Finset.filter (fun j =>
              (∑ D ∈ A.powersetCard j,
                ((A \ D).filter fun a =>
                  Nat.sqrt n <
                    (subsetSums (insert a D) \
                      subsetSums D).card).card
              ) * Nat.factorial j *
                Nat.factorial (k - j - 1) >
                Nat.factorial k / 7) (Finset.range k),
            Nat.factorial k / 7) ≤
            n * Nat.factorial k / (s + 1) := by
        refine le_trans ?_ h_pigeonhole
        rw [Finset.sum_filter]
        exact Finset.sum_le_sum fun i _ => by
          split_ifs
          · exact le_of_lt ‹_›
          · exact Nat.zero_le _
      rw [Nat.le_div_iff_mul_le] at * <;> norm_num at *
      nlinarith [ Nat.div_mul_cancel ( show 7 ∣ k.factorial from Nat.dvd_factorial ( by decide ) ( by linarith [ Nat.sqrt_pos.mpr ( show 0 < Fintype.card G from Fintype.card_pos ) ] ) ), Nat.factorial_pos k ]
    have h_pigeonhole_shifted :
        Finset.card (Finset.filter (fun j =>
          (∑ D ∈ A.powersetCard (j - 1),
            ((A \ D).filter fun a =>
              Nat.sqrt n <
                (subsetSums (insert a D) \ subsetSums D).card).card
          ) * Nat.factorial (j - 1) *
            Nat.factorial (k - (j - 1) - 1) >
            Nat.factorial k / 7)
          (Finset.Icc (26 * s + 1) (75 * s))) ≤
        7 * n / (s + 1) := by
      refine le_trans ?_ h_pigeonhole
      rw [Finset.card_filter, Finset.card_filter]
      erw [Finset.sum_Ico_eq_sum_range]
      simp +zetaDelta at *
      let l := 26 * ( Fintype.card G ).sqrt
      apply le_trans ( b := ((( Finset.range (75 * ( Fintype.card G ).sqrt - l)).filter
        (fun x => (#A).factorial / 7 < (∑ x ∈ A.powersetCard (l+x), #({ a ∈ A \ x | (Fintype.card G).sqrt < #(subsetSums (insert a x) \ subsetSums x)})) * (l + x).factorial * (#A - (l+x) - 1).factorial)).image (fun x => l+x)).card)
      · rw [Finset.card_image_of_injective _
          fun x y hxy => by simpa using hxy]
      · apply Finset.card_mono
        simp only [le_eq_subset]
        grind
    have h_pigeonhole_combined :
        Finset.card (Finset.filter (fun j =>
          (∑ D ∈ A.powersetCard j,
            ((A \ D).filter fun a =>
              Nat.sqrt n <
                (subsetSums (insert a D) \
                  subsetSums D).card).card
          ) * Nat.factorial j *
            Nat.factorial (k - j - 1) >
            Nat.factorial k / 7 ∨
          (∑ D ∈ A.powersetCard (j - 1),
            ((A \ D).filter fun a =>
              Nat.sqrt n <
                (subsetSums (insert a D) \
                  subsetSums D).card).card
          ) * Nat.factorial (j - 1) *
            Nat.factorial (k - (j - 1) - 1) >
            Nat.factorial k / 7)
          (Finset.Icc (26 * s + 1) (75 * s))) ≤
        2 * (7 * n / (s + 1)) := by
      have h_pigeonhole_combined :
          Finset.card (Finset.filter (fun j =>
            (∑ D ∈ A.powersetCard j,
              ((A \ D).filter fun a =>
                Nat.sqrt n <
                  (subsetSums (insert a D) \
                    subsetSums D).card).card
            ) * Nat.factorial j *
              Nat.factorial (k - j - 1) >
              Nat.factorial k / 7)
            (Finset.Icc (26 * s + 1) (75 * s))) ≤
          7 * n / (s + 1) := by
        refine le_trans ?_ h_pigeonhole
        refine Finset.card_mono ?_
        simp +contextual [Finset.subset_iff]
        grind +splitImp
      rw [Finset.filter_or]
      grind +qlia
    contrapose! h_pigeonhole_combined
    rw [Finset.filter_true_of_mem fun j hj =>
      Classical.or_iff_not_imp_left.2 fun h =>
        h_pigeonhole_combined j hj <| le_of_not_gt h]
    norm_num
    rw [Nat.lt_iff_add_one_le, Nat.le_sub_iff_add_le] <;>
      nlinarith only [Nat.lt_succ_sqrt n,
        Nat.div_mul_le_self (7 * n) (s + 1), hAlt, hAcard]
  have h_bad_add_bound :
      (∑ D ∈ A.powersetCard j,
        ((A \ D).filter fun a =>
          Nat.sqrt n <
            (subsetSums (insert a D) \ subsetSums D).card).card) ≤
        (k - j) * Nat.choose k j / 7 ∧
      (∑ D ∈ A.powersetCard (j - 1),
        ((A \ D).filter fun a =>
          Nat.sqrt n <
            (subsetSums (insert a D) \ subsetSums D).card).card) ≤
        (k - (j - 1)) * Nat.choose k (j - 1) / 7 := by
    constructor <;> rw [Nat.le_div_iff_mul_le] <;> norm_num
    · rw [Nat.le_div_iff_mul_le] at hj <;> norm_num at *
      rw [← Nat.choose_mul_factorial_mul_factorial
        (show j ≤ k from by linarith)] at *
      rcases x : k - j with _ | _ | k <;>
        simp_all +decide [Nat.factorial_succ, mul_assoc]
      · grind +splitImp
      · nlinarith [Nat.factorial_pos j]
      · nlinarith [show 0 < j.factorial * (k + 1) * k.factorial
          by positivity]
    · rw [Nat.le_div_iff_mul_le] at hj <;> norm_num at *
      rw [Nat.le_div_iff_mul_le] at hj <;> norm_num at *
      rw [← Nat.choose_mul_factorial_mul_factorial
        (show j - 1 ≤ k from ?_)] at *
      · rcases j with _ | j <;>
          simp_all +decide [Nat.factorial_succ,
            mul_assoc, mul_comm, mul_left_comm]
        rw [show k - j = (k - j - 1) + 1 by
          rw [Nat.sub_add_cancel
            (Nat.sub_pos_of_lt (by linarith))]] at *
        simp_all +decide [Nat.factorial_succ, mul_comm]
        nlinarith [show 0 < j.factorial * (k - j - 1).factorial by exact mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)]
      · omega
  have h_bad_rem_bound :
      (∑ D ∈ A.powersetCard j,
        (D.filter fun b =>
          Nat.sqrt n <
            (subsetSums D \ subsetSums (D.erase b)).card).card) ≤
        j * Nat.choose k j / 7 := by
    have h_bad_rem_bound :
        (∑ D ∈ A.powersetCard j,
          (D.filter fun b =>
            Nat.sqrt n <
              (subsetSums D \ subsetSums (D.erase b)).card).card) =
        (∑ D ∈ A.powersetCard (j - 1),
          ((A \ D).filter fun a =>
            Nat.sqrt n <
              (subsetSums (insert a D) \ subsetSums D).card).card) := by
      rcases j with _ | j <;> simp_all +decide
      convert bad_rem_sum_eq A j using 1
    rcases j with _ | j <;> simp_all +decide [mul_assoc]
    rw [Nat.mul_comm, Nat.choose_succ_right_eq] at *
    simpa only [mul_comm] using h_bad_add_bound.2
  apply exists_D_at_level
  any_goals exact j
  · linarith [Finset.mem_Icc.mp hj.1]
  · grind
  · grind
  · exact h_bad_add_bound.1
  · exact h_bad_rem_bound

/-- **Existence of compatible sets**: assembles the matrix argument inputs. -/
theorem exists_compatible_sets {G : Type*} [DecidableEq G]
    [AddCommGroup G] [Fintype G] {A : Finset G}
    (hAcard : 100 * Nat.sqrt (Fintype.card G) ≤ A.card)
    (hAlt : A.card < Fintype.card G) :
    ∃ D adds removes : Finset G,
      D ⊆ A ∧ adds ⊆ A ∧ removes ⊆ D ∧ Disjoint adds D ∧
      (∀ a ∈ adds,
        (subsetSums (insert a D) \ subsetSums D).card ≤
          Nat.sqrt (Fintype.card G)) ∧
      (∀ b ∈ removes,
        (subsetSums D \ subsetSums (D.erase b)).card ≤
          Nat.sqrt (Fintype.card G)) ∧
      3 * Nat.sqrt (Fintype.card G) < adds.card ∧
      3 * Nat.sqrt (Fintype.card G) < removes.card := by
  obtain ⟨D, hDA, hAdds, hRems⟩ := exists_good_D hAcard hAlt
  refine ⟨D,
    (A \ D).filter fun a =>
      (subsetSums (insert a D) \ subsetSums D).card ≤
        Nat.sqrt (Fintype.card G),
    D.filter fun b =>
      (subsetSums D \ subsetSums (D.erase b)).card ≤
        Nat.sqrt (Fintype.card G),
    hDA, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _ |>.trans Finset.sdiff_subset
  · exact Finset.filter_subset _ _
  · exact Finset.disjoint_of_subset_left
      (Finset.filter_subset _ _) Finset.sdiff_disjoint
  · intro a ha; exact (Finset.mem_filter.mp ha).2
  · intro b hb; exact (Finset.mem_filter.mp hb).2
  · exact hAdds
  · exact hRems

/-! ## Generalized theorem for finite abelian groups -/

/-- **Erdős 540 (generalized)**: In any finite abelian group `G`, if `A ⊆ G` satisfies
`0 ∉ A`, `|A| ≥ 100√|G|`, and `|A| < |G|`, then `A` has a non-empty zero-sum subset. -/
theorem erdos_540_generalized {G : Type*} [DecidableEq G]
    [AddCommGroup G] [Fintype G] {A : Finset G}
    (h0A : (0 : G) ∉ A)
    (hAcard : 100 * Nat.sqrt (Fintype.card G) ≤ A.card)
    (hAlt : A.card < Fintype.card G) :
    hasZeroSum A := by
  obtain ⟨D, adds, removes, hDA, hAddsA, hRemsD, hDisj,
    hAddG, hRemG, hAddC, hRemC⟩ :=
    exists_compatible_sets hAcard hAlt
  exact matrix_argument hDA hAddsA hRemsD hDisj h0A
    hAddG hRemG hAddC hRemC

/-! ## Main theorem for `ℤ/Nℤ` -/

/-- For `N` small enough relative to `C`, the condition `C√N ≤ |A|` forces
`|A| ≥ N`, making the theorem trivial. -/
lemma erdos_540_small_N (N : ℕ) (hN : 0 < N)
    (A : Finset (ZMod N)) (hA : (N : ℝ) ≤ ↑A.card) :
    hasZeroSum A := by
  have hNZ : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
  have hAuniv : A = Finset.univ := by
    rw [eq_univ_iff_forall]
    intro x
    by_contra hx
    have h1 : A.card < Fintype.card (ZMod N) := by
      calc A.card < (insert x A).card := by simp [hx]
        _ ≤ Fintype.card (ZMod N) := Finset.card_le_univ _
    rw [ZMod.card] at h1
    have h2 : N ≤ A.card := by exact_mod_cast hA
    omega
  exact hasZeroSum_of_zero_mem (hAuniv ▸ Finset.mem_univ 0)

/-- **Erdős Problem 540**: There exists a constant `C > 0` such that for every positive
integer `N`, any subset of `ℤ/Nℤ` of cardinality at least `C√N` contains a non-empty
subset summing to zero. -/
theorem erdos_540 : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (_ : 0 < N) (A : Finset (ZMod N)),
    C * Real.sqrt N ≤ ↑A.card →
    hasZeroSum A := by
  refine ⟨10000, by positivity, fun N hN A hA => ?_⟩
  by_cases h0 : (0 : ZMod N) ∈ A
  · exact hasZeroSum_of_zero_mem h0
  · by_cases hAN : (N : ℝ) ≤ ↑A.card
    · exact erdos_540_small_N N hN A hAN
    · simp only [not_le] at hAN
      have hNZ : NeZero N := ⟨Nat.pos_iff_ne_zero.mp hN⟩
      have hAcard :
          100 * Nat.sqrt (Fintype.card (ZMod N)) ≤ A.card := by
        rw [ZMod.card]
        have h1 : (10000 : ℝ) * Real.sqrt N ≤ ↑A.card := hA
        have hns : (Nat.sqrt N : ℝ) ≤ Real.sqrt N := by
          rw [show (Nat.sqrt N : ℝ) =
            Real.sqrt ((Nat.sqrt N : ℝ) ^ 2) from by
              rw [Real.sqrt_sq (Nat.cast_nonneg _)]]
          apply Real.sqrt_le_sqrt
          have : (Nat.sqrt N : ℝ) ^ 2 =
              (Nat.sqrt N : ℝ) * (Nat.sqrt N : ℝ) := sq _
          rw [this]
          exact_mod_cast Nat.sqrt_le N
        have h2 : (100 : ℝ) * Nat.sqrt N ≤
            (10000 : ℝ) * Real.sqrt N := calc
          (100 : ℝ) * Nat.sqrt N ≤
              100 * Real.sqrt N := by
            apply mul_le_mul_of_nonneg_left hns (by positivity)
          _ ≤ 10000 * Real.sqrt N := by
            apply mul_le_mul_of_nonneg_right (by norm_num)
              (Real.sqrt_nonneg _)
        have h3 : (100 * Nat.sqrt N : ℝ) ≤ ↑A.card :=
          le_trans h2 h1
        exact_mod_cast h3
      have hAlt : A.card < Fintype.card (ZMod N) := by
        rw [ZMod.card]
        exact_mod_cast hAN
      exact erdos_540_generalized h0 hAcard hAlt

#print axioms erdos_540
-- 'Erdos540.erdos_540' depends on axioms: [propext, Classical.choice, Quot.sound]

end

end Erdos540
