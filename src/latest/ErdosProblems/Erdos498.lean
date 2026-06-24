/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 498.
https://www.erdosproblems.com/forum/thread/498

Informal authors:
- Daniel J. Kleitman

Formal authors:
- Gemini Flash
- Gemini Pro
- Claude Opus
- Aristotle
- JoshuaB

URLs:
- https://www.erdosproblems.com/forum/thread/498#post-3844
-/
/-
This file was edited by Aristotle.

This project request had uuid: e07f279d-17a1-4ca1-89e7-6994f503a77e

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle (and also everything which I wrote "by Aristotle" or similar):

- lemma chain_extension_is_chain {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
    (hC : IsChain (· ⊆ ·) (C : Set (Finset α))) :
    ∀ C' ∈ chain_extension C, IsChain (· ⊆ ·) (C' : Set (Finset (Option α)))

- lemma chain_extension_is_symmetric {α : Type*} [Fintype α] {C : Finset (Finset α)}
    (hS : IsSymmetricChain C) :
    ∀ C' ∈ chain_extension C, IsSymmetricChain C'

- lemma chain_extension_disjoint {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
    (C1 C2 : Finset (Finset (Option α))) (h1 : C1 ∈ chain_extension C)
    (h2 : C2 ∈ chain_extension C) (hne : C1 ≠ C2) :
    Disjoint (C1 : Set (Finset (Option α))) (C2 : Set (Finset (Option α)))

- lemma chain_extension_covers_base {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
    {S : Finset (Option α)} :
    (∃ C' ∈ chain_extension C, S ∈ C') ↔
    (∃ A ∈ C, S = (Finset.mapEmbedding Function.Embedding.some).toEmbedding A) ∨
    (∃ A ∈ C, S = (Finset.mapEmbedding Function.Embedding.some).toEmbedding A ∪ {none})

- lemma chain_extension_partition {α : Type*} [Fintype α] (D : Finset (Finset (Finset α)))
    (hD : IsSymmetricChainDecomposition D) :
    IsSymmetricChainDecomposition (D.biUnion chain_extension)

- lemma scd_middle_rank_sum {G : Type*} [Fintype G] (T : Set G) [DecidablePred (· ∈ T)]
    (CT : Finset (Finset (Finset T))) (DTC : Finset (Finset (Finset (Tᶜ : Set G))))
    (hCT : IsSymmetricChainDecomposition CT)
    (hDTC : IsSymmetricChainDecomposition DTC) :
    let n
-/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option maxHeartbeats 2000000
-- Several generated Littlewood-Offord estimates time out at the default heartbeat limit.


open Complex ArithmeticFunction Int Set Real Filter Topology BigOperators Metric

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Erdos498

variable {n : ℕ}

/-!
# Upper Half Plane Encoding (Relational)
-/

-- Predicate for Upper Half Plane
def inUHP (w : ℂ) : Prop := 0 < w.im ∨ (w.im = 0 ∧ 0 ≤ w.re)

-- Predicate for Base Sign
def IsBaseSign (z : ℂ) (s : ℤ) : Prop :=
  (inUHP z → s = 1) ∧ (¬inUHP z → s = -1)

-- Predicate for Aligned Z
def IsAlignedZ (z : ℂ) (w : ℂ) : Prop :=
  ∃ s : ℤ, IsBaseSign z s ∧ w = (s : ℂ) * z

lemma exists_unique_baseSign (z : ℂ) : ∃! s, IsBaseSign z s := by
  dsimp [IsBaseSign]
  by_cases h : inUHP z
  · use 1; constructor <;> simp [h]
  · use -1; constructor <;> simp [h]

lemma exists_unique_alignedZ (z : ℂ) : ∃! w, IsAlignedZ z w := by
  obtain ⟨s, hs, hunique⟩ := exists_unique_baseSign z
  use ((s : ℂ) * z)
  dsimp [IsAlignedZ]
  refine ⟨⟨s, hs, rfl⟩, ?_⟩
  intro y hy
  rcases hy with ⟨s', hs', rfl⟩
  have : s' = s := hunique s' hs'
  rw [this]

/-!
# Bijection: Set-based
-/

def signToSet (z : Fin n → ℂ) (ε : Fin n → ℤ) : Set (Fin n) :=
  {i | IsBaseSign (z i) (ε i)}

-- Helper lemmas
lemma mem_signToSet_iff {z : Fin n → ℂ} {ε : Fin n → ℤ} {i : Fin n} :
    i ∈ signToSet z ε ↔ IsBaseSign (z i) (ε i) := Iff.rfl

lemma IsBaseSign_sq_eq_one {z : ℂ} {s : ℤ} (h : IsBaseSign z s) : (s : ℂ)^2 = 1 := by
  unfold IsBaseSign at h
  by_cases hz : inUHP z
  · rw [h.1 hz]; norm_num
  · rw [h.2 hz]; norm_num

lemma IsBaseSign_abs_eq_one {z : ℂ} {s : ℤ} (h : IsBaseSign z s) : |s| = 1 := by
  unfold IsBaseSign at h
  by_cases hz : inUHP z
  · rw [h.1 hz]; norm_num
  · rw [h.2 hz]; norm_num

lemma eq_neg_of_ne_baseSign {z : ℂ} {s ε : ℤ} (hs : IsBaseSign z s)
    (hε : ε = 1 ∨ ε = -1) (hne : ε ≠ s) : ε = -s := by
  have hs_val : s = 1 ∨ s = -1 := by
    unfold IsBaseSign at hs
    by_cases h : inUHP z
    · simp [hs.1 h]
    · simp [hs.2 h]
  rcases hs_val with (rfl | rfl) <;> rcases hε with (rfl | rfl)
  · contradiction
  · rfl
  · rfl
  · contradiction

lemma signToSet_injective_on_signs (z : Fin n → ℂ) (ε₁ ε₂ : Fin n → ℤ)
    (hε₁ : ∀ i, ε₁ i = 1 ∨ ε₁ i = -1) (hε₂ : ∀ i, ε₂ i = 1 ∨ ε₂ i = -1)
    (heq : signToSet z ε₁ = signToSet z ε₂) : ε₁ = ε₂ := by
  ext i
  obtain ⟨s, hs, hunique⟩ := exists_unique_baseSign (z i)
  have h1 : IsBaseSign (z i) (ε₁ i) ↔ IsBaseSign (z i) (ε₂ i) := by
    exact Set.ext_iff.mp heq i
  by_cases hi : i ∈ signToSet z ε₁
  · have h_eps1 : IsBaseSign (z i) (ε₁ i) := hi
    have h_eps2 : IsBaseSign (z i) (ε₂ i) := h1.1 hi
    rw [hunique (ε₁ i) h_eps1, hunique (ε₂ i) h_eps2]
  · have h_not_eps1 : ¬IsBaseSign (z i) (ε₁ i) := hi
    have h_not_eps2 : ¬IsBaseSign (z i) (ε₂ i) := mt h1.2 hi
    have ne1 : ε₁ i ≠ s := fun h => h_not_eps1 (cast (congrArg (IsBaseSign (z i)) h.symm) hs)
    have ne2 : ε₂ i ≠ s := fun h => h_not_eps2 (cast (congrArg (IsBaseSign (z i)) h.symm) hs)
    rw [eq_neg_of_ne_baseSign hs (hε₁ i) ne1, eq_neg_of_ne_baseSign hs (hε₂ i) ne2]

/-!
# Sum Difference
-/

lemma sum_diff_subset_exists_aligned (z : Fin n → ℂ) (A B : Finset (Fin n)) (hAB : A ⊆ B)
    (εA εB : Fin n → ℤ)
    (hεA : ∀ i, εA i = 1 ∨ εA i = -1) (hεB : ∀ i, εB i = 1 ∨ εB i = -1)
    (hA : signToSet z εA = (A : Set (Fin n))) (hB : signToSet z εB = (B : Set (Fin n))) :
    ∃ w : Fin n → ℂ, (∀ i, IsAlignedZ (z i) (w i)) ∧
    (∑ i, (εB i : ℂ) * z i) - (∑ i, (εA i : ℂ) * z i) = 2 * ∑ i ∈ B \ A, w i := by
  let w := fun i => (Classical.choose (exists_unique_alignedZ (z i)))
  use w; constructor
  · intro i; exact (Classical.choose_spec (exists_unique_alignedZ (z i))).1
  · rw [←Finset.sum_sub_distrib, Finset.mul_sum]
    have h_zero : ∀ i, i ∉ B \ A → (εB i : ℂ) * z i - (εA i : ℂ) * z i = 0 := by
      intro i hi_out; obtain ⟨s, hs, hunique⟩ := exists_unique_baseSign (z i)
      rw [Finset.mem_sdiff, not_and_or] at hi_out
      by_cases hBi : i ∈ B
      · have hAi : i ∈ A := by
          rcases hi_out with h | h
          · contradiction
          · exact not_not.mp h
        have hBin : IsBaseSign (z i) (εB i) := by
          rw [←mem_signToSet_iff, hB, Finset.mem_coe]
          exact hBi
        have hAin : IsBaseSign (z i) (εA i) := by
          rw [←mem_signToSet_iff, hA, Finset.mem_coe]
          exact hAi
        rw [hunique (εB i) hBin, hunique (εA i) hAin]; ring
      · have hAi : i ∉ A := fun h => hBi (hAB h)
        have hBout : ¬IsBaseSign (z i) (εB i) := by
          rw [←mem_signToSet_iff, hB, Finset.mem_coe]
          exact hBi
        have hAout : ¬IsBaseSign (z i) (εA i) := by
          rw [←mem_signToSet_iff, hA, Finset.mem_coe]
          exact hAi
        have eb : εB i = -s :=
          eq_neg_of_ne_baseSign hs (hεB i) (fun h => hBout (by
            rw [h]
            exact hs))
        have ea : εA i = -s :=
          eq_neg_of_ne_baseSign hs (hεA i) (fun h => hAout (by
            rw [h]
            exact hs))
        rw [eb, ea]; ring
    have h_eq : ∀ i ∈ B \ A, (εB i : ℂ) * z i - (εA i : ℂ) * z i = 2 * w i := by
      intro i hi; rw [Finset.mem_sdiff] at hi
      obtain ⟨s, hs, hunique⟩ := exists_unique_baseSign (z i)
      have hBin : IsBaseSign (z i) (εB i) := by
        rw [←mem_signToSet_iff, hB, Finset.mem_coe]
        exact hi.1
      have hAout : ¬IsBaseSign (z i) (εA i) := by
        rw [←mem_signToSet_iff, hA, Finset.mem_coe]
        exact hi.2
      have eb : εB i = s := hunique (εB i) hBin
      have ea : εA i = -s :=
        eq_neg_of_ne_baseSign hs (hεA i) (fun h => hAout (by
          rw [h]
          exact hs))
      have ws : w i = (s : ℂ) * z i := by
        obtain ⟨s', hs', rfl'⟩ := (Classical.choose_spec (exists_unique_alignedZ (z i))).1
        rw [hunique s' hs'] at rfl'; exact rfl'
      rw [eb, ea, ws]; simp only [Int.cast_neg]; ring
    calc
      ∑ i, (↑(εB i) * z i - ↑(εA i) * z i) =
          ∑ i ∈ B \ A, (↑(εB i) * z i - ↑(εA i) * z i) := by
        refine (Finset.sum_subset (Finset.subset_univ (B \ A)) ?_).symm
        intro i _ hi_out; exact h_zero i hi_out
      _ = ∑ i ∈ B \ A, (2 * w i) := by
        apply Finset.sum_congr rfl; intro i hi; exact h_eq i hi

lemma IsAlignedZ_isUHP {z w : ℂ} (h : IsAlignedZ z w) : inUHP w := by
  rcases h with ⟨s, hs, rfl⟩
  unfold IsBaseSign at hs
  by_cases hu : inUHP z
  · rw [hs.1 hu]; simp; exact hu
  · rw [hs.2 hu]
    simp
    unfold inUHP at *
    push Not at hu
    rcases hu with ⟨h1, h2⟩
    have neg_z : (-z).im = -z.im := by simp
    by_cases him : z.im = 0
    · simp [him] at *
      have : z.re < 0 := h2
      linarith
    · left
      have z_neg : z.im < 0 := lt_of_le_of_ne h1 him
      have : 0 < (-z).im := by rw [neg_z]; linarith
      exact this

/-! ## Main Geometry -/

lemma complex_sum_re {α : Type*} (S : Finset α) (f : α → ℂ) :
    (∑ i ∈ S, f i).re = ∑ i ∈ S, (f i).re := by
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_re, ih]

lemma complex_sum_im {α : Type*} (S : Finset α) (f : α → ℂ) :
    (∑ i ∈ S, f i).im = ∑ i ∈ S, (f i).im := by
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_im, ih]

lemma sum_sq_le_sq {α : Type*} (S : Finset α) (f : α → ℝ) (hf : ∀ i ∈ S, 0 ≤ f i) :
    ∑ i ∈ S, (f i)^2 ≤ (∑ i ∈ S, f i)^2 := by
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_elem : 0 ≤ f a := hf a (Finset.mem_insert_self _ _)
    have h_sub : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    specialize ih h_sub
    have sum_pos : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg h_sub
    nlinarith

lemma pure_sum_norm_gt_sqrt (S : Finset (Fin n)) (w : Fin n → ℂ)
    (hS : S.Nonempty)
    (h_pure :
        (∀ i ∈ S, 0 ≤ (w i).re ∧ 0 ≤ (w i).im) ∨
        (∀ i ∈ S, (w i).re < 0 ∧ 0 ≤ (w i).im))
    (hNorm : ∀ i ∈ S, 1 < ‖w i‖) :
    1 < ‖∑ i ∈ S, w i‖ := by
  have h_norm_sq_def (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [←Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [pow_two]
  have ineq_sum : 1 < ∑ i ∈ S, ((w i).re ^ 2 + (w i).im ^ 2) := by
    have : ∑ i ∈ S, (1 : ℝ) < ∑ i ∈ S, (‖w i‖^2) := by
      apply Finset.sum_lt_sum
      · intro i hi; nlinarith [hNorm i hi, norm_nonneg (w i)]
      · obtain ⟨i₀, hi₀⟩ := hS
        use i₀, hi₀
        nlinarith [hNorm i₀ hi₀, norm_nonneg (w i₀)]
    simp at this
    have card_ge_one : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast (Finset.card_pos.mpr hS)
    have : 1 < ∑ i ∈ S, (‖w i‖^2) := lt_of_le_of_lt card_ge_one this
    refine lt_of_lt_of_le this (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [h_norm_sq_def]
  have h_sq_bound : 1 < (∑ i ∈ S, (w i).re)^2 + (∑ i ∈ S, (w i).im)^2 := by
    rcases h_pure with hQ1 | hQ2
    · let SR := ∑ i ∈ S, (w i).re
      let SI := ∑ i ∈ S, (w i).im
      have ineqR : ∑ i ∈ S, ((w i).re)^2 ≤ SR^2 :=
        sum_sq_le_sq _ _ (fun i hi => (hQ1 i hi).1)
      have ineqI : ∑ i ∈ S, ((w i).im)^2 ≤ SI^2 :=
        sum_sq_le_sq _ _ (fun i hi => (hQ1 i hi).2)
      rw [Finset.sum_add_distrib] at ineq_sum
      linarith
    · let SR : ℝ := ∑ i ∈ S, (w i).re
      let SI : ℝ := ∑ i ∈ S, (w i).im
      have ineqR : ∑ i ∈ S, (w i).re^2 ≤ SR^2 := by
        have : ∑ i ∈ S, (-(w i).re)^2 ≤ (∑ i ∈ S, -(w i).re)^2 :=
          sum_sq_le_sq _ _ (fun i hi => neg_nonneg.mpr (le_of_lt (hQ2 i hi).1))
        rw [Finset.sum_neg_distrib] at this
        simp only [neg_sq] at this
        exact this
      have ineqI : ∑ i ∈ S, ((w i).im)^2 ≤ SI^2 :=
        sum_sq_le_sq _ _ (fun i hi => (hQ2 i hi).2)
      rw [Finset.sum_add_distrib] at ineq_sum
      linarith
  change 1 < ‖∑ i ∈ S, w i‖
  have h_sq :
      ‖∑ i ∈ S, w i‖ ^ 2 =
        (∑ i ∈ S, (w i).re) ^ 2 + (∑ i ∈ S, (w i).im) ^ 2 := by
    rw [h_norm_sq_def, complex_sum_re, complex_sum_im]
  nlinarith [norm_nonneg (∑ i ∈ S, w i)]

/-! ## Main Theorem -/

/-!
## Symmetric Chain Decomposition Support

We define Symmetric Chain Decompositions (SCD) manually to support the grid argument.
-/

/-- A chain is symmetric in `α` if it 'skips' the same number of ranks from top and bottom. -/
def IsSymmetricChain {α : Type*} [Fintype α] (C : Finset (Finset α)) : Prop :=
  ∃ (start : Finset α) (k : ℕ),
    IsChain (· ⊆ ·) (C : Set (Finset α)) ∧
    C.card = k + 1 ∧
    start ∈ C ∧ (∀ X ∈ C, start ⊆ X) ∧
    start.card + (start.card + k) = Fintype.card α ∧
    (∃ last ∈ C, (∀ X ∈ C, X ⊆ last) ∧ last.card = start.card + k)

/-- A Symmetric Chain Decomposition of `α`. -/
def IsSymmetricChainDecomposition {α : Type*} [Fintype α]
    (D : Finset (Finset (Finset α))) : Prop :=
  (∀ C ∈ D, IsSymmetricChain C) ∧
  (∀ A : Finset α, ∃! C ∈ D, A ∈ C)

/-- The base case: Empty type has a valid SCD (consisting of the single chain {∅}). -/
lemma scd_empty : IsSymmetricChainDecomposition (α := Empty) {{(∅ : Finset Empty)}} := by
  constructor
  · intro C hC
    rw [Finset.mem_singleton] at hC; subst hC
    use ∅, 0
    constructor
    · simp [IsChain.singleton]
    · constructor
      · simp -- C.card = 1
      · constructor
        · simp -- start ∈ C
        · constructor
          · intro X hX; simp at hX; subst hX; exact Finset.empty_subset _ -- start ⊆ X
          · constructor
            · simp -- card α
            · use ∅; simp -- last ∈ C and last.card = start.card + k and ∀ X, X ⊆ last
  · intro A
    use {∅}
    simp only [Finset.mem_singleton]
    constructor
    · constructor
      · trivial
      · exact Finset.eq_empty_of_isEmpty A
    · intro y hy; rcases hy with ⟨rfl, _⟩; rfl

/-- Extending a chain C in α to Option α.
    Returns a set of one or two chains in Option α. -/
noncomputable def chain_extension {α : Type*} [DecidableEq α]
    (C : Finset (Finset α)) : Finset (Finset (Finset (Option α))) :=
  if h : C.Nonempty then
    let top := Classical.choose (Finset.exists_max_image C Finset.card h)
    let emb := (Finset.mapEmbedding Function.Embedding.some).toEmbedding
    -- C1: Original chain lifted, plus top ∪ {none}
    let C1 := insert (emb top ∪ {none}) (C.map emb)
    -- C2: Rest lifted, plus {none} attached
    let rest := C.erase top
    let C2 := rest.image (fun A => emb A ∪ {none})
    if C2.Nonempty then {C1, C2} else {C1}
  else
    ∅

lemma chain_extension_is_chain {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
    (hC : IsChain (· ⊆ ·) (C : Set (Finset α))) :
    ∀ C' ∈ chain_extension C, IsChain (· ⊆ ·) (C' : Set (Finset (Option α))) := by
  unfold chain_extension;
  split_ifs <;> simp_all +decide [ IsChain ];
  split_ifs <;> simp_all +decide [ Set.Pairwise ];
  · refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩;
    · intro a ha hne
      have h_subset :
          a ⊆ Classical.choose (Finset.exists_max_image C Finset.card ‹_›) ∨
            Classical.choose (Finset.exists_max_image C Finset.card ‹_›) ⊆ a := by
        have := Classical.choose_spec ( Finset.exists_max_image C Finset.card ‹_› );
        cases eq_or_ne a
            ( Classical.choose ( Finset.exists_max_image C Finset.card ‹_› ) ) <;>
          aesop;
      rcases h_subset with h_subset | h_subset <;> simp_all +decide [ Finset.subset_iff ];
      · simp_all +decide [ Finset.mapEmbedding ];
        simp_all +decide [ OrderEmbedding.ofMapLEIff ];
      · simp_all +decide [ Finset.mapEmbedding ];
        simp_all +decide [ OrderEmbedding.ofMapLEIff ];
        have := Classical.choose_spec ( Finset.exists_max_image C Finset.card ‹_› );
        exact fun x hx => by
          have hcard := this.2 a ha
          exact Classical.not_not.1 fun hx' =>
            (not_lt_of_ge hcard) <|
              Finset.card_lt_card <|
                Finset.ssubset_iff_subset_ne.2 ⟨h_subset, by aesop⟩
    · intro x hx; refine ⟨ ?_, ?_ ⟩;
      · intro hx';
        by_cases h : x ⊆ Classical.choose ( Finset.exists_max_image C Finset.card ‹_› ) <;>
          simp_all +decide [ Finset.subset_iff ];
        · exact Or.inl fun y hy => by
            rcases Finset.mem_map.mp hy with ⟨ z, hz, rfl ⟩
            exact Or.inr ( Finset.mem_map.mpr ⟨ z, h hz, rfl ⟩ )
        · have := Classical.choose_spec ( Finset.exists_max_image C Finset.card ‹_› );
          contrapose! this;
          exact fun _ => ⟨ x, hx, Finset.card_lt_card <| Finset.ssubset_iff_subset_ne.mpr ⟨ by
            grind, by
            grind ⟩ ⟩;
      · intro y hy hxy; specialize hC hx hy; simp_all +decide [ Finset.subset_iff ] ;
        cases hC <;> simp_all +decide [ Function.Embedding.some ];
        · exact Or.inl fun z hz => by
            rcases Finset.mem_map.mp hz with ⟨ w, hw, rfl ⟩
            exact Finset.mem_map.mpr ⟨ w, by aesop ⟩
        · exact Or.inr fun z hz => by
            rcases Finset.mem_map.mp hz with ⟨ w, hw, rfl ⟩
            exact Finset.mem_map.mpr ⟨ w, by aesop ⟩
    · -- Since C is a chain, any two elements in C are comparable.
      -- Therefore, their images under the embedding should also be comparable.
      intros x y hx hy hxy;
      rintro _ z hz hz' rfl hne; subst_vars; simp_all +decide [ Finset.subset_iff ] ;
      cases hC hy hz' ( by aesop ) <;> simp_all +decide [ Finset.mapEmbedding ];
      · simp_all +decide [ Finset.ext_iff, OrderEmbedding.ofMapLEIff ];
      · simp_all +decide [ Finset.ext_iff, OrderEmbedding.ofMapLEIff ];
  · -- Since the rest of the chain is empty, there are no elements in it to check.
    -- The subset relationship is therefore trivially satisfied.
    have h_empty :
        C.erase (Classical.choose (Finset.exists_max_image C Finset.card ‹_›)) = ∅ →
          ∀ a ∈ C, a = Classical.choose (Finset.exists_max_image C Finset.card ‹_›) := by
      simp +contextual [ Finset.ext_iff ];
      intro h a ha x; specialize h a x; contrapose! h; aesop;
    grind

noncomputable section AristotleLemmas

/-
The cardinality of a set mapped by `some` is the same as the original set.
-/
lemma card_map_some {α : Type*} (A : Finset α) :
    (A.map Function.Embedding.some).card = A.card := by
      grind

/-
The cardinality of a set mapped by `some` and with `none` inserted is the
original cardinality plus one.
-/
lemma card_map_some_insert_none {α : Type*} (A : Finset α) :
    (insert none (A.map Function.Embedding.some)).card = A.card + 1 := by
      convert Finset.card_insert_of_notMem _ <;> simp +decide [ Function.Embedding.some ]

/-
Since `some` is injective, the image of A is a subset of the image of B if and
only if A is a subset of B.
-/
lemma map_some_subset_map_some_iff {α : Type*} {A B : Finset α} :
    A.map Function.Embedding.some ⊆ B.map Function.Embedding.some ↔ A ⊆ B := by
      rw [ Finset.map_subset_map ]

/-
The image of A under `some` is a subset of `insert none (image of B)` if and
only if A is a subset of B.
-/
lemma map_some_subset_insert_none {α : Type*} {A B : Finset α} :
    A.map Function.Embedding.some ⊆ insert none (B.map Function.Embedding.some) ↔ A ⊆ B := by
      simp +decide [ Finset.subset_iff ]

/-
`insert none (image of A)` is a subset of `insert none (image of B)` if and only
if A is a subset of B.
-/
lemma insert_none_subset_insert_none_iff {α : Type*} {A B : Finset α} :
    insert none (A.map Function.Embedding.some) ⊆
      insert none (B.map Function.Embedding.some) ↔ A ⊆ B := by
      aesop

/-
The cardinality of the lifted set of sets is the same as the original, because
the lifting map is injective.
-/
lemma card_image_lift_add {α : Type*} (S : Finset (Finset α)) :
    (S.image (fun A => insert none (A.map Function.Embedding.some))).card = S.card := by
      rw [ Finset.card_image_of_injective ];
      intro A B h; ext x; replace h := Finset.ext_iff.mp h ( Option.some x ) ; aesop;

/-
A sufficient condition for a chain to be symmetric: it has a minimum and maximum
element, the sum of their cardinalities is the total cardinality, and the chain's
length corresponds to the difference in their cardinalities plus one (implying
no gaps).
-/
lemma check_symmetric {α : Type*} [Fintype α] (C : Finset (Finset α)) (start last : Finset α)
    (h_chain : IsChain (· ⊆ ·) (C : Set (Finset α)))
    (h_start : start ∈ C)
    (h_last : last ∈ C)
    (h_min : ∀ X ∈ C, start ⊆ X)
    (h_max : ∀ X ∈ C, X ⊆ last)
    (h_card_sum : start.card + last.card = Fintype.card α)
    (h_card_diff : C.card = last.card - start.card + 1) :
    Erdos498.IsSymmetricChain C := by
      have hle : start.card ≤ last.card := Finset.card_le_card (h_min last h_last)
      refine ⟨start, last.card - start.card, h_chain, h_card_diff, h_start, h_min, ?_, ?_⟩
      · rw [Nat.add_sub_of_le hle]
        exact h_card_sum
      · exact ⟨last, h_last, h_max, by rw [Nat.add_sub_of_le hle]⟩

/-
If C is a symmetric chain with maximum element `top`, then the extension C1
(which is C lifted plus `top ∪ {none}`) is a symmetric chain in `Option α`.
Proof idea:
1. Identify `start` of C. Lift it to `start'`.
2. Identify `last` of C1 as `top' = top ∪ {none}`.
3. Verify C1 is a chain.
4. Verify `start'.card + top'.card = Fintype.card (Option α)`.
5. Verify `C1.card = top'.card - start'.card + 1`.
Use `check_symmetric`.
-/
set_option linter.style.cases false in
lemma symmetric_chain_extension_C1 {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (Finset α)) (top : Finset α)
    (hS : Erdos498.IsSymmetricChain C)
    (htop : top ∈ C)
    (hmax : ∀ X ∈ C, X ⊆ top) :
    Erdos498.IsSymmetricChain
      (insert (insert none (top.map Function.Embedding.some))
        (C.map (Finset.mapEmbedding Function.Embedding.some).toEmbedding)) := by
      cases' hS with start k hS;
      rcases k with ⟨ k, hk₁, hk₂, hk₃, hk₄, hk₅, hk₆ ⟩;
      refine ⟨ start.map Function.Embedding.some, k + 1, ?_, ?_, ?_, ?_, ?_ ⟩ <;> simp_all +decide;
      · intro x hx y hy hxy; simp_all +decide [ Finset.subset_iff ] ;
        rcases hx with ( rfl | ⟨ x, hx, rfl ⟩ ) <;>
          rcases hy with ( rfl | ⟨ y, hy, rfl ⟩ ) <;>
          simp_all +decide;
        · simp_all +decide [ Finset.mapEmbedding ];
          simp_all +decide [ Finset.ext_iff, OrderEmbedding.ofMapLEIff ];
          exact fun x hx => hmax _ hy hx;
        · exact Or.inl fun y hy => by
            rcases Finset.mem_map.mp hy with ⟨ z, hz, rfl ⟩
            exact Or.inr ⟨ z, hmax _ hx hz, rfl ⟩
        · cases hk₁ hx hy hxy <;> simp_all +decide [ Function.Embedding.some ];
          · simp_all +decide [ Finset.mapEmbedding ];
            simp_all +decide [ OrderEmbedding.ofMapLEIff ];
          · simp_all +decide [ Finset.mapEmbedding ];
            simp_all +decide [ OrderEmbedding.ofMapLEIff ];
      · rw [ Finset.card_insert_of_notMem ] <;> simp_all +decide ;
        intro X hX h; replace h := Finset.ext_iff.mp h Option.none; simp_all +decide ;
        simpa using Finset.mem_map.mp h |> fun ⟨ x, hx, hx' ⟩ => by cases hx' ;
      · exact Or.inr ⟨ start, hk₃, rfl ⟩;
      · simp_all +decide [ Finset.subset_iff, Finset.mapEmbedding ];
        exact fun X hX x hx => Finset.mem_map_of_mem _ ( hk₄ X hX hx );
      · refine ⟨ by linarith, Or.inl ⟨ ?_, ?_ ⟩ ⟩;
        · simp_all +decide [ Finset.subset_iff ];
          rintro X hX x hx
          rcases Finset.mem_map.mp hx with ⟨ y, hy, rfl ⟩
          exact Or.inr ⟨ y, hmax X hX hy, rfl ⟩
        · obtain ⟨ last, hlast₁, hlast₂, hlast₃ ⟩ := hk₆
          have := hmax _ hlast₁
          simp_all +decide [ Finset.subset_iff ] ;
          linarith [ show top.card = last.card from by
            rw [ show top = last from Finset.Subset.antisymm ( by aesop ) ( by aesop ) ] ]

/-
The cardinality function is injective on a chain of finite sets.
-/
lemma chain_map_card_injective {α : Type*} (C : Finset (Finset α))
    (h_chain : IsChain (· ⊆ ·) (C : Set (Finset α))) :
    Set.InjOn Finset.card (C : Set (Finset α)) := by
      -- Since C is a chain, two elements with the same cardinality must be equal.
      intros X hX Y hY h_eq_card
      have h_sub : X ⊆ Y ∨ Y ⊆ X := by
        exact h_chain.total hX hY;
      rcases h_sub with h_sub | h_sub
      · exact Finset.eq_of_subset_of_card_le h_sub ( by linarith )
      · exact Eq.symm ( Finset.eq_of_subset_of_card_le h_sub ( by linarith ) )

/-
If a chain C has length equal to the difference of the cardinalities of its max
and min elements plus one, then the set of cardinalities of elements in C is
exactly the interval [min_card, max_card].
-/
lemma card_image_eq_Icc_of_chain_card_diff {α : Type*} (C : Finset (Finset α))
    (h_chain : IsChain (· ⊆ ·) (C : Set (Finset α)))
    (start last : Finset α)
    (h_min : ∀ X ∈ C, start ⊆ X)
    (h_max : ∀ X ∈ C, X ⊆ last)
    (h_len : C.card = last.card - start.card + 1) :
    C.image Finset.card = Finset.Icc start.card last.card := by
      refine Finset.eq_of_subset_of_card_le ( fun x hx => ?_ ) ?_;
      · simp +zetaDelta at *;
        exact ⟨
          by
            obtain ⟨ a, ha, rfl ⟩ := hx
            exact Finset.card_le_card ( h_min a ha ),
          by
            obtain ⟨ a, ha, rfl ⟩ := hx
            exact Finset.card_le_card ( h_max a ha ) ⟩;
      · rw [ Finset.card_image_of_injOn ];
        · simp +zetaDelta at *;
          omega;
        · exact chain_map_card_injective C h_chain

lemma exists_second_top {α : Type*} [Fintype α] (C : Finset (Finset α)) (top : Finset α)
    (hS : Erdos498.IsSymmetricChain C)
    (htop : top ∈ C)
    (hmax : ∀ X ∈ C, X ⊆ top)
    (hrest : (C.erase top).Nonempty) :
    ∃ second_top ∈ C.erase top,
      (∀ X ∈ C.erase top, X ⊆ second_top) ∧ second_top.card = top.card - 1 := by
      rcases hS with ⟨ start, k, h_chain, h_card, h_start, h_min, h_max ⟩;
      -- By definition of $C.erase top$, there is an element just below `top`.
      obtain ⟨second_top, h_second_top⟩ :
          ∃ second_top ∈ C.erase top, second_top.card = top.card - 1 := by
        have h_card_image : C.image Finset.card = Finset.Icc start.card top.card := by
          apply Erdos498.card_image_eq_Icc_of_chain_card_diff C h_chain start top h_min hmax;
          obtain ⟨ last, hlast, hlast', hlast'' ⟩ := h_max.2;
          have h_card_eq : top = last := by
            exact Finset.Subset.antisymm ( hlast' _ htop ) ( hmax _ hlast );
          aesop;
        replace h_card_image := Finset.ext_iff.mp h_card_image ( top.card - 1 )
        rcases k with ( _ | k ) <;> simp_all +decide ;
        · rw [ Finset.card_eq_one ] at h_card ; aesop;
        · contrapose! h_card_image;
          have := Finset.eq_of_subset_of_card_le
            ( show start ⊆ top from fun x hx => hmax _ h_start hx )
          simp_all +decide ;
          grind;
      use second_top;
      have h_second_top_max : ∀ X ∈ C.erase top, X ⊆ second_top := by
        intro X hX
        have h_card : X.card ≤ second_top.card := by
          have h_card : X.card ≤ top.card - 1 := by
            exact Nat.le_sub_one_of_lt
              ( lt_of_le_of_ne
                ( Finset.card_le_card ( hmax X ( Finset.mem_of_mem_erase hX ) ) )
                (fun h => by
                  have := Finset.eq_of_subset_of_card_le
                    ( hmax X ( Finset.mem_of_mem_erase hX ) ) ( by linarith )
                  aesop) );
          grind
        have h_card_eq : X ⊆ second_top ∨ second_top ⊆ X := by
          have := h_chain.total
            ( Finset.mem_coe.mpr ( Finset.mem_of_mem_erase hX ) )
            ( Finset.mem_coe.mpr ( Finset.mem_of_mem_erase h_second_top.1 ) )
          aesop;
        cases h_card_eq <;> simp_all +decide [ Finset.subset_iff ];
        have := Finset.eq_of_subset_of_card_le ( show second_top ⊆ X from by aesop ) ; aesop;
      exact ⟨ h_second_top.1, h_second_top_max, h_second_top.2 ⟩

/-
If C \ {top} is nonempty, then the minimum element `start` is not equal to `top`.
-/
set_option linter.unusedVariables false in
lemma start_ne_top_of_rest_nonempty {α : Type*} [Finite α] (C : Finset (Finset α))
    (top : Finset α) (start : Finset α)
    (h_start : start ∈ C)
    (h_min : ∀ X ∈ C, start ⊆ X)
    (h_top : top ∈ C)
    (h_max : ∀ X ∈ C, X ⊆ top)
    (h_rest : (C.erase top).Nonempty) :
    start ≠ top := by
  letI := Fintype.ofFinite α
  intro h_eq
  have h_singleton : C = {top} := by
    ext X
    constructor
    · intro hX
      have h1 := h_min X hX
      have h2 := h_max X hX
      rw [h_eq] at h1
      have h_eq_X : X = top := Finset.Subset.antisymm h2 h1
      rw [h_eq_X]
      exact Finset.mem_singleton_self top
    · intro hX
      rw [Finset.mem_singleton] at hX
      rw [hX]
      exact h_top
  have h_empty : C.erase top = ∅ := by
    rw [h_singleton]
    simp
  rw [h_empty] at h_rest
  simp at h_rest

/-
Lifting a chain by adding `none` preserves the chain property.
-/
lemma lift_is_chain {α : Type*} (S : Finset (Finset α))
    (hS : IsChain (· ⊆ ·) (S : Set (Finset α))) :
    IsChain (· ⊆ ·)
      ((S.image (fun A => insert none (A.map Function.Embedding.some))) :
        Set (Finset (Option α))) := by
      intro x hx y hy; aesop;

/-
Lifting a chain preserves the minimum and maximum elements.
-/
set_option linter.unusedVariables false in
lemma lift_chain_min_max {α : Type*} (S : Finset (Finset α)) (start last : Finset α)
    (hS : IsChain (· ⊆ ·) (S : Set (Finset α)))
    (h_start : start ∈ S)
    (h_last : last ∈ S)
    (h_min : ∀ X ∈ S, start ⊆ X)
    (h_max : ∀ X ∈ S, X ⊆ last) :
    let lift := fun A => insert none (A.map Function.Embedding.some)
    let S' := S.image lift
    let start' := lift start
    let last' := lift last
    start' ∈ S' ∧ last' ∈ S' ∧
      (∀ X' ∈ S', start' ⊆ X') ∧ (∀ X' ∈ S', X' ⊆ last') := by
  intro lift S' start' last'
  refine ⟨Finset.mem_image_of_mem lift h_start, Finset.mem_image_of_mem lift h_last, ?_, ?_⟩
  · intro X' hX'
    rcases Finset.mem_image.mp hX' with ⟨X, hX, rfl⟩
    rw [Erdos498.insert_none_subset_insert_none_iff]
    exact h_min X hX
  · intro X' hX'
    rcases Finset.mem_image.mp hX' with ⟨X, hX, rfl⟩
    rw [Erdos498.insert_none_subset_insert_none_iff]
    exact h_max X hX

lemma symmetric_chain_extension_C2 {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (Finset α)) (top : Finset α)
    (hS : Erdos498.IsSymmetricChain C)
    (htop : top ∈ C)
    (hmax : ∀ X ∈ C, X ⊆ top)
    (hrest : (C.erase top).Nonempty) :
    Erdos498.IsSymmetricChain
      ((C.erase top).image (fun A => insert none (A.map Function.Embedding.some))) := by
      obtain ⟨ start, k, h_chain, hk, h_start, h_min, h_top, h_max,
        h_card_sum, h_card_diff ⟩ := hS;
      have h_second_top :
          ∃ second_top ∈ C.erase top,
            (∀ X ∈ C.erase top, X ⊆ second_top) ∧
              second_top.card = h_max.card - 1 := by
        convert Erdos498.exists_second_top C top _ _ _ _ using 1;
        · congr! 1;
          congr! 2;
          · convert rfl;
          · simp +decide [ Finset.subset_iff ];
          · rw [ show h_max = top from
              Finset.Subset.antisymm ( hmax _ h_card_sum ) ( h_card_diff.1 _ htop ) ];
        · exact ⟨ start, k, h_chain, hk, h_start, h_min, by linarith,
            ⟨ h_max, h_card_sum, h_card_diff ⟩ ⟩;
        · exact htop;
        · exact hmax;
        · grind;
      obtain ⟨ second_top, h_second_top_mem, h_second_top_max,
        h_second_top_card ⟩ := h_second_top;
      apply Erdos498.check_symmetric;
      rotate_left;
      rotate_left;
      · exact Finset.mem_image_of_mem _ h_second_top_mem;
      rotate_left;
      · grind;
      rotate_left;
      rotate_left;
      · exact Insert.insert Option.none ( Finset.map Function.Embedding.some start );
      · intro x hx y hy; aesop;
      · grind;
      · grind;
      · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;>
          simp +decide [ h_card_diff, h_second_top_card ];
        grind;
      · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
        · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;>
            simp +decide [ Finset.mem_map, Function.Embedding.some ];
          grind;
        · simp +contextual [ Finset.ext_iff ];
          intro a₁ a₂ h a; specialize h ( Option.some a ) ; aesop;

/-
If C is a symmetric chain with maximum element `top` and `C \ {top}` is
nonempty, then the extension C2 (which is C \ {top} lifted plus {none}) is a
symmetric chain in `Option α`.
-/
lemma symmetric_chain_extension_C2_aux {α : Type*} [Fintype α] [DecidableEq α]
    (C : Finset (Finset α)) (top : Finset α)
    (hS : Erdos498.IsSymmetricChain C)
    (htop : top ∈ C)
    (hmax : ∀ X ∈ C, X ⊆ top)
    (hrest : (C.erase top).Nonempty) :
    Erdos498.IsSymmetricChain
      ((C.erase top).image (fun A => insert none (A.map Function.Embedding.some))) := by
      convert Erdos498.symmetric_chain_extension_C2 C top hS htop hmax hrest using 1

end AristotleLemmas

set_option linter.style.cases false in
lemma chain_extension_is_symmetric {α : Type*} [Fintype α] {C : Finset (Finset α)}
    (hS : IsSymmetricChain C) :
    ∀ C' ∈ chain_extension C, IsSymmetricChain C' := by
  unfold Erdos498.chain_extension;
  simp +zetaDelta at *;
  split_ifs <;> simp_all +decide;
  · have := Classical.choose_spec ( Finset.exists_max_image C Finset.card ‹_› );
    -- Show that `top` is the maximum element of `C` with respect to inclusion.
    have h_top_max :
        ∀ X ∈ C, X ⊆ Classical.choose (Finset.exists_max_image C Finset.card ‹_›) := by
      cases' hS with start k hS_subset;
      -- Since C is a chain, any two elements are comparable.
      -- Hence X is below the chosen top, or the chosen top is below X.
      have h_chain : IsChain (· ⊆ ·) (C : Set (Finset α)) := by
        exact k.choose_spec.1;
      intro X hX;
      rcases h_chain.total hX this.1 with h | h <;> simp_all +decide [ Finset.subset_iff ];
      have := this.2 X hX; have := Finset.eq_of_subset_of_card_le h; aesop;
    exact ⟨
      Erdos498.symmetric_chain_extension_C1 _ _ hS this.1 h_top_max,
      Erdos498.symmetric_chain_extension_C2_aux _ _ hS this.1 h_top_max ‹_› ⟩;
  · convert Erdos498.symmetric_chain_extension_C1 _ _ _ _ _;
    all_goals try assumption;
    · exact Classical.choose_spec ( Finset.exists_max_image _ _ ‹_› ) |>.1;
    · exact fun X hX =>
        Classical.not_not.1 fun h =>
          Finset.notMem_empty _ <|
            ‹C.erase _ = ∅› ▸ Finset.mem_erase_of_ne_of_mem ( by aesop ) hX

lemma chain_extension_disjoint {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
    (C1 C2 : Finset (Finset (Option α))) (h1 : C1 ∈ chain_extension C)
    (h2 : C2 ∈ chain_extension C) (hne : C1 ≠ C2) :
    Disjoint (C1 : Set (Finset (Option α))) (C2 : Set (Finset (Option α))) := by
  -- Since C1 and C2 are different chains in the extension, their elements must be distinct.
  have h_distinct : ∀ x ∈ C1, x ∉ C2 := by
    unfold Erdos498.chain_extension at *;
    split_ifs at h1 h2 <;> simp_all +decide;
    split_ifs at h1 h2 <;> simp_all +decide;
    rcases h1 with ( rfl | rfl ) <;> rcases h2 with ( rfl | rfl ) <;> simp_all +decide;
      · -- If x is not the top element, then the lifted images cannot be equal.
        have h_top_unique :
            ∀ x ∈ C,
              x ≠ Classical.choose (Finset.exists_max_image C Finset.card ‹_›) →
                ¬(Insert.insert Option.none ((Finset.mapEmbedding Function.Embedding.some) x) =
                  Insert.insert Option.none
                    ((Finset.mapEmbedding Function.Embedding.some)
                      (Classical.choose (Finset.exists_max_image C Finset.card ‹_›)))) := by
          intro x hx hx' h; simp_all +decide [ Finset.ext_iff ] ;
          obtain ⟨ y, hy ⟩ := hx'; specialize h ( Option.some y ) ; simp_all +decide ;
        -- The top element's image has an extra `none`.
        have h_second_part :
            ∀ x ∈ C,
              x ≠ Classical.choose (Finset.exists_max_image C Finset.card ‹_›) →
                ∀ a ∈ C,
                  ¬(Insert.insert Option.none
                    ((Finset.mapEmbedding Function.Embedding.some :
                      Finset α → Finset (Option α)) x) =
                    (Finset.mapEmbedding Function.Embedding.some :
                      Finset α → Finset (Option α)) a) := by
          intro x hx hx' a ha h; replace h := Finset.ext_iff.mp h Option.none; simp_all +decide ;
        exact ⟨
          fun x hx hx' => h_top_unique x hx' hx,
          fun a ha x hx hx' => h_second_part x hx' hx a ha ⟩;
    · intro x y hy₁ hy₂ hx; subst hx; simp_all +decide [ Finset.ext_iff ] ;
      obtain ⟨ x, hx ⟩ := hy₁;
      refine ⟨ ⟨ Option.some x, ?_ ⟩, ?_ ⟩ <;> simp_all +decide [ Finset.mapEmbedding ];
      · simp_all +decide [ OrderEmbedding.ofMapLEIff ];
      · intro z hz; use Option.none; simp +decide ;
        exact fun h => by have := Finset.mem_map.mp h; aesop;
  exact Set.disjoint_left.mpr h_distinct

lemma chain_extension_covers_base {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
    {S : Finset (Option α)} :
    (∃ C' ∈ chain_extension C, S ∈ C') ↔
    (∃ A ∈ C, S = (Finset.mapEmbedding Function.Embedding.some).toEmbedding A) ∨
    (∃ A ∈ C, S = (Finset.mapEmbedding Function.Embedding.some).toEmbedding A ∪ {none}) := by
  unfold Erdos498.chain_extension;
  by_cases h : C.Nonempty <;> simp +decide [ h ];
  · split_ifs <;> simp +decide [ Finset.Nonempty ] at *;
    · -- Since S is in the second chain, it has the form insert none (map some A).
      apply Iff.intro;
      · rintro ( ( rfl | ⟨ A, hA, rfl ⟩ ) | ⟨ A, ⟨ hA₁, hA₂ ⟩, rfl ⟩ )
        · exact Or.inr
            ⟨ _, Classical.choose_spec ( Finset.exists_max_image C Finset.card h ) |>.1,
              rfl ⟩
        · exact Or.inl ⟨ _, hA, rfl ⟩
        · exact Or.inr ⟨ _, hA₂, rfl ⟩
      · grind;
    · grind;
  · aesop

noncomputable section AristotleLemmas

/-
Every subset of Option α is either the image of a subset of α or that image plus 'none'.
-/
lemma option_finset_cases {α : Type*} [DecidableEq α] (S : Finset (Option α)) :
    ∃ A : Finset α,
      S = A.map Function.Embedding.some ∨ S = insert none (A.map Function.Embedding.some) := by
      -- Let `A` be the set of `x` such that `some x ∈ S`.
      set A := S.filterMap id;
      by_cases h : Option.none ∈ S
      · refine ⟨ A ?_, Or.inr ?_ ⟩;
        · intros; subst_vars; rfl
        · ext ( _ | x ) <;> aesop
      · refine ⟨ A ?_, Or.inl ?_ ⟩;
        · intros; subst_vars; rfl
        ext ( _ | x ) <;> aesop

end AristotleLemmas

lemma chain_extension_partition {α : Type*} [Fintype α] (D : Finset (Finset (Finset α)))
    (hD : IsSymmetricChainDecomposition D) :
    IsSymmetricChainDecomposition (D.biUnion chain_extension) := by
  -- Let's unfold the definition of `IsSymmetricChainDecomposition`.
  unfold IsSymmetricChainDecomposition at *;
  refine ⟨ ?_, ?_ ⟩;
  · simp +zetaDelta at *;
    exact fun C x hx hC => chain_extension_is_symmetric ( hD.1 x hx ) C hC;
  · intro A;
    -- By `option_finset_cases`, `A` is `emb A'` or `emb A' ∪ {none}`.
    obtain ⟨A', hA'⟩ :
        ∃ A' : Finset α,
          A = Finset.map Function.Embedding.some A' ∨
            A = Finset.map Function.Embedding.some A' ∪ {none} := by
      exact Erdos498.option_finset_cases A |> fun ⟨ A', hA' ⟩ => ⟨ A', by simpa using hA' ⟩;
    obtain ⟨C, hC⟩ : ∃! C ∈ D, A' ∈ C := by
      exact hD.2 A';
    -- By `chain_extension_covers_base`, there is a unique such extended chain.
    obtain ⟨C', hC'⟩ : ∃! C' ∈ chain_extension C, A ∈ C' := by
      obtain ⟨C', hC'⟩ : ∃ C' ∈ chain_extension C, A ∈ C' := by
        apply (chain_extension_covers_base).mpr;
        exact Or.imp ( fun h => ⟨ A', hC.1.2, h ⟩ ) ( fun h => ⟨ A', hC.1.2, h ⟩ ) hA';
      refine ⟨ C', hC', fun C'' hC'' => ?_ ⟩;
      have h_disjoint :
          Disjoint (C' : Set (Finset (Option α))) (C'' : Set (Finset (Option α))) ∨
            C' = C'' := by
        exact Classical.or_iff_not_imp_left.2 fun h =>
          by_contradiction fun hne =>
            h <| chain_extension_disjoint _ _ hC'.1 hC''.1 hne;
      exact h_disjoint.resolve_left
        ( Set.not_disjoint_iff_nonempty_inter.mpr ⟨ A, hC'.2, hC''.2 ⟩ ) ▸ rfl;
    refine ⟨ C', ?_, ?_ ⟩ <;> simp_all +decide [ Finset.mem_biUnion ];
    · exact ⟨ C, hC.1.1, hC'.1.1 ⟩;
    · intro y x hx hy hyA
      have hx_eq_C : x = C := by
        apply hC.2 x hx;
        have := chain_extension_covers_base.mp ⟨ y, hy, hyA ⟩;
        simp +zetaDelta at *;
        rcases this with ( ⟨ B, hB, rfl ⟩ | ⟨ B, hB, rfl ⟩ ) <;>
          simp_all +decide [ Finset.mapEmbedding ];
        · simp_all +decide [ Finset.ext_iff, OrderEmbedding.ofMapLEIff ];
          rcases hA' with hA' | hA' <;> have := hA' ( Option.none ) <;> simp_all +decide;
          convert hB using 1;
          ext a; specialize hA' ( Option.some a ) ; aesop;
        · simp_all +decide [ Finset.ext_iff, OrderEmbedding.ofMapLEIff ];
          rcases hA' with hA' | hA' <;> have := hA' Option.none <;> simp_all +decide;
          have hA'_eq_B : A' = B := by
            ext a; specialize hA' ( Option.some a ) ; aesop;
          grind;
      grind

/-- The inductive step: Option α has a valid SCD if α does. -/
lemma scd_option {α : Type*} [Fintype α] (D : Finset (Finset (Finset α)))
    (hD : IsSymmetricChainDecomposition D) :
    ∃ D' : Finset (Finset (Finset (Option α))), IsSymmetricChainDecomposition D' := by
  use D.biUnion chain_extension
  exact chain_extension_partition D hD

/-- Transfer SCD across an equivalence. (proven by Aristotle) -/
lemma scd_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    (D : Finset (Finset (Finset α))) (hD : IsSymmetricChainDecomposition D) :
    ∃ D' : Finset (Finset (Finset β)), IsSymmetricChainDecomposition D' := by
  use D.image (fun C => C.image (fun A => A.image e));
  constructor;
  · intro C hC;
    obtain ⟨ C', hC', rfl ⟩ := Finset.mem_image.mp hC;
    obtain ⟨ start, k, h_chain, h_card, h_start_in, h_start_min, h_symm,
      ⟨ last, h_last_in, h_last_max, h_last_card ⟩ ⟩ := hD.1 C' hC';
    refine ⟨ start.image e, k, ?_, ?_, ?_, ?_, ?_, ⟨ last.image e, ?_, ?_, ?_ ⟩ ⟩;
    · intro x hx y hy aesop;
      obtain ⟨ A, hA, rfl ⟩ := Finset.mem_image.mp hx
      obtain ⟨ B, hB, rfl ⟩ := Finset.mem_image.mp hy
      specialize h_chain ( show A ∈ C' from hA ) ( show B ∈ C' from hB )
      simp_all +decide [ Finset.subset_iff ] ;
      exact h_chain fun a => aesop (congrArg (Finset.image ⇑e) a);
    · rw [ Finset.card_image_of_injective _
        (fun x y hxy => by
          simpa using Finset.image_injective e.injective hxy), h_card ];
    · exact Finset.mem_image_of_mem _ h_start_in;
    · simp +contextual [ Finset.image_subset_iff ];
      exact fun A hA x hx => h_start_min A hA hx;
    · simp_all +decide [ Finset.card_image_of_injective _ e.injective ];
      exact Fintype.card_congr e;
    · exact Finset.mem_image_of_mem _ h_last_in;
    · simp +contextual [ Finset.image_subset_iff ];
      exact fun A hA x hx => h_last_max A hA hx;
    · simp_all +decide [ Finset.card_image_of_injective _ e.injective ];
  · intro A;
    obtain ⟨ C, hC₁, hC₂ ⟩ := hD.2 ( A.image e.symm );
    use Finset.image (fun A => Finset.image e A) C;
    refine ⟨ ⟨ Finset.mem_image_of_mem _ hC₁.1, ?_ ⟩, ?_ ⟩;
    · simp +decide;
      exact ⟨ _, hC₁.2, by rw [ Finset.image_image ] ; aesop ⟩;
    · rintro y ⟨ hy₁, hy₂ ⟩;
      obtain ⟨ C', hC'₁, rfl ⟩ := Finset.mem_image.mp hy₁;
      specialize hC₂ C' ⟨ hC'₁, by
        rw [ Finset.mem_image ] at hy₂
        obtain ⟨ B, hB₁, rfl ⟩ := hy₂
        simp +decide [ Finset.image_image ] ;
        exact hB₁ ⟩ ; aesop

lemma exists_SCD_fin (n : ℕ) :
    ∃ D : Finset (Finset (Finset (Fin n))), IsSymmetricChainDecomposition D := by
  induction n with
  | zero =>
    exact scd_equiv finZeroEquiv.symm {{(∅ : Finset Empty)}} scd_empty
  | succ n ih =>
    obtain ⟨D, hD⟩ := ih
    obtain ⟨D', hD'⟩ := scd_option D hD
    exact scd_equiv (finSuccEquiv n).symm D' hD'

lemma exists_SCD (α : Type*) [Fintype α] :
    ∃ D : Finset (Finset (Finset α)), IsSymmetricChainDecomposition D := by
  obtain ⟨D, hD⟩ := exists_SCD_fin (Fintype.card α)
  exact scd_equiv (Fintype.equivFin α).symm D hD

lemma kleitman_bound_unique_proj_C {α : Type*} [Finite α] (T : Set α)
    (C D : Finset (Finset α))
    (hD : IsChain (· ⊆ ·) (D : Set (Finset α)))
    (h_suppC : ∀ A ∈ C, (A : Set α) ⊆ T)
    (h_suppD : ∀ B ∈ D, (B : Set α) ⊆ Tᶜ)
    (F_part : Set (Finset α))
    (h_inter : ∀ A B, A ∈ F_part → B ∈ F_part → A ⊂ B →
        (((B : Set α) \ A) ∩ T).Nonempty ∧ (((B : Set α) \ A) ∩ Tᶜ).Nonempty)
    (h_subset : F_part ⊆ {U ∪ V | (U ∈ C) (V ∈ D)})
    (X Y : Finset α) (hX : X ∈ F_part) (hY : Y ∈ F_part)
    (h_eq : (X : Set α) ∩ T = (Y : Set α) ∩ T) : X = Y := by
      classical
      letI := Fintype.ofFinite α
      -- By h_subset, there exist Ux, Vx, Uy, Vy such that X = Ux ∪ Vx and Y = Uy ∪ Vy.
      obtain ⟨Ux, Vx, hx⟩ : ∃ Ux Vx, Ux ∈ C ∧ Vx ∈ D ∧ X = Ux ∪ Vx := by
        simpa [ eq_comm ] using h_subset hX
      obtain ⟨Uy, Vy, hy⟩ : ∃ Uy Vy, Uy ∈ C ∧ Vy ∈ D ∧ Y = Uy ∪ Vy := by
        simpa [ eq_comm ] using h_subset hY;
      -- By h_suppC and h_suppD, we know that Ux = Uy and Vx ⊆ Vy or Vy ⊆ Vx.
      have hU_eq : Ux = Uy := by
        ext a
        constructor
        · intro ha
          have haT : a ∈ T := h_suppC Ux hx.1 ha
          have hxmem : a ∈ (X : Set α) ∩ T := by
            constructor
            · change a ∈ X
              rw [hx.2.2]
              exact Finset.mem_union_left Vx ha
            · exact haT
          have hymem : a ∈ (Y : Set α) ∩ T := by
            rw [h_eq] at hxmem
            exact hxmem
          have hay : a ∈ Y := hymem.1
          change a ∈ Y at hay
          rw [hy.2.2, Finset.mem_union] at hay
          rcases hay with hauy | havy
          · exact hauy
          · exact False.elim ((h_suppD Vy hy.2.1 havy) haT)
        · intro ha
          have haT : a ∈ T := h_suppC Uy hy.1 ha
          have hymem : a ∈ (Y : Set α) ∩ T := by
            constructor
            · change a ∈ Y
              rw [hy.2.2]
              exact Finset.mem_union_left Vy ha
            · exact haT
          have hxmem : a ∈ (X : Set α) ∩ T := by
            rw [← h_eq] at hymem
            exact hymem
          have hax : a ∈ X := hxmem.1
          change a ∈ X at hax
          rw [hx.2.2, Finset.mem_union] at hax
          rcases hax with haux | havx
          · exact haux
          · exact False.elim ((h_suppD Vx hx.2.1 havx) haT)
      have hV_subset : Vx ⊆ Vy ∨ Vy ⊆ Vx := by
        exact hD.total hx.2.1 hy.2.1 |> Or.imp id fun h => h.trans ( Finset.Subset.refl _ ) ;
      simp_all +decide [ Set.Nonempty, Set.ext_iff ];
      grind

/-- The core local bound for the Kleitman argument on a product of two chains. -/
lemma kleitman_grid_bound {α : Type*} [Finite α] (T : Set α)
    (C D : Finset (Finset α))
    (hC : IsChain (· ⊆ ·) (C : Set (Finset α)))
    (hD : IsChain (· ⊆ ·) (D : Set (Finset α)))
    (h_suppC : ∀ A ∈ C, (A : Set α) ⊆ T)
    (h_suppD : ∀ B ∈ D, (B : Set α) ⊆ Tᶜ)
    (F_part : Set (Finset α))
    (h_inter : ∀ A B, A ∈ F_part → B ∈ F_part → A ⊂ B →
        (((B : Set α) \ A) ∩ T).Nonempty ∧ (((B : Set α) \ A) ∩ Tᶜ).Nonempty)
    (h_subset : F_part ⊆ {U ∪ V | (U ∈ C) (V ∈ D)}) :
    F_part.ncard ≤ min C.card D.card := by
  classical
  letI := Fintype.ofFinite α
  have h_card_le_C : F_part.ncard ≤ C.card := by
    have h_card_le_C :
        F_part.ncard ≤
          (Finset.image
            (fun X => X ∩ Finset.filter (fun x => x ∈ T) Finset.univ)
            (Finset.filter (fun X => X ∈ F_part) Finset.univ)).card := by
      rw [ ← Set.ncard_coe_finset ];
      apply Set.ncard_le_ncard_of_injOn;
      any_goals exact Set.toFinite _;
      case f => exact fun X => X ∩ Finset.filter ( fun x => x ∈ T ) Finset.univ;
      · grind;
      · intro X hX Y hY h_eq;
        apply kleitman_bound_unique_proj_C T C D hD h_suppC h_suppD F_part
          h_inter h_subset X Y hX hY;
        simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
    refine h_card_le_C.trans ( Finset.card_le_card ?_ );
    intro aesop;
    simp +zetaDelta at *;
    intro x hx hx'
    obtain ⟨ U, hU, V, hV, rfl ⟩ := h_subset hx
    simp_all +decide [ Finset.ext_iff, Set.subset_def ] ;
    convert hU using 1;
    grind;
  refine le_min h_card_le_C ( ?_ : F_part.ncard ≤ D.card );
  -- By definition of $F_part$, every $X \in F_part$ has the form $U \cup V$.
  have h_exists_UV : ∀ X ∈ F_part, ∃ U ∈ C, ∃ V ∈ D, X = U ∪ V := by
    exact fun X hX => by
      obtain ⟨ U, hU, V, hV, rfl ⟩ := h_subset hX
      exact ⟨ U, hU, V, hV, rfl ⟩
  -- This lets us choose the D-coordinate function on `F_part`.
  have h_f :
      ∃ f : Finset α → Finset α,
        (∀ X ∈ F_part, f X ∈ D) ∧
          (∀ X Y, X ∈ F_part → Y ∈ F_part → X ≠ Y → f X ≠ f Y) := by
    choose! U hU V hV hUV using h_exists_UV;
    refine ⟨ V, hV, fun X Y hX hY hne h => ?_ ⟩;
    -- Since $V X = V Y$, the chain order puts one chosen U below the other.
    have h_subset : X ⊂ Y ∨ Y ⊂ X := by
      have h_subset : U X ⊆ U Y ∨ U Y ⊆ U X := by
        exact hC.total ( hU X hX ) ( hU Y hY );
      grind;
    rcases h_subset with ( h_subset | h_subset );
    · obtain ⟨ x, hx ⟩ := h_inter X Y hX hY h_subset |>.2;
      grind;
    · specialize h_inter Y X hY hX h_subset;
      obtain ⟨ x, hx ⟩ := h_inter.2;
      grind;
  obtain ⟨ f, hf₁, hf₂ ⟩ := h_f;
  have h_f_image : (Set.image f F_part).ncard ≤ D.card := by
    rw [ ← Set.ncard_coe_finset ]
    exact Set.ncard_le_ncard
      ( Set.image_subset_iff.mpr fun x hx => Finset.mem_coe.mpr ( hf₁ x hx ) )
  rwa [ Set.InjOn.ncard_image fun X hX Y hY hXY => by
    contrapose! hXY
    exact hf₂ X Y hX hY hXY ] at h_f_image

/-- Mapping a chain from a subtype preserves the chain property. -/
lemma map_chain_is_chain {α β : Type*} [Finite α] [Finite β] (emb : β ↪ α)
    (C : Finset (Finset β))
    (hC : IsChain (· ⊆ ·) (C : Set (Finset β))) :
    IsChain (· ⊆ ·) ((C.map (Finset.mapEmbedding emb).toEmbedding) : Set (Finset α)) := by
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  intro A hA B hB hneq
  -- Lift A and B back to C
  change A ∈ C.map (Finset.mapEmbedding emb).toEmbedding at hA
  change B ∈ C.map (Finset.mapEmbedding emb).toEmbedding at hB
  rw [Finset.mem_map] at hA hB
  rcases hA with ⟨a, ha, rfl⟩
  rcases hB with ⟨b, hb, rfl⟩
  -- Use chain property of C
  have h_eq : a ≠ b := by
    intro h_eq
    apply hneq
    congr
  rcases hC ha hb h_eq with (h_sub | h_sub)
  · left
    exact Finset.map_subset_map.mpr h_sub
  · right
    exact Finset.map_subset_map.mpr h_sub

/-- Mapping a chain from a subtype T to alpha lands in T. -/
lemma map_chain_support {α : Type*} [Finite α] (T : Set α)
    (emb : T ↪ α) (h_emb : ∀ x, emb x ∈ T)
    (C : Finset (Finset T)) :
    let C' := C.map (Finset.mapEmbedding emb).toEmbedding
    ∀ A ∈ C', (A : Set α) ⊆ T := by
  classical
  letI := Fintype.ofFinite α
  intro C' A hA
  rw [Finset.mem_map] at hA
  rcases hA with ⟨B, _, rfl⟩
  intro x hx
  change x ∈ B.map emb at hx
  rw [Finset.mem_map] at hx
  rcases hx with ⟨b, _, rfl⟩
  exact h_emb b

/-- The rectangles formed by SCDs of T and Tc are disjoint. (from Aristotle) -/
lemma scd_partition_disjoint {α : Type*} [Fintype α] (T : Set α) [DecidablePred (· ∈ T)]
    (CT : Finset (Finset (Finset T))) (DTC : Finset (Finset (Finset (Tᶜ : Set α))))
    (hCT : IsSymmetricChainDecomposition CT)
    (hDTC : IsSymmetricChainDecomposition DTC) :
    let embT : T ↪ α := Function.Embedding.subtype _
    let embTC : (Tᶜ : Set α) ↪ α := Function.Embedding.subtype _
    let P (C D) := {U.map embT ∪ V.map embTC | (U ∈ C) (V ∈ D)}
    ∀ C1 ∈ CT, ∀ D1 ∈ DTC, ∀ C2 ∈ CT, ∀ D2 ∈ DTC, (C1, D1) ≠ (C2, D2) →
    Disjoint (P C1 D1) (P C2 D2) := by
  simp +zetaDelta at *;
  intro C1 hC1 D1 hD1 C2 hC2 D2 hD2 hne;
  rw [ Set.disjoint_left ];
  rintro x ⟨ U1, hU1, V1, hV1, rfl ⟩ ⟨ U2, hU2, V2, hV2, hx ⟩;
  -- Since $U1 \cup V1 = U2 \cup V2$, we have $U1 = U2$ and $V1 = V2$.
  have h_eq : U1 = U2 ∧ V1 = V2 := by
    have h_eq : U1 = U2 := by
      ext x; replace hx := Finset.ext_iff.mp hx ( Subtype.mk x ( by aesop ) ) ; aesop;
    simp_all +decide [ Finset.ext_iff ];
    intro a ha; specialize hx a; aesop;
  have := hCT.2 U1; have := hDTC.2 V1; simp_all +decide [ ExistsUnique ] ;
  grind

/-- The rectangles formed by SCDs of T and Tc cover the power set. -/
-- from aristotle
lemma scd_partition_cover {α : Type*} [Fintype α] (T : Set α) [DecidablePred (· ∈ T)]
    (CT : Finset (Finset (Finset T))) (DTC : Finset (Finset (Finset (Tᶜ : Set α))))
    (hCT : IsSymmetricChainDecomposition CT)
    (hDTC : IsSymmetricChainDecomposition DTC) :
    let embT : T ↪ α := Function.Embedding.subtype _
    let embTC : (Tᶜ : Set α) ↪ α := Function.Embedding.subtype _
    let P (C D) := {U.map embT ∪ V.map embTC | (U ∈ C) (V ∈ D)}
    Set.univ = ⋃ (C ∈ CT) (D ∈ DTC), P C D := by
  have := hCT.2;
  have := hDTC.2;
  ext x;
  simp +decide [ Finset.ext_iff ];
  obtain ⟨ U, hU ⟩ :=
    ‹∀ A : Finset T, ∃! C : Finset ( Finset T ), C ∈ CT ∧ A ∈ C›
      ( Finset.filter ( fun y => y.val ∈ x ) Finset.univ );
  obtain ⟨ V, hV ⟩ :=
    ‹∀ A : Finset ( Tᶜ : Set α ),
      ∃! C : Finset ( Finset ( Tᶜ : Set α ) ), C ∈ DTC ∧ A ∈ C›
      ( Finset.filter ( fun y => y.val ∈ x ) Finset.univ );
  refine ⟨ U, hU.1.1, V, hV.1.1,
    Finset.filter ( fun y : T => y.val ∈ x ) Finset.univ, hU.1.2,
    Finset.filter ( fun y : ( Tᶜ : Set α ) => y.val ∈ x ) Finset.univ, hV.1.2, ?_ ⟩;
  intro a; by_cases ha : a ∈ T <;> simp +decide [ ha ] ;

/-- The set of elements of rank `k` in the power set of `α`. -/
def rankSet (α : Type*) [Fintype α] (k : ℕ) : Set (Finset α) :=
  {s | s.card = k}

/-- A symmetric chain covers a contiguous range of ranks. -/
lemma IsSymmetricChain_ranks {α : Type*} [Fintype α] {C : Finset (Finset α)}
    (hS : IsSymmetricChain C) :
    ∃ (k : ℕ), ∀ r, (rankSet α r ∩ C).Nonempty ↔ k ≤ r ∧ r ≤ Fintype.card α - k := by
  obtain
    ⟨start, k, h_chain, h_card, h_start_in, h_start_min, h_symm,
      ⟨last, h_last_in, h_last_max, h_last_card⟩⟩ := hS
  use start.card
  intro r
  let ranks := C.image Finset.card
  have h_inj : Set.InjOn Finset.card (C : Set (Finset α)) := by
    intro X hX Y hY h_eq
    rcases h_chain.total (Finset.mem_coe.mp hX) (Finset.mem_coe.mp hY) with hsub | hsub
    · exact Finset.eq_of_subset_of_card_le hsub h_eq.ge
    · exact (Finset.eq_of_subset_of_card_le hsub h_eq.le).symm
  have h_ranks_card : ranks.card = k + 1 := by
    rw [Finset.card_image_of_injOn h_inj, h_card]
  have h_ranks_eq : ranks = Finset.Icc start.card (start.card + k) := by
    apply Finset.eq_of_subset_of_card_le
    · intro r' hr'
      obtain ⟨X, hXC, rfl⟩ := Finset.mem_image.mp hr'
      rw [Finset.mem_Icc]
      exact
        ⟨Finset.card_le_card (h_start_min X hXC),
          (Finset.card_le_card (h_last_max X hXC)).trans h_last_card.le⟩
    · rw [h_ranks_card, Nat.card_Icc]; omega
  have h_bound : start.card + k = Fintype.card α - start.card := by omega
  constructor
  · rintro ⟨X, rfl, hXC⟩
    have : X.card ∈ ranks := Finset.mem_image_of_mem _ hXC
    rw [h_ranks_eq, Finset.mem_Icc, h_bound] at this
    exact this
  · intro h
    have h_in_ranks : r ∈ ranks := by
      rw [h_ranks_eq, Finset.mem_Icc, h_bound]
      exact h
    obtain ⟨X, hXC, rfl⟩ := Finset.mem_image.mp h_in_ranks
    exact ⟨X, rfl, hXC⟩

/-- Each symmetric chain intersects the middle rank exactly once. -/
lemma IsSymmetricChain_inter_middle {α : Type*} [Fintype α] {C : Finset (Finset α)}
    (hS : IsSymmetricChain C) :
    ((C : Set (Finset α)) ∩ rankSet α (Fintype.card α / 2)).ncard = 1 := by
  obtain ⟨k, h_ranks⟩ := IsSymmetricChain_ranks hS
  have h_mid : k ≤ Fintype.card α / 2 ∧ Fintype.card α / 2 ≤ Fintype.card α - k := by
    obtain
      ⟨start, k', h_chain, h_card, h_start_in, h_start_min, h_symm,
        ⟨last, h_last_in, h_last_max, h_last_card⟩⟩ := hS
    have h1 := (h_ranks start.card).mp ⟨start, rfl, h_start_in⟩
    have h2 := (h_ranks last.card).mp ⟨last, rfl, h_last_in⟩
    constructor
    · apply h1.1.trans; omega
    · apply le_trans _ h2.2; omega
  have h_nonempty := (h_ranks (Fintype.card α / 2)).mpr h_mid
  obtain ⟨X, hX_rank, hXC⟩ := h_nonempty
  have h_fin :
      ((C : Set (Finset α)) ∩ rankSet α (Fintype.card α / 2)).Finite :=
    (Finset.finite_toSet C).inter_of_left _
  apply Set.ncard_eq_one.mpr
  use X
  ext Y
  constructor
  · rintro ⟨hYC, hY_rank⟩
    obtain ⟨start, k', h_chain, -, -, -, -, -⟩ := hS
    have h_card_eq : X.card = Y.card := hX_rank.trans hY_rank.symm
    rw [Set.mem_singleton_iff]
    rcases h_chain.total hXC hYC with hsub | hsub
    · exact (Finset.eq_of_subset_of_card_le hsub h_card_eq.ge).symm
    · exact Finset.eq_of_subset_of_card_le hsub h_card_eq.le
  · rintro h; rw [Set.mem_singleton_iff] at h; subst h; exact ⟨hXC, hX_rank⟩

/-- The size of the intersection of two intervals centered around the same point. (by Aristotle) -/
lemma symmetric_interval_inter_card {nA nB kC kD S : ℕ}
    (h_nA : 2 * kC ≤ nA) (h_nB : 2 * kD ≤ nB) (h_S : S = (nA + nB) / 2) :
    let IC := Finset.Icc kC (nA - kC)
    let IC_shifted := Finset.Icc (S - (nB - kD)) (S - kD)
    (IC ∩ IC_shifted).card = min (nA - 2 * kC + 1) (nB - 2 * kD + 1) := by
  simp +zetaDelta at *;
  rw [
    show Finset.Icc kC ( nA - kC ) ∩
        Finset.Icc ( S - ( nB - kD ) ) ( S - kD ) =
        Finset.Icc ( Max.max kC ( S - ( nB - kD ) ) )
          ( Min.min ( nA - kC ) ( S - kD ) ) from ?_,
    Nat.card_Icc ];
  · omega;
  · ext; aesop

/-- Filtering a product of two intervals by their sum is equivalent to an
intersection of intervals. -/
lemma filter_Icc_sum_eq_S_card {nA nB kC kD S : ℕ} (hS : S = (nA + nB) / 2)
    (h_nA_2kC : 2 * kC ≤ nA) (h_nB_2kD : 2 * kD ≤ nB) :
    let IC := Finset.Icc kC (nA - kC)
    let ID := Finset.Icc kD (nB - kD)
    let IC_shifted := Finset.Icc (S - (nB - kD)) (S - kD)
    (Finset.filter (fun p : ℕ × ℕ => p.1 + p.2 = S) (IC ×ˢ ID)).card =
      (IC ∩ IC_shifted).card := by
  intro IC ID IC_shifted
  let f : ℕ × ℕ → ℕ := fun p => p.1
  have hf :
      ∀ p ∈ (Finset.filter (fun p : ℕ × ℕ => p.1 + p.2 = S) (IC ×ˢ ID)),
        f p ∈ IC ∩ IC_shifted := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_inter, IC, ID,
      IC_shifted, f, Finset.mem_Icc] at hp ⊢
    repeat constructor <;> (zify at *; omega)
  have hf_inj :
      Set.InjOn f
        ((Finset.filter (fun p : ℕ × ℕ => p.1 + p.2 = S) (IC ×ˢ ID)) :
          Set (ℕ × ℕ)) := by
    intro p1 h1 p2 h2 heq
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at h1 h2
    simp only [f, IC, ID, Finset.mem_Icc] at h1 h2 heq
    ext
    · exact heq
    · zify at *; omega
  rw [← Finset.card_image_of_injOn hf_inj]
  congr 1; ext r; constructor
  · intro h; rw [Finset.mem_image] at h; obtain ⟨p, hp, rfl⟩ := h; exact hf p hp
  · intro hr
    rw [Finset.mem_inter, Finset.mem_Icc, Finset.mem_Icc] at hr
    dsimp [IC, ID, f, IC_shifted] at *
    have hr_le_S : r ≤ S := by zify at *; omega
    simp only [Finset.mem_image, Prod.exists]
    use r, S - r
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    repeat' constructor <;> try (zify at *; omega)

/-- The intersection of a rectangle (product of two chains) with the global middle rank.
    The size of this intersection is exactly the width of the rectangle, min(|C|, |D|). -/
lemma rectangle_middle_inter_size {α β : Type*} [Fintype α] [Fintype β]
    {C : Finset (Finset α)} {D : Finset (Finset β)}
    (hC : IsSymmetricChain C) (hD : IsSymmetricChain D) :
    let n := Fintype.card α + Fintype.card β
    let P : Set (Finset (α ⊕ β)) :=
      {U.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ V.map ⟨Sum.inr, Sum.inr_injective⟩ |
        (U ∈ C) (V ∈ D)}
    (P ∩ rankSet (α ⊕ β) (n / 2)).ncard = min C.card D.card := by
  intro total_n P_val
  let p_emb : Finset α × Finset β → Finset (α ⊕ β) := fun p =>
    p.1.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ p.2.map ⟨Sum.inr, Sum.inr_injective⟩
  have h_f_inj : Function.Injective p_emb := by
    intro p1 p2 h; apply Prod.ext
    · ext x
      have h_mem := congrArg (fun s => Sum.inl x ∈ s) h
      simp [p_emb] at h_mem
      exact h_mem
    · ext x
      have h_mem := congrArg (fun s => Sum.inr x ∈ s) h
      simp [p_emb] at h_mem
      exact h_mem
  have h_card_sum : ∀ U V, (p_emb (U, V)).card = U.card + V.card := by
    intro U V; rw [Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]; rintro x h1 h2; simp [Finset.mem_map] at h1 h2
      obtain ⟨a, -, rfl⟩ := h1; obtain ⟨b, -, hb⟩ := h2; cases hb
  let Pairs :=
    { p : Finset α × Finset β |
      p.1 ∈ C ∧ p.2 ∈ D ∧ p.1.card + p.2.card = total_n / 2 }
  have h_iso_set : (P_val ∩ rankSet (α ⊕ β) (total_n / 2)) = p_emb '' Pairs := by
    ext X; constructor
    · rintro ⟨⟨U, hUC, V, hVD, rfl⟩, hX_rank⟩
      exact ⟨(U, V), ⟨hUC, hVD, by simpa [p_emb, rankSet, h_card_sum] using hX_rank⟩, rfl⟩
    · rintro ⟨⟨U, V⟩, ⟨hUC, hVD, h_rank⟩, rfl⟩
      exact ⟨⟨U, hUC, V, hVD, rfl⟩, by simpa [p_emb, rankSet, h_card_sum] using h_rank⟩
  rw [h_iso_set, Set.ncard_image_of_injective Pairs h_f_inj]
  obtain ⟨kC, hRC⟩ := IsSymmetricChain_ranks hC
  obtain ⟨kD, hRD⟩ := IsSymmetricChain_ranks hD
  let nA := Fintype.card α
  let nB := Fintype.card β
  let S := total_n / 2
  let IC := Finset.Icc kC (nA - kC)
  let ID := Finset.Icc kD (nB - kD)
  have h_Pairs_fin : Pairs.Finite :=
    Set.Finite.subset (Finset.finite_toSet (C ×ˢ D)) (fun p hp => by
      simp [hp.1, hp.2.1])
  let fr : Finset α × Finset β → ℕ × ℕ := fun p => (p.1.card, p.2.card)
  have hr_inj : Set.InjOn fr ((C ×ˢ D : Finset _) : Set (Finset α × Finset β)) := by
    rintro ⟨U1, V1⟩ h1 ⟨U2, V2⟩ h2 h_eq
    simp at h1 h2; have h_eq' := Prod.ext_iff.1 h_eq
    obtain ⟨startC, kc, h_chainC, -⟩ := hC; obtain ⟨startD, kd, h_chainD, -⟩ := hD
    have hUeq : U1 = U2 := by
      rcases h_chainC.total h1.1 h2.1 with h | h
      · exact Finset.eq_of_subset_of_card_le h h_eq'.1.ge
      · exact (Finset.eq_of_subset_of_card_le h h_eq'.1.le).symm
    have hVeq : V1 = V2 := by
      rcases h_chainD.total h1.2 h2.2 with h | h
      · exact Finset.eq_of_subset_of_card_le h h_eq'.2.ge
      · exact (Finset.eq_of_subset_of_card_le h h_eq'.2.le).symm
    exact Prod.ext hUeq hVeq
  have h_Pairs_card :
      Pairs.ncard =
        (Finset.filter (fun (p : ℕ × ℕ) => p.1 + p.2 = S) (IC ×ˢ ID)).card := by
    have h_img :
        fr '' Pairs =
          ((Finset.filter (fun (p : ℕ × ℕ) => p.1 + p.2 = S) (IC ×ˢ ID)) :
            Set (ℕ × ℕ)) := by
      ext ⟨r1, r2⟩; constructor
      · rintro ⟨⟨U, V⟩, ⟨hUC, hVD, h_sum⟩, h_eq⟩
        have h1 : U.card = r1 := (Prod.ext_iff.1 h_eq).1
        have h2 : V.card = r2 := (Prod.ext_iff.1 h_eq).2
        rw [← h1, ← h2]; simp [IC, ID, h_sum, S]
        exact ⟨(hRC U.card).mp ⟨U, rfl, hUC⟩, (hRD V.card).mp ⟨V, rfl, hVD⟩⟩
      · rintro h; simp [IC, ID, S] at h
        obtain ⟨⟨hr1, hr2⟩, h_sum⟩ := h
        obtain ⟨U, rfl, hUC⟩ := (hRC r1).mpr hr1
        obtain ⟨V, rfl, hVD⟩ := (hRD r2).mpr hr2
        exact ⟨(U, V), ⟨hUC, hVD, h_sum⟩, rfl⟩
    rw [← Set.InjOn.ncard_image
      (hr_inj.mono (fun p hp => by
        simp [Pairs] at hp
        simp [hp.1, hp.2.1])), h_img]
    exact Set.ncard_coe_finset _
  rw [h_Pairs_card]
  have h_nA_2kC : 2 * kC ≤ nA := by
    obtain
      ⟨startC, k, h_chain, h_card, h_start_in, h_start_min, h_symm,
        ⟨last, h_last_in, h_last_max, h_last_card⟩⟩ := hC
    have h_start_mem : (rankSet α startC.card ∩ C).Nonempty :=
      ⟨startC, by simp [rankSet, h_start_in]⟩
    obtain ⟨h_low, h_high⟩ := (hRC startC.card).mp h_start_mem
    omega
  have h_nB_2kD : 2 * kD ≤ nB := by
    obtain
      ⟨startD, k, h_chain, h_card, h_start_in, h_start_min, h_symm,
        ⟨last, h_last_in, h_last_max, h_last_card⟩⟩ := hD
    have h_start_mem : (rankSet β startD.card ∩ D).Nonempty :=
      ⟨startD, by simp [rankSet, h_start_in]⟩
    obtain ⟨h_low, h_high⟩ := (hRD startD.card).mp h_start_mem
    omega
  rw [filter_Icc_sum_eq_S_card (by omega) h_nA_2kC h_nB_2kD]
  rw [symmetric_interval_inter_card h_nA_2kC h_nB_2kD (by rfl)]
  have h_C_card : C.card = nA - 2 * kC + 1 := by
    obtain
      ⟨startC, k, h_chain, h_card, h_start_in, h_start_min, h_symm,
        ⟨last, h_last_in, h_last_max, h_last_card⟩⟩ := hC
    have h_kC_val : kC = startC.card := by
      have h_start_mem : (rankSet α startC.card ∩ C).Nonempty :=
        ⟨startC, by simp [rankSet, h_start_in]⟩
      have h1 : kC ≤ startC.card := ((hRC startC.card).mp h_start_mem).1
      have h_kC_mem : kC ≤ kC ∧ kC ≤ Fintype.card α - kC := by
        obtain ⟨h_low, h_high⟩ := (hRC startC.card).mp h_start_mem
        exact ⟨le_rfl, h1.trans h_high⟩
      obtain ⟨X, hX_rank, hXC⟩ := (hRC kC).mpr h_kC_mem
      have h2 : startC.card ≤ kC := by
        rw [← hX_rank]
        exact Finset.card_le_card (h_start_min X hXC)
      omega
    rw [h_kC_val, h_card]; omega
  have h_D_card : D.card = nB - 2 * kD + 1 := by
    obtain
      ⟨startD, k, h_chain, h_card, h_start_in, h_start_min, h_symm,
        ⟨last, h_last_in, h_last_max, h_last_card⟩⟩ := hD
    have h_kD_val : kD = startD.card := by
      have h_start_mem : (rankSet β startD.card ∩ D).Nonempty :=
        ⟨startD, by simp [rankSet, h_start_in]⟩
      have h1 : kD ≤ startD.card := ((hRD startD.card).mp h_start_mem).1
      have h_kD_mem : kD ≤ kD ∧ kD ≤ Fintype.card β - kD := by
        obtain ⟨h_low, h_high⟩ := (hRD startD.card).mp h_start_mem
        exact ⟨le_rfl, h1.trans h_high⟩
      obtain ⟨X, hX_rank, hXD⟩ := (hRD kD).mpr h_kD_mem
      have h2 : startD.card ≤ kD := by
        rw [← hX_rank]
        exact Finset.card_le_card (h_start_min X hXD)
      omega
    rw [h_kD_val, h_card]; omega
  rw [h_C_card, h_D_card]

lemma sum_ncard_product_eq_ncard_biUnion {I J X : Type*}
    {s : Finset I} {t : Finset J} {f : I → J → Set X}
    (h_disj : (↑(s.product t) : Set (I × J)).PairwiseDisjoint (fun p => f p.1 p.2))
    (h_fin : ∀ i ∈ s, ∀ j ∈ t, (f i j).Finite) :
    ∑ i ∈ s, ∑ j ∈ t, (f i j).ncard = (⋃ p ∈ s.product t, f p.1 p.2).ncard := by
  classical
  have h_fin_map : ∀ p ∈ s.product t, (f p.1 p.2).Finite := fun p hp => by
    simp at hp; exact h_fin p.1 hp.1 p.2 hp.2
  let t_finset := s.product t
  have ht_fin : (↑t_finset : Set (I × J)).Finite := Finset.finite_toSet t_finset
  have h1 := Set.Finite.ncard_biUnion ht_fin h_fin_map h_disj
  have h2 := finsum_mem_eq_finite_toFinset_sum (fun p => (f p.1 p.2).ncard) ht_fin
  have h3 := Finset.sum_product (s := s) (t := t) (f := fun p => (f p.1 p.2).ncard)
  have h_eq : t_finset = ht_fin.toFinset := by simp
  have h_sum_prod_val :
      ∑ i ∈ s, ∑ j ∈ t, (f i j).ncard =
        ∑ p ∈ ht_fin.toFinset, (f p.1 p.2).ncard := by
    rw [h_eq.symm]; exact h3.symm
  exact h_sum_prod_val.trans (h2.symm.trans h1.symm)

/-- The combinatorial sum identity for partitioned products. -/
lemma scd_middle_rank_sum {G : Type*} [Fintype G] (T : Set G) [DecidablePred (· ∈ T)]
    (CT : Finset (Finset (Finset T))) (DTC : Finset (Finset (Finset (Tᶜ : Set G))))
    (hCT : IsSymmetricChainDecomposition CT)
    (hDTC : IsSymmetricChainDecomposition DTC) :
    let n := Fintype.card G
    let embT : T ↪ G := Function.Embedding.subtype _
    let embTC : (Tᶜ : Set G) ↪ G := Function.Embedding.subtype _
    let P (C : Finset (Finset T)) (D : Finset (Finset (Tᶜ : Set G))) : Set (Finset G) :=
       { (Finset.map embT U ∪ Finset.map embTC V : Finset G) | (U ∈ C) (V ∈ D) }
    (∑ C ∈ CT, ∑ D ∈ DTC, (P C D ∩ rankSet G (n / 2)).ncard) = n.choose (n / 2) := by
  have h_union :
      ⋃ C ∈ CT, ⋃ D ∈ DTC,
        {U.map (Function.Embedding.subtype fun x => x ∈ T) ∪
          V.map (Function.Embedding.subtype fun x => x ∈ Tᶜ) | (U ∈ C) (V ∈ D)} =
        Set.univ := by
    have := Erdos498.scd_partition_cover T CT DTC hCT hDTC;
    exact this.symm;
  convert
    Set.ncard_eq_toFinset_card'
      ( Set.univ ∩ Erdos498.rankSet G ( Fintype.card G / 2 ) ) using 1;
  · rw [ ← h_union, Set.ncard_eq_toFinset_card' ];
    rw [ Set.toFinset_card ];
    convert sum_ncard_product_eq_ncard_biUnion _ _;
    · rw [ Set.ncard_eq_toFinset_card' ];
      rw [ Fintype.card_of_subtype ];
      simp +decide [ Finset.mem_product ];
      exact fun x =>
        ⟨fun ⟨ a, b, h, h', hx ⟩ =>
          ⟨⟨a, h'.1, b, h'.2, h.choose, h.choose_spec.1,
            h.choose_spec.2.choose, h.choose_spec.2.choose_spec.1,
            h.choose_spec.2.choose_spec.2⟩, hx⟩,
        fun ⟨⟨a, ha, b, hb, U, hU, V, hV, hx⟩, hx'⟩ =>
          ⟨a, b, ⟨U, hU, V, hV, hx⟩, ⟨ha, hb⟩, hx'⟩⟩;
    · intro p hp q hq hpq;
      have h_disjoint :
          Disjoint
            ({U.map (Function.Embedding.subtype fun x => x ∈ T) ∪
              V.map (Function.Embedding.subtype fun x => x ∈ Tᶜ) |
              (U ∈ p.1) (V ∈ p.2)} : Set (Finset G))
            ({U.map (Function.Embedding.subtype fun x => x ∈ T) ∪
              V.map (Function.Embedding.subtype fun x => x ∈ Tᶜ) |
              (U ∈ q.1) (V ∈ q.2)} : Set (Finset G)) := by
        have := scd_partition_disjoint T CT DTC hCT hDTC;
        exact this _ ( Finset.mem_product.mp hp |>.1 ) _
          ( Finset.mem_product.mp hp |>.2 ) _
          ( Finset.mem_product.mp hq |>.1 ) _ ( Finset.mem_product.mp hq |>.2 )
          ( by simpa using hpq );
      exact Set.disjoint_left.mpr fun x hx₁ hx₂ => h_disjoint.le_bot ⟨ hx₁.1, hx₂.1 ⟩;
    · exact fun C hC D hD => Set.toFinite _;
  · simp +decide [ Erdos498.rankSet ]

/-- The global summation identity: sum of min chain lengths equals the central
binomial coefficient. -/
lemma scd_product_identity {α β : Type*} [Fintype α] [Fintype β]
    (Cα : Finset (Finset (Finset α))) (Cβ : Finset (Finset (Finset β)))
    (hα : IsSymmetricChainDecomposition Cα)
    (hβ : IsSymmetricChainDecomposition Cβ) :
    (∑ C ∈ Cα, ∑ D ∈ Cβ, min C.card D.card) =
    (Fintype.card α + Fintype.card β).choose ((Fintype.card α + Fintype.card β) / 2) := by
  let G := α ⊕ β; let n := Fintype.card G
  let P (C : Finset (Finset α)) (D : Finset (Finset β)) : Set (Finset G) :=
    { (U.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
        V.map ⟨Sum.inr, Sum.inr_injective⟩ : Finset G) | (U ∈ C) (V ∈ D) }
  have h_univ : (⋃ p ∈ Cα.product Cβ, P p.1 p.2) = Set.univ := by
    apply Set.eq_univ_of_forall; intro x
    let U_fin : Finset α := x.preimage Sum.inl (fun _ _ _ _ h => Sum.inl_injective h)
    let V_fin : Finset β := x.preimage Sum.inr (fun _ _ _ _ h => Sum.inr_injective h)
    obtain ⟨C, ⟨hC_mem, hU_in⟩, -⟩ := hα.2 U_fin
    obtain ⟨D, ⟨hD_mem, hV_in⟩, -⟩ := hβ.2 V_fin
    refine Set.mem_iUnion.mpr ⟨(C, D), Set.mem_iUnion.mpr ⟨(by simp [hC_mem, hD_mem]), ?_⟩⟩
    simp only [P, Set.mem_setOf_eq]; use U_fin, hU_in, V_fin, hV_in
    · ext z; rcases z with a|b <;> (simp; exact Finset.mem_preimage)
  have length_sum_congr : (∑ C ∈ Cα, ∑ D ∈ Cβ, min C.card D.card)
      = (∑ C ∈ Cα, ∑ D ∈ Cβ, (P C D ∩ rankSet G (n / 2)).ncard) := by
        apply Finset.sum_congr rfl; intro C hC; apply Finset.sum_congr rfl; intro D hD
        dsimp [P, n, G]; rw [Fintype.card_sum]
        exact (rectangle_middle_inter_size (hα.1 C hC) (hβ.1 D hD)).symm
  have h_disj :
      ((Cα.product Cβ : Set (Finset (Finset α) × Finset (Finset β))).PairwiseDisjoint
        (fun p => P p.1 p.2 ∩ rankSet G (n / 2))) := by
    rintro ⟨C1, D1⟩ hp1 ⟨C2, D2⟩ hp2 h_ne
    dsimp [Function.onFun]; rw [Set.disjoint_left]; rintro x ⟨hx1, -⟩ ⟨hx2, -⟩
    obtain ⟨U1, hU1, V1, hV1, rfl⟩ := hx1
    obtain ⟨U2, hU2, V2, hV2, hx_eq⟩ := hx2
    have h_eq : U1 = U2 ∧ V1 = V2 := by
      constructor <;> ext x
      · replace hx_eq := Finset.ext_iff.mp hx_eq (Sum.inl x)
        aesop
      · replace hx_eq := Finset.ext_iff.mp hx_eq (Sum.inr x)
        aesop
    have ⟨hU, hV⟩ := h_eq; subst hU; subst hV
    obtain ⟨hp1_1, hp1_2⟩ := Finset.mem_product.mp hp1
    obtain ⟨hp2_1, hp2_2⟩ := Finset.mem_product.mp hp2
    have h_uniq_C := (hα.2 U1).unique ⟨hp1_1, hU1⟩ ⟨hp2_1, hU2⟩
    have h_uniq_D := (hβ.2 V1).unique ⟨hp1_2, hV1⟩ ⟨hp2_2, hV2⟩
    exact h_ne (Prod.ext h_uniq_C h_uniq_D)
  calc
    (∑ C ∈ Cα, ∑ D ∈ Cβ, min C.card D.card)
      = (∑ C ∈ Cα, ∑ D ∈ Cβ, (P C D ∩ rankSet G (n / 2)).ncard) := length_sum_congr
    _ = (⋃ p ∈ Cα.product Cβ, P p.1 p.2 ∩ rankSet G (n / 2)).ncard := by
      exact sum_ncard_product_eq_ncard_biUnion h_disj (fun _ _ _ _ => Set.toFinite _)
    _ = (Fintype.card α + Fintype.card β).choose ((Fintype.card α + Fintype.card β) / 2) := by
      have h_eq :
          (⋃ p ∈ Cα.product Cβ, P p.1 p.2 ∩ rankSet G (n / 2)) =
            (⋃ p ∈ Cα.product Cβ, P p.1 p.2) ∩ rankSet G (n / 2) := by
        ext x; simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_and_right]
      rw [h_eq, h_univ, Set.univ_inter,
          Set.ncard_eq_toFinset_card (rankSet G (n / 2)) (Set.toFinite _)]
      simp [rankSet, n, G, Fintype.card_sum]

theorem kleitman_bound_theorem {α : Type*} [Fintype α] (F : Set (Set α))
  (T : Set α) :
  (∀ A B, A ∈ F → B ∈ F → A ⊂ B → (B \ A ∩ T).Nonempty ∧ (B \ A ∩ Tᶜ).Nonempty) →
  F.ncard ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  intro h_kleitman
  haveI : DecidablePred (· ∈ T) := Classical.decPred _
  let Tc := Tᶜ
  obtain ⟨CT, hCT⟩ := exists_SCD { x // x ∈ T }
  obtain ⟨DTC, hDTC⟩ := exists_SCD { x // x ∈ Tc }
  let embT : T ↪ α := Function.Embedding.subtype _
  let embTC : Tc ↪ α := Function.Embedding.subtype _
  -- F converted to Finsets
  let toFin : Set α → Finset α := fun s => s.toFinset
  let F_fin : Set (Finset α) := toFin '' F
  have F_card : F.ncard = F_fin.ncard := by
    rw [Set.InjOn.ncard_image]
    · apply Set.injOn_of_injective
      intro x y h; dsimp [toFin] at h
      exact Set.toFinset_inj.mp h
  let P (C : Finset (Finset T)) (D : Finset (Finset Tc)) :=
    {U.map embT ∪ V.map embTC | (U ∈ C) (V ∈ D)}
  let F_part (C : Finset (Finset T)) (D : Finset (Finset Tc)) := F_fin ∩ P C D
  have h_bound : ∀ C ∈ CT, ∀ D ∈ DTC, (F_part C D).ncard ≤ min C.card D.card := by
    intro C hCin D hDin
    let C' := C.map (Finset.mapEmbedding embT).toEmbedding
    let D' := D.map (Finset.mapEmbedding embTC).toEmbedding
    have hC' : IsChain (· ⊆ ·) (C' : Set (Finset α)) := by
      obtain ⟨_, _, h_chain, _, _, _⟩ := hCT.1 C hCin
      exact map_chain_is_chain embT C h_chain
    have hD' : IsChain (· ⊆ ·) (D' : Set (Finset α)) := by
      obtain ⟨_, _, h_chain, _, _, _⟩ := hDTC.1 D hDin
      exact map_chain_is_chain embTC D h_chain
    have h_suppC : ∀ A ∈ C', (A : Set α) ⊆ T :=
      map_chain_support T embT (fun x => x.2) C
    have h_suppD : ∀ B ∈ D', (B : Set α) ⊆ Tc :=
      map_chain_support Tc embTC (fun x => x.2) D
    have h_match : F_part C D = F_fin ∩ {U' ∪ V' | (U' ∈ C') (V' ∈ D')} := by
       ext S; constructor <;> intro hS
       · obtain ⟨h1, ⟨U, hU, V, hV, rfl⟩⟩ := hS
         refine ⟨h1, U.map embT, ?_, V.map embTC, ?_, rfl⟩
         · exact Finset.mem_map.mpr ⟨U, hU, rfl⟩
         · exact Finset.mem_map.mpr ⟨V, hV, rfl⟩
       · obtain ⟨h1, U', hU', V', hV', rfl⟩ := hS
         rw [Finset.mem_map] at hU' hV'
         obtain ⟨U, hU, rfl⟩ := hU'
         obtain ⟨V, hV, rfl⟩ := hV'
         exact ⟨h1, U, hU, V, hV, rfl⟩
    have h_card_C : C'.card = C.card := Finset.card_map _
    have h_card_D : D'.card = D.card := Finset.card_map _
    rw [h_match, ←h_card_C, ←h_card_D]
    apply kleitman_grid_bound T C' D' hC' hD' h_suppC h_suppD
    · intro A B hA hB hsub
      obtain ⟨hAF, -⟩ := hA
      obtain ⟨hBF, -⟩ := hB
      obtain ⟨A0, hA0, rfl⟩ := hAF
      obtain ⟨B0, hB0, rfl⟩ := hBF
      dsimp [toFin] at hsub
      have h_ssub : A0 ⊂ B0 := Set.toFinset_ssubset_toFinset.mp hsub
      simpa [toFin] using h_kleitman A0 B0 hA0 hB0 h_ssub
    · exact fun x hx => hx.2
  have h_cover : F_fin = ⋃ x ∈ (CT.product DTC), (F_part x.1 x.2) := by
    ext S; constructor
    · intro hS
      have hS_univ : S ∈ Set.univ := Set.mem_univ S
      rw [scd_partition_cover T CT DTC hCT hDTC] at hS_univ
      simp only [Set.mem_iUnion] at hS_univ
      rcases hS_univ with ⟨C, hCin, D, hDin, hS_P⟩
      rw [Set.mem_iUnion]; use (C, D)
      rw [Set.mem_iUnion]; use Finset.mem_product.mpr ⟨hCin, hDin⟩
      exact ⟨hS, hS_P⟩
    · intro hS
      simp only [Set.mem_iUnion] at hS
      rcases hS with ⟨x, hx, hS_in_part⟩
      exact hS_in_part.1
  have total_card : F_fin.ncard = ∑ C ∈ CT, ∑ D ∈ DTC, (F_part C D).ncard := by
    classical
    have hf_fin : F_fin.Finite := Set.finite_univ.subset (Set.subset_univ F_fin)
    have hf_part : ∀ C D, (F_part C D).Finite := fun C D =>
      hf_fin.subset (@Set.inter_subset_left _ F_fin (P C D))
    rw [h_cover]
    have hf_union : (⋃ x ∈ CT.product DTC, F_part x.1 x.2).Finite := by
      rw [←h_cover]
      exact hf_fin
    rw [Set.ncard_eq_toFinset_card _ hf_union]
    have h_toF :
        hf_union.toFinset =
          (CT.product DTC).biUnion (fun p => (hf_part p.1 p.2).toFinset) := by
      ext S
      rw [Finset.mem_biUnion, Set.Finite.mem_toFinset hf_union]
      constructor
      · intro h
        simp only [Set.mem_iUnion] at h
        rcases h with ⟨p, hp, hS⟩
        exact ⟨p, hp, (Set.Finite.mem_toFinset _).mpr hS⟩
      · rintro ⟨p, hp, hS_fin⟩
        simp only [Set.mem_iUnion]
        use p, hp
        exact (Set.Finite.mem_toFinset _).mp hS_fin
    rw [h_toF, Finset.card_biUnion]
    · erw [Finset.sum_product]
      apply Finset.sum_congr rfl; intro C hC; apply Finset.sum_congr rfl; intro D hD
      exact (Set.ncard_eq_toFinset_card _ (hf_part C D)).symm
    · intro p hp q hq hne
      dsimp [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx
      rw [Set.Finite.mem_toFinset (hf_part p.1 p.2)] at hx
      rw [Set.Finite.mem_toFinset (hf_part q.1 q.2)]
      have disj :=
        scd_partition_disjoint T CT DTC hCT hDTC p.1
          (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2 q.1
          (Finset.mem_product.mp hq).1 q.2 (Finset.mem_product.mp hq).2 hne
      exact
        Set.disjoint_left.mp
          (Set.disjoint_of_subset
            (@Set.inter_subset_right _ F_fin (P p.1 p.2))
            (@Set.inter_subset_right _ F_fin (P q.1 q.2)) disj) hx
  have split_card : Fintype.card α = Fintype.card ↑T + Fintype.card ↑Tc := by
    classical rw [← Fintype.card_sum]; exact Fintype.card_congr (Equiv.sumCompl T).symm
  rw [F_card, total_card, split_card]
  apply le_trans (Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun D hD => h_bound C hC D hD)
  exact le_of_eq (scd_product_identity CT DTC hCT hDTC)

lemma kleitman_case_T_empty (z : Fin n → ℂ) (hz : ∀ i, 1 < ‖z i‖) (c : ℂ)
    (A B : Finset (Fin n)) (hAB : A ⊂ B)
    (εA εB : Fin n → ℤ)
    (w : Fin n → ℂ) (hw_align : ∀ i, IsAlignedZ (z i) (w i))
    (h_diff : (∑ i, (εB i : ℂ) * z i) - (∑ i, (εA i : ℂ) * z i) = 2 * ∑ i ∈ B \ A, w i)
    (validA : (∑ i, (εA i : ℂ) * z i) ∈ Metric.closedBall c 1)
    (validB : (∑ i, (εB i : ℂ) * z i) ∈ Metric.closedBall c 1)
    (h_T_empty :
      ((B : Set (Fin n)) \ (A : Set (Fin n)) ∩
        {i : Fin n | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}) = ∅) :
    False := by
  let val_aligned_set := {i : Fin n | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}
  let S := B \ A
  have hS_ne : S.Nonempty := by
    obtain ⟨x, hx_sub⟩ := Finset.exists_of_ssubset hAB
    use x; exact Finset.mem_sdiff.mpr hx_sub
  have h_pure' : ∀ i ∈ S, (w i).re < 0 ∧ 0 ≤ (w i).im := by
    intro i hi
    have zi_nz : ‖z i‖ ≠ 0 := by have := hz i; linarith
    have uhp := IsAlignedZ_isUHP (hw_align i)
    unfold inUHP at uhp
    have w_eq : w i = Classical.choose (exists_unique_alignedZ (z i)) := by
      obtain ⟨x, hx, u⟩ := exists_unique_alignedZ (z i)
      rw [u _ (hw_align i), u _ (Classical.choose_spec (exists_unique_alignedZ (z i))).1]
    have hi_S : i ∈ (↑B : Set (Fin n)) \ ↑A := by
      obtain ⟨hiB, hiA⟩ := Finset.mem_sdiff.mp hi
      exact ⟨Finset.mem_coe.mpr hiB, fun h => hiA (Finset.mem_coe.mp h)⟩
    have not_T : i ∉ val_aligned_set := by
      intro h; exact Set.eq_empty_iff_forall_notMem.mp h_T_empty i ⟨hi_S, h⟩
    have im_pos : 0 ≤ (w i).im := by
      rcases uhp with h|⟨h,_⟩ <;> linarith
    have re_neg : (w i).re < 0 := by
      dsimp [val_aligned_set] at not_T
      rw [w_eq]; linarith [not_T]
    exact ⟨re_neg, im_pos⟩
  have h_norm : 1 < ‖∑ i ∈ B \ A, w i‖ := by
    apply pure_sum_norm_gt_sqrt _ _ hS_ne (Or.inr h_pure')
    intro i hi
    rcases (hw_align i) with ⟨s, hs, h_eq⟩
    rw [h_eq, Complex.norm_mul]; norm_cast
    rw [IsBaseSign_abs_eq_one hs]; simp; exact hz i
  have : ‖(∑ i, (εB i : ℂ) * z i) - (∑ i, (εA i : ℂ) * z i)‖ > 2 := by
    rw [h_diff, Complex.norm_mul, Complex.norm_two]
    have : 1 < ‖∑ i ∈ B \ A, w i‖ := h_norm
    linarith
  have dist_val : ‖(∑ i, (εB i : ℂ) * z i) - (∑ i, (εA i : ℂ) * z i)‖ ≤ 2 := by
    rw [←dist_eq_norm]
    apply le_trans (dist_triangle (∑ i, (εB i : ℂ) * z i) c (∑ i, (εA i : ℂ) * z i))
    rw [dist_comm c (∑ i, (εA i : ℂ) * z i)]
    rw [mem_closedBall] at validA validB
    linarith
  linarith

lemma kleitman_case_Tc_empty (z : Fin n → ℂ) (hz : ∀ i, 1 < ‖z i‖) (c : ℂ)
    (A B : Finset (Fin n)) (hAB : A ⊂ B)
    (εA εB : Fin n → ℤ)
    (w : Fin n → ℂ) (hw_align : ∀ i, IsAlignedZ (z i) (w i))
    (h_diff : (∑ i, (εB i : ℂ) * z i) - (∑ i, (εA i : ℂ) * z i) = 2 * ∑ i ∈ B \ A, w i)
    (validA : (∑ i, (εA i : ℂ) * z i) ∈ Metric.closedBall c 1)
    (validB : (∑ i, (εB i : ℂ) * z i) ∈ Metric.closedBall c 1)
    (h_Tc_empty :
      ((B : Set (Fin n)) \ (A : Set (Fin n)) ∩
        {i : Fin n | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}ᶜ) = ∅) :
    False := by
  let val_aligned_set := {i : Fin n | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}
  let S := B \ A
  have hS_ne : S.Nonempty := by
    obtain ⟨x, hx_sub⟩ := Finset.exists_of_ssubset hAB
    use x; exact Finset.mem_sdiff.mpr hx_sub
  have h_pure' : ∀ i ∈ S, 0 ≤ (w i).re ∧ 0 ≤ (w i).im := by
    intro i hi
    have zi_nz : ‖z i‖ ≠ 0 := by have := hz i; linarith
    have uhp := IsAlignedZ_isUHP (hw_align i)
    unfold inUHP at uhp
    have w_eq : w i = Classical.choose (exists_unique_alignedZ (z i)) := by
      obtain ⟨x, hx, u⟩ := exists_unique_alignedZ (z i)
      rw [u _ (hw_align i), u _ (Classical.choose_spec (exists_unique_alignedZ (z i))).1]
    have hi_S : i ∈ (↑B : Set (Fin n)) \ ↑A := by
      obtain ⟨hiB, hiA⟩ := Finset.mem_sdiff.mp hi
      exact ⟨Finset.mem_coe.mpr hiB, fun h => hiA (Finset.mem_coe.mp h)⟩
    have in_T : i ∈ val_aligned_set := by
      by_contra h; exact Set.eq_empty_iff_forall_notMem.mp h_Tc_empty i ⟨hi_S, h⟩
    have im_pos : 0 ≤ (w i).im := by
      rcases uhp with h|⟨h,_⟩ <;> linarith
    have re_pos : 0 ≤ (w i).re := by
      dsimp [val_aligned_set] at in_T
      rw [w_eq]; exact in_T
    exact ⟨re_pos, im_pos⟩
  have h_norm : 1 < ‖∑ i ∈ B \ A, w i‖ := by
    apply pure_sum_norm_gt_sqrt _ _ hS_ne (Or.inl h_pure')
    intro i hi
    rcases (hw_align i) with ⟨s, hs, h_eq⟩
    rw [h_eq, Complex.norm_mul]; norm_cast
    rw [IsBaseSign_abs_eq_one hs]; simp; exact hz i
  have : ‖(∑ i, (εB i : ℂ) * z i) - (∑ i, (εA i : ℂ) * z i)‖ > 2 := by
    rw [h_diff, Complex.norm_mul, Complex.norm_two]
    have : 1 < ‖∑ i ∈ B \ A, w i‖ := h_norm
    linarith
  have dist_val : ‖(∑ i, (εB i : ℂ) * z i) - (∑ i, (εA i : ℂ) * z i)‖ ≤ 2 := by
    rw [←dist_eq_norm]
    apply le_trans (dist_triangle (∑ i, (εB i : ℂ) * z i) c (∑ i, (εA i : ℂ) * z i))
    rw [dist_comm c (∑ i, (εA i : ℂ) * z i)]
    rw [mem_closedBall] at validA validB
    linarith
  linarith

lemma kleitman_compatibility (z : Fin n → ℂ) (hz : ∀ i, 1 < ‖z i‖) (c : ℂ)
    (A B : Finset (Fin n)) (hAB : A ⊂ B)
    (εA εB : Fin n → ℤ)
    (hεA : ∀ i, εA i = 1 ∨ εA i = -1) (hεB : ∀ i, εB i = 1 ∨ εB i = -1)
    (hA : signToSet z εA = (A : Set (Fin n))) (hB : signToSet z εB = (B : Set (Fin n)))
    (validA : (∑ i, (εA i : ℂ) * z i) ∈ Metric.closedBall c 1)
    (validB : (∑ i, (εB i : ℂ) * z i) ∈ Metric.closedBall c 1) :
    ((B : Set (Fin n)) \ (A : Set (Fin n)) ∩
      {i : Fin n | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}).Nonempty ∧
    ((B : Set (Fin n)) \ (A : Set (Fin n)) ∩
      {i : Fin n | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}ᶜ).Nonempty := by
  let val_aligned_set := {i : Fin n | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}
  by_contra h_contra
  rw [not_and_or] at h_contra
  push Not at h_contra
  have h_sub_fin : A ⊆ B := hAB.subset
  have h_exists := sum_diff_subset_exists_aligned z A B h_sub_fin εA εB hεA hεB hA hB
  rcases h_exists with ⟨w, hw_align, h_diff⟩
  rcases h_contra with h_T_empty | h_Tc_empty
  · exact kleitman_case_T_empty z hz c A B hAB εA εB w hw_align h_diff validA validB h_T_empty
  · exact kleitman_case_Tc_empty z hz c A B hAB εA εB w hw_align h_diff validA validB h_Tc_empty

lemma compatibility_helper (z : Fin n → ℂ) (hz : ∀ i, 1 < ‖z i‖) (c : ℂ)
    (valid_sums : Set (Fin n → ℤ))
    (h_valid :
      ∀ ε ∈ valid_sums,
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
          (∑ i, (ε i : ℂ) * z i) ∈ Metric.closedBall c 1)
    (A B : Set (Fin n)) (εA εB : Fin n → ℤ)
    (hAF_val : εA ∈ valid_sums) (hBF_val : εB ∈ valid_sums)
    (T : Set (Fin n))
    (hA_aligned : signToSet z εA = A) (hB_aligned : signToSet z εB = B)
    (hsub : A ⊂ B)
    (hT : T = {i | 0 ≤ (Classical.choose (exists_unique_alignedZ (z i))).re}) :
    (B \ A ∩ T).Nonempty ∧ (B \ A ∩ Tᶜ).Nonempty := by
  let Af := A.toFinset
  let Bf := B.toFinset
  have hεA : ∀ i, εA i = 1 ∨ εA i = -1 := (h_valid εA hAF_val).1
  have hεB : ∀ i, εB i = 1 ∨ εB i = -1 := (h_valid εB hBF_val).1
  have ballA : (∑ i, (εA i : ℂ) * z i) ∈ Metric.closedBall c 1 := (h_valid εA hAF_val).2
  have ballB : (∑ i, (εB i : ℂ) * z i) ∈ Metric.closedBall c 1 := (h_valid εB hBF_val).2
  have hAf_s : (Af : Set (Fin n)) = A := coe_toFinset A
  have hBf_s : (Bf : Set (Fin n)) = B := coe_toFinset B
  have hsub_f : Af ⊂ Bf := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro i; rw [mem_toFinset, mem_toFinset]; apply hsub.1
    · intro h_eq; apply hsub.ne; rw [←hAf_s, ←hBf_s]; simp only [h_eq]
  have hAf_eq : signToSet z εA = (Af : Set (Fin n)) := by rw [hAf_s, hA_aligned]
  have hBf_eq : signToSet z εB = (Bf : Set (Fin n)) := by rw [hBf_s, hB_aligned]
  have res := kleitman_compatibility z hz c Af Bf hsub_f εA εB hεA hεB hAf_eq hBf_eq ballA ballB
  rw [←hAf_s, ←hBf_s, hT]
  exact res

theorem littlewood_offord_complex_bound (n : ℕ) (z : Fin n → ℂ) (hz : ∀ i, 1 < ‖z i‖) (c : ℂ) :
    let signs : Finset ℤ := {-1, 1}
    let all_coeffs : Set (Fin n → ℤ) := {ε | ∀ i, ε i ∈ signs}
    let valid_sums : Set (Fin n → ℤ) :=
      {ε | ε ∈ all_coeffs ∧ (∑ i, (ε i : ℂ) * z i) ∈ Metric.closedBall c 1}
    valid_sums.ncard ≤ Nat.choose n (n / 2) := by
  intro signs all_coeffs valid_sums
  let F : Set (Set (Fin n)) := (signToSet z) '' valid_sums
  have hinj : Set.InjOn (signToSet z) valid_sums := by
    intro ε₁ hε₁ ε₂ hε₂ heq
    have h1 : ∀ i, ε₁ i = 1 ∨ ε₁ i = -1 := by
      intro i
      have := hε₁.1 i
      simp [signs] at this
      rcases this with h|h <;> rw [h] <;> norm_num
    have h2 : ∀ i, ε₂ i = 1 ∨ ε₂ i = -1 := by
      intro i
      have := hε₂.1 i
      simp [signs] at this
      rcases this with h|h <;> rw [h] <;> norm_num
    exact signToSet_injective_on_signs z ε₁ ε₂ h1 h2 heq
  have card_eq : valid_sums.ncard = F.ncard := (Set.InjOn.ncard_image hinj).symm
  let aligned := fun i => Classical.choose (exists_unique_alignedZ (z i))
  let T : Set (Fin n) := {i | (aligned i).re ≥ 0}
  have bound : F.ncard ≤ (Fintype.card (Fin n)).choose (Fintype.card (Fin n) / 2) := by
    apply kleitman_bound_theorem F T
    intro A B hAF hBF hsub
    rcases hAF with ⟨εA, hA_val, hA_eq⟩
    rcases hBF with ⟨εB, hB_val, hB_eq⟩
    let helper_valid :
        ∀ ε ∈ valid_sums,
          (∀ i, ε i = 1 ∨ ε i = -1) ∧
            (∑ i, (ε i : ℂ) * z i) ∈ Metric.closedBall c 1 := by
      intro ε hε
      constructor
      · intro i
        have := hε.1 i
        simp [signs] at this
        rcases this with h|h <;> rw [h] <;> norm_num
      · exact hε.2
    let res :=
      compatibility_helper z hz c valid_sums helper_valid A B εA εB hA_val hB_val T
        hA_eq hB_eq hsub (by rfl)
    exact res
  rw [card_eq]
  simp only [Fintype.card_fin] at bound
  exact bound

#print axioms littlewood_offord_complex_bound
-- 'Erdos498.littlewood_offord_complex_bound' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end Erdos498
