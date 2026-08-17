import Mathlib

/-!
# Intersection strata for the second-moment argument in Erdős Problem 807

This file isolates the finite combinatorics used when a second moment is split according to the
intersection size of two `k`-subsets.  It contains no graph-specific definitions, so the lemmas can
be reused for whichever family of certificates is used in the final proof.
-/

open scoped BigOperators

namespace Erdos807

namespace Overlap

open Finset

variable {α : Type*} [DecidableEq α]

/-- Ordered pairs of `k`-subsets of `s` having intersection of cardinality `i`. -/
def pairs (s : Finset α) (k i : ℕ) : Finset (Finset α × Finset α) :=
  (s.powersetCard k ×ˢ s.powersetCard k).filter fun p ↦ #(p.1 ∩ p.2) = i

@[simp]
theorem mem_pairs {s : Finset α} {k i : ℕ} {A B : Finset α} :
    (A, B) ∈ pairs s k i ↔ A ⊆ s ∧ #A = k ∧ B ⊆ s ∧ #B = k ∧ #(A ∩ B) = i := by
  simp [pairs, and_assoc]

/-- For a fixed `k`-subset `A`, the number of `k`-subsets meeting it in exactly `i` points. -/
theorem card_fixed_left (s A : Finset α) (k i : ℕ) (hAs : A ⊆ s) (hAk : #A = k)
    (hik : i ≤ k) :
    #((s.powersetCard k).filter fun B ↦ #(A ∩ B) = i) =
      Nat.choose k i * Nat.choose (#s - k) (k - i) := by
  let source := A.powersetCard i ×ˢ (s \ A).powersetCard (k - i)
  let target := (s.powersetCard k).filter fun B ↦ #(A ∩ B) = i
  have hcard : #source = #target := by
    apply Finset.card_nbij' (fun p ↦ p.1 ∪ p.2) (fun B ↦ (A ∩ B, B \ A))
    · intro p hp
      rcases mem_product.mp hp with ⟨hpI, hpC⟩
      rcases mem_powersetCard.mp hpI with ⟨hIA, hIi⟩
      rcases mem_powersetCard.mp hpC with ⟨hCsA, hCki⟩
      have hdisj : Disjoint p.1 p.2 := by
        rw [Finset.disjoint_left]
        intro x hxI hxC
        exact (mem_sdiff.mp (hCsA hxC)).2 (hIA hxI)
      have hinter : A ∩ (p.1 ∪ p.2) = p.1 := by
        ext x
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨hxA, hxI | hxC⟩
          · exact hxI
          · exact False.elim ((mem_sdiff.mp (hCsA hxC)).2 hxA)
        · intro hxI
          exact ⟨hIA hxI, Or.inl hxI⟩
      apply mem_filter.mpr
      constructor
      · apply mem_powersetCard.mpr
        constructor
        · exact union_subset (hIA.trans hAs) (hCsA.trans sdiff_subset)
        · rw [card_union_of_disjoint hdisj, hIi, hCki, Nat.add_sub_of_le hik]
      · rw [hinter, hIi]
    · intro B hB
      rcases mem_filter.mp hB with ⟨hBk, hABi⟩
      rcases mem_powersetCard.mp hBk with ⟨hBs, hBcard⟩
      apply mem_product.mpr
      constructor
      · exact mem_powersetCard.mpr ⟨inter_subset_left, hABi⟩
      · apply mem_powersetCard.mpr
        constructor
        · intro x hx
          exact mem_sdiff.mpr ⟨hBs (mem_sdiff.mp hx).1, (mem_sdiff.mp hx).2⟩
        · rw [card_sdiff, hABi, hBcard]
    · intro p hp
      rcases mem_product.mp hp with ⟨hpI, hpC⟩
      rcases mem_powersetCard.mp hpI with ⟨hIA, -⟩
      rcases mem_powersetCard.mp hpC with ⟨hCsA, -⟩
      apply Prod.ext
      · ext x
        simp only [mem_inter, mem_union]
        constructor
        · rintro ⟨hxA, hxI | hxC⟩
          · exact hxI
          · exact False.elim ((mem_sdiff.mp (hCsA hxC)).2 hxA)
        · intro hxI
          exact ⟨hIA hxI, Or.inl hxI⟩
      · ext x
        simp only [mem_sdiff, mem_union]
        constructor
        · rintro ⟨hxI | hxC, hxnotA⟩
          · exact False.elim (hxnotA (hIA hxI))
          · exact hxC
        · intro hxC
          exact ⟨Or.inr hxC, (mem_sdiff.mp (hCsA hxC)).2⟩
    · intro B hB
      rcases mem_filter.mp hB with ⟨hBk, -⟩
      rcases mem_powersetCard.mp hBk with ⟨-, -⟩
      ext x
      simp only [mem_union, mem_inter, mem_sdiff]
      tauto
  rw [← hcard]
  simp [source, hAk, card_sdiff_of_subset hAs]

/-- Exact number of ordered pairs of `k`-subsets of an `n`-set whose intersection has size `i`.
The three factors choose the first set, its intersection with the second, and the part of the
second set outside the first. -/
theorem card_pairs (s : Finset α) (k i : ℕ) (hik : i ≤ k) :
    #(pairs s k i) =
      Nat.choose #s k * Nat.choose k i * Nat.choose (#s - k) (k - i) := by
  classical
  let S := s.powersetCard k
  have hmap : Set.MapsTo Prod.fst (pairs s k i : Set (Finset α × Finset α)) S := by
    intro p hp
    exact (mem_product.mp (mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hfiber (A : Finset α) (hA : A ∈ S) :
      #{p ∈ pairs s k i | p.1 = A} =
        #((S).filter fun B ↦ #(A ∩ B) = i) := by
    apply Finset.card_nbij' Prod.snd (fun B ↦ (A, B))
    · intro p hp
      rcases mem_filter.mp hp with ⟨hppair, hpA⟩
      rcases mem_pairs.mp hppair with ⟨-, -, hps, hpk, hpinter⟩
      subst A
      exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hps, hpk⟩, hpinter⟩
    · intro B hB
      rcases mem_filter.mp hB with ⟨hBS, hinter⟩
      rcases mem_powersetCard.mp hA with ⟨hAs, hAk⟩
      rcases mem_powersetCard.mp hBS with ⟨hBs, hBk⟩
      exact mem_filter.mpr ⟨mem_pairs.mpr ⟨hAs, hAk, hBs, hBk, hinter⟩, rfl⟩
    · intro p hp
      exact Prod.ext (mem_filter.mp hp).2.symm rfl
    · intro B hB
      rfl
  calc
    ∑ A ∈ S, #{p ∈ pairs s k i | p.1 = A} =
        ∑ A ∈ S, #((S).filter fun B ↦ #(A ∩ B) = i) := by
          apply sum_congr rfl
          intro A hA
          exact hfiber A hA
    _ = ∑ _A ∈ S, Nat.choose k i * Nat.choose (#s - k) (k - i) := by
          apply sum_congr rfl
          intro A hA
          rcases mem_powersetCard.mp hA with ⟨hAs, hAk⟩
          exact card_fixed_left s A k i hAs hAk hik
    _ = Nat.choose #s k * Nat.choose k i * Nat.choose (#s - k) (k - i) := by
          simp [S, mul_assoc]

/-! ## Consecutive intersection strata -/

/-- The hypergeometric weight of the intersection-`i` stratum, before division by the total
number of `k`-subsets. -/
def intersectionWeight (n k i : ℕ) : ℕ :=
  Nat.choose k i * Nat.choose (n - k) (k - i)

/-- Exact cross-multiplied ratio of consecutive intersection weights.  The last factor on the
left is the number of still-available points outside the first `k`-set.  This form avoids division
and remains true even when one of the binomial coefficients vanishes. -/
theorem intersectionWeight_succ_ratio (n k i : ℕ) (hik : i < k) :
    intersectionWeight n k (i + 1) * (i + 1) * ((n - k) - (k - i - 1)) =
      intersectionWeight n k i * (k - i) ^ 2 := by
  have hki : k - i - 1 + 1 = k - i := by omega
  have hfirst := Nat.choose_succ_right_eq k i
  have hsecond := Nat.choose_succ_right_eq (n - k) (k - i - 1)
  rw [hki] at hsecond
  change
    (Nat.choose k (i + 1) * Nat.choose (n - k) (k - (i + 1))) * (i + 1) *
        ((n - k) - (k - i - 1)) =
      (Nat.choose k i * Nat.choose (n - k) (k - i)) * (k - i) ^ 2
  have hsub : k - (i + 1) = k - i - 1 := by omega
  rw [hsub]
  calc
    (Nat.choose k (i + 1) * Nat.choose (n - k) (k - i - 1)) * (i + 1) *
          ((n - k) - (k - i - 1)) =
        (Nat.choose k (i + 1) * (i + 1)) *
          (Nat.choose (n - k) (k - i - 1) * ((n - k) - (k - i - 1))) := by ring
    _ = (Nat.choose k i * (k - i)) *
          (Nat.choose (n - k) (k - i) * (k - i)) := by rw [hfirst, ← hsecond]
    _ = (Nat.choose k i * Nat.choose (n - k) (k - i)) * (k - i) ^ 2 := by ring

/-! ## Ratio bounds and finite geometric tails -/

/-- Multiplying two nonnegative consecutive-ratio bounds multiplies their ratio constants.  In
the second moment, `f` is the intersection-count factor and `h` is the probability/correlation
factor. -/
theorem moderate_overlap_ratio {f h a b : ℝ} (hh : 0 ≤ h)
    (hb : 0 ≤ b) {f' h' : ℝ}
    (hfr : f' ≤ a * f) (hhr : h' ≤ b * h) (hf' : 0 ≤ f') :
    f' * h' ≤ (a * b) * (f * h) := by
  calc
    f' * h' ≤ f' * (b * h) := mul_le_mul_of_nonneg_left hhr hf'
    _ ≤ (a * f) * (b * h) := mul_le_mul_of_nonneg_right hfr (mul_nonneg hb hh)
    _ = (a * b) * (f * h) := by ring

/-- Iterating a one-step ratio estimate. -/
theorem geometric_decay_iterate (u : ℕ → ℝ) (q : ℝ) (m t : ℕ) (hq : 0 ≤ q)
    (hu : ∀ j, m ≤ j → u (j + 1) ≤ q * u j) :
    u (m + t) ≤ q ^ t * u m := by
  induction t with
  | zero => simp
  | succ t iht =>
      calc
        u (m + (t + 1)) = u ((m + t) + 1) := by rw [Nat.add_assoc]
        _ ≤ q * u (m + t) := hu (m + t) (Nat.le_add_right m t)
        _ ≤ q * (q ^ t * u m) := mul_le_mul_of_nonneg_left iht hq
        _ = q ^ (t + 1) * u m := by ring

/-- A finite geometric sum with ratio at most one half is at most two. -/
theorem finite_geometric_sum_le_two (q : ℝ) (N : ℕ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    ∑ t ∈ range N, q ^ t ≤ 2 := by
  calc
    ∑ t ∈ range N, q ^ t ≤ ∑ t ∈ range N, (1 / 2 : ℝ) ^ t := by
      apply sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hq0 hq t
    _ ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have hp : 0 ≤ (1 / 2 : ℝ) ^ N := pow_nonneg (by norm_num) N
      norm_num
      linarith

/-- The standard moderate-overlap summation step: a nonnegative sequence whose consecutive terms
shrink by a factor at most `q ≤ 1/2` has every finite tail bounded by twice its first term. -/
theorem moderate_overlap_sum_le_two (u : ℕ → ℝ) (q : ℝ) (m N : ℕ)
    (hu0 : ∀ j, 0 ≤ u j) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2)
    (hratio : ∀ j, m ≤ j → u (j + 1) ≤ q * u j) :
    ∑ t ∈ range N, u (m + t) ≤ 2 * u m := by
  calc
    ∑ t ∈ range N, u (m + t) ≤ ∑ t ∈ range N, q ^ t * u m := by
      apply sum_le_sum
      intro t ht
      exact geometric_decay_iterate u q m t hq0 hratio
    _ = (∑ t ∈ range N, q ^ t) * u m := by rw [sum_mul]
    _ ≤ 2 * u m := mul_le_mul_of_nonneg_right (finite_geometric_sum_le_two q N hq0 hq) (hu0 m)

/-! ## The large-overlap labelled-matrix reconstruction bound -/

/-- The free Boolean coordinates when two labelled templates differ in `j` vertices.  The first
factor records the `r * j` missing `B`-positions.  The second records at most
`(90*r) * floor(j/10)` whole `A`-blocks missed by the overlap. -/
abbrev FreeExtensionCode (r j : ℕ) :=
  ((Fin r × Fin j) → Bool) × ((Fin (90 * r) × Fin (j / 10)) → Bool)

/-- There are exactly `2^(r*j + (90*r)*floor(j/10))` free-coordinate codes. -/
theorem card_freeExtensionCode (r j : ℕ) :
    Fintype.card (FreeExtensionCode r j) = 2 ^ (r * j + (90 * r) * (j / 10)) := by
  simp [FreeExtensionCode, pow_add]

/-- The two sorts of free coordinates together use at most `10*r*j` bits. -/
theorem free_bits_le_ten_mul (r j : ℕ) :
    r * j + (90 * r) * (j / 10) ≤ 10 * r * j := by
  have hfloor : (j / 10) * 10 ≤ j := Nat.div_mul_le_self j 10
  calc
    r * j + (90 * r) * (j / 10) = r * j + (9 * r) * ((j / 10) * 10) := by ring
    _ ≤ r * j + (9 * r) * j :=
      Nat.add_le_add_left (Nat.mul_le_mul_left (9 * r) hfloor) _
    _ = 10 * r * j := by ring

/-- Generic reconstruction/extension count (the formal analogue of ABH Claim 3.1).
If every compatible extension is determined by its values on the two sets of free coordinates,
then the number of compatible extensions is at most
`2^(r*j + (90*r)*floor(j/10))`. -/
theorem card_extensions_le_free_bits {σ : Type*} (F : Finset σ) (r j : ℕ)
    (encode : σ → FreeExtensionCode r j)
    (hinj : (F : Set σ).InjOn encode) :
    #F ≤ 2 ^ (r * j + (90 * r) * (j / 10)) := by
  classical
  calc
    #F ≤ #(Finset.univ : Finset (FreeExtensionCode r j)) :=
      Finset.card_le_card_of_injOn encode (fun _ _ ↦ Finset.mem_univ _) hinj
    _ = Fintype.card (FreeExtensionCode r j) := Finset.card_univ
    _ = 2 ^ (r * j + (90 * r) * (j / 10)) := card_freeExtensionCode r j

/-- Coarser but convenient `2^(10*r*j)` version of `card_extensions_le_free_bits`. -/
theorem card_extensions_le_ten_mul {σ : Type*} (F : Finset σ) (r j : ℕ)
    (encode : σ → FreeExtensionCode r j)
    (hinj : (F : Set σ).InjOn encode) :
    #F ≤ 2 ^ (10 * r * j) :=
  (card_extensions_le_free_bits F r j encode hinj).trans
    (Nat.pow_le_pow_right (by omega) (free_bits_le_ten_mul r j))

/-! ### A stable-slot version of the reconstruction code

For some concrete encodings it is more convenient to allocate nine `A`-slots for every missing
vertex rather than pack only the wholly missing blocks.  This wastes no more than the already used
coarse exponent `10*r*j`, and makes every slot type independent of division and rounding.
-/

/-- Stable free slots: one `r × j` Boolean matrix and one `(9*r) × j` Boolean matrix. -/
abbrev SlotFreeCode (r j : ℕ) :=
  ((Fin r × Fin j) → Bool) × ((Fin (9 * r) × Fin j) → Bool)

/-- The stable-slot code has exactly `2^(10*r*j)` elements. -/
theorem card_slotFreeCode (r j : ℕ) :
    Fintype.card (SlotFreeCode r j) = 2 ^ (10 * r * j) := by
  simp [SlotFreeCode]
  ring

/-- Generic stable-slot reconstruction bound.  Any family admitting an injective stable-slot
encoding has at most `2^(10*r*j)` compatible extensions. -/
theorem card_extensions_le_slotFree {σ : Type*} (F : Finset σ) (r j : ℕ)
    (encode : σ → SlotFreeCode r j)
    (hinj : (F : Set σ).InjOn encode) :
    #F ≤ 2 ^ (10 * r * j) := by
  classical
  calc
    #F ≤ #(Finset.univ : Finset (SlotFreeCode r j)) :=
      Finset.card_le_card_of_injOn encode (fun _ _ ↦ Finset.mem_univ _) hinj
    _ = Fintype.card (SlotFreeCode r j) := Finset.card_univ
    _ = 2 ^ (10 * r * j) := card_slotFreeCode r j

end Overlap

end Erdos807
