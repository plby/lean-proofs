import Mathlib

/-!
# Erdős Problem 220: elementary finite infrastructure

This file fixes the canonical increasing enumeration of the reduced residue
classes in `[0,n)`, the internal consecutive-gap square sum, and the finite
interval/window counts used by the analytic part of the proof.
-/

open scoped BigOperators

namespace Erdos220

/-- The canonical representatives in `[0,n)` of the units modulo `n`. -/
def reducedResidueFinset (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun a => n.Coprime a

@[simp] lemma mem_reducedResidueFinset {n a : ℕ} :
    a ∈ reducedResidueFinset n ↔ a < n ∧ n.Coprime a := by
  simp [reducedResidueFinset]

@[simp] lemma card_reducedResidueFinset (n : ℕ) :
    (reducedResidueFinset n).card = n.totient := by
  simpa [reducedResidueFinset] using (Nat.totient_eq_card_coprime n).symm

@[simp] lemma reducedResidueFinset_zero : reducedResidueFinset 0 = ∅ := by
  simp [reducedResidueFinset]

@[simp] lemma reducedResidueFinset_one : reducedResidueFinset 1 = {0} := by
  ext a
  simp [mem_reducedResidueFinset]

/-- The reduced residues, in strictly increasing order. -/
noncomputable def reducedResidue (n : ℕ) : Fin n.totient ↪o ℕ :=
  (reducedResidueFinset n).orderEmbOfFin (card_reducedResidueFinset n)

@[simp] lemma reducedResidue_mem (n : ℕ) (i : Fin n.totient) :
    reducedResidue n i ∈ reducedResidueFinset n := by
  exact Finset.orderEmbOfFin_mem _ _ _

lemma reducedResidue_lt (n : ℕ) (i : Fin n.totient) :
    reducedResidue n i < n :=
  (mem_reducedResidueFinset.mp (reducedResidue_mem n i)).1

lemma reducedResidue_coprime (n : ℕ) (i : Fin n.totient) :
    n.Coprime (reducedResidue n i) :=
  (mem_reducedResidueFinset.mp (reducedResidue_mem n i)).2

lemma reducedResidue_strictMono (n : ℕ) : StrictMono (reducedResidue n) :=
  (reducedResidue n).strictMono

lemma reducedResidue_injective (n : ℕ) : Function.Injective (reducedResidue n) :=
  (reducedResidue n).injective

@[simp] lemma image_reducedResidue_univ (n : ℕ) :
    Finset.image (reducedResidue n) Finset.univ = reducedResidueFinset n := by
  exact Finset.image_orderEmbOfFin_univ _ _

@[simp] lemma map_reducedResidue_univ (n : ℕ) :
    Finset.map (reducedResidue n).toEmbedding Finset.univ = reducedResidueFinset n := by
  exact Finset.map_orderEmbOfFin_univ _ _

lemma reducedResidue_pos {n : ℕ} (hn : 1 < n) (i : Fin n.totient) :
    0 < reducedResidue n i := by
  by_contra h
  have hz : reducedResidue n i = 0 := by omega
  have hn1 : n = 1 :=
    (Nat.coprime_zero_right n).mp (hz ▸ reducedResidue_coprime n i)
  omega

@[simp] lemma reducedResidue_one_apply (i : Fin (Nat.totient 1)) :
    reducedResidue 1 i = 0 := by
  have hlt := reducedResidue_lt 1 i
  omega

lemma one_mem_reducedResidueFinset {n : ℕ} (hn : 1 < n) :
    1 ∈ reducedResidueFinset n := by
  simp [mem_reducedResidueFinset, hn]

/-- The index of the left endpoint of the internal gap numbered by `k`. -/
def gapLeftIndex (n : ℕ) (k : Fin (n.totient - 1)) : Fin n.totient :=
  ⟨k.1, by omega⟩

/-- The index of the right endpoint of the internal gap numbered by `k`. -/
def gapRightIndex (n : ℕ) (k : Fin (n.totient - 1)) : Fin n.totient :=
  ⟨k.1 + 1, by omega⟩

@[simp] lemma gapLeftIndex_val (n : ℕ) (k : Fin (n.totient - 1)) :
    (gapLeftIndex n k).val = k.val := rfl

@[simp] lemma gapRightIndex_val (n : ℕ) (k : Fin (n.totient - 1)) :
    (gapRightIndex n k).val = k.val + 1 := rfl

lemma gapLeftIndex_lt_gapRightIndex (n : ℕ) (k : Fin (n.totient - 1)) :
    gapLeftIndex n k < gapRightIndex n k := by
  simp [gapLeftIndex, gapRightIndex]

lemma reducedResidue_gap_lt (n : ℕ) (k : Fin (n.totient - 1)) :
    reducedResidue n (gapLeftIndex n k) < reducedResidue n (gapRightIndex n k) :=
  (reducedResidue n).strictMono (gapLeftIndex_lt_gapRightIndex n k)

/-- The positive natural-number length of the `k`-th internal gap. -/
noncomputable def internalGap (n : ℕ) (k : Fin (n.totient - 1)) : ℕ :=
  reducedResidue n (gapRightIndex n k) - reducedResidue n (gapLeftIndex n k)

lemma internalGap_pos (n : ℕ) (k : Fin (n.totient - 1)) :
    0 < internalGap n k := by
  exact Nat.sub_pos_of_lt (reducedResidue_gap_lt n k)

lemma internalGap_le_n (n : ℕ) (k : Fin (n.totient - 1)) :
    internalGap n k ≤ n := by
  dsimp [internalGap]
  exact (Nat.sub_le _ _).trans (Nat.le_of_lt (reducedResidue_lt n _))

/-- The sum of the squares of the gaps between consecutive reduced residues.

There is deliberately no wrap-around term here: this is exactly the sum in
Erdős Problem 220.
-/
noncomputable def gapSquareSum (n : ℕ) : ℝ :=
  ∑ k : Fin (n.totient - 1),
    (((reducedResidue n (gapRightIndex n k) : ℕ) : ℝ) -
      ((reducedResidue n (gapLeftIndex n k) : ℕ) : ℝ)) ^ 2

lemma gapSquareSum_eq_sum_internalGap (n : ℕ) :
    gapSquareSum n = ∑ k : Fin (n.totient - 1), (internalGap n k : ℝ) ^ 2 := by
  apply Finset.sum_congr rfl
  intro k _
  rw [internalGap, Nat.cast_sub (Nat.le_of_lt (reducedResidue_gap_lt n k))]

lemma gapSquareSum_nonneg (n : ℕ) : 0 ≤ gapSquareSum n := by
  simp only [gapSquareSum]
  positivity

lemma gapSquareSum_eq_zero_of_totient_le_one {n : ℕ} (hφ : n.totient ≤ 1) :
    gapSquareSum n = 0 := by
  rw [gapSquareSum]
  apply Finset.sum_eq_zero
  intro k _
  have hk := k.isLt
  omega

@[simp] lemma gapSquareSum_zero : gapSquareSum 0 = 0 := by
  apply gapSquareSum_eq_zero_of_totient_le_one
  simp

@[simp] lemma gapSquareSum_one : gapSquareSum 1 = 0 := by
  apply gapSquareSum_eq_zero_of_totient_le_one
  simp

/-! ## Literal list formulation of the problem -/

/-- Sum of squared differences of adjacent entries of a natural-number list. -/
def sumSquaredGaps : List ℕ → ℕ
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)
  | _ => 0

@[simp] lemma sumSquaredGaps_nil : sumSquaredGaps [] = 0 := rfl

@[simp] lemma sumSquaredGaps_singleton (a : ℕ) : sumSquaredGaps [a] = 0 := rfl

@[simp] lemma sumSquaredGaps_cons_cons (a b : ℕ) (rest : List ℕ) :
    sumSquaredGaps (a :: b :: rest) =
      (b - a) ^ 2 + sumSquaredGaps (b :: rest) := rfl

/-- The list in the statement of Erdős Problem 220: all `m` with
`1 ≤ m < n` and `(m,n)=1`, in increasing order. -/
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.Ico 1 n).filter fun m => m.Coprime n).sort (· ≤ ·)

@[simp] lemma mem_sortedTotatives {n m : ℕ} :
    m ∈ sortedTotatives n ↔ 1 ≤ m ∧ m < n ∧ m.Coprime n := by
  simp [sortedTotatives, and_assoc]

@[simp] lemma sortedTotatives_zero : sortedTotatives 0 = [] := by
  simp [sortedTotatives]

@[simp] lemma sortedTotatives_one : sortedTotatives 1 = [] := by
  simp [sortedTotatives]

lemma literalTotativeFinset_eq_reducedResidueFinset {n : ℕ} (hn : 2 ≤ n) :
    (Finset.Ico 1 n).filter (fun m => m.Coprime n) = reducedResidueFinset n := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico, mem_reducedResidueFinset]
  constructor
  · rintro ⟨⟨_, hmn⟩, hcop⟩
    exact ⟨hmn, hcop.symm⟩
  · rintro ⟨hmn, hcop⟩
    have hm0 : m ≠ 0 := by
      intro hm
      have hn1 : n = 1 := (Nat.coprime_zero_right n).mp (hm ▸ hcop)
      omega
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hm0, hmn⟩, hcop.symm⟩

lemma sortedTotatives_eq_reducedResidueSort {n : ℕ} (hn : 2 ≤ n) :
    sortedTotatives n = (reducedResidueFinset n).sort (· ≤ ·) := by
  rw [sortedTotatives, literalTotativeFinset_eq_reducedResidueFinset hn]

lemma sortedTotatives_eq_ofFn_reducedResidue {n : ℕ} (hn : 2 ≤ n) :
    sortedTotatives n = List.ofFn (reducedResidue n) := by
  rw [sortedTotatives_eq_reducedResidueSort hn, List.ofFn_eq_map]
  exact (Finset.listMap_orderEmbOfFin_finRange
    (reducedResidueFinset n) (card_reducedResidueFinset n)).symm

/-- Adjacent differences of a finite tuple are precisely the sum over its
consecutive `Fin` indices. -/
lemma sumSquaredGaps_ofFn (n : ℕ) (f : Fin n → ℕ) :
    sumSquaredGaps (List.ofFn f) =
      ∑ k : Fin (n - 1),
        (f ⟨k.val + 1, by omega⟩ - f ⟨k.val, by omega⟩) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simp [List.ofFn_succ]
      | succ m =>
          let f' : Fin (m + 1) → ℕ := fun i => f i.succ
          rw [List.ofFn_succ (f := f)]
          rw [List.ofFn_succ (f := f')]
          simp only [sumSquaredGaps]
          rw [← List.ofFn_succ (f := f')]
          rw [ih f']
          change _ = ∑ k : Fin (m + 1),
            (f ⟨k.val + 1, by omega⟩ - f ⟨k.val, by omega⟩) ^ 2
          rw [Fin.sum_univ_succ]
          congr 1

/-- For `n ≥ 2`, the literal natural-number list sum in the problem is
exactly the canonical real-valued `gapSquareSum`. -/
theorem cast_sumSquaredGaps_sortedTotatives {n : ℕ} (hn : 2 ≤ n) :
    (sumSquaredGaps (sortedTotatives n) : ℝ) = gapSquareSum n := by
  rw [sortedTotatives_eq_ofFn_reducedResidue hn]
  rw [sumSquaredGaps_ofFn]
  rw [gapSquareSum_eq_sum_internalGap]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  rfl

/-- Number of integers `t` with `1 ≤ t ≤ h` for which `x+t` is a unit
modulo `n`.  Coprimality is already periodic, so no explicit `% n` is needed.
-/
def unitCount (n h x : ℕ) : ℕ :=
  ((Finset.Icc 1 h).filter fun t => n.Coprime (x + t)).card

@[simp] lemma unitCount_zero (n x : ℕ) : unitCount n 0 x = 0 := by
  simp [unitCount]

lemma unitCount_le (n h x : ℕ) : unitCount n h x ≤ h := by
  calc
    unitCount n h x ≤ (Finset.Icc 1 h).card := Finset.card_filter_le _ _
    _ ≤ h := by simp

lemma unitCount_eq_zero_iff {n h x : ℕ} :
    unitCount n h x = 0 ↔
      ∀ t : ℕ, 1 ≤ t → t ≤ h → ¬n.Coprime (x + t) := by
  simp only [unitCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_Icc]
  constructor
  · intro H t ht1 hth hcop
    exact H ⟨ht1, hth⟩ hcop
  · intro H t ht hcop
    exact H t ht.1 ht.2 hcop

/-- Starting points `x ∈ [0,n)` whose following interval of length `h`
contains no unit modulo `n`. -/
def emptyWindows (n h : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun x => unitCount n h x = 0

@[simp] lemma mem_emptyWindows {n h x : ℕ} :
    x ∈ emptyWindows n h ↔ x < n ∧ unitCount n h x = 0 := by
  simp [emptyWindows]

lemma mem_emptyWindows_iff_forall {n h x : ℕ} :
    x ∈ emptyWindows n h ↔
      x < n ∧ ∀ t : ℕ, 1 ≤ t → t ≤ h → ¬n.Coprime (x + t) := by
  rw [mem_emptyWindows, unitCount_eq_zero_iff]

lemma emptyWindows_subset_range (n h : ℕ) :
    emptyWindows n h ⊆ Finset.range n := by
  intro x hx
  exact Finset.mem_range.mpr (mem_emptyWindows.mp hx).1

lemma card_emptyWindows_le (n h : ℕ) : (emptyWindows n h).card ≤ n := by
  exact (Finset.card_le_card (emptyWindows_subset_range n h)).trans_eq (Finset.card_range n)

@[simp] lemma emptyWindows_zero_left (h : ℕ) : emptyWindows 0 h = ∅ := by
  simp [emptyWindows]

@[simp] lemma emptyWindows_zero_right (n : ℕ) : emptyWindows n 0 = Finset.range n := by
  simp [emptyWindows]

@[simp] lemma card_emptyWindows_zero_right (n : ℕ) : (emptyWindows n 0).card = n := by
  simp

/-- The proportion of residue classes modulo `n` which are units. -/
noncomputable def density (n : ℕ) : ℝ :=
  (n.totient : ℝ) / (n : ℝ)

@[simp] lemma density_zero : density 0 = 0 := by
  simp [density]

@[simp] lemma density_one : density 1 = 1 := by
  simp [density]

lemma density_nonneg (n : ℕ) : 0 ≤ density n := by
  rw [density]
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma density_pos {n : ℕ} (hn : 0 < n) : 0 < density n := by
  rw [density]
  exact div_pos (by exact_mod_cast Nat.totient_pos.mpr hn) (by exact_mod_cast hn)

lemma density_le_one (n : ℕ) : density n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  rw [density, div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < n)]
  exact_mod_cast Nat.totient_le n

lemma totient_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < n.totient :=
  Nat.totient_pos.mpr hn

lemma totient_ne_zero_of_pos {n : ℕ} (hn : 0 < n) : n.totient ≠ 0 :=
  Nat.ne_of_gt (totient_pos_of_pos hn)

end Erdos220
