import ErdosProblems.Erdos421.Rejection
import ErdosProblems.Erdos421.IntervalPointCount

/-!
# Counting short raw rejected gaps

We use integer powers for the short-gap threshold: `g^20 <= p` is the
integer formulation of `g <= p^(1/20)`.
-/

namespace Erdos421

noncomputable def gapLength (k : ℕ) : ℕ := prime (k + 1) - prime k

def ShortGap (k : ℕ) : Prop := (gapLength k) ^ 20 ≤ prime k

/-- A canonical raw witness whose earlier block is an ordinary interval. -/
structure RawWitness (k : ℕ) where
  a : ℕ
  b : ℕ
  m : ℕ
  n : ℕ
  two_le_a : 2 ≤ a
  earlier_nonempty : a ≤ b
  separated : b < m
  gap_left : prime k < m
  later_nonempty : m ≤ n
  gap_right : n < prime (k + 1)
  earlier_block : IsBlock (stage k ∪ Finset.Ioc (prime k) (prime (k + 1))) (Finset.Icc a b)
  product_eq : (Finset.Icc a b).prod id = (Finset.Icc m n).prod id

def Raw (k : ℕ) : Prop := Rejected k ∧ Nonempty (RawWitness k)

def RawWitness.earlierLength {k : ℕ} (w : RawWitness k) : ℕ := w.b - w.a + 1
def RawWitness.laterLength {k : ℕ} (w : RawWitness k) : ℕ := w.n - w.m + 1

theorem fallingNatProduct_eq_Icc {a b : ℕ} (hab : a ≤ b) :
    fallingNatProduct b (b - a + 1) = (Finset.Icc a b).prod id := by
  unfold fallingNatProduct
  apply Finset.prod_bij (fun i _ ↦ b - i)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩
  · intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    omega
  · intro x hx
    obtain ⟨hax, hxb⟩ := Finset.mem_Icc.mp hx
    exact ⟨b - x, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

theorem intervalProduct_eq_Icc {m n : ℕ} (hmn : m ≤ n) :
    intervalProduct m (n - m + 1) = (Finset.Icc m n).prod id := by
  unfold intervalProduct
  apply Finset.prod_bij (fun i _ ↦ m + i)
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ hij
    omega
  · intro x hx
    obtain ⟨hmx, hxn⟩ := Finset.mem_Icc.mp hx
    exact ⟨x - m, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

theorem RawWitness.earlier_card {k : ℕ} (w : RawWitness k) :
    (Finset.Icc w.a w.b).card = w.earlierLength := by
  rw [Nat.card_Icc]
  unfold earlierLength
  have := w.earlier_nonempty
  omega

theorem RawWitness.later_card {k : ℕ} (w : RawWitness k) :
    (Finset.Icc w.m w.n).card = w.laterLength := by
  rw [Nat.card_Icc]
  unfold laterLength
  have := w.later_nonempty
  omega

theorem RawWitness.laterLength_pos {k : ℕ} (w : RawWitness k) : 0 < w.laterLength := by
  unfold laterLength
  omega

theorem RawWitness.length_lt {k : ℕ} (w : RawWitness k) : w.laterLength < w.earlierLength := by
  have h := earlier_card_gt
    (Finset.nonempty_Icc.mpr w.earlier_nonempty) (Finset.nonempty_Icc.mpr w.later_nonempty)
    (by intro x hx; have := (Finset.mem_Icc.mp hx).1; have := w.two_le_a; omega)
    (by
      intro x hx y hy
      have := (Finset.mem_Icc.mp hx).2
      have := (Finset.mem_Icc.mp hy).1
      have := w.separated
      omega) w.product_eq
  rwa [w.earlier_card, w.later_card] at h

theorem RawWitness.mem_solutions {k B : ℕ} (w : RawWitness k) (hB : prime (k + 1) ≤ B) :
    (w.b, w.m) ∈ intervalSolutions B w.earlierLength w.laterLength := by
  apply mem_intervalSolutions.mpr
  have ha := w.two_le_a
  have hab := w.earlier_nonempty
  have hbm := w.separated
  have hmn := w.later_nonempty
  have hnq := w.gap_right
  refine ⟨?_, by omega, by omega, by omega, ?_⟩
  · unfold earlierLength
    omega
  · exact (fallingNatProduct_eq_Icc hab).trans
      (w.product_eq.trans (intervalProduct_eq_Icc hmn).symm)

theorem prime_gap_index_unique {i j m : ℕ}
    (hi : prime i < m) (hi' : m < prime (i + 1))
    (hj : prime j < m) (hj' : m < prime (j + 1)) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with hij | hji
  · have hle := prime_strictMono.monotone (show i + 1 ≤ j from hij)
    omega
  · have hle := prime_strictMono.monotone (show j + 1 ≤ i from hji)
    omega

theorem ShortGap.length_le_scale {k u : ℕ} (hshort : ShortGap k)
    (hB : prime (k + 1) ≤ 2 ^ (60 * u)) : gapLength k ≤ 2 ^ (3 * u) := by
  have hpq := prime_strictMono (Nat.lt_succ_self k)
  have hg : (gapLength k) ^ 20 ≤ 2 ^ (60 * u) := hshort.trans (hpq.le.trans hB)
  have hp : (2 ^ (3 * u)) ^ 20 = 2 ^ (60 * u) := by
    rw [← pow_mul]
    congr 1
    omega
  by_contra h
  have hlt := Nat.pow_lt_pow_left (show 2 ^ (3 * u) < gapLength k by omega)
    (by decide : 20 ≠ 0)
  rw [hp] at hlt
  omega

theorem sixty_mul_le_two_pow {u : ℕ} (hu : 10 ≤ u) : 60 * u ≤ 2 ^ u := by
  induction u, hu using Nat.le_induction with
  | base => norm_num
  | succ u hu ih =>
    calc
      60 * (u + 1) ≤ 2 * (60 * u) := by omega
      _ ≤ 2 * 2 ^ u := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (u + 1) := by rw [pow_succ]; omega

theorem RawWitness.length_le_scale {k u : ℕ} (w : RawWitness k)
    (hshort : ShortGap k) (hB : prime (k + 1) ≤ 2 ^ (60 * u)) (hu : 10 ≤ u) :
    w.earlierLength ≤ 2 ^ (4 * u) := by
  have hs : w.laterLength ≤ 2 ^ (3 * u) := by
    apply le_trans _ (hshort.length_le_scale hB)
    unfold laterLength gapLength
    have := w.gap_left
    have := w.gap_right
    have := w.later_nonempty
    omega
  have hpower := witness_power_bound
    (by intro e he; have := (Finset.mem_Icc.mp he).1; have := w.two_le_a; omega)
    (by
      intro t ht
      have := (Finset.mem_Icc.mp ht).2
      have := w.gap_right
      exact (show t ≤ prime (k + 1) by omega).trans hB) w.product_eq
  rw [w.earlier_card, w.later_card, ← pow_mul] at hpower
  have hr : w.earlierLength ≤ (60 * u) * w.laterLength :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpower
  calc
    w.earlierLength ≤ (60 * u) * 2 ^ (3 * u) := hr.trans (Nat.mul_le_mul_left _ hs)
    _ ≤ 2 ^ u * 2 ^ (3 * u) := Nat.mul_le_mul_right _ (sixty_mul_le_two_pow hu)
    _ = 2 ^ (4 * u) := by rw [← pow_add]; congr 1; omega

abbrev IntervalWitnessCode := (Σ _ : ℕ × ℕ, ℕ × ℕ)

def allIntervalSolutions (B L : ℕ) : Finset IntervalWitnessCode :=
  (lengthPairs L).sigma (fun p ↦ intervalSolutions B p.1 p.2)

def RawWitness.code {k : ℕ} (w : RawWitness k) : IntervalWitnessCode :=
  ⟨(w.earlierLength, w.laterLength), (w.b, w.m)⟩

theorem RawWitness.code_mem {k B L : ℕ} (w : RawWitness k) (hB : prime (k + 1) ≤ B)
    (hL : w.earlierLength ≤ L) : w.code ∈ allIntervalSolutions B L := by
  apply Finset.mem_sigma.mpr
  refine ⟨?_, w.mem_solutions hB⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, w.length_lt⟩
  · exact Finset.mem_Icc.mpr ⟨(w.laterLength_pos.trans w.length_lt), hL⟩
  · exact Finset.mem_Icc.mpr ⟨w.laterLength_pos, w.length_lt.le.trans hL⟩

noncomputable def shortRawGaps (B : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range B).filter (fun k ↦ Raw k ∧ ShortGap k ∧ prime (k + 1) ≤ B)

theorem mem_shortRawGaps {B k : ℕ} :
    k ∈ shortRawGaps B ↔ Raw k ∧ ShortGap k ∧ prime (k + 1) ≤ B := by
  classical
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    have hidx : k + 1 ≤ prime (k + 1) := prime_strictMono.id_le (k + 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hidx.trans hk.2.2), hk⟩

/-- The selected paper's raw-gap exponent, proved here using the positive
convex-branch count instead of a general affine-curve estimate. -/
theorem shortRawGaps_card_scale {u : ℕ} (hu : 10 ≤ u) :
    (shortRawGaps (2 ^ (60 * u))).card ≤ 6 * 2 ^ (48 * u) := by
  classical
  let S := shortRawGaps (2 ^ (60 * u))
  let C := allIntervalSolutions (2 ^ (60 * u)) (2 ^ (4 * u))
  have hmem : ∀ k : S, Raw k ∧ ShortGap k ∧ prime (k + 1) ≤ 2 ^ (60 * u) :=
    fun k ↦ mem_shortRawGaps.mp k.property
  let w : (k : S) → RawWitness k := fun k ↦ Classical.choice (hmem k).1.2
  let f : S → C := fun k ↦ ⟨(w k).code,
    (w k).code_mem (hmem k).2.2 ((w k).length_le_scale (hmem k).2.1 (hmem k).2.2 hu)⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hm : (w i).m = (w j).m := congrArg (fun c : C ↦ c.val.2.2) hij
    apply Subtype.ext
    apply prime_gap_index_unique (w i).gap_left ((w i).later_nonempty.trans_lt (w i).gap_right)
    · rw [hm]
      exact (w j).gap_left
    · rw [hm]
      exact (w j).later_nonempty.trans_lt (w j).gap_right
  have hcard := Fintype.card_le_of_injective f hinj
  have hcount : S.card ≤ ∑ p ∈ lengthPairs (2 ^ (4 * u)),
      (intervalSolutions (2 ^ (60 * u)) p.1 p.2).card := by
    simpa only [Fintype.card_coe, C, allIntervalSolutions, Finset.card_sigma] using hcard
  exact hcount.trans (sum_intervalSolutions_card_bound_scale u)

end Erdos421
