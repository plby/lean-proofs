/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Abel

/-!
# Partial Abel sums for generalized parking words

The numbers in this file are the Abel (rooted-forest) factors which occur in
the first-violation decomposition of a generalized parking word.
-/

namespace Erdos896.Ford

open scoped BigOperators

/-- The rooted-forest factor in Abel's generalized binomial identity. -/
def parkingAbelP : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, W => W * (W + j + 1) ^ j

@[simp] theorem parkingAbelP_zero (W : ℕ) : parkingAbelP 0 W = 1 := rfl

@[simp] theorem parkingAbelP_succ (j W : ℕ) :
    parkingAbelP (j + 1) W = W * (W + j + 1) ^ j := rfl

/-- The natural Abel factor agrees with evaluation of the real Abel
polynomial at a natural argument. -/
theorem cast_parkingAbelP (j W : ℕ) :
    (parkingAbelP j W : ℝ) = (abelPolynomial j).eval (W : ℝ) := by
  cases j with
  | zero => simp
  | succ j =>
      rw [parkingAbelP_succ, eval_abelPolynomial_succ]
      push_cast
      ring

/-- Abel's generalized power identity, in the form used by the parking
first-violation recurrence. -/
theorem parkingAbel_power_identity_real (k : ℕ) (W B : ℝ) :
    (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (abelPolynomial j).eval W *
          (B - j) ^ (k - j)) =
      (W + B) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have habel := abelPolynomial_binomial_eval (k + 1) W (B - (k + 1))
      rw [Finset.sum_range_succ] at habel
      have hfirst :
          (∑ j ∈ Finset.range (k + 1),
              ((k + 1).choose j : ℝ) * (abelPolynomial j).eval W *
                ((B - (k + 1)) * (B - j) ^ (k - j))) +
              (abelPolynomial (k + 1)).eval W =
            (abelPolynomial (k + 1)).eval (W + B - (k + 1)) := by
        calc
          (∑ j ∈ Finset.range (k + 1),
                ((k + 1).choose j : ℝ) * (abelPolynomial j).eval W *
                  ((B - (k + 1)) * (B - j) ^ (k - j))) +
              (abelPolynomial (k + 1)).eval W =
              (∑ j ∈ Finset.range (k + 1),
                ((k + 1).choose j : ℝ) * (abelPolynomial j).eval W *
                  (abelPolynomial (k + 1 - j)).eval (B - (k + 1))) +
                ((k + 1).choose (k + 1) : ℝ) *
                  (abelPolynomial (k + 1)).eval W *
                  (abelPolynomial (k + 1 - (k + 1))).eval (B - (k + 1)) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              have hj : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
              have hn : k + 1 - j = (k - j) + 1 := by omega
              rw [hn, eval_abelPolynomial_succ]
              rw [Nat.cast_sub hj]
              push_cast
              congr 1
              ring
            · simp
          _ = (abelPolynomial (k + 1)).eval (W + (B - (k + 1))) := habel
          _ = (abelPolynomial (k + 1)).eval (W + B - (k + 1)) := by ring_nf
      have hdecomp :
          (∑ j ∈ Finset.range (k + 1),
              ((k + 1).choose j : ℝ) * (abelPolynomial j).eval W *
                (B - j) ^ (k + 1 - j)) =
            (∑ j ∈ Finset.range (k + 1),
              ((k + 1).choose j : ℝ) * (abelPolynomial j).eval W *
                ((B - (k + 1)) * (B - j) ^ (k - j))) +
              (k + 1) *
                (∑ j ∈ Finset.range (k + 1),
                  (k.choose j : ℝ) * (abelPolynomial j).eval W *
                    (B - j) ^ (k - j)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hj : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
        have hchoose :
            (((k + 1).choose j : ℕ) : ℝ) * ((k + 1 : ℝ) - j) =
              (k + 1 : ℝ) * (k.choose j : ℝ) := by
          have hn := (Nat.choose_mul_succ_eq k j).symm
          have hnR :
              ((((k + 1).choose j) * (k + 1 - j) : ℕ) : ℝ) =
                (((k + 1) * k.choose j : ℕ) : ℝ) := by
            exact_mod_cast (by simpa [Nat.mul_comm] using hn)
          push_cast [Nat.cast_sub (by omega : j ≤ k + 1)] at hnR
          simpa using hnR
        rw [show B - j = (B - (k + 1)) + (k + 1 - j) by
          push_cast; ring]
        rw [add_mul]
        linear_combination
          (abelPolynomial j).eval W * (B - j) ^ (k - j) * hchoose
      calc
        (∑ j ∈ Finset.range (k + 1),
              ((k + 1).choose j : ℝ) * (abelPolynomial j).eval W *
                (B - j) ^ (k + 1 - j)) +
            ((k + 1).choose (k + 1) : ℝ) *
              (abelPolynomial (k + 1)).eval W *
                (B - (k + 1 : ℕ)) ^ (k + 1 - (k + 1)) =
            ((∑ j ∈ Finset.range (k + 1),
                ((k + 1).choose j : ℝ) * (abelPolynomial j).eval W *
                  ((B - (k + 1)) * (B - j) ^ (k - j))) +
                (abelPolynomial (k + 1)).eval W) +
              (k + 1) *
                (∑ j ∈ Finset.range (k + 1),
                  (k.choose j : ℝ) * (abelPolynomial j).eval W *
                    (B - j) ^ (k - j)) := by
              rw [hdecomp]
              simp
              ring
        _ = (abelPolynomial (k + 1)).eval (W + B - (k + 1)) +
              (k + 1) * (W + B) ^ k := by rw [hfirst, ih]
        _ = (W + B) ^ (k + 1) := by
              rw [eval_abelPolynomial_succ]
              push_cast
              ring

/-- The endpoint form of Abel's identity.  This is precisely the recurrence
which identifies the `U = 1` parking factor. -/
theorem parkingAbelP_add_recurrence (k W : ℕ) (hk : 1 ≤ k) :
    parkingAbelP k W +
        (∑ j ∈ Finset.range k,
          k.choose j * parkingAbelP j W * (k - 1 - j) ^ (k - j)) =
      (k - 1 + W) ^ k := by
  have hreal := parkingAbel_power_identity_real k (W : ℝ) (k - 1 : ℕ)
  have hnat :
      (∑ j ∈ Finset.range (k + 1),
          k.choose j * parkingAbelP j W * (k - 1 - j) ^ (k - j)) =
        (k - 1 + W) ^ k := by
    apply Nat.cast_injective (R := ℝ)
    rw [Nat.cast_sum]
    push_cast
    simp_rw [cast_parkingAbelP]
    convert hreal using 1
    · apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      by_cases hjk : j = k
      · subst j
        simp
      · have hjpred : j ≤ k - 1 := by omega
        rw [Nat.cast_sub hjpred, Nat.cast_sub hk]
    · ring
  rw [Finset.sum_range_succ] at hnat
  simpa [Nat.add_comm] using hnat

/-- Subtractive form of `parkingAbelP_add_recurrence`, convenient when a
first-violation count has already been written as a complement. -/
theorem parkingAbelP_recurrence (k W : ℕ) (hk : 1 ≤ k) :
    parkingAbelP k W =
      (k - 1 + W) ^ k -
        ∑ j ∈ Finset.range k,
          k.choose j * parkingAbelP j W * (k - 1 - j) ^ (k - j) := by
  exact Nat.eq_sub_of_add_eq (parkingAbelP_add_recurrence k W hk)

/-- For the parameters arising from the parking remainder, the positivity
cutoff in Ford's sum is exactly `U < j`.  This is the form in which the
partial Abel estimate is normally applied. -/
theorem fordLemmaFourTwoSum_parking (k U W : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) :
    fordLemmaFourTwoSum (k + 1) (-(U : ℝ)) ((W : ℝ) - 1) =
      ∑ j ∈ Finset.Icc (U + 1) k,
        ((k + 1).choose j : ℝ) * ((j : ℝ) - U) ^ (j - 1) *
          ((W : ℝ) + (k - j : ℕ)) ^ (k - j) := by
  unfold fordLemmaFourTwoSum
  have hset :
      (Finset.Icc 1 ((k + 1) - 1)).filter
          (fun j : ℕ ↦ 0 < -(U : ℝ) + (j : ℝ)) =
        Finset.Icc (U + 1) k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [show k + 1 - 1 = k by omega]
    constructor
    · rintro ⟨⟨hjone, hjk⟩, hjpos⟩
      have hUjR : (U : ℝ) < j := by linarith
      have hUj : U < j := by exact_mod_cast hUjR
      exact ⟨by omega, hjk⟩
    · rintro ⟨hUj, hjk⟩
      have hUjR : (U : ℝ) < j := by exact_mod_cast (by omega : U < j)
      exact ⟨⟨by omega, hjk⟩, by linarith⟩
  rw [hset]
  apply Finset.sum_congr rfl
  intro j hj
  have hjtop : j ≤ k := (Finset.mem_Icc.mp hj).2
  rw [show k + 1 - j - 1 = k - j by omega]
  congr 1
  · ring
  · congr 1
    rw [show k + 1 - j = (k - j) + 1 by omega,
      Nat.cast_add, Nat.cast_one, Nat.cast_sub hjtop]
    push_cast
    ring

/-! ## The strict Raney multiplicity bound -/

/-- Every nonempty prefix of the indicated cyclic cut has negative sum. -/
def strictNegativeRotate (l : List ℤ) (r : ℕ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ l.length → ((l.rotate r).take j).sum < 0

noncomputable instance (l : List ℤ) :
    DecidablePred (strictNegativeRotate l) :=
  Classical.decPred _

private theorem strictNegativeRotate_take_between
    (l : List ℤ) {r q : ℕ} (hrq : r < q) (hq : q ≤ l.length) :
    ((l.rotate r).take (q - r)).sum =
      (l.take q).sum - (l.take r).sum := by
  have hr : r ≤ l.length := hrq.le.trans hq
  rw [List.rotate_eq_drop_append_take hr]
  rw [List.take_append_of_le_length]
  · have hsplit :
        (l.take (r + (q - r))).sum =
          (l.take r).sum + ((l.drop r).take (q - r)).sum := by
      rw [List.take_add, List.sum_append]
    rw [show r + (q - r) = q by omega] at hsplit
    omega
  · simp
    omega

private theorem strictNegativeRotate_take_wrap
    (l : List ℤ) {r q : ℕ} (hrq : r < q) (hq : q < l.length) :
    ((l.rotate q).take (l.length - q + r)).sum =
      l.sum - (l.take q).sum + (l.take r).sum := by
  have hqle : q ≤ l.length := hq.le
  rw [List.rotate_eq_drop_append_take hqle]
  rw [List.take_append]
  have hdrop : (l.drop q).length = l.length - q := List.length_drop
  have htakeDrop : (l.drop q).take (l.length - q + r) = l.drop q := by
    apply List.take_of_length_le
    omega
  rw [htakeDrop, List.sum_append]
  have hsub : l.length - q + r - (l.drop q).length = r := by omega
  rw [hsub, List.take_take, min_eq_left]
  · have hsplit : (l.take q).sum + (l.drop q).sum = l.sum := by
      simpa using congrArg List.sum (l.take_append_drop q)
    omega
  · omega

private theorem strictNegativeRotate_score_pair
    {l : List ℤ} {U r q : ℕ}
    (hsum : l.sum = -(U : ℤ))
    (hr : r < l.length) (hq : q < l.length)
    (hgoodr : strictNegativeRotate l r)
    (hgoodq : strictNegativeRotate l q)
    (hrq : r < q) :
    (l.take q).sum < (l.take r).sum ∧
      (l.take r).sum - (l.take q).sum < U := by
  have hjpos : 1 ≤ q - r := by omega
  have hjle : q - r ≤ l.length := by omega
  have hneg1 := hgoodr (q - r) hjpos hjle
  rw [strictNegativeRotate_take_between l hrq hq.le] at hneg1
  have hwrapPos : 1 ≤ l.length - q + r := by omega
  have hwrapLe : l.length - q + r ≤ l.length := by omega
  have hneg2 := hgoodq (l.length - q + r) hwrapPos hwrapLe
  rw [strictNegativeRotate_take_wrap l hrq hq] at hneg2
  rw [hsum] at hneg2
  constructor <;> omega

/-- Strict Raney upper bound.  If an integer list has total sum `-U`, at
most `U` cyclic cuts can have every nonempty prefix strictly negative.

For a confined-parking occupancy vector `b`, the transformed list
`[-b₀, 1-b₁, …]` has total `-U`, and the parking barriers say exactly
that its cut at zero has this property. -/
theorem card_strictNegativeRotate_le
    (l : List ℤ) (U : ℕ) (hsum : l.sum = -(U : ℤ)) :
    ((Finset.range l.length).filter (strictNegativeRotate l)).card ≤ U := by
  classical
  let S := (Finset.range l.length).filter (strictNegativeRotate l)
  by_cases hS : S.Nonempty
  · have hU : 0 < U := by
      obtain ⟨r, hr⟩ := hS
      have hrange : r < l.length :=
        Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hgood := (Finset.mem_filter.mp hr).2
      have hfull := hgood l.length (by omega) (by omega)
      have htake : (l.rotate r).take l.length = l.rotate r := by
        apply List.take_of_length_le
        simp
      rw [htake] at hfull
      have hrotSum : (l.rotate r).sum = l.sum := by
        rw [List.rotate_eq_drop_append_take (Nat.le_of_lt hrange),
          List.sum_append]
        have hsplit : (l.take r).sum + (l.drop r).sum = l.sum := by
          simpa using congrArg List.sum (l.take_append_drop r)
        omega
      rw [hrotSum, hsum] at hfull
      omega
    let r0 := S.min' hS
    have hr0S : r0 ∈ S := Finset.min'_mem S hS
    have hr0lt : r0 < l.length :=
      Finset.mem_range.mp (Finset.mem_filter.mp hr0S).1
    have hr0good : strictNegativeRotate l r0 :=
      (Finset.mem_filter.mp hr0S).2
    let code : {r // r ∈ S} → Fin U := fun r ↦ ⟨
      Int.toNat ((l.take r0).sum - (l.take r.1).sum), by
        have hr0le : r0 ≤ r.1 := Finset.min'_le S r.1 r.2
        by_cases heq : r0 = r.1
        · rw [heq]
          simpa using hU
        · have hr0r : r0 < r.1 := lt_of_le_of_ne hr0le heq
          have hrlt : r.1 < l.length :=
            Finset.mem_range.mp (Finset.mem_filter.mp r.2).1
          have hrgood : strictNegativeRotate l r.1 :=
            (Finset.mem_filter.mp r.2).2
          have hp := strictNegativeRotate_score_pair hsum hr0lt hrlt
            hr0good hrgood hr0r
          have hnonneg : 0 ≤ (l.take r0).sum - (l.take r.1).sum := by omega
          rw [Int.toNat_lt hnonneg]
          exact hp.2⟩
    have hinj : Function.Injective code := by
      intro r q heq
      apply Subtype.ext
      by_contra hrq
      rcases lt_or_gt_of_ne hrq with hrq | hqr
      · have hrlt : r.1 < l.length :=
          Finset.mem_range.mp (Finset.mem_filter.mp r.2).1
        have hqlt : q.1 < l.length :=
          Finset.mem_range.mp (Finset.mem_filter.mp q.2).1
        have hrgood : strictNegativeRotate l r.1 :=
          (Finset.mem_filter.mp r.2).2
        have hqgood : strictNegativeRotate l q.1 :=
          (Finset.mem_filter.mp q.2).2
        have hp := strictNegativeRotate_score_pair hsum hrlt hqlt
          hrgood hqgood hrq
        have hdiffR : 0 ≤ (l.take r0).sum - (l.take r.1).sum := by
          have hmin := Finset.min'_le S r.1 r.2
          by_cases h0 : r0 = r.1
          · rw [h0]
            simp
          · have hpair := strictNegativeRotate_score_pair hsum hr0lt hrlt
                hr0good hrgood (lt_of_le_of_ne hmin h0)
            omega
        have hdiffQ : 0 ≤ (l.take r0).sum - (l.take q.1).sum := by
          have hmin := Finset.min'_le S q.1 q.2
          by_cases h0 : r0 = q.1
          · rw [h0]
            simp
          · have hpair := strictNegativeRotate_score_pair hsum hr0lt hqlt
                hr0good hqgood (lt_of_le_of_ne hmin h0)
            omega
        have hnat := congrArg Fin.val heq
        dsimp [code] at hnat
        have hint := congrArg (fun n : ℕ ↦ (n : ℤ)) hnat
        rw [Int.toNat_of_nonneg hdiffR, Int.toNat_of_nonneg hdiffQ] at hint
        omega
      · have hrlt : r.1 < l.length :=
          Finset.mem_range.mp (Finset.mem_filter.mp r.2).1
        have hqlt : q.1 < l.length :=
          Finset.mem_range.mp (Finset.mem_filter.mp q.2).1
        have hrgood : strictNegativeRotate l r.1 :=
          (Finset.mem_filter.mp r.2).2
        have hqgood : strictNegativeRotate l q.1 :=
          (Finset.mem_filter.mp q.2).2
        have hp := strictNegativeRotate_score_pair hsum hqlt hrlt
          hqgood hrgood hqr
        have hdiffR : 0 ≤ (l.take r0).sum - (l.take r.1).sum := by
          have hmin := Finset.min'_le S r.1 r.2
          by_cases h0 : r0 = r.1
          · rw [h0]
            simp
          · have hpair := strictNegativeRotate_score_pair hsum hr0lt hrlt
                hr0good hrgood (lt_of_le_of_ne hmin h0)
            omega
        have hdiffQ : 0 ≤ (l.take r0).sum - (l.take q.1).sum := by
          have hmin := Finset.min'_le S q.1 q.2
          by_cases h0 : r0 = q.1
          · rw [h0]
            simp
          · have hpair := strictNegativeRotate_score_pair hsum hr0lt hqlt
                hr0good hqgood (lt_of_le_of_ne hmin h0)
            omega
        have hnat := congrArg Fin.val heq
        dsimp [code] at hnat
        have hint := congrArg (fun n : ℕ ↦ (n : ℤ)) hnat
        rw [Int.toNat_of_nonneg hdiffR, Int.toNat_of_nonneg hdiffQ] at hint
        omega
    have hcard := Fintype.card_le_of_injective code hinj
    simpa [S] using hcard
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    have hzero : S.card = 0 := by rw [hS]; simp
    simpa [S] using hzero.trans_le (Nat.zero_le U)

end Erdos896.Ford
