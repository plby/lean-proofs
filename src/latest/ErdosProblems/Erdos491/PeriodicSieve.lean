import Mathlib

/-!
# Finite periodic second moments

Only complete-period cancellation, the Chinese remainder theorem, and
bounding the final incomplete period are used here.
-/

open scoped BigOperators

namespace Erdos491

lemma sum_range_periodic_mul (f : ℕ → ℝ) (q k : ℕ)
    (hf : Function.Periodic f q) :
    (∑ n ∈ Finset.range (k * q), f n) = (k : ℝ) * ∑ n ∈ Finset.range q, f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have heq : (∑ n ∈ Finset.range q, f (k * q + n)) =
          ∑ n ∈ Finset.range q, f n := by
        apply Finset.sum_congr rfl
        intro n _
        simpa only [Nat.cast_id, add_comm] using hf.nat_mul k n
      rw [heq]
      push_cast
      ring

lemma sum_range_periodic (f : ℕ → ℝ) (q T : ℕ)
    (hf : Function.Periodic f q) :
    (∑ n ∈ Finset.range T, f n) =
      ((T / q : ℕ) : ℝ) * (∑ n ∈ Finset.range q, f n) +
        ∑ n ∈ Finset.range (T % q), f n := by
  conv_lhs => rw [← Nat.div_add_mod T q, Nat.mul_comm q]
  rw [Finset.sum_range_add, sum_range_periodic_mul f q (T / q) hf]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  simpa only [Nat.cast_id, add_comm] using hf.nat_mul (T / q) n

lemma abs_sum_range_periodic_zero (f : ℕ → ℝ) (q T : ℕ) (hq : 0 < q)
    (hf : Function.Periodic f q) (hzero : ∑ n ∈ Finset.range q, f n = 0)
    (hbound : ∀ n, |f n| ≤ 1) :
    |∑ n ∈ Finset.range T, f n| ≤ q := by
  rw [sum_range_periodic f q T hf, hzero, mul_zero, zero_add]
  calc
    _ ≤ ∑ n ∈ Finset.range (T % q), |f n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (T % q), (1 : ℝ) :=
      Finset.sum_le_sum fun n _ ↦ hbound n
    _ = (T % q : ℕ) := by simp
    _ ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt T hq).le

lemma sum_range_periodic_le (f : ℕ → ℝ) (q T : ℕ) (hq : 0 < q)
    (hf : Function.Periodic f q) {D : ℝ} (hD : 0 ≤ D)
    (hmean : ∑ n ∈ Finset.range q, f n ≤ D)
    (hbound : ∀ n, f n ≤ 1) :
    (∑ n ∈ Finset.range T, f n) ≤ (T : ℝ) / q * D + q := by
  rw [sum_range_periodic f q T hf]
  have hrem : (∑ n ∈ Finset.range (T % q), f n) ≤ q := by
    calc
      _ ≤ ∑ _n ∈ Finset.range (T % q), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ ↦ hbound n
      _ = (T % q : ℕ) := by simp
      _ ≤ (q : ℝ) := by exact_mod_cast (Nat.mod_lt T hq).le
  exact add_le_add
    ((mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right Nat.cast_div_le hD)) hrem

lemma sum_range_zmod {q : ℕ} [NeZero q] (F : ZMod q → ℝ) :
    (∑ n ∈ Finset.range q, F n) = ∑ z : ZMod q, F z := by
  classical
  apply Finset.sum_bij (fun (n : ℕ) _ ↦ (n : ZMod q))
  · simp
  · intro a ha b hb hab
    have h := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using h
  · intro z _
    exact ⟨z.val, Finset.mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · simp

noncomputable def centeredResidue {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (z : ZMod q) : ℝ :=
  (if z ∈ A then 1 else 0) - (A.card : ℝ) / q

lemma centeredResidue_mean_zero {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    ∑ z : ZMod q, centeredResidue A z = 0 := by
  classical
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  simp only [centeredResidue, Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp
  ring

lemma abs_centeredResidue_le_one {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (z : ZMod q) : |centeredResidue A z| ≤ 1 := by
  classical
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hcard : (A.card : ℝ) ≤ q := by
    exact_mod_cast (show A.card ≤ q by simpa using A.card_le_univ)
  have hnonneg : 0 ≤ (A.card : ℝ) / q := by positivity
  have hle : (A.card : ℝ) / q ≤ 1 := (div_le_one hq).mpr hcard
  unfold centeredResidue
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

lemma centeredResidue_square_sum {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) :
    (∑ z : ZMod q, centeredResidue A z ^ 2) ≤ A.card := by
  classical
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have heq (z : ZMod q) : centeredResidue A z ^ 2 =
      (if z ∈ A then (1 : ℝ) else 0) * (1 - 2 * (A.card : ℝ) / q) +
        ((A.card : ℝ) / q) ^ 2 := by
    unfold centeredResidue
    split_ifs <;> ring
  simp_rw [heq, Finset.sum_add_distrib, ← Finset.sum_mul]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hnonneg : 0 ≤ (A.card : ℝ) ^ 2 / q := div_nonneg (sq_nonneg _) hq.le
  calc
    _ = (A.card : ℝ) - (A.card : ℝ) ^ 2 / q := by field_simp; ring
    _ ≤ _ := sub_le_self _ hnonneg

lemma periodic_natCast {q : ℕ} (F : ZMod q → ℝ) :
    Function.Periodic (fun n : ℕ ↦ F n) q := by
  intro n
  simp

lemma sum_range_mul_of_coprime {q r : ℕ} [NeZero q] [NeZero r]
    (hcop : q.Coprime r) (F : ZMod q → ℝ) (G : ZMod r → ℝ) :
    (∑ n ∈ Finset.range (q * r), F n * G n) =
      (∑ x : ZMod q, F x) * ∑ y : ZMod r, G y := by
  classical
  let e := ZMod.chineseRemainder hcop
  have he (n : ℕ) : e (n : ZMod (q * r)) = ((n : ZMod q), (n : ZMod r)) := by
    rw [map_natCast]
    rfl
  calc
    _ = ∑ n ∈ Finset.range (q * r), F (e (n : ZMod (q * r))).1 *
        G (e (n : ZMod (q * r))).2 := by simp only [he]
    _ = ∑ z : ZMod (q * r), F (e z).1 * G (e z).2 :=
      sum_range_zmod (fun z : ZMod (q * r) ↦ F (e z).1 * G (e z).2)
    _ = ∑ z : ZMod q × ZMod r, F z.1 * G z.2 :=
      e.toEquiv.sum_comp (fun z : ZMod q × ZMod r ↦ F z.1 * G z.2)
    _ = _ := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul]

lemma centeredResidue_covariance {q r : ℕ} [NeZero q] [NeZero r]
    (hcop : q.Coprime r) (A : Finset (ZMod q)) (B : Finset (ZMod r)) (T : ℕ) :
    |∑ n ∈ Finset.range T, centeredResidue A n * centeredResidue B n| ≤
      (q : ℝ) * r := by
  have hper : Function.Periodic
      (fun n : ℕ ↦ centeredResidue A n * centeredResidue B n) (q * r) := by
    intro n
    simp [Nat.cast_add, Nat.cast_mul]
  have hzero : (∑ n ∈ Finset.range (q * r),
      centeredResidue A n * centeredResidue B n) = 0 := by
    rw [sum_range_mul_of_coprime hcop, centeredResidue_mean_zero, zero_mul]
  have hbound (n : ℕ) : |centeredResidue A n * centeredResidue B n| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul (abs_centeredResidue_le_one A n)
      (abs_centeredResidue_le_one B n) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [Nat.cast_mul] using abs_sum_range_periodic_zero _ (q * r) T
    (Nat.mul_pos (NeZero.pos q) (NeZero.pos r)) hper hzero hbound

lemma centeredResidue_diagonal {q : ℕ} [NeZero q]
    (A : Finset (ZMod q)) (T : ℕ) :
    (∑ n ∈ Finset.range T, centeredResidue A n ^ 2) ≤
      (T : ℝ) / q * A.card + q := by
  apply sum_range_periodic_le _ q T (NeZero.pos q)
    (periodic_natCast (fun z ↦ centeredResidue A z ^ 2)) (Nat.cast_nonneg _)
  · rw [sum_range_zmod (fun z ↦ centeredResidue A z ^ 2)]
    exact centeredResidue_square_sum A
  · intro n
    have h := (abs_le.mp (abs_centeredResidue_le_one A n))
    nlinarith [sq_nonneg (centeredResidue A n - 1),
      mul_nonneg (by linarith : 0 ≤ 1 - centeredResidue A n)
        (by linarith : 0 ≤ 1 + centeredResidue A n)]

end Erdos491
