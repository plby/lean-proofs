import ErdosProblems.Erdos1141.BurgessCounting

/-!
# Weighted fourth moments for Burgess averaging
-/

open scoped BigOperators

namespace Erdos1141

/-- Two applications of Cauchy–Schwarz, using the integrality of the weights. -/
lemma weighted_sum_fourth_le {ι : Type*} [Fintype ι] (ν : ι → ℕ) (T : ι → ℝ) :
    (∑ x, (ν x : ℝ) * T x) ^ 4 ≤
      (∑ x, (ν x : ℝ) ^ 2) ^ 3 * ∑ x, T x ^ 4 := by
  have hfirst := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x ↦ Real.sqrt (ν x : ℝ)) (fun x ↦ Real.sqrt (ν x : ℝ) * T x)
  have hid : ∀ x, Real.sqrt (ν x : ℝ) * (Real.sqrt (ν x : ℝ) * T x) = (ν x : ℝ) * T x := by
    intro x
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp only [hid, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hfirst
  have hsecond := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x ↦ (ν x : ℝ)) (fun x ↦ T x ^ 2)
  have hweights : ∑ x, (ν x : ℝ) ≤ ∑ x, (ν x : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro x _
    have hn : ν x ≤ ν x ^ 2 := by simpa [pow_two] using Nat.le_mul_self (ν x)
    exact_mod_cast hn
  have hV : 0 ≤ ∑ x, (ν x : ℝ) * T x ^ 2 := by positivity
  have hE : 0 ≤ ∑ x, (ν x : ℝ) ^ 2 := by positivity
  have hS : 0 ≤ ∑ x, (ν x : ℝ) := by positivity
  have hM : 0 ≤ ∑ x, T x ^ 4 := by positivity
  calc
    (∑ x, (ν x : ℝ) * T x) ^ 4 = ((∑ x, (ν x : ℝ) * T x) ^ 2) ^ 2 := by ring
    _ ≤ ((∑ x, (ν x : ℝ)) * ∑ x, (ν x : ℝ) * T x ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ = (∑ x, (ν x : ℝ)) ^ 2 * (∑ x, (ν x : ℝ) * T x ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (∑ x, (ν x : ℝ) ^ 2) ^ 2 *
        ((∑ x, (ν x : ℝ) ^ 2) * ∑ x, T x ^ 4) := by
      apply mul_le_mul (pow_le_pow_left₀ hS hweights 2)
      · simpa only [← pow_mul] using hsecond
      · positivity
      · positivity
    _ = _ := by ring

lemma sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ k ∈ Finset.range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

lemma abs_sum_range_shift_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (M N : ℕ) :
    |∑ n ∈ Finset.range N, f (M + n)| ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, |f (M + n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := Finset.sum_le_sum (fun n _ ↦ hf (M + n))
    _ = _ := by simp

/-- Translating an interval changes a bounded sum by at most twice the displacement. -/
lemma abs_sum_range_shift_sub_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N H : ℕ) :
    |(∑ n ∈ Finset.range N, f (H + n)) - ∑ n ∈ Finset.range N, f n| ≤ 2 * H := by
  have htot : (∑ n ∈ Finset.range N, f n) + (∑ n ∈ Finset.range H, f (N + n)) =
      (∑ n ∈ Finset.range H, f n) + (∑ n ∈ Finset.range N, f (H + n)) := by
    rw [← Finset.sum_range_add, ← Finset.sum_range_add, Nat.add_comm N H]
  have hid : (∑ n ∈ Finset.range N, f (H + n)) - ∑ n ∈ Finset.range N, f n =
      (∑ n ∈ Finset.range H, f (N + n)) - ∑ n ∈ Finset.range H, f n := by linarith
  rw [hid]
  calc
    _ ≤ |∑ n ∈ Finset.range H, f (N + n)| + |∑ n ∈ Finset.range H, f n| := abs_sub _ _
    _ ≤ (H : ℝ) + H := add_le_add (abs_sum_range_shift_le f hf N H)
      (by simpa using abs_sum_range_shift_le f hf 0 H)
    _ = _ := by ring

lemma abs_sum_Icc_shift_sub_le (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) (N H : ℕ) :
    |(∑ n ∈ Finset.Icc 1 N, f (n + H)) - ∑ n ∈ Finset.Icc 1 N, f n| ≤ 2 * H := by
  rw [sum_Icc_one_eq_sum_range, sum_Icc_one_eq_sum_range]
  simpa only [Nat.add_comm H, Nat.add_right_comm] using
    abs_sum_range_shift_sub_le (fun n ↦ f (n + 1)) (fun n ↦ hf (n + 1)) N H

lemma residue_ratio_eq_iff {q a n : ℕ} {x : ZMod q} (ha : a.Coprime q) :
    (n : ZMod q) * (a : ZMod q)⁻¹ = x ↔ (n : ZMod q) = x * (a : ZMod q) := by
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  constructor
  · intro h
    rw [← h, mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
  · intro h
    rw [h, mul_assoc, ZMod.mul_inv_of_unit _ hu, mul_one]

/-- Regroup a double sum by its residue-class ratio. -/
lemma ratioFiber_weighted_sum (q A N : ℕ) [NeZero q] (g : ZMod q → ℝ) :
    (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) * g x) =
      ∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ a.Coprime q),
        ∑ n ∈ Finset.Icc 1 N, g ((n : ZMod q) * (a : ZMod q)⁻¹) := by
  classical
  let S := ((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).product (Finset.Icc 1 N)
  let ratio : ℕ × ℕ → ZMod q := fun z ↦ (z.2 : ZMod q) * (z.1 : ZMod q)⁻¹
  have hFiber : ∀ x : ZMod q, S.filter (fun z ↦ ratio z = x) = ratioFiber q A N x := by
    intro x
    ext ⟨a, n⟩
    by_cases ha : a.Coprime q
    · simp [S, ratio, ratioFiber, residue_ratio_eq_iff ha, and_assoc]
      tauto
    · simp [S, ratio, ratioFiber, ha]
  calc
    _ = ∑ x : ZMod q, ∑ _z ∈ S.filter (fun z ↦ ratio z = x), g x := by
      simp [hFiber]
    _ = ∑ z ∈ S, g (ratio z) := Finset.sum_fiberwise' S ratio g
    _ = _ := by simp [S, ratio, Finset.sum_product]

lemma averaged_shift_error (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1)
    (s : Finset ℕ) (A B N : ℕ) (hs : ∀ a ∈ s, a ≤ A) :
    |(s.card : ℝ) * B * (∑ n ∈ Finset.Icc 1 N, f n) -
      ∑ a ∈ s, ∑ b ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 N, f (n + a * b)| ≤
      2 * s.card * B * A * B := by
  have hpoint : ∀ a ∈ s, ∀ b ∈ Finset.Icc 1 B,
      |(∑ n ∈ Finset.Icc 1 N, f n) - ∑ n ∈ Finset.Icc 1 N, f (n + a * b)| ≤
        2 * (A : ℝ) * B := by
    intro a ha b hb
    have hshift := abs_sum_Icc_shift_sub_le f hf N (a * b)
    rw [abs_sub_comm] at hshift
    have hprod : ((a * b : ℕ) : ℝ) ≤ (A : ℝ) * B := by
      exact_mod_cast Nat.mul_le_mul (hs a ha) (Finset.mem_Icc.mp hb).2
    exact hshift.trans (by linarith)
  have hid : (s.card : ℝ) * B * (∑ n ∈ Finset.Icc 1 N, f n) -
      (∑ a ∈ s, ∑ b ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 N, f (n + a * b)) =
      ∑ a ∈ s, ∑ b ∈ Finset.Icc 1 B,
        ((∑ n ∈ Finset.Icc 1 N, f n) - ∑ n ∈ Finset.Icc 1 N, f (n + a * b)) := by
    simp [Finset.sum_sub_distrib]
    ring
  rw [hid]
  calc
    _ ≤ ∑ a ∈ s, |∑ b ∈ Finset.Icc 1 B,
        ((∑ n ∈ Finset.Icc 1 N, f n) - ∑ n ∈ Finset.Icc 1 N, f (n + a * b))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ s, ∑ b ∈ Finset.Icc 1 B,
        |(∑ n ∈ Finset.Icc 1 N, f n) - ∑ n ∈ Finset.Icc 1 N, f (n + a * b)| :=
      Finset.sum_le_sum fun a _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ s, ∑ _b ∈ Finset.Icc 1 B, 2 * (A : ℝ) * B := by
      apply Finset.sum_le_sum; intro a ha
      exact Finset.sum_le_sum fun b hb ↦ hpoint a ha b hb
    _ = _ := by simp; ring

lemma character_shift_sum_abs {q : ℕ} (χ : ZMod q → ℝ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hunit : ∀ a : ℕ, a.Coprime q → |χ (a : ZMod q)| = 1)
    (a n B : ℕ) (ha : a.Coprime q) :
    |∑ b ∈ Finset.Icc 1 B, χ ((n + a * b : ℕ) : ZMod q)| =
      |∑ b ∈ Finset.Icc 1 B, χ ((n : ZMod q) * (a : ZMod q)⁻¹ + b)| := by
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have heq : ∀ b : ℕ, ((n + a * b : ℕ) : ZMod q) =
      (a : ZMod q) * ((n : ZMod q) * (a : ZMod q)⁻¹ + b) := by
    intro b
    push_cast
    calc
      (n : ZMod q) + a * b = ((a : ZMod q) * (a : ZMod q)⁻¹) * n + a * b := by
        rw [ZMod.mul_inv_of_unit _ hu, one_mul]
      _ = _ := by ring
  simp_rw [heq, hmul]
  rw [← Finset.mul_sum, abs_mul, hunit a ha, one_mul]

lemma character_averaged_sum_abs_le (q A B N : ℕ) [NeZero q] (χ : ZMod q → ℝ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hunit : ∀ a : ℕ, a.Coprime q → |χ (a : ZMod q)| = 1) :
    |∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ a.Coprime q),
      ∑ b ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 N, χ ((n + a * b : ℕ) : ZMod q)| ≤
      ∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) *
        |∑ b ∈ Finset.Icc 1 B, χ (x + b)| := by
  rw [ratioFiber_weighted_sum]
  conv_lhs => arg 1; arg 2; ext a; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ a.Coprime q),
        |∑ n ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 B, χ ((n + a * b : ℕ) : ZMod q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ (Finset.Icc 1 A).filter (fun a ↦ a.Coprime q),
        ∑ n ∈ Finset.Icc 1 N, |∑ b ∈ Finset.Icc 1 B, χ ((n + a * b : ℕ) : ZMod q)| :=
      Finset.sum_le_sum fun a _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl; intro a ha
      apply Finset.sum_congr rfl; intro n _
      exact character_shift_sum_abs χ hmul hunit a n B (Finset.mem_filter.mp ha).2

/-- The averaged short sums dominate a prefix sum, up to the translation error. -/
theorem character_prefix_average_le (q A B N : ℕ) [NeZero q] (χ : ZMod q → ℝ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hunit : ∀ a : ℕ, a.Coprime q → |χ (a : ZMod q)| = 1)
    (hbound : ∀ x, |χ x| ≤ 1) :
    (((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card : ℝ) * B *
        |∑ n ∈ Finset.Icc 1 N, χ n| ≤
      (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) *
        |∑ b ∈ Finset.Icc 1 B, χ (x + b)|) +
      2 * ((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card * B * A * B := by
  classical
  let s := (Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)
  let S := ∑ n ∈ Finset.Icc 1 N, χ (n : ZMod q)
  let V := ∑ a ∈ s, ∑ b ∈ Finset.Icc 1 B,
    ∑ n ∈ Finset.Icc 1 N, χ ((n + a * b : ℕ) : ZMod q)
  have herror := averaged_shift_error (fun n ↦ χ (n : ZMod q))
    (fun n ↦ hbound n) s A B N (fun a ha ↦
      (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2)
  have havg := character_averaged_sum_abs_le q A B N χ hmul hunit
  have htriangle : |(s.card : ℝ) * B * S| ≤ |V| + |(s.card : ℝ) * B * S - V| := by
    have h := abs_add_le V ((s.card : ℝ) * B * S - V)
    simpa only [add_sub_cancel] using h
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (Nat.cast_nonneg _)] at htriangle
  exact htriangle.trans (add_le_add havg herror)

/-- A finite Burgess inequality. All constants and averaging lengths remain explicit. -/
theorem character_prefix_fourth_le (q A B N : ℕ) [NeZero q] (χ : ZMod q → ℝ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hunit : ∀ a : ℕ, a.Coprime q → |χ (a : ZMod q)| = 1)
    (hbound : ∀ x, |χ x| ≤ 1) :
    ((((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card : ℝ) * B *
        |∑ n ∈ Finset.Icc 1 N, χ n|) ^ 4 ≤
      8 * ((∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) ^ 2) ^ 3 *
        ∑ x : ZMod q, (∑ b ∈ Finset.Icc 1 B, χ (x + b)) ^ 4) +
      8 * (2 * ((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card * B * A * B) ^ 4 := by
  classical
  let V := ∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) *
    |∑ b ∈ Finset.Icc 1 B, χ (x + b)|
  let R : ℝ := 2 * ((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card * B * A * B
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hweighted := weighted_sum_fourth_le (fun x : ZMod q ↦ (ratioFiber q A N x).card)
    (fun x ↦ |∑ b ∈ Finset.Icc 1 B, χ (x + b)|)
  simp only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] at hweighted
  norm_num only [← pow_mul] at hweighted
  have hprefix := character_prefix_average_le q A B N χ hmul hunit hbound
  calc
    _ ≤ (V + R) ^ 4 := pow_le_pow_left₀ (by positivity) hprefix 4
    _ ≤ 8 * (V ^ 4 + R ^ 4) := by
      have h := add_pow_le hV hR 4
      norm_num at h
      exact h
    _ ≤ _ := by dsimp [V, R] at *; nlinarith [hweighted]

/-- Divide the finite averaging inequality by the number of shifts. -/
theorem character_prefix_fourth_le_of_estimates (q A B N : ℕ) [NeZero q]
    (χ : ZMod q → ℝ)
    (hmul : ∀ x y, χ (x * y) = χ x * χ y)
    (hunit : ∀ a : ℕ, a.Coprime q → |χ (a : ZMod q)| = 1)
    (hbound : ∀ x, |χ x| ≤ 1)
    (D E M : ℝ) (hD : 0 < D) (hE : 0 ≤ E) (hM : 0 ≤ M) (hB : 0 < B)
    (hcount : D ≤ (((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card : ℝ))
    (henergy : (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) ^ 2) ≤ E)
    (hmoment : (∑ x : ZMod q, (∑ b ∈ Finset.Icc 1 B, χ (x + b)) ^ 4) ≤ M) :
    |∑ n ∈ Finset.Icc 1 N, χ n| ^ 4 ≤
      8 * E ^ 3 * M / (D * B) ^ 4 + 128 * ((A : ℝ) * B) ^ 4 := by
  classical
  let C : ℝ := ((Finset.Icc 1 A).filter (fun a ↦ a.Coprime q)).card
  have hC : 0 < C := hD.trans_le hcount
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hbase := character_prefix_fourth_le q A B N χ hmul hunit hbound
  have hmain :
      (∑ x : ZMod q, ((ratioFiber q A N x).card : ℝ) ^ 2) ^ 3 *
        (∑ x : ZMod q, (∑ b ∈ Finset.Icc 1 B, χ (x + b)) ^ 4) ≤ E ^ 3 * M := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) henergy 3) hmoment
      (by positivity) (pow_nonneg hE 3)
  have hnormalized : |∑ n ∈ Finset.Icc 1 N, χ n| ^ 4 ≤
      8 * E ^ 3 * M / (C * B) ^ 4 + 128 * ((A : ℝ) * B) ^ 4 := by
    apply (mul_le_mul_iff_of_pos_right (pow_pos (mul_pos hC hBr) 4)).mp
    have heq :
        (8 * E ^ 3 * M / (C * B) ^ 4 + 128 * ((A : ℝ) * B) ^ 4) * (C * B) ^ 4 =
          8 * E ^ 3 * M + 8 * (2 * C * B * A * B) ^ 4 := by
      field_simp
      ring
    rw [heq]
    dsimp [C] at *
    nlinarith [hbase, hmain]
  apply hnormalized.trans
  exact add_le_add (div_le_div_of_nonneg_left (by positivity) (pow_pos (mul_pos hD hBr) 4)
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hcount hBr.le) 4)) le_rfl

end Erdos1141
