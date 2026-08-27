import ErdosProblems.Erdos587.HooleyProgressionGcd

/-!
# Reindexing positive residue classes as short affine progressions

The progression starts with its least nonnegative residue. Enlarging its
last value to `X + q` permits one common index interval, including the
zero residue because its Delta weight is zero.
-/

open scoped BigOperators

namespace Erdos587

open Classical in
lemma delta_sum_residue_le_progression {q : ℕ} (hq : 0 < q) (X c : ℕ)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = c), w n) ≤
      ∑ j ∈ Finset.Icc 1 (X / q + 1), w (c + q * (j - 1)) := by
  let S := (Finset.Icc 1 X).filter (fun n => n % q = c)
  let J := Finset.Icc 1 (X / q + 1)
  let i : ℕ → ℕ := fun j => c + q * (j - 1)
  have hsub : S ⊆ J.image i := by
    intro n hn
    obtain ⟨hnX, hmod⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_image.mpr ⟨n / q + 1, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.succ_pos _,
        Nat.succ_le_succ (Nat.div_le_div_right (Finset.mem_Icc.mp hnX).2)⟩
    · dsimp only [i]
      simpa only [Nat.add_sub_cancel, hmod] using Nat.mod_add_div n q
  have hinj : Set.InjOn i (J : Set ℕ) := by
    intro j hj k hk heq
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hk1 := (Finset.mem_Icc.mp hk).1
    change c + q * (j - 1) = c + q * (k - 1) at heq
    have hmul : q * (j - 1) = q * (k - 1) := by omega
    have hsub := Nat.eq_of_mul_eq_mul_left hq hmul
    omega
  calc
    _ ≤ ∑ n ∈ J.image i, w n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hw n)
    _ = _ := Finset.sum_image hinj

lemma delta_residue_affine_value (c q : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    ((c : ℤ) - q + (q : ℤ) * j).natAbs = c + q * (j - 1) := by
  have heq : (c : ℤ) - q + (q : ℤ) * j = ((c + q * (j - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hj, Nat.cast_one]
    ring
  rw [heq, Int.natAbs_natCast]

theorem exists_delta_residue_progression_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ X q c : ℕ, 0 < q → c < q → 16 ≤ X / q →
      X + q ≤ (X / q + 1) ^ r →
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = c), (hooleyDelta n : ℝ)) ≤
        C * (Nat.gcd c q).divisors.card * (X / q + 1 : ℕ) *
          (max 1 (Real.log (Real.log ((X + q : ℕ) : ℝ)))) ^ 6 := by
  classical
  obtain ⟨C, hC, hmean⟩ := exists_hooleyDelta_progression_mean r hr
  refine ⟨C, hC, ?_⟩
  intro X q c hq hc hlength hsize
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hX : 1 ≤ X := by
    have hdiv := Nat.div_le_self X q
    omega
  have hvalues : ∀ j ∈ Finset.Icc 1 (X / q + 1),
      ((c : ℤ) - q + (q : ℤ) * j).natAbs ≤ X + q := by
    intro j hj
    obtain ⟨hj1, hjmax⟩ := Finset.mem_Icc.mp hj
    rw [delta_residue_affine_value c q hj1]
    have hjdiv : j - 1 ≤ X / q := by omega
    have hmul := Nat.mul_le_mul_left q hjdiv
    have hdiv := Nat.mul_div_le X q
    nlinarith
  have hbound := hmean ((c : ℤ) - q) q hqZ (X + q) (X / q + 1)
    (by omega) (by omega) hsize hvalues
  have hgcd : Int.gcd ((c : ℤ) - q) q = Nat.gcd c q := by
    rw [Int.gcd_sub_self_left, Int.gcd_natCast_natCast]
  rw [hgcd] at hbound
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 (X / q + 1), (hooleyDelta (c + q * (j - 1)) : ℝ) :=
      delta_sum_residue_le_progression hq X c (fun n => (hooleyDelta n : ℝ))
        (fun n => by positivity)
    _ = ∑ j ∈ Finset.Icc 1 (X / q + 1),
        (hooleyDelta (((c : ℤ) - q + (q : ℤ) * j).natAbs) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [delta_residue_affine_value c q (Finset.mem_Icc.mp hj).1]
    _ ≤ _ := hbound

theorem exists_delta_residue_mean_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ X q c : ℕ, 0 < q → c < q → 16 ≤ X / q → X ≤ (X / q) ^ r →
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => n % q = c), (hooleyDelta n : ℝ)) ≤
        C * (Nat.gcd c q).divisors.card * ((X : ℝ) / q) *
          (max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
  classical
  obtain ⟨C, hC, hmean⟩ := exists_delta_residue_progression_bound (r + 1) (by omega)
  refine ⟨128 * C, by positivity, ?_⟩
  intro X q c hq hc hlength hsize
  have hX : 2 ≤ X := by have := Nat.div_le_self X q; omega
  have hqX : q ≤ X := by
    simpa only [one_mul] using (Nat.le_div_iff_mul_le hq).mp (by omega : 1 ≤ X / q)
  have hsize' : X + q ≤ (X / q + 1) ^ (r + 1) := by
    have hpow : X ≤ (X / q + 1) ^ r :=
      hsize.trans (Nat.pow_le_pow_left (Nat.le_succ _) r)
    calc
      _ ≤ 2 * X := by omega
      _ ≤ (X / q + 1) * (X / q + 1) ^ r :=
        Nat.mul_le_mul (by omega : 2 ≤ X / q + 1) hpow
      _ = _ := (pow_succ' _ _).symm
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogXq : 0 < Real.log ((X + q : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X + q by omega))
  have hlarge : max 1 (Real.log (Real.log ((X + q : ℕ) : ℝ))) ≤
      2 * max 1 (Real.log (Real.log (X : ℝ))) := by
    apply le_trans _ (delta_loglog_square_le hX)
    apply max_le_max le_rfl
    apply Real.log_le_log hlogXq
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show X + q ≤ X ^ 2 by nlinarith)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hratio : (1 : ℝ) ≤ (X : ℝ) / q :=
    (le_div_iff₀ hqR).mpr (by simpa only [one_mul] using (show (q : ℝ) ≤ X by exact_mod_cast hqX))
  have hY : ((X / q + 1 : ℕ) : ℝ) ≤ 2 * ((X : ℝ) / q) := by
    have hfloor : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / q := Nat.cast_div_le
    push_cast
    linarith
  calc
    _ ≤ C * (Nat.gcd c q).divisors.card * (X / q + 1 : ℕ) *
        (max 1 (Real.log (Real.log ((X + q : ℕ) : ℝ)))) ^ 6 :=
      hmean X q c hq hc hlength hsize'
    _ ≤ C * (Nat.gcd c q).divisors.card * (2 * ((X : ℝ) / q)) *
        (2 * max 1 (Real.log (Real.log (X : ℝ)))) ^ 6 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hY (by positivity)
      · exact pow_le_pow_left₀ (by positivity) hlarge 6
      · positivity
      · positivity
    _ = _ := by ring

end Erdos587
