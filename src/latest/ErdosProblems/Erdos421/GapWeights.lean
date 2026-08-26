import ErdosProblems.Erdos421.UnequalParentCount
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Harmonic weights give a sharper direct count of unequal parents -/

namespace Erdos421

theorem prime_gap_intervals_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Finset.Ioc (prime i) (prime (i + 1)))
      (Finset.Ioc (prime j) (prime (j + 1))) := by
  apply Finset.disjoint_left.mpr
  intro n hni hnj
  obtain ⟨hpi, hqi⟩ := Finset.mem_Ioc.mp hni
  obtain ⟨hpj, hqj⟩ := Finset.mem_Ioc.mp hnj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := prime_strictMono.monotone (show i + 1 ≤ j from hij)
    omega
  · have h := prime_strictMono.monotone (show j + 1 ≤ i from hji)
    omega

theorem gap_ratio_le_harmonic_block (k : ℕ) :
    (gapLength k : ℝ) / prime k ≤
      2 * (∑ n ∈ Finset.Ioc (prime k) (prime (k + 1)), (n : ℝ)⁻¹) := by
  have hp : (0 : ℝ) < prime k := by exact_mod_cast (prime_prime k).pos
  have hcard : (Finset.Ioc (prime k) (prime (k + 1))).card = gapLength k := Nat.card_Ioc _ _
  calc
    (gapLength k : ℝ) / prime k =
        ∑ _n ∈ Finset.Ioc (prime k) (prime (k + 1)), (1 : ℝ) / prime k := by
      simp only [Finset.sum_const, nsmul_eq_mul, hcard, mul_one_div]
    _ ≤ ∑ n ∈ Finset.Ioc (prime k) (prime (k + 1)), 2 * (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hpn, hnq⟩ := Finset.mem_Ioc.mp hn
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast ((prime_prime k).pos.trans hpn)
      have hn2 : (n : ℝ) ≤ 2 * prime k := by
        exact_mod_cast hnq.trans (prime_succ_le_two_mul k)
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ hp hnpos).mpr
      nlinarith
    _ = _ := (Finset.mul_sum ..).symm

/-- Disjoint prime gaps and Bertrand's bound control the sum of relative lengths. -/
theorem sum_gap_ratio_le (I : Finset ℕ) (X : ℕ)
    (hX : ∀ i ∈ I, prime (i + 1) ≤ X) :
    (∑ i ∈ I, (gapLength i : ℝ) / prime i) ≤ 2 * (harmonic X : ℝ) := by
  classical
  let U := I.biUnion (fun i ↦ Finset.Ioc (prime i) (prime (i + 1)))
  have hdisj : (↑I : Set ℕ).Pairwise
      (fun i j ↦ Disjoint (Finset.Ioc (prime i) (prime (i + 1)))
        (Finset.Ioc (prime j) (prime (j + 1)))) :=
    fun _ _ _ _ hij ↦ prime_gap_intervals_disjoint hij
  have hsub : U ⊆ Finset.Icc 1 X := by
    intro n hn
    obtain ⟨i, hi, hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hpn, hnq⟩ := Finset.mem_Ioc.mp hn
    have hp : 1 ≤ prime i := (prime_prime i).pos
    exact Finset.mem_Icc.mpr ⟨hp.trans hpn.le, hnq.trans (hX i hi)⟩
  calc
    _ ≤ ∑ i ∈ I, 2 * (∑ n ∈ Finset.Ioc (prime i) (prime (i + 1)), (n : ℝ)⁻¹) :=
      Finset.sum_le_sum (fun i _ ↦ gap_ratio_le_harmonic_block i)
    _ = 2 * (∑ n ∈ U, (n : ℝ)⁻¹) := by
      simp only [U, Finset.sum_biUnion hdisj, Finset.mul_sum]
    _ ≤ 2 * (∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)) (by norm_num)
    _ = _ := by simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem unequal_large_parent_card_mul_bound (I : Finset ℕ) (X H P : ℕ)
    (hX : ∀ i ∈ I, prime (i + 1) ≤ X)
    (hP : ∀ i ∈ I, P ≤ prime i)
    (hH : ∀ i ∈ I, 2 * H ≤ prime i)
    (hineq : ∀ i ∈ I, (prime i) ^ 2 ≤ X * gapLength i + prime i * H) :
    (P : ℝ) * I.card ≤ 4 * X * (harmonic X : ℝ) := by
  have hpoint : ∀ i ∈ I, (P : ℝ) ≤ 2 * X * ((gapLength i : ℝ) / prime i) := by
    intro i hi
    have hsq : (prime i) ^ 2 ≤ 2 * X * gapLength i := by
      have hh := hH i hi
      have h := hineq i hi
      nlinarith
    have hPp : P * prime i ≤ 2 * X * gapLength i := by
      have h := Nat.mul_le_mul_right (prime i) (hP i hi)
      nlinarith
    have hp : (0 : ℝ) < prime i := by exact_mod_cast (prime_prime i).pos
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp).mpr
    exact_mod_cast hPp
  calc
    (P : ℝ) * I.card = ∑ _i ∈ I, (P : ℝ) := by simp [mul_comm]
    _ ≤ ∑ i ∈ I, 2 * X * ((gapLength i : ℝ) / prime i) := Finset.sum_le_sum hpoint
    _ = (2 * X : ℝ) * (∑ i ∈ I, (gapLength i : ℝ) / prime i) := (Finset.mul_sum ..).symm
    _ ≤ (2 * X : ℝ) * (2 * (harmonic X : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_gap_ratio_le I X hX) (by positivity)
    _ = _ := by ring

/-- A direct square-root-scale parent count, with an explicit harmonic factor. -/
theorem unequal_parent_card_mul_bound (I : Finset ℕ) (X H P : ℕ) (hHP : 2 * H ≤ P)
    (hX : ∀ i ∈ I, prime (i + 1) ≤ X)
    (hineq : ∀ i ∈ I, (prime i) ^ 2 ≤ X * gapLength i + prime i * H) :
    (P : ℝ) * I.card ≤ (P : ℝ) ^ 2 + 4 * X * (harmonic X : ℝ) := by
  classical
  let small := I.filter (fun i ↦ prime i < P)
  have hsmall : small ⊆ I := Finset.filter_subset _ _
  have hsmallcard : small.card ≤ P := by
    calc
      small.card = (small.image prime).card :=
        (Finset.card_image_of_injective small prime_strictMono.injective).symm
      _ ≤ (Finset.range P).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      _ = P := Finset.card_range _
  have hlargeP : ∀ i ∈ I \ small, P ≤ prime i := by
    intro i hi
    obtain ⟨hiI, hinot⟩ := Finset.mem_sdiff.mp hi
    by_contra h
    exact hinot (Finset.mem_filter.mpr ⟨hiI, by omega⟩)
  have hlarge := unequal_large_parent_card_mul_bound (I \ small) X H P
    (fun i hi ↦ hX i (Finset.mem_sdiff.mp hi).1) hlargeP
    (fun i hi ↦ hHP.trans (hlargeP i hi))
    (fun i hi ↦ hineq i (Finset.mem_sdiff.mp hi).1)
  have hcards : ((I \ small).card : ℝ) + small.card = I.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsmall
  have hs : (small.card : ℝ) ≤ P := by exact_mod_cast hsmallcard
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  nlinarith

theorem harmonic_pow_two_le (K : ℕ) :
    (harmonic (2 ^ K) : ℝ) ≤ 1 + K := by
  have h := harmonic_le_one_add_log (2 ^ K)
  have hlog : Real.log 2 ≤ 1 := by
    have h' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hKpos : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h
  nlinarith

theorem harmonic_scale_le (u : ℕ) :
    (harmonic (2 ^ (60 * u)) : ℝ) ≤ 1 + 60 * u := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using harmonic_pow_two_le (60 * u)

theorem unequal_parent_card_bound_square_scale (I : Finset ℕ) (J H : ℕ)
    (hH : 2 * H ≤ 2 ^ J)
    (hX : ∀ i ∈ I, prime (i + 1) ≤ 2 ^ (2 * J))
    (hineq : ∀ i ∈ I, (prime i) ^ 2 ≤
      2 ^ (2 * J) * gapLength i + prime i * H) :
    I.card ≤ (5 + 8 * J) * 2 ^ J := by
  have h := unequal_parent_card_mul_bound I (2 ^ (2 * J)) H (2 ^ J) hH hX hineq
  have hpow : ((2 ^ J : ℕ) : ℝ) ^ 2 = ((2 ^ (2 * J) : ℕ) : ℝ) := by
    norm_cast
    rw [← pow_mul, Nat.mul_comm J 2]
  have hP : (0 : ℝ) < (2 ^ J : ℕ) := by positivity
  have hhar := harmonic_pow_two_le (2 * J)
  have hmul := mul_le_mul_of_nonneg_left hhar
    (show (0 : ℝ) ≤ 4 * (2 ^ (2 * J) : ℕ) by positivity)
  rw [← hpow] at h hmul
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hmul
  have hbound : (I.card : ℝ) ≤ (5 + 8 * J) * (2 ^ J : ℕ) := by
    nlinarith
  exact_mod_cast hbound

/-- At `X=2^(60u)`, the number of unequal parents is bounded by
`(5+240u) sqrt(X)`. This bound does not distinguish long and short parents. -/
theorem unequal_parent_card_bound_sharp (I : Finset ℕ) {u : ℕ} (hu : 1 ≤ u)
    (hX : ∀ i ∈ I, prime (i + 1) ≤ 2 ^ (60 * u))
    (hineq : ∀ i ∈ I, (prime i) ^ 2 ≤
      2 ^ (60 * u) * gapLength i + prime i * 2 ^ (3 * u)) :
    I.card ≤ (5 + 240 * u) * 2 ^ (30 * u) := by
  have hHP : 2 * 2 ^ (3 * u) ≤ 2 ^ (30 * u) := by
    calc
      _ = 2 ^ (3 * u + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (30 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  have h := unequal_parent_card_mul_bound I (2 ^ (60 * u)) (2 ^ (3 * u))
    (2 ^ (30 * u)) hHP hX hineq
  have hpow : ((2 ^ (30 * u) : ℕ) : ℝ) ^ 2 = ((2 ^ (60 * u) : ℕ) : ℝ) := by
    norm_cast
    rw [← pow_mul]
    congr 1
    omega
  have hP : (0 : ℝ) < (2 ^ (30 * u) : ℕ) := by positivity
  have hhar := harmonic_scale_le u
  have hmul := mul_le_mul_of_nonneg_left hhar
    (show (0 : ℝ) ≤ 4 * (2 ^ (60 * u) : ℕ) by positivity)
  rw [← hpow] at h hmul
  have hbound : (I.card : ℝ) ≤ (5 + 240 * u) * (2 ^ (30 * u) : ℕ) := by
    nlinarith
  exact_mod_cast hbound

end Erdos421
