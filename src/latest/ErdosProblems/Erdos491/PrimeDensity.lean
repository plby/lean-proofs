import ErdosProblems.Erdos491.LargePrimes

/-! # A positive prime coefficient forces positive prime density -/

open Filter
open scoped BigOperators

namespace Erdos491

noncomputable def positivePrimesBetween (u : ℕ → ℝ) (N Y : ℕ) : Finset ℕ :=
  (Nat.primesLE Y \ Nat.primesLE N).filter (fun q ↦ 0 < u q)

lemma mem_positivePrimesBetween (u : ℕ → ℝ) (N Y p : ℕ) :
    p ∈ positivePrimesBetween u N Y ↔ p.Prime ∧ N < p ∧ p ≤ Y ∧ 0 < u p := by
  classical
  simp only [positivePrimesBetween, Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
  grind

lemma positivePrimesBetween_mono (u : ℕ → ℝ) (N : ℕ) {Y Z : ℕ} (hYZ : Y ≤ Z) :
    positivePrimesBetween u N Y ⊆ positivePrimesBetween u N Z := by
  classical
  exact Finset.filter_subset_filter _ (Finset.sdiff_subset_sdiff (Nat.primesLE_mono hYZ) le_rfl)

lemma affine_total_lower {u : ℕ → ℝ} (hu : PosCompletelyAdditive u) {K : ℝ}
    (hgap : ∀ n : ℕ, 0 < n → |u (n + 1) - u n| ≤ K)
    (a N : ℕ) (ha : 0 < a) :
    (N : ℝ) * (u a - K) ≤ ∑ m ∈ Finset.Icc 1 N, (u (a * m + 1) - u m) := by
  calc
    _ = ∑ _m ∈ Finset.Icc 1 N, (u a - K) := by simp; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
      have h := (abs_le.mp (hgap (a * m) (Nat.mul_pos ha hmpos))).1
      rw [hu ha hmpos] at h
      linarith

lemma affine_large_sum_identity {u : ℕ → ℝ} (hu : PosCompletelyAdditive u)
    {a N Y : ℕ} (haY : a * N + 1 ≤ Y) (hNY : N ≤ Y) :
    (∑ m ∈ Finset.Icc 1 N, primePart u (Nat.primesLE Y \ Nat.primesLE N) (a * m + 1)) =
      (∑ m ∈ Finset.Icc 1 N, (u (a * m + 1) - u m)) -
        ∑ m ∈ Finset.Icc 1 N,
          (primePart u (Nat.primesLE N) (a * m + 1) - primePart u (Nat.primesLE N) m) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hmI := Finset.mem_Icc.mp hm
  have hamY : a * m + 1 ≤ Y :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left a hmI.2) 1).trans haY
  rw [← hu.sub_primePart (by omega : 0 < a * m + 1) hamY hNY,
    hu.eq_primePart hmI.1 hmI.2]
  ring

lemma affine_range_bounds {a N : ℕ} (ha : 1 ≤ a) (hN : a + 2 ≤ N) :
    N ≤ a * N + 1 ∧ a * N + 1 < N ^ 2 ∧ a * N + 1 ≤ (a + 1) * N := by
  have hNpos : 0 < N := by omega
  have hmul := Nat.mul_le_mul_right N ha
  constructor
  · simpa using hmul.trans (Nat.le_succ (a * N))
  constructor <;> nlinarith

lemma log_affine_le_two_log {a N : ℕ} (ha : 1 ≤ a) (hN : a + 2 ≤ N) :
    Real.log ((a * N + 1 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have h := (affine_range_bounds ha hN).2.1.le
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < ((a * N + 1 : ℕ) : ℝ))
    (show ((a * N + 1 : ℕ) : ℝ) ≤ ((N ^ 2 : ℕ) : ℝ) by exact_mod_cast h)
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hl

/-- All constants are chosen before `N` tends to infinity. In particular,
the valuation error used to choose `r` is independent of `r`. -/
theorem positive_prime_density {u : ℕ → ℝ} (hu : PosCompletelyAdditive u)
    {K : ℝ} (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, 0 < n → |u (n + 1) - u n| ≤ K)
    {p : ℕ} (hp : p.Prime) (hup : 0 < u p) :
    ∃ L : ℕ, 1 < L ∧ ∃ d : ℝ, 0 < d ∧
      ∀ᶠ N : ℕ in atTop,
        d * N ≤ ((positivePrimesBetween u N (L * N)).card : ℝ) * Real.log (N : ℝ) := by
  classical
  obtain ⟨C, hC, hgrowth⟩ := hu.exists_log_bound hK hgap
  let D : ℝ := 2 * C * (Real.log 4 + 1)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  obtain ⟨r : ℕ, hr⟩ := exists_nat_gt ((K + D + 1) / u p)
  have hrval : K + D + 1 < ((r + 1 : ℕ) : ℝ) * u p := by
    have h := (div_lt_iff₀ hup).mp hr
    push_cast
    nlinarith
  let a := p ^ (r + 1)
  have ha : 1 ≤ a := Nat.one_le_pow _ _ hp.one_le
  have huaval : K + D + 1 < u a := by
    dsimp [a]
    rwa [hu.pow hp.pos]
  refine ⟨a + 1, by omega, 1 / (2 * C), by positivity, ?_⟩
  filter_upwards [eventually_prime_count_log_bound, eventually_ge_atTop (a + 2)] with N hpi hN
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hNpos)
  obtain ⟨hNY, hYsq, hYL⟩ := affine_range_bounds ha hN
  have hlogY := log_affine_le_two_log ha hN
  let small := ∑ m ∈ Finset.Icc 1 N,
    (primePart u (Nat.primesLE N) (a * m + 1) - primePart u (Nat.primesLE N) m)
  let large := ∑ m ∈ Finset.Icc 1 N,
    primePart u (Nat.primesLE (a * N + 1) \ Nat.primesLE N) (a * m + 1)
  have hsmall : small ≤ D * N := by
    have hsmall₀ := small_prime_affine_error_le u hC.le
      (fun q hq ↦ hgrowth q hq.pos) hp (by omega : 0 < r + 1) hup.le
      (le_refl (a * N + 1)) hNY
    calc
      small ≤ C * Real.log ((a * N + 1 : ℕ) : ℝ) * (Nat.primesLE N).card := hsmall₀
      _ ≤ C * (2 * Real.log (N : ℝ)) * (Nat.primesLE N).card := by
        gcongr
      _ = 2 * C * (((Nat.primesLE N).card : ℝ) * Real.log (N : ℝ)) := by ring
      _ ≤ 2 * C * ((Real.log 4 + 1) * N) :=
        mul_le_mul_of_nonneg_left hpi (by positivity)
      _ = D * N := by dsimp [D]; ring
  have hlargeLower : (N : ℝ) ≤ large := by
    have hfull := affine_total_lower hu hgap a N ha
    have heq := affine_large_sum_identity hu (le_refl (a * N + 1)) hNY
    change large = _ - small at heq
    nlinarith
  have hlargeUpper : large ≤
      ((positivePrimesBetween u N ((a + 1) * N)).card : ℝ) * (2 * C * Real.log (N : ℝ)) := by
    have hlarge₀ := large_prime_affine_sum_le u hC.le
      (fun q hq ↦ hgrowth q hq.pos) ha (by omega : a < N) (le_refl (a * N + 1)) hYsq
    have hcard : ((positivePrimesBetween u N (a * N + 1)).card : ℝ) ≤
        ((positivePrimesBetween u N ((a + 1) * N)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (positivePrimesBetween_mono u N hYL)
    calc
      large ≤ ((positivePrimesBetween u N (a * N + 1)).card : ℝ) *
          (C * Real.log ((a * N + 1 : ℕ) : ℝ)) := hlarge₀
      _ ≤ ((positivePrimesBetween u N ((a + 1) * N)).card : ℝ) *
          (C * (2 * Real.log (N : ℝ))) := by
        apply mul_le_mul hcard (mul_le_mul_of_nonneg_left hlogY hC.le)
        · exact mul_nonneg hC.le (Real.log_nonneg (by exact_mod_cast (show 1 ≤ a * N + 1 by omega)))
        · exact Nat.cast_nonneg _
      _ = _ := by ring
  calc
    (1 / (2 * C)) * N = (N : ℝ) / (2 * C) := by ring
    _ ≤ ((positivePrimesBetween u N ((a + 1) * N)).card : ℝ) * Real.log (N : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * C)).mpr
      nlinarith

end Erdos491
