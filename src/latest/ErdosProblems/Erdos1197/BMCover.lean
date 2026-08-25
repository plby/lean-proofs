import ErdosProblems.Erdos1197.BMCoverBasics

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

lemma bm_nearest_grid (q k : ℕ) (hq : 0 < q) (x : ℝ) :
    ∃ j : PrimeIdx k, ∃ n : ℤ,
      |x + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
  let N : ℕ := 2 ^ k
  let t : ℝ := (q : ℝ) * (N : ℝ) * x
  let M : ℤ := round t
  let r : ℤ := (-M) % N
  let n : ℤ := -((-M) / N)
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hr_nonneg : 0 ≤ r := by
    dsimp [r, N]
    exact Int.emod_nonneg _ (by exact_mod_cast hN_pos.ne')
  have hr_lt : r < N := by
    dsimp [r, N]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast hN_pos)
  have hr_lt_nat : Int.toNat r < N := by
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hN_pos)).2 (by simpa [N] using hr_lt)
  let j : PrimeIdx k := ⟨Int.toNat r, by
    simpa [N] using hr_lt_nat⟩
  refine ⟨j, n, ?_⟩
  have hj_eq_int : ((j : ℕ) : ℤ) = r := by
    dsimp [j]
    simp [Int.toNat_of_nonneg hr_nonneg]
  have hj_eq : (j : ℝ) = r := by
    exact_mod_cast hj_eq_int
  have hdecomp : (N : ℤ) * ((-M) / N) + (-M) % N = -M := by
    simpa [N] using (Int.mul_ediv_add_emod (-M) N)
  have hdecompZ : r - (N : ℤ) * n = -M := by
    dsimp [r, n]
    linarith
  have hdecomp' : (r : ℝ) - (N : ℝ) * (n : ℝ) = -(M : ℝ) := by
    exact_mod_cast hdecompZ
  have hround : |t - M| ≤ 1 / 2 := by
    simpa [t, M] using (abs_sub_round t)
  have hqN_pos : 0 < (q : ℝ) * (N : ℝ) := by
    positivity
  have hmul :
      ((q : ℝ) * (N : ℝ)) *
          |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        1 / 2 := by
    calc
      ((q : ℝ) * (N : ℝ)) *
          |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)|
          = |((q : ℝ) * (N : ℝ)) *
              (x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ))| := by
              rw [abs_mul, abs_of_pos hqN_pos]
      _ = |t - M| := by
            congr 1
            dsimp [t]
            have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
            have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
            field_simp [hqreal, hNreal]
            linarith [hdecomp']
      _ ≤ 1 / 2 := hround
  have hbound :
      |x + (r : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        (1 / 2) / ((q : ℝ) * (N : ℝ)) := by
    exact (le_div_iff₀ hqN_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hbound' :
      |x + (j : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        (1 / 2) / ((q : ℝ) * (N : ℝ)) := by
    simpa [hj_eq] using hbound
  have htarget :
      (1 / 2 : ℝ) / ((q : ℝ) * (N : ℝ)) = 1 / (2 * (q : ℝ) * (N : ℝ)) := by
    have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    field_simp [hqreal, hNreal]
  have hbound'' :
      |x + (j : ℝ) / ((q : ℝ) * (N : ℝ)) - (n : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (N : ℝ)) := by
    exact htarget ▸ hbound'
  simpa [N] using hbound''

lemma bm_prime_cover_of_positive_q
    {k ν q : ℕ} (hq : 0 < q)
    (p : PrimeIdx k → ℕ) (a : PrimeIdx k → ℤ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (happrox :
      ∀ i,
        |(q : ℝ) * Real.logb 2 (p i : ℝ) - (a i : ℝ) - (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * (2 : ℝ) ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
  intro y hy
  obtain ⟨j, n₀, hgrid⟩ := bm_nearest_grid q k hq (Real.logb 2 y)
  have hqreal_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have happrox_div :
      |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
          (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
    have hmul :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ) <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ)
            = (q : ℝ) *
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                    (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by ring
        _ = |(q : ℝ) *
                (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| := by
              rw [abs_mul, abs_of_pos hqreal_pos]
        _ = |(q : ℝ) * Real.logb 2 (p j : ℝ) - (a j : ℝ) - (j : ℝ) / (2 : ℝ) ^ k| := by
              congr 1
              field_simp [hq.ne']
        _ < 1 / (4 * (2 : ℝ) ^ k) := happrox j
    have hdiv :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
          (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) := by
      exact (lt_div_iff₀ hqreal_pos).2 hmul
    have htarget :
        (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) =
          1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hqreal]
    exact htarget ▸ hdiv
  have hpj_mem :
      (p j : ℝ) ∈ Ioo (((23 : ℝ) / 16) * (2 : ℝ) ^ ν) (((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := hp_window j
  have hpj_pos : 0 < p j := by
    have hpj_pos_real : 0 < (p j : ℝ) := by
      rcases hpj_mem with ⟨hpj_lower, _⟩
      have : 0 < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by positivity
      linarith
    exact_mod_cast hpj_pos_real
  have hsum :
      |Real.logb 2 y + Real.logb 2 (p j : ℝ) - ((n₀ + a j : ℤ) : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
    have htri :
        |(Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)) +
            (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
              (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| <
          1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
      have hnorm :
          |(Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)) +
              (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| ≤
            |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by
        exact abs_add_le _ _
      have hbound :
          |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
            1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
        have hsum_lt :
            |Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ)| +
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) -
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
              1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
          nlinarith
        have htarget :
            1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) <
              1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
          have hq2k_pos : 0 < (q : ℝ) * (2 : ℝ) ^ k := by positivity
          have hq2k_ne : (q : ℝ) * (2 : ℝ) ^ k ≠ 0 := hq2k_pos.ne'
          field_simp [hq2k_ne]
          nlinarith
        exact lt_trans hsum_lt htarget
      exact lt_of_le_of_lt hnorm hbound
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using htri
  refine ⟨p j, hpj_pos, bm_prime_mul_mem_window ν hpj_mem hy, ?_⟩
  refine ⟨n₀ + a j, ?_⟩
  have hy_pos : 0 < y := by
    rcases hy with ⟨hy₁, _⟩
    linarith
  rw [Real.logb_mul] <;> try positivity
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using hsum

lemma bm_prime_cover_of_negative_q
    {k ν q : ℕ} (hq : 0 < q)
    (p : PrimeIdx k → ℕ) (a : PrimeIdx k → ℤ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (happrox :
      ∀ i,
        |(q : ℝ) * Real.logb 2 (p i : ℝ) - (a i : ℝ) + (i : ℝ) / (2 : ℝ) ^ k| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
      (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * (2 : ℝ) ^ ν) ((2 : ℝ) ^ ν) ∧
      ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
  intro y hy
  obtain ⟨j, n₀, hgrid_raw⟩ := bm_nearest_grid q k hq (-Real.logb 2 y)
  have hgrid :
      |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| ≤
        1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
    let t : ℝ :=
      Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)
    have htmp : |-t| ≤ 1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hEq :
          -t =
            -Real.logb 2 y + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - (n₀ : ℝ) / (q : ℝ) := by
        dsimp [t]
        have hdiv : -((n₀ : ℝ) / (q : ℝ)) = -(n₀ : ℝ) / (q : ℝ) := by ring
        simp [sub_eq_add_neg, add_comm, Int.cast_neg, hdiv]
      rw [hEq]
      exact hgrid_raw
    have htarget : |t| ≤ 1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) := by
      simpa [abs_neg] using htmp
    simpa [t] using htarget
  have hqreal_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have happrox_div :
      |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) + (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
    have hmul :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ) <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| * (q : ℝ)
            = (q : ℝ) *
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                    (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by ring
        _ = |(q : ℝ) *
                (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| := by
              rw [abs_mul, abs_of_pos hqreal_pos]
        _ = |(q : ℝ) * Real.logb 2 (p j : ℝ) - (a j : ℝ) + (j : ℝ) / (2 : ℝ) ^ k| := by
              congr 1
              field_simp [hq.ne']
        _ < 1 / (4 * (2 : ℝ) ^ k) := happrox j
    have hdiv :
        |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
            (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
          (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) := by
      exact (lt_div_iff₀ hqreal_pos).2 hmul
    have htarget :
        (1 / (4 * (2 : ℝ) ^ k)) / (q : ℝ) =
          1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
      have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hqreal]
    exact htarget ▸ hdiv
  have hpj_mem :
      (p j : ℝ) ∈ Ioo (((23 : ℝ) / 16) * (2 : ℝ) ^ ν) (((3 : ℝ) / 2) * (2 : ℝ) ^ ν) := hp_window j
  have hpj_pos : 0 < p j := by
    have hpj_pos_real : 0 < (p j : ℝ) := by
      rcases hpj_mem with ⟨hpj_lower, _⟩
      have : 0 < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by positivity
      linarith
    exact_mod_cast hpj_pos_real
  have hsum :
      |Real.logb 2 y + Real.logb 2 (p j : ℝ) - (((-n₀ + a j : ℤ) : ℝ) / (q : ℝ))| <
        1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
    have htri :
        |(Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)) +
            (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
              (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| <
          1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
      have hnorm :
          |(Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)) +
              (Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k))| ≤
            |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| := by
        exact abs_add_le _ _
      have hbound :
          |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
              |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
            1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
        have hsum_lt :
            |Real.logb 2 y - (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k) - ((-n₀ : ℤ) : ℝ) / (q : ℝ)| +
                |Real.logb 2 (p j : ℝ) - (a j : ℝ) / (q : ℝ) +
                  (j : ℝ) / ((q : ℝ) * (2 : ℝ) ^ k)| <
              1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
          nlinarith
        have htarget :
            1 / (2 * (q : ℝ) * (2 : ℝ) ^ k) +
                1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) <
              1 / ((q : ℝ) * (2 : ℝ) ^ k) := by
          have hq2k_pos : 0 < (q : ℝ) * (2 : ℝ) ^ k := by positivity
          have hq2k_ne : (q : ℝ) * (2 : ℝ) ^ k ≠ 0 := hq2k_pos.ne'
          field_simp [hq2k_ne]
          nlinarith
        exact lt_trans hsum_lt htarget
      exact lt_of_le_of_lt hnorm hbound
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using htri
  refine ⟨p j, hpj_pos, bm_prime_mul_mem_window ν hpj_mem hy, ?_⟩
  refine ⟨-n₀ + a j, ?_⟩
  have hy_pos : 0 < y := by
    rcases hy with ⟨hy₁, _⟩
    linarith
  rw [Real.logb_mul] <;> try positivity
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_div] using hsum

lemma bm_integer_cover_of_nonzero_q
    {k ν : ℕ} {q : ℤ} (hq : q ≠ 0) (hν : 3 ≤ ν)
    {p : PrimeIdx k → ℕ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  intro n hn
  exact bm_integer_lattice_of_common_q hq hm hn hν

lemma bm_integer_cover_of_coordinate_data
    {k ν : ℕ} {q : ℤ} (hq : q ≠ 0) (hν : 3 ≤ ν)
    (a : IntIdx ν → ℤ)
    (happrox :
      ∀ j : IntIdx ν,
        |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (Int.natAbs q : ℝ)| <
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
  intro n hn
  obtain ⟨j, rfl⟩ := exists_bmIntVal_eq_of_mem_Ioo ν hν hn
  let z : ℤ := Int.sign q * a j
  refine ⟨z, ?_⟩
  have hcoord :
      |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| <
        1 / (4 * (2 : ℝ) ^ k) := happrox j
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs_pos : 0 < |(q : ℝ)| := by
    exact abs_pos.mpr hqreal
  have hscaled :
      |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)| <
        (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| := by
    have hmul :
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)| <
          1 / (4 * (2 : ℝ) ^ k) := by
      calc
        |(q : ℝ)| *
            |Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ)|
            = |(q : ℝ) * (Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ) / (q : ℝ))| := by
                rw [abs_mul]
        _ = |(q : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) - (a j : ℝ)| := by
              congr 1
              field_simp [hq]
        _ < 1 / (4 * (2 : ℝ) ^ k) := by simpa [abs_sub_comm] using hcoord
    exact (lt_div_iff₀ hqabs_pos).2 (by simpa [mul_comm] using hmul)
  have hrewrite :
      ((z : ℝ) / (Int.natAbs q : ℝ)) = (a j : ℝ) / (q : ℝ) := by
    simpa [z] using int_sign_mul_div_natAbs q (a j) hq
  rw [hrewrite]
  have hqabs_cast : (Int.natAbs q : ℝ) = |(q : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hqabs_cast_pos : 0 < (Int.natAbs q : ℝ) := by
    rw [hqabs_cast]
    exact hqabs_pos
  have htarget :
      (1 / (4 * (2 : ℝ) ^ k)) / |(q : ℝ)| =
        1 / (4 * ((Int.natAbs q : ℝ)) * (2 : ℝ) ^ k) := by
    rw [← hqabs_cast]
    field_simp [hqabs_cast_pos.ne']
  rw [hqabs_cast]
  convert hscaled using 1
  ring_nf

lemma bm_integer_cover_of_positive_q
    {k ν q : ℕ} (hq : 0 < q) (hν : 3 ≤ ν)
    {p : PrimeIdx k → ℕ}
    {m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ}
    (hm :
      ∀ j,
        |((q : ℤ) : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
          1 / (4 * (2 : ℝ) ^ k)) :
    ∀ n : ℕ, (n : ℝ) ∈ Ioo (((7 : ℝ) / 8) * 2 ^ ν) (((9 : ℝ) / 8) * 2 ^ ν) →
      ∃ z : ℤ, |Real.logb 2 (n : ℝ) - (z : ℝ) / (q : ℝ)| <
        1 / (4 * (q : ℝ) * (2 : ℝ) ^ k) := by
  intro n hn
  obtain ⟨z, hz⟩ :=
    bm_integer_lattice_of_common_q
      (k := k) (ν := ν) (p := p) (q := (q : ℤ))
      (by exact_mod_cast hq.ne') hm hn hν
  refine ⟨z, ?_⟩
  simpa using hz



end

end Erdos1197
