/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Greedy Egyptian expansions for Erdős 308

This is the self-contained greedy existence argument used only to dispose of
the finitely many target integers preceding the uniform Croot construction.
It is isolated here so Problem 308 does not import unrelated developments or
their local resource settings.
-/

namespace Erdos308.GreedyEgyptian

open Finset

/-- The harmonic series partial sums grow without bound. -/
private lemma harmonic_mono_aux (m n : ℕ) (h : m ≤ n) : harmonic m ≤ harmonic n := by
  induction n, h using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih =>
    rw [harmonic_succ]
    have h_pos : (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ)⁻¹ := by positivity
    linarith

/-- For any rational `R`, there exists a natural `N` with `harmonic N > R`. -/
private lemma exists_harmonic_gt_aux (R : ℚ) : ∃ N : ℕ, harmonic N > R := by
  have h : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (1 : ℝ) / (↑i + 1))
      Filter.atTop Filter.atTop := Real.tendsto_sum_range_one_div_nat_succ_atTop
  rw [Filter.tendsto_atTop_atTop] at h
  obtain ⟨N, hN⟩ := h ((R : ℝ) + 1)
  use N
  have h_eq : (∑ i ∈ Finset.range N, (1 : ℝ) / (↑i + 1)) = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rw [show (Finset.Icc 1 N) = (Finset.range N).image (· + 1) from ?_]
    · rw [Finset.sum_image (fun a _ b _ h => by simp at h; omega)]
      simp
    · ext x
      constructor
      · intro hx
        rw [Finset.mem_Icc] at hx
        rw [Finset.mem_image]
        refine ⟨x - 1, ?_, by omega⟩
        rw [Finset.mem_range]
        omega
      · intro hx
        rw [Finset.mem_image] at hx
        rcases hx with ⟨a, ha, rfl⟩
        rw [Finset.mem_range] at ha
        rw [Finset.mem_Icc]
        omega
  have h_test : ((R : ℝ) + 1) ≤ (harmonic N : ℝ) := h_eq ▸ hN N le_rfl
  have h_cast : (R : ℝ) < (harmonic N : ℝ) := by linarith
  exact_mod_cast h_cast

/-- The harmonic tail `∑_{j=L+1}^N 1/j` equals `harmonic N - harmonic L`. -/
private lemma harmonicTail_eq_aux (L N : ℕ) (h : L ≤ N) :
    ∑ j ∈ Finset.Ioc L N, (1 : ℚ) / j = harmonic N - harmonic L := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
  rw [show Finset.Ioc L N = Finset.Icc (L+1) N from by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]]
  have h_split : Finset.Icc 1 N = Finset.Icc 1 L ∪ Finset.Icc (L+1) N := by
    ext x; simp [Finset.mem_Icc, Finset.mem_union]; omega
  rw [h_split, Finset.sum_union ?_]
  · simp [one_div]
  · rw [Finset.disjoint_left]
    intro x hx_left hx_right
    rw [Finset.mem_Icc] at hx_left hx_right
    omega

/-- For any positive rational `R` and natural `L`, there exists `N ≥ L` such that
the harmonic tail from `L+1` to `N` is at least `R`. -/
private lemma exists_harmonicTail_ge_aux (R : ℚ) (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ R ≤ ∑ j ∈ Finset.Ioc L N, (1 : ℚ) / j := by
  obtain ⟨N₀, hN₀⟩ := exists_harmonic_gt_aux (R + harmonic L)
  refine ⟨max N₀ L, le_max_right _ _, ?_⟩
  have hLN : L ≤ max N₀ L := le_max_right _ _
  rw [harmonicTail_eq_aux _ _ hLN]
  have h_mono : harmonic N₀ ≤ harmonic (max N₀ L) :=
    harmonic_mono_aux _ _ (le_max_left _ _)
  linarith

/-- Algebraic identity: rewrite `R - 1/q` as a `Rat.divInt`. -/
private lemma sub_one_div_eq_divInt_aux (R : ℚ) (q : ℕ) (hq_pos : 0 < q) :
    R - 1/(q : ℚ) = ((R.num * q - R.den : ℤ) : ℚ) / ((R.den * q : ℕ) : ℤ) := by
  have hRd : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_pos.ne'
  have hq_q : (q : ℚ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hR_eq : (R.num : ℚ) = R * R.den := by
    have h := Rat.num_div_den R
    field_simp at h
    linarith
  push_cast
  rw [eq_div_iff (by positivity : (R.den : ℚ) * q ≠ 0)]
  rw [sub_mul]
  rw [show R * ((R.den : ℚ) * q) = (R * R.den) * q from by ring]
  rw [← hR_eq]
  rw [show (1 / (q : ℚ)) * ((R.den : ℚ) * q) = ((q : ℚ) * (q : ℚ)⁻¹) * R.den from by
    rw [one_div]; ring]
  rw [mul_inv_cancel₀ hq_q, one_mul]

/-- The greedy step decreases the numerator (in `natAbs`). -/
private lemma greedy_num_decrease_aux (R : ℚ) (hR : 0 < R)
    (h_neq : R ≠ 1 / (⌈(R⁻¹ : ℚ)⌉₊ : ℚ)) :
    (R - 1 / (⌈(R⁻¹ : ℚ)⌉₊ : ℚ)).num.natAbs < R.num.natAbs := by
  set q : ℕ := ⌈(R⁻¹ : ℚ)⌉₊ with hq_def
  have hq_pos : 0 < q := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hq
    have h : (R⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
    have h_pos : (0 : ℚ) < R⁻¹ := inv_pos.mpr hR
    linarith
  have ha_pos : 0 < R.num := Rat.num_pos.mpr hR
  have hb_pos : (0 : ℕ) < R.den := R.den_pos
  have hR_inv : (R⁻¹ : ℚ) = (R.den : ℚ) / R.num := by
    rw [show R = (R.num : ℚ) / R.den from (Rat.num_div_den R).symm]
    rw [inv_div, Rat.num_div_den]
  have ha_pos_q : (0 : ℚ) < R.num := by exact_mod_cast ha_pos
  have hb_pos_q : (0 : ℚ) < R.den := by exact_mod_cast hb_pos
  have h_qa_ge_b : (R.den : ℤ) ≤ R.num * q := by
    have h1 : (R⁻¹ : ℚ) ≤ q := Nat.le_ceil _
    rw [hR_inv] at h1
    rw [div_le_iff₀ ha_pos_q] at h1
    have h_int : (R.den : ℤ) ≤ (q : ℤ) * R.num := by exact_mod_cast h1
    linarith
  have h_qa_lt : (R.num : ℤ) * q < R.den + R.num := by
    have h2 : ((q : ℚ) : ℚ) < R⁻¹ + 1 :=
      Nat.ceil_lt_add_one (le_of_lt (inv_pos.mpr hR))
    rw [hR_inv] at h2
    have h3 : (q : ℚ) * R.num < R.den + R.num := by
      have := mul_lt_mul_of_pos_right h2 ha_pos_q
      rw [add_mul, div_mul_cancel₀ _ ha_pos_q.ne', one_mul] at this
      exact this
    have h_int : (q : ℤ) * R.num < R.den + R.num := by exact_mod_cast h3
    linarith
  have h_div : (R - 1/(q : ℚ)).num ∣ (R.num * q - R.den : ℤ) := by
    rw [sub_one_div_eq_divInt_aux R q hq_pos]
    have h_cast : ((R.den * q : ℕ) : ℤ) = (R.den : ℤ) * q := by push_cast; ring
    rw [h_cast]
    rw [show ((R.num * q - R.den : ℤ) : ℚ) / ((R.den : ℤ) * q : ℤ) =
            Rat.divInt (R.num * q - R.den) ((R.den : ℤ) * q) from
      (Rat.divInt_eq_div _ _).symm]
    apply Rat.num_dvd
    have h1 : 0 < (q : ℤ) := by exact_mod_cast hq_pos
    have h2 : 0 < (R.den : ℤ) := by exact_mod_cast hb_pos
    positivity
  have h_nonneg : 0 ≤ R.num * q - R.den := by linarith
  have h_lt' : R.num * q - R.den < R.num := by linarith
  have h_diff_pos : 0 < R.num * q - R.den := by
    by_contra h_neg
    push Not at h_neg
    have h_eq : R.num * q - R.den = 0 := by omega
    have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
    have h_R_eq : R = 1/(q : ℚ) := by
      rw [show R = (R.num : ℚ) / R.den from (Rat.num_div_den R).symm]
      rw [div_eq_div_iff hb_pos_q.ne' hq_pos_q.ne']
      have : (R.num * q : ℤ) = R.den := by linarith
      have hh : (R.num : ℚ) * q = R.den := by exact_mod_cast this
      linarith
    exact h_neq h_R_eq
  have ha_eq : (R.num.natAbs : ℤ) = R.num := Int.natAbs_of_nonneg ha_pos.le
  have hd_eq : ((R.num * q - R.den).natAbs : ℤ) = R.num * q - R.den :=
    Int.natAbs_of_nonneg h_nonneg
  have h_lt_natabs : (R.num * q - R.den).natAbs < R.num.natAbs := by
    have : ((R.num * q - R.den).natAbs : ℤ) < R.num.natAbs := by
      rw [hd_eq, ha_eq]; exact h_lt'
    exact_mod_cast this
  have h_pos_natabs : 0 < (R.num * q - R.den).natAbs := by
    have : 0 < ((R.num * q - R.den).natAbs : ℤ) := by rw [hd_eq]; exact h_diff_pos
    exact_mod_cast this
  have h_le_natabs : (R - 1/(q : ℚ)).num.natAbs ≤ (R.num * q - R.den).natAbs :=
    Nat.le_of_dvd h_pos_natabs (Int.natAbs_dvd_natAbs.mpr h_div)
  omega

/-- For positive rational `R`, `0 ≤ R - 1/⌈R⁻¹⌉₊`. -/
private lemma greedy_step_nonneg_aux (R : ℚ) (hR : 0 < R) :
    0 ≤ R - 1/((⌈(R⁻¹ : ℚ)⌉₊ : ℕ) : ℚ) := by
  set q := ⌈(R⁻¹ : ℚ)⌉₊
  have hq_pos : 0 < q := by
    apply Nat.one_le_iff_ne_zero.mpr
    intro hq
    have h : (R⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
    have h_pos : (0 : ℚ) < R⁻¹ := inv_pos.mpr hR
    linarith
  have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
  have h1 : (R⁻¹ : ℚ) ≤ q := Nat.le_ceil _
  rw [sub_nonneg, div_le_iff₀ hq_pos_q, mul_comm, ← div_le_iff₀ hR, one_div]
  exact h1

/-- Greedy expansion for a residual `S` with the precondition that
`minDen ≥ 2` and either `S = 0` or `⌈S⁻¹⌉₊ ≥ minDen`.
This produces a finite set of distinct integers `≥ minDen` whose reciprocals
sum to `S`.

Proven by strong induction on `S.num.natAbs`. -/
private lemma greedy_residual_aux (n : ℕ) :
    ∀ (S : ℚ), 0 ≤ S → S.num.natAbs ≤ n → ∀ (minDen : ℕ), 2 ≤ minDen →
      (S = 0 ∨ minDen ≤ ⌈(S⁻¹ : ℚ)⌉₊) →
      ∃ E : Finset ℕ, (∀ e ∈ E, minDen ≤ e) ∧ S = ∑ e ∈ E, (1 : ℚ) / e := by
  induction n with
  | zero =>
    intros S hS_nonneg hS_num minDen _ _
    have hS_num_zero : S.num.natAbs = 0 := Nat.le_zero.mp hS_num
    have hS_zero_num : S.num = 0 := Int.natAbs_eq_zero.mp hS_num_zero
    have hS : S = 0 := Rat.num_eq_zero.mp hS_zero_num
    refine ⟨∅, by simp, ?_⟩
    rw [hS]; simp
  | succ n ih =>
    intros S hS_nonneg hS_num minDen hminDen_two hS_inv
    by_cases hS_zero : S = 0
    · refine ⟨∅, by simp, ?_⟩
      rw [hS_zero]; simp
    have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_zero)
    have hq_ge : minDen ≤ ⌈(S⁻¹ : ℚ)⌉₊ := by
      rcases hS_inv with hS_eq | hq_le
      · exact (hS_zero hS_eq).elim
      · exact hq_le
    set q : ℕ := ⌈(S⁻¹ : ℚ)⌉₊ with hq_def
    have hq_pos : 0 < q := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hq
      have h : (S⁻¹ : ℚ) ≤ 0 := by rw [Nat.ceil_eq_zero] at hq; exact hq
      have h_pos : (0 : ℚ) < S⁻¹ := inv_pos.mpr hS_pos
      linarith
    have hq_ge_two : 2 ≤ q := by omega
    have hq_pos_q : (0 : ℚ) < q := by exact_mod_cast hq_pos
    -- Case: S = 1/q
    by_cases h_eq : S = 1/(q : ℚ)
    · refine ⟨{q}, ?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        rw [he]
        exact hq_ge
      · rw [Finset.sum_singleton]; exact h_eq
    -- S ≠ 1/q: greedy step
    have h_nonneg' : 0 ≤ S - 1/(q : ℚ) := greedy_step_nonneg_aux S hS_pos
    have h_num_lt : (S - 1/(q : ℚ)).num.natAbs < S.num.natAbs :=
      greedy_num_decrease_aux S hS_pos h_eq
    have h_num_le : (S - 1/(q : ℚ)).num.natAbs ≤ n := by omega
    -- Need: (S - 1/q) = 0 OR ⌈(S-1/q)⁻¹⌉₊ ≥ q + 1.
    have h_new_inv : (S - 1/(q : ℚ)) = 0 ∨ q + 1 ≤ ⌈((S - 1/(q : ℚ))⁻¹ : ℚ)⌉₊ := by
      by_cases h_zero : S - 1/(q : ℚ) = 0
      · left; exact h_zero
      right
      have h_pos' : 0 < S - 1/(q : ℚ) := lt_of_le_of_ne h_nonneg' (Ne.symm h_zero)
      have hq_minus_one_pos : (0 : ℚ) < (q : ℚ) - 1 := by
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq_ge_two
        linarith
      -- Step 1: S⁻¹ > q - 1 (since q = ⌈S⁻¹⌉₊).
      have hSinv_gt : (q : ℚ) - 1 < S⁻¹ := by
        by_contra h_neg
        push Not at h_neg
        -- S⁻¹ ≤ q - 1, so ⌈S⁻¹⌉₊ ≤ ⌈q - 1⌉₊ = q - 1, contradicting q = ⌈S⁻¹⌉₊.
        have h_ceil_le : ⌈(S⁻¹ : ℚ)⌉₊ ≤ ⌈((q : ℚ) - 1)⌉₊ := Nat.ceil_le_ceil h_neg
        have h_eq_cast : ((q : ℚ) - 1) = ((q - 1 : ℕ) : ℚ) := by
          have hq_ge : 1 ≤ q := by omega
          rw [Nat.cast_sub hq_ge]; push_cast; ring
        rw [h_eq_cast, Nat.ceil_natCast] at h_ceil_le
        omega
      -- Step 2: 1/(q-1) ≤ 2/q (since q ≥ 2).
      have h_two_q_ineq : 1/((q : ℚ) - 1) ≤ 2/(q : ℚ) := by
        rw [div_le_div_iff₀ hq_minus_one_pos hq_pos_q]
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq_ge_two
        nlinarith
      -- Step 3: S < 1/(q-1)
      have hS_lt_inv : S < 1/((q : ℚ) - 1) := by
        have h1 : (q : ℚ) - 1 < S⁻¹ := hSinv_gt
        rw [lt_div_iff₀ hq_minus_one_pos]
        have h2 : ((q : ℚ) - 1) * S < S⁻¹ * S := by
          have := mul_lt_mul_of_pos_right h1 hS_pos
          linarith
        rw [inv_mul_cancel₀ hS_pos.ne'] at h2
        linarith
      -- Step 4: S - 1/q < 1/q
      have hS_lt_two_q : S < 2/(q : ℚ) := lt_of_lt_of_le hS_lt_inv h_two_q_ineq
      have h_diff_lt : S - 1/(q : ℚ) < 1/(q : ℚ) := by
        have : (2 : ℚ) / q = 1/(q : ℚ) + 1/(q : ℚ) := by ring
        linarith
      -- Step 5: (S - 1/q)⁻¹ > q.
      have h_inv_gt : (q : ℚ) < (S - 1/(q : ℚ))⁻¹ := by
        rw [lt_inv_comm₀ hq_pos_q h_pos']
        have : (1 : ℚ) / q = (q : ℚ)⁻¹ := one_div _
        linarith
      -- Step 6: ⌈(S-1/q)⁻¹⌉₊ ≥ q + 1.
      rw [Nat.add_one_le_iff, Nat.lt_ceil]
      exact h_inv_gt
    obtain ⟨E', hE'_lb, hE'_sum⟩ := ih (S - 1/(q : ℚ)) h_nonneg' h_num_le (q + 1)
      (by omega) h_new_inv
    have hq_notin : q ∉ E' := by
      intro h
      have := hE'_lb q h
      omega
    refine ⟨insert q E', ?_, ?_⟩
    · intro e he
      rw [Finset.mem_insert] at he
      rcases he with rfl | he
      · exact hq_ge
      · have := hE'_lb e he
        omega
    · rw [Finset.sum_insert hq_notin, ← hE'_sum]
      ring

/-- Auxiliary: a single Egyptian expansion exists (greedy).

The proof uses a harmonic-tail prelude to reduce to a small residual `S ≤ 1/N`,
then applies the greedy step recursion `greedy_residual_aux`. -/
lemma egyptian_expansion_exists (R : ℚ) (hR : 0 < R) (L : ℕ) :
    ∃ E : Finset ℕ, (∀ e ∈ E, L < e) ∧ R = ∑ e ∈ E, (1 : ℚ) / e := by
  classical
  -- Lift to L' = max L 1 so that minDen ≥ 2.
  set L' := max L 1 with hL'_def
  have hL'_ge : 1 ≤ L' := le_max_right _ _
  have hL_le_L' : L ≤ L' := le_max_left _ _
  -- Find smallest N ≥ L' with R ≤ harmonicTail L' N. Such N exists by harmonic divergence.
  set P : ℕ → Prop := fun N => L' ≤ N ∧ R ≤ ∑ j ∈ Finset.Ioc L' N, (1 : ℚ) / j with hP_def
  have hP_ex : ∃ N, P N := exists_harmonicTail_ge_aux R L'
  set N := Nat.find hP_ex with hN_def
  have hN_spec : P N := Nat.find_spec hP_ex
  obtain ⟨hLN, hRle⟩ := hN_spec
  have hN_min : ∀ M, M < N → ¬ P M := fun M hM => Nat.find_min hP_ex hM
  -- Note R > 0, harmonicTail L' L' = 0, so N ≠ L'. Hence N > L'.
  have hN_gt : L' < N := by
    rcases lt_or_eq_of_le hLN with h | h
    · exact h
    · -- N = L', so harmonicTail L' L' = 0 ≥ R, contradicting R > 0.
      exfalso
      rw [← h, Finset.Ioc_self, Finset.sum_empty] at hRle
      linarith
  -- The harmonicTail to N-1 is < R (otherwise N is not minimal).
  have hN_minus_one_lt : ∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j < R := by
    by_contra h_neg
    push Not at h_neg
    have hN_minus_pos : N - 1 < N := by omega
    have hLeN : L' ≤ N - 1 := by omega
    apply hN_min (N - 1) hN_minus_pos
    exact ⟨hLeN, h_neg⟩
  -- Residual S = R - harmonicTail L' (N-1).
  set S := R - ∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j with hS_def
  have hS_pos : 0 < S := by simp only [hS_def]; linarith
  -- The harmonic sum to N is harmonic to N-1 plus 1/N (since N > L').
  have hSplit : (∑ j ∈ Finset.Ioc L' N, (1 : ℚ) / j) =
                (∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j) + 1/(N : ℚ) := by
    have h_succ : N = (N - 1) + 1 := by omega
    have hLeN_minus : L' ≤ N - 1 := by omega
    have hN_minus_le_N : N - 1 ≤ N := by omega
    rw [show Finset.Ioc L' N = Finset.Ioc L' (N - 1) ∪ Finset.Ioc (N - 1) N from ?_]
    · rw [Finset.sum_union ?_]
      · congr 1
        rw [show Finset.Ioc (N - 1) N = {N} from by
          ext x; simp [Finset.mem_Ioc]; omega]
        rw [Finset.sum_singleton]
      · rw [Finset.disjoint_left]
        intros a ha hb
        simp [Finset.mem_Ioc] at ha hb
        omega
    · ext x
      simp [Finset.mem_Ioc, Finset.mem_union]
      omega
  -- S ≤ 1/N
  have hS_le : S ≤ 1/(N : ℚ) := by
    simp only [hS_def]
    have := hRle
    rw [hSplit] at this
    linarith
  -- N ≥ 2 (since L' ≥ 1 and N > L')
  have hN_ge_two : 2 ≤ N := by omega
  -- Apply greedy on S with minDen = N.
  have hN_pos : 0 < (N : ℚ) := by exact_mod_cast (by omega : 0 < N)
  -- Need to show N ≤ ⌈S⁻¹⌉₊.
  have hSinv_ge : (N : ℚ) ≤ S⁻¹ := by
    rw [le_inv_comm₀ hN_pos hS_pos]
    rwa [one_div] at hS_le
  have h_minDen_le_ceil : N ≤ ⌈(S⁻¹ : ℚ)⌉₊ := by
    have : (N : ℚ) ≤ ⌈(S⁻¹ : ℚ)⌉₊ := le_trans hSinv_ge (Nat.le_ceil _)
    exact_mod_cast this
  obtain ⟨E', hE'_lb, hE'_sum⟩ :=
    greedy_residual_aux S.num.natAbs S hS_pos.le le_rfl N hN_ge_two
      (Or.inr h_minDen_le_ceil)
  -- Combine harmonic-tail with E'.
  refine ⟨Finset.Ioc L' (N - 1) ∪ E', ?_, ?_⟩
  · -- All elements > L
    intros e he
    rw [Finset.mem_union] at he
    rcases he with he | he
    · -- e ∈ Ioc L' (N-1), so e > L' ≥ L
      simp [Finset.mem_Ioc] at he
      omega
    · -- e ∈ E', so e ≥ N > L' ≥ L
      have := hE'_lb e he
      omega
  · -- Sum
    have h_disj : Disjoint (Finset.Ioc L' (N - 1)) E' := by
      rw [Finset.disjoint_left]
      intros a ha hb
      simp [Finset.mem_Ioc] at ha
      have := hE'_lb a hb
      omega
    rw [Finset.sum_union h_disj]
    have : R = (∑ j ∈ Finset.Ioc L' (N - 1), (1 : ℚ) / j) + S := by
      simp only [hS_def]; ring
    rw [this]
    rw [← hE'_sum]


end Erdos308.GreedyEgyptian

