import ErdosProblems.Erdos444.Basic
import ErdosProblems.Erdos444.Regular

/-!
# Elementary growth bounds for Erdős Problem 444

The reciprocal mass of an arbitrary set is bounded by the full harmonic
sum.  Consequently its logarithm, normalized by `log log x`, is uniformly
bounded on a sufficiently large tail.  This is the only growth input needed
to select regular cutoffs in the divergent-mass argument.
-/

open scoped BigOperators

namespace Erdos444

/-- The logarithmic normalization used to select regular cutoffs. -/
noncomputable def normalizedLogMass (A : Set ℕ) (x : ℕ) : ℝ :=
  Real.log (reciprocalMassNat A x) / Real.log (Real.log (x : ℝ))

/-- Every reciprocal prefix is bounded by the full harmonic sum, and hence
by `1 + log x`. -/
theorem reciprocalMassNat_le_one_add_log (A : Set ℕ) (x : ℕ) :
    reciprocalMassNat A x ≤ 1 + Real.log (x : ℝ) := by
  classical
  have hsub : (positiveBelowNat x).filter (fun a ↦ a ∈ A) ⊆
      Finset.Icc 1 x := by
    intro a ha
    have ha' := mem_positiveBelowNat_iff.mp (Finset.mem_filter.mp ha).1
    exact Finset.mem_Icc.mpr ⟨ha'.1, ha'.2.le⟩
  calc
    reciprocalMassNat A x
        ≤ ∑ a ∈ Finset.Icc 1 x, (a : ℝ)⁻¹ := by
          unfold reciprocalMassNat
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun a _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg a))
    _ = (harmonic x : ℝ) := by
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
            Rat.cast_natCast]
    _ ≤ 1 + Real.log (x : ℝ) := harmonic_le_one_add_log x

/-- A convenient explicit tail on which both logarithms in
`normalizedLogMass` are positive. -/
theorem two_lt_log_natCast {x : ℕ} (hx : 9 ≤ x) :
    2 < Real.log (x : ℝ) := by
  have hlog3 : 1 < Real.log (3 : ℝ) := by
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    exact Real.exp_one_lt_three
  have hlog9 : 2 < Real.log (9 : ℝ) := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  exact hlog9.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hx))

theorem one_lt_log_natCast {x : ℕ} (hx : 9 ≤ x) :
    1 < Real.log (x : ℝ) :=
  one_lt_two.trans (two_lt_log_natCast hx)

theorem log_log_natCast_pos {x : ℕ} (hx : 9 ≤ x) :
    0 < Real.log (Real.log (x : ℝ)) :=
  Real.log_pos (one_lt_log_natCast hx)

/-- Uniform harmonic-growth bound for the normalized logarithmic mass. -/
theorem normalizedLogMass_le_two (A : Set ℕ) {x : ℕ} (hx : 9 ≤ x) :
    normalizedLogMass A x ≤ 2 := by
  let L : ℝ := Real.log (x : ℝ)
  have hL1 : 1 < L := one_lt_log_natCast hx
  have hL2 : 2 < L := two_lt_log_natCast hx
  have hL0 : 0 < L := zero_lt_one.trans hL1
  have hmass := reciprocalMassNat_le_one_add_log A x
  have hquad : 1 + L ≤ L ^ 2 := by nlinarith
  have hmass2 : reciprocalMassNat A x ≤ L ^ 2 := hmass.trans hquad
  have hlogmass : Real.log (reciprocalMassNat A x) ≤ 2 * Real.log L := by
    by_cases hm : reciprocalMassNat A x = 0
    · simp [hm, Real.log_nonneg hL1.le]
    · have hmpos : 0 < reciprocalMassNat A x :=
        lt_of_le_of_ne (reciprocalMassNat_nonneg A x) (Ne.symm hm)
      calc
        Real.log (reciprocalMassNat A x) ≤ Real.log (L ^ 2) :=
          Real.log_le_log hmpos hmass2
        _ = 2 * Real.log L := by rw [Real.log_pow]; norm_num
  unfold normalizedLogMass
  change Real.log (reciprocalMassNat A x) / Real.log L ≤ 2
  exact (div_le_iff₀ (Real.log_pos hL1)).2 (by linarith)

/-- A regular point selected from any tail beginning at a cutoff at least
eight.  The conclusion controls the normalized logarithmic mass throughout
that whole tail, including any seed used to choose it. -/
theorem exists_regular_normalizedLogMass (A : Set ℕ) (N : ℕ) (hN : 9 ≤ N)
    (hpos : ∃ n, N ≤ n ∧ 0 < normalizedLogMass A n) :
    ∃ x, N ≤ x ∧ 0 < normalizedLogMass A x ∧
      ∀ y, N ≤ y → normalizedLogMass A y ≤
        2 * normalizedLogMass A x := by
  exact exists_tail_two_regular_strong (normalizedLogMass A) N 2 hpos
    (fun n hn ↦ normalizedLogMass_le_two A (hN.trans hn))

/-- Unfolding the normalization at two positive cutoffs.  This packages the
division algebra used when a regular point is moved to a later cutoff. -/
theorem log_reciprocalMassNat_le_of_normalizedLogMass_le
    (A : Set ℕ) {x y : ℕ}
    (hx : 9 ≤ x) (hy : 9 ≤ y)
    (h : normalizedLogMass A y ≤ 2 * normalizedLogMass A x) :
    Real.log (reciprocalMassNat A y) ≤
      2 * Real.log (reciprocalMassNat A x) *
        (Real.log (Real.log (y : ℝ)) /
          Real.log (Real.log (x : ℝ))) := by
  have hLx : 0 < Real.log (Real.log (x : ℝ)) := log_log_natCast_pos hx
  have hLy : 0 < Real.log (Real.log (y : ℝ)) := log_log_natCast_pos hy
  unfold normalizedLogMass at h
  have hmul := (div_le_iff₀ hLy).mp h
  calc
    Real.log (reciprocalMassNat A y) ≤
        (2 * (Real.log (reciprocalMassNat A x) /
          Real.log (Real.log (x : ℝ)))) *
            Real.log (Real.log (y : ℝ)) := hmul
    _ = 2 * Real.log (reciprocalMassNat A x) *
        (Real.log (Real.log (y : ℝ)) /
          Real.log (Real.log (x : ℝ))) := by ring

/-- If the later double logarithm grows by at most a factor three, a regular
normalized point loses at most a factor six in the logarithm of the mass. -/
theorem log_reciprocalMassNat_le_six_of_regular
    (A : Set ℕ) {x y : ℕ}
    (hx : 9 ≤ x) (hy : 9 ≤ y)
    (hmass : 1 ≤ reciprocalMassNat A x)
    (hreg : normalizedLogMass A y ≤ 2 * normalizedLogMass A x)
    (hloglog : Real.log (Real.log (y : ℝ)) ≤
      3 * Real.log (Real.log (x : ℝ))) :
    Real.log (reciprocalMassNat A y) ≤
      6 * Real.log (reciprocalMassNat A x) := by
  have hLx : 0 < Real.log (Real.log (x : ℝ)) := log_log_natCast_pos hx
  have hlogmass : 0 ≤ Real.log (reciprocalMassNat A x) :=
    Real.log_nonneg hmass
  have hratio : Real.log (Real.log (y : ℝ)) /
      Real.log (Real.log (x : ℝ)) ≤ 3 :=
    (div_le_iff₀ hLx).2 (by simpa [mul_comm] using hloglog)
  calc
    Real.log (reciprocalMassNat A y) ≤
        2 * Real.log (reciprocalMassNat A x) *
          (Real.log (Real.log (y : ℝ)) /
            Real.log (Real.log (x : ℝ))) :=
      log_reciprocalMassNat_le_of_normalizedLogMass_le A hx hy hreg
    _ ≤ 2 * Real.log (reciprocalMassNat A x) * 3 := by
      exact mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hlogmass)
    _ = 6 * Real.log (reciprocalMassNat A x) := by ring

end Erdos444
