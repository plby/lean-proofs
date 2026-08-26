import ErdosProblems.Erdos1002.GaussDenominatorTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniformity on linearly growing integer windows

The elementary lemma in this file makes explicit a step used in the
continued-fraction time change.  Pointwise convergence of `u n / n` implies
an `o(L)` error uniformly for all integer times `n ≤ C L`, for every fixed
integer `C`.  The finitely many early times are kept in the proof rather than
silently absorbed into the asymptotic notation.
-/

open Filter Set
open scoped Topology BigOperators

namespace Erdos1002

noncomputable section

/-- If `u n / n` tends to `mean`, then the linear approximation is uniformly
`o(L)` on every fixed linearly growing integer window `n ≤ C L`.

The value at `n = 0` and all other finitely many early values are controlled
by an explicit finite sum, so no convention about division by zero is used in
the asymptotic part of the argument. -/
theorem eventually_uniform_linear_window_of_tendsto_div
    (u : ℕ → ℝ) (mean : ℝ)
    (h : Tendsto (fun n : ℕ ↦ u n / (n : ℝ)) atTop (𝓝 mean))
    (C : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ L : ℕ in atTop, ∀ n : ℕ, n ≤ C * L →
      |u n - (n : ℝ) * mean| ≤ epsilon * (L : ℝ) := by
  let delta : ℝ := epsilon / ((C : ℝ) + 1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h delta hdelta
  let N₀ : ℕ := max N 1
  have htail : ∀ n : ℕ, N₀ ≤ n →
      |u n / (n : ℝ) - mean| < delta := by
    intro n hn
    have hNn : N ≤ n := (le_max_left N 1).trans hn
    simpa only [Real.dist_eq] using! hN n hNn
  let M : ℝ := ∑ n ∈ Finset.range N₀, |u n - (n : ℝ) * mean|
  have hM0 : 0 ≤ M := by
    dsimp [M]
    positivity
  have hMdiv : Tendsto (fun L : ℕ ↦ M / (L : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat M
  obtain ⟨L₀, hL₀⟩ := Metric.tendsto_atTop.mp hMdiv epsilon hepsilon
  filter_upwards [eventually_ge_atTop (max L₀ 1)] with L hL
  intro n hnwindow
  have hL₀L : L₀ ≤ L := (le_max_left L₀ 1).trans hL
  have hLposNat : 0 < L := (le_max_right L₀ 1).trans hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLposNat
  have hMsmallDist : dist (M / (L : ℝ)) 0 < epsilon := hL₀ L hL₀L
  have hMsmall : M < epsilon * (L : ℝ) := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hM0 hLpos.le)] at hMsmallDist
    exact (div_lt_iff₀ hLpos).mp hMsmallDist
  by_cases hnEarly : n < N₀
  · have hnmem : n ∈ Finset.range N₀ := Finset.mem_range.mpr hnEarly
    have htermM : |u n - (n : ℝ) * mean| ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum
        (fun k hk ↦ abs_nonneg (u k - (k : ℝ) * mean)) hnmem
    exact htermM.trans hMsmall.le
  · have hnTail : N₀ ≤ n := Nat.le_of_not_gt hnEarly
    have hnposNat : 0 < n := (le_max_right N 1).trans hnTail
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
    have hratio := htail n hnTail
    have hncast : (n : ℝ) ≤ (C : ℝ) * (L : ℝ) := by
      exact_mod_cast hnwindow
    have hfactor :
        |u n - (n : ℝ) * mean| =
          (n : ℝ) * |u n / (n : ℝ) - mean| := by
      rw [show u n - (n : ℝ) * mean =
          (n : ℝ) * (u n / (n : ℝ) - mean) by
            field_simp [ne_of_gt hnpos]]
      rw [abs_mul, abs_of_pos hnpos]
    rw [hfactor]
    calc
      (n : ℝ) * |u n / (n : ℝ) - mean|
          ≤ (n : ℝ) * delta :=
            mul_le_mul_of_nonneg_left hratio.le hnpos.le
      _ ≤ ((C : ℝ) * (L : ℝ)) * delta :=
            mul_le_mul_of_nonneg_right hncast hdelta.le
      _ ≤ epsilon * (L : ℝ) := by
            dsimp [delta]
            have hCnonneg : (0 : ℝ) ≤ C := by positivity
            have hCle : (C : ℝ) ≤ (C : ℝ) + 1 := by linarith
            have hfrac : (C : ℝ) / ((C : ℝ) + 1) ≤ 1 := by
              exact (div_le_one (by positivity)).mpr hCle
            calc
              ((C : ℝ) * (L : ℝ)) *
                    (epsilon / ((C : ℝ) + 1)) =
                  (epsilon * (L : ℝ)) *
                    ((C : ℝ) / ((C : ℝ) + 1)) := by ring
              _ ≤ (epsilon * (L : ℝ)) * 1 := by
                    exact mul_le_mul_of_nonneg_left hfrac
                      (mul_nonneg hepsilon.le hLpos.le)
              _ = epsilon * (L : ℝ) := by ring

/-- Specialization of the preceding deterministic lemma to actual Gauss
prefix denominators.  A pointwise roof law of large numbers therefore gives
the exact uniform denominator-time estimate needed on every fixed linear
index window. -/
theorem eventually_uniform_gaussPrefixDenominator_time
    {x mean : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonzero : ∀ j : ℕ, gaussOrbit j x ≠ 0)
    (hroof : Tendsto
      (fun n : ℕ ↦ gaussRoofSum n x / (n : ℝ))
      atTop (𝓝 mean))
    (C : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ L : ℕ in atTop, ∀ n : ℕ, n ≤ C * L →
      |Real.log (gaussPrefixDenominator n x : ℝ) -
          (n : ℝ) * mean| ≤ epsilon * (L : ℝ) := by
  exact eventually_uniform_linear_window_of_tendsto_div
    (fun n : ℕ ↦ Real.log (gaussPrefixDenominator n x : ℝ)) mean
    (tendsto_log_gaussPrefixDenominator_div_of_roofAverage hx hnonzero hroof)
    C hepsilon

end

end Erdos1002
