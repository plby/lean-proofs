import ErdosProblems.Erdos4.OuterDensity

/-!
# Growth and random-sieve accuracy on the outer ray

All moving finite prime sets are instantiated after the uniform accuracy
threshold. The fourth-power small cutoff dominates the square of the
logarithm of the full tuple extent.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.OuterAccuracy

open SmoothParameters OuterRay OuterDensity

instance randomPrimes_factPrime (a r : ℕ) (p : randomPrimes a r) : Fact (p : ℕ).Prime :=
  ⟨(ChebyshevIntervals.mem_primeInterval.mp p.property).1⟩

theorem primaryExponent_le_primary (a r : ℕ) : primaryExponent a r ≤ primaryFrontier a r :=
  (show primaryExponent a r < 2 ^ primaryExponent a r from Nat.lt_two_pow_self).le

theorem self_le_primaryExponent (a r : ℕ) : r ≤ primaryExponent a r :=
  (self_le_core r).trans (core_le_primaryExponent a r)

theorem tendsto_core : Tendsto core atTop atTop := tendsto_atTop_mono self_le_core tendsto_id
theorem tendsto_exponent (a : ℕ) : Tendsto (primaryExponent a) atTop atTop :=
  tendsto_atTop_mono (self_le_primaryExponent a) tendsto_id
theorem tendsto_primary (a : ℕ) : Tendsto (primaryFrontier a) atTop atTop :=
  tendsto_atTop_mono (primaryExponent_le_primary a) (tendsto_exponent a)
theorem tendsto_base (a : ℕ) : Tendsto (base a) atTop atTop :=
  tendsto_atTop_mono (primary_le_base a) (tendsto_primary a)
theorem tendsto_frontier (a : ℕ) : Tendsto (frontier a) atTop atTop :=
  tendsto_atTop_mono (base_le_frontier a) (tendsto_base a)

theorem tendsto_length (a : ℕ) {D : ℕ} (hD : 1 ≤ D) : Tendsto (length a D) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (tendsto_frontier a)
  filter_upwards [eventually_ge_atTop 1] with r hr
  exact frontier_le_length a hD hr

def extent (a D H r : ℕ) : ℕ := length a D r + H * frontier a r

theorem tendsto_extent (a H : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    Tendsto (extent a D H) atTop atTop :=
  tendsto_atTop_mono (fun r => Nat.le_add_right _ _) (tendsto_length a hD)

theorem extent_le (a D H r : ℕ) :
    extent a D H r ≤ (256 * (D + H)) * primaryFrontier a r ^ 50 * core r ^ 2 := by
  have hV : 1 ≤ core r ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (core_pos r).ne')
  have hH : H * frontier a r ≤ (256 * H) * primaryFrontier a r ^ 50 * core r ^ 2 := by
    have hh := Nat.mul_le_mul_left (H * frontier a r) hV
    calc
      _ ≤ H * frontier a r * core r ^ 2 := by simpa only [mul_one] using hh
      _ = _ := by unfold OuterRay.frontier OuterRay.base; ring
  have hh := Nat.add_le_add (length_le_core_square a D r) hH
  exact hh.trans_eq (by ring)

theorem eventually_log_extent_sq_le_small (a H : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ r : ℕ in atTop, Real.log (extent a D H r : ℝ) ^ 2 ≤ smallCutoff a r := by
  let M : ℕ := 256 * (D + H)
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
  have hEtop : Tendsto (fun r : ℕ => (primaryExponent a r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_exponent a)
  filter_upwards [eventually_ge_atTop 1,
    hEtop.eventually (eventually_ge_atTop (Real.log M + 50 * Real.log 2 + 3))] with r hr hElarge
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have ht : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hE : (0 : ℝ) < primaryExponent a r := by exact_mod_cast primaryExponent_pos a r
  have hE1 : (1 : ℝ) ≤ primaryExponent a r := by exact_mod_cast primaryExponent_pos a r
  have hB : 0 < extent a D H r :=
    (frontier_pos a r).trans_le ((frontier_le_length a hD hr).trans (Nat.le_add_right _ _))
  have hBR : (0 : ℝ) < extent a D H r := by exact_mod_cast hB
  have hlogB0 : 0 ≤ Real.log (extent a D H r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hB)
  have hlogV : Real.log (core r : ℝ) ≤ primaryExponent a r := by
    have hh := Real.log_le_sub_one_of_pos hV
    have hVE : (core r : ℝ) ≤ primaryExponent a r := by exact_mod_cast core_le_primaryExponent a r
    linarith
  have hlogt : Real.log (primaryFrontier a r : ℝ) = (primaryExponent a r : ℝ) * Real.log 2 := by
    rw [primaryFrontier, Nat.cast_pow, Real.log_pow]
    norm_num
  have hlogB := Real.log_le_log hBR
    (by exact_mod_cast extent_le a D H r :
      (extent a D H r : ℝ) ≤ (M : ℝ) * (primaryFrontier a r : ℝ) ^ 50 * (core r : ℝ) ^ 2)
  rw [Real.log_mul (mul_pos hMR (pow_pos ht 50)).ne' (pow_pos hV 2).ne',
    Real.log_mul hMR.ne' (pow_pos ht 50).ne', Real.log_pow, Real.log_pow, hlogt] at hlogB
  have hlinear : Real.log (extent a D H r : ℝ) ≤
      Real.log M + (50 * Real.log 2 + 2) * primaryExponent a r := by
    norm_num at hlogB
    nlinarith
  have hquad : Real.log (extent a D H r : ℝ) ≤ (primaryExponent a r : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hElarge hE.le
    nlinarith [mul_nonneg hlogM (sub_nonneg.mpr hE1)]
  have hsq := (sq_le_sq₀ hlogB0 (sq_nonneg (primaryExponent a r : ℝ))).mpr hquad
  simpa only [smallCutoff, Nat.cast_pow, ← pow_mul] using hsq

/-- The random prime set on the concrete ray satisfies the uniform joint
survival estimate for all bounded tuples in its full geometric extent. -/
theorem eventually_random_accuracy (a H k : ℕ) {D : ℕ} (hD : 1 ≤ D) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, TupleSurvivalBounds.Accurate
      (fun p : randomPrimes a r => (p : ℕ)) (extent a D H r) (2 * k) ε := by
  have hacc := (tendsto_extent a H hD).eventually
    (TupleSurvivalBounds.eventually_accurate (2 * k) hε)
  filter_upwards [hacc, eventually_log_extent_sq_le_small a H hD] with r hr hlog
  apply hr (randomPrimes a r) (fun p : randomPrimes a r => (p : ℕ)) Subtype.val_injective
  intro p
  exact hlog.trans (by exact_mod_cast (ChebyshevIntervals.mem_primeInterval.mp p.property).2.1.le)

end Erdos4.OuterAccuracy
