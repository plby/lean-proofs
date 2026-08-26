import ErdosProblems.Erdos856b.PrimeEstimates
import ErdosProblems.Erdos856b.Bucketing

/-!
# Prime buckets at the logarithmic scale

We use the cutoff `exp (log N / (log log N)^2)`. It has harmonic prime mass
`(1 + o(1)) log log N`, and products of `O(log log N)` primes below it lie in `[1,N]`.
This is a harmless simplification of the moving cutoff in Theorem 3.5 of the source.
-/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

noncomputable def logScale (N : ℕ) : ℝ := log (log N)

noncomputable def bucketCount (a : ℝ) (N : ℕ) : ℕ := ⌊a * logScale N⌋₊

noncomputable def primeCutoff (N : ℕ) : ℝ := exp (exp (logScale N) / logScale N ^ 2)

theorem tendsto_logScale : Tendsto logScale atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_bucketCount_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N => (bucketCount a N : ℝ) / logScale N) atTop (𝓝 a) := by
  have hlo : Tendsto (fun N => a - 1 / logScale N) atTop (𝓝 a) := by
    have hzero : Tendsto (fun N => (1 : ℝ) / logScale N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_logScale
    simpa using (tendsto_const_nhds (x := a)).sub hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [tendsto_logScale.eventually_gt_atTop 0] with N hL
    have hfloor := Nat.lt_floor_add_one (a * logScale N)
    dsimp [bucketCount]
    apply (le_div_iff₀ hL).mpr
    have hdiv : (1 / logScale N) * logScale N = 1 := by field_simp
    nlinarith
  · filter_upwards [tendsto_logScale.eventually_gt_atTop 0] with N hL
    apply (div_le_iff₀ hL).mpr
    exact Nat.floor_le (mul_nonneg ha.le hL.le)

theorem tendsto_bucketCount {a : ℝ} (ha : 0 < a) : Tendsto (bucketCount a) atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [tendsto_logScale.eventually_ge_atTop ((m : ℝ) / a)] with N hN
  apply Nat.le_floor
  exact (div_le_iff₀ ha).mp hN |>.trans_eq (mul_comm _ _)

theorem tendsto_primeCutoff : Tendsto primeCutoff atTop atTop :=
  tendsto_exp_atTop.comp ((tendsto_exp_div_pow_atTop 2).comp tendsto_logScale)

theorem log_log_primeCutoff {N : ℕ} (hL : 0 < logScale N) :
    log (log (primeCutoff N)) = logScale N - 2 * log (logScale N) := by
  rw [primeCutoff, log_exp, log_div (exp_ne_zero _) (pow_ne_zero _ hL.ne'), log_exp, log_pow]
  norm_num

theorem tendsto_log_log_primeCutoff_div :
    Tendsto (fun N => log (log (primeCutoff N)) / logScale N) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun N => log (logScale N) / logScale N) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_logScale
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (hsmall.const_mul 2)
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [tendsto_logScale.eventually_gt_atTop 0] with N hN
  rw [log_log_primeCutoff hN]
  field_simp

theorem tendsto_primeHarmonic_cutoff_div :
    Tendsto (fun N => primeHarmonic (primeCutoff N) / logScale N) atTop (𝓝 1) := by
  have h1 := tendsto_primeHarmonic_div_log_log.comp tendsto_primeCutoff
  have h := h1.mul tendsto_log_log_primeCutoff_div
  simp only [one_mul] at h
  apply h.congr'
  have hlog := tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_primeCutoff)
  filter_upwards [hlog.eventually_gt_atTop 0] with N hN
  change 0 < log (log (primeCutoff N)) at hN
  dsimp [Function.comp_def]
  field_simp [hN.ne']

theorem eventually_primeCutoff_pow_bucketCount {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ primeCutoff N ∧ primeCutoff N ^ bucketCount a N ≤ N := by
  filter_upwards [tendsto_logScale.eventually_ge_atTop a, eventually_gt_atTop (1 : ℕ)]
    with N hL hN
  have hLpos : 0 < logScale N := ha.trans_le hL
  have hcount : (bucketCount a N : ℝ) ≤ logScale N ^ 2 := by
    have hfloor := Nat.floor_le (mul_nonneg ha.le hLpos.le)
    dsimp [bucketCount]
    nlinarith
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hNpos : (0 : ℝ) < N := by positivity
  have hexpL : exp (logScale N) = log N := exp_log hlogN
  constructor
  · apply one_le_exp_iff.mpr
    exact div_nonneg (exp_pos _).le (sq_nonneg _)
  · rw [primeCutoff, ← exp_nat_mul]
    calc
      exp (bucketCount a N * (exp (logScale N) / logScale N ^ 2)) ≤ exp (exp (logScale N)) := by
        apply exp_le_exp.mpr
        have hdivpos : 0 ≤ exp (logScale N) / logScale N ^ 2 := by positivity
        have h := mul_le_mul_of_nonneg_right hcount hdivpos
        have heq : logScale N ^ 2 * (exp (logScale N) / logScale N ^ 2) = exp (logScale N) := by
          field_simp
        exact h.trans_eq heq
      _ = N := by rw [hexpL, exp_log hNpos]

noncomputable def primeWindow (Y X : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊X⌋₊).filter (fun p => Y < (p : ℝ))

theorem primeWindow_sum {Y X : ℝ} (hYX : Y ≤ X) :
    (∑ p ∈ primeWindow Y X, (p : ℝ)⁻¹) = primeHarmonic X - primeHarmonic Y := by
  have hsub := Nat.primesLE_mono (Nat.floor_mono hYX)
  have heq : primeWindow Y X = Nat.primesLE ⌊X⌋₊ \ Nat.primesLE ⌊Y⌋₊ := by
    ext p
    simp only [primeWindow, Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hpX, hp⟩, hYp⟩
      refine ⟨⟨hpX, hp⟩, ?_⟩
      intro h
      exact (not_le_of_gt hYp) ((Nat.le_floor_iff' hp.ne_zero).mp h.1)
    · rintro ⟨⟨hpX, hp⟩, hnot⟩
      refine ⟨⟨hpX, hp⟩, ?_⟩
      by_contra h
      exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩
  rw [heq]
  exact eq_sub_iff_add_eq.mpr (Finset.sum_sdiff hsub)

theorem tendsto_primeWindow_div (Y : ℝ) :
    Tendsto (fun N => (∑ p ∈ primeWindow Y (primeCutoff N), (p : ℝ)⁻¹) / logScale N)
      atTop (𝓝 1) := by
  have h := tendsto_primeHarmonic_cutoff_div.sub
    ((tendsto_const_nhds (x := primeHarmonic Y)).div_atTop tendsto_logScale)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [tendsto_primeCutoff.eventually_ge_atTop Y] with N hN
  rw [primeWindow_sum hN, sub_div]

theorem eventually_prime_buckets {a z δ : ℝ} (ha : 0 < a) (hz : 0 < z) (hδ : 0 < δ)
    (haz : a * (z + δ) < 1) :
    ∀ᶠ N : ℕ in atTop, 0 < bucketCount a N ∧ 1 ≤ primeCutoff N ∧
      primeCutoff N ^ bucketCount a N ≤ N ∧
      ∃ P : Fin (bucketCount a N) → Finset ℕ,
        (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
        (∀ i p, p ∈ P i → p.Prime ∧ (p : ℝ) ≤ primeCutoff N) ∧
        ∀ i, z ≤ ∑ p ∈ P i, (p : ℝ)⁻¹ := by
  let Y : ℝ := max 2 (δ⁻¹)
  have hmass := (tendsto_primeWindow_div Y).eventually (lt_mem_nhds haz)
  filter_upwards [hmass, (tendsto_bucketCount ha).eventually_gt_atTop 0,
    tendsto_logScale.eventually_gt_atTop 0, eventually_primeCutoff_pow_bucketCount ha]
    with N hmass ht hL hsize
  have htotal : bucketCount a N * (z + δ) ≤
      ∑ p ∈ primeWindow Y (primeCutoff N), (p : ℝ)⁻¹ := by
    have hfloor := Nat.floor_le (mul_nonneg ha.le hL.le)
    have hbound := (lt_div_iff₀ hL).mp hmass
    have hmul := mul_le_mul_of_nonneg_right hfloor (by positivity : 0 ≤ z + δ)
    dsimp [bucketCount] at *
    nlinarith
  have hsmall : ∀ p ∈ primeWindow Y (primeCutoff N), (p : ℝ)⁻¹ < δ := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hp0 : (0 : ℝ) < p := by
      exact_mod_cast (Nat.mem_primesLE.mp hmem.1).2.pos
    exact (inv_lt_comm₀ hp0 hδ).mpr ((le_max_right _ _).trans_lt hmem.2)
  obtain ⟨P, hP, hdis, hw⟩ := exists_weight_buckets (bucketCount a N) hz hδ hsmall htotal
  refine ⟨ht, hsize.1, hsize.2, P, hdis, ?_, fun i => (hw i).1⟩
  intro i p hp
  have hmem := Nat.mem_primesLE.mp (Finset.mem_filter.mp (hP i hp)).1
  exact ⟨hmem.2, (Nat.le_floor_iff' hmem.2.ne_zero).mp hmem.1⟩

end Erdos856b
