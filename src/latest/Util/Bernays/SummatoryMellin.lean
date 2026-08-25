import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Mellin continuation from a bound on summatory coefficients
-/

open Filter Topology Asymptotics MeasureTheory Set

namespace Bernays

noncomputable def realSummatory (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, f k

theorem realSummatory_zero_of_lt_one (f : ℕ → ℂ) {x : ℝ} (hx : x < 1) :
    realSummatory f x = 0 := by
  unfold realSummatory
  rw [Nat.floor_eq_zero.mpr hx]
  simp

theorem realSummatory_locallyIntegrable (f : ℕ → ℂ) :
    LocallyIntegrableOn (realSummatory f) (Ioi 0) := by
  have h : LocallyIntegrableOn (realSummatory f) (Ici 0) := by
    change LocallyIntegrableOn (fun t : ℝ => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) (Ici 0)
    simpa only [one_mul] using
      (locallyIntegrableOn_mul_sum_Icc f (m := 1) (a := 0) le_rfl (locallyIntegrableOn_const 1))
  exact h.mono_set Ioi_subset_Ici_self

theorem realSummatory_bigO_atTop {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ r) :
    realSummatory f =O[atTop] fun x : ℝ => x ^ r := by
  exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans
    (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))

theorem realSummatory_bigO_zero (f : ℕ → ℂ) (r : ℝ) :
    realSummatory f =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ r := by
  apply IsBigO.of_bound 0
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall] with x hx
  simp only [realSummatory_zero_of_lt_one f hx, norm_zero, zero_mul, le_refl]

noncomputable def summatoryLSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * mellin (realSummatory f) (-s)

theorem mellin_realSummatory (f : ℕ → ℂ) (s : ℂ) :
    mellin (realSummatory f) (-s) =
      ∫ t in Ioi (1 : ℝ), realSummatory f t * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin
  simp only [smul_eq_mul]
  have hrestrict : (∫ t in Ici (1 : ℝ), (t : ℂ) ^ (-s - 1) * realSummatory f t) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-s - 1) * realSummatory f t := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ici_subset_Ioi.mpr zero_lt_one)
    intro t ht
    rw [realSummatory_zero_of_lt_one f (lt_of_not_ge ht.2), mul_zero]
  rw [← hrestrict, integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [show -s - 1 = -(s + 1) by ring, mul_comm]

theorem summatoryLSeries_eq {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) (hS : LSeriesSummable f s) :
    summatoryLSeries f s = LSeries f s := by
  rw [summatoryLSeries, mellin_realSummatory, LSeries_eq_mul_integral f hr hs hS hO]
  rfl

theorem summatoryLSeries_differentiableAt {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => (n : ℝ) ^ r)
    {s : ℂ} (hs : r < s.re) : DifferentiableAt ℂ (summatoryLSeries f) s := by
  have htop : realSummatory f =O[atTop] fun x : ℝ => x ^ (-(-r)) := by
    simpa only [neg_neg] using realSummatory_bigO_atTop hr hO
  have hm := mellin_differentiableAt_of_isBigO_rpow
    (realSummatory_locallyIntegrable f) htop
    (show (-s).re < -r by simpa only [Complex.neg_re] using neg_lt_neg hs)
    (realSummatory_bigO_zero f (-((-s).re - 1))) (show (-s).re - 1 < (-s).re by linarith)
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

end Bernays
