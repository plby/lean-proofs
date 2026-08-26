import ErdosProblems.Erdos380.SaddleQuotient
import ErdosProblems.Erdos380.SmoothRankin

/-! # Uniform upper bounds for smooth numbers at fixed powers of the scale -/

open Filter
open scoped Topology

namespace Erdos380

/-- The cutoff may vary anywhere between `N / S^c` and `N`. The strict
integer inequality on `k * r` leaves room for the Euler-product error. -/
theorem eventually_smoothCount_scale_upper {k r : ℕ} (hk : 0 < k)
    (hkr : k * r < 1000000) (c : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℕ, x ≤ N → N ≤ x * scaleBase N ^ c →
      (smoothCount x (scaleBase N ^ k) : ℝ) ≤ (x : ℝ) / (scaleBase N : ℝ) ^ r := by
  let ε : ℝ := 1 / 10000000
  have hε : 0 < ε := by norm_num [ε]
  have hε1 : ε < 1 := by norm_num [ε]
  have hcoef : 0 ≤ 1 - 2 * ε := by norm_num [ε]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨u₀, hu₀, hbound⟩ := smoothCount_growing_parameter_upper hε hε1 (by norm_num : (0 : ℝ) ≤ 2)
  have hgap : (r : ℝ) < (1 - 2 * ε) * (1000000 / k) := by
    have hkr' : (r : ℝ) * k ≤ 999999 := by
      exact_mod_cast (show r * k ≤ 999999 by rw [Nat.mul_comm]; omega)
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hkR).mpr
    norm_num [ε]
    linarith
  have hcost := (saddleQuotient_log_cost hk c).const_mul (1 - 2 * ε)
  filter_upwards [hcost.eventually (lt_mem_nhds hgap),
    (saddleQuotient_tendsto_atTop hk c).eventually (eventually_ge_atTop u₀),
    (loglog_scaleBase_pow_div_log_saddleQuotient hk c).eventually
      (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    (log_saddleQuotient_div_log_scaleBase hk 0).eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < (k : ℝ) / 2)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    scaleBase_tendsto_atTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
      with N hcost hmin hloglog hlogmax hS hS2 hN
  intro x hxN hNx
  have hx : 0 < x := by
    by_contra h
    have hx0 : x = 0 := by omega
    rw [hx0, zero_mul] at hNx
    omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast (by omega : 0 < scaleBase N)
  have hy : 2 ≤ scaleBase N ^ k := hS2.trans (le_self_pow (by omega) hk.ne')
  have hks : 0 < (k : ℝ) * Real.log (scaleBase N : ℝ) := mul_pos hkR hS
  have hlogy : Real.log (scaleBase N ^ k : ℕ) = (k : ℝ) * Real.log (scaleBase N : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hloglower := Real.log_le_log hNpos
    (show (N : ℝ) ≤ (x : ℝ) * (scaleBase N : ℝ) ^ c by exact_mod_cast hNx)
  rw [Real.log_mul hxR.ne' (pow_ne_zero c hSpos.ne'), Real.log_pow] at hloglower
  have hlogupper : Real.log (x : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hxR (by exact_mod_cast hxN)
  let u := Real.log (x : ℝ) / ((k : ℝ) * Real.log (scaleBase N : ℝ))
  have hminu : saddleQuotient k c N ≤ u :=
    div_le_div_of_nonneg_right (by linarith) hks.le
  have humax : u ≤ saddleQuotient k 0 N := by
    simpa only [saddleQuotient, Nat.cast_zero, zero_mul, sub_zero] using
      div_le_div_of_nonneg_right hlogupper hks.le
  have hmin1 : 1 < saddleQuotient k c N := hu₀.trans_le hmin
  have hu1 : 1 < u := hmin1.trans_le hminu
  have hlogmin : 0 < Real.log (saddleQuotient k c N) := Real.log_pos hmin1
  have hlogu : Real.log (saddleQuotient k c N) ≤ Real.log u :=
    Real.log_le_log (by linarith) hminu
  have hparam : Real.log (x : ℝ) = u * Real.log (scaleBase N ^ k : ℕ) := by
    rw [hlogy]
    exact (div_mul_cancel₀ _ hks.ne').symm
  have hloglogu : Real.log (Real.log (scaleBase N ^ k : ℕ)) ≤ 2 * Real.log u := by
    have h := (div_le_iff₀ hlogmin).mp hloglog.le
    linarith
  have hloguupper : Real.log u ≤ Real.log (scaleBase N ^ k : ℕ) / 2 := by
    have hmax := (div_le_iff₀ hS).mp hlogmax.le
    have hh := Real.log_le_log (by linarith : 0 < u) humax
    rw [hlogy]
    linarith
  have hcount := hbound x (scaleBase N ^ k) hx hy u (hmin.trans hminu) hparam hloglogu hloguupper
  have hmain : (r : ℝ) * Real.log (scaleBase N : ℝ) ≤
      (1 - 2 * ε) * u * Real.log u := by
    have hcost' : (r : ℝ) ≤ ((1 - 2 * ε) * saddleQuotient k c N *
        Real.log (saddleQuotient k c N)) / Real.log (scaleBase N : ℝ) := by
      simpa only [mul_div_assoc, mul_assoc] using hcost.le
    have hcost'' := (le_div_iff₀ hS).mp hcost'
    have hprod := mul_le_mul hminu hlogu hlogmin.le (by linarith : 0 ≤ u)
    have hm := mul_le_mul_of_nonneg_left hprod hcoef
    nlinarith
  apply hcount.trans
  calc
    (x : ℝ) * Real.exp (-(1 - 2 * ε) * u * Real.log u) ≤
        (x : ℝ) * Real.exp (-(r : ℝ) * Real.log (scaleBase N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hxR.le
      apply Real.exp_le_exp.mpr
      linarith
    _ = (x : ℝ) / (scaleBase N : ℝ) ^ r := by
      rw [show -(r : ℝ) * Real.log (scaleBase N : ℝ) = -Real.log ((scaleBase N : ℝ) ^ r) by
        rw [Real.log_pow]; ring, Real.exp_neg, Real.exp_log (pow_pos hSpos r)]
      rfl

end Erdos380
