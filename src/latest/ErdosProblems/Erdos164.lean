/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 164.
https://www.erdosproblems.com/forum/thread/164

Formal authors:
- Codex
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos164.md
-/
import Mathlib

open scoped Topology

noncomputable section

namespace Erdos164

noncomputable def baseFlow (N M : ℕ) : ℝ :=
  if 1 < N then
    if M ∣ N then
      let q := N / M
      if IsPrimePow q then
        ArithmeticFunction.vonMangoldt q / ((N : ℝ) * (Real.log N) ^ 2)
      else
        0
    else
      0
  else
    0

noncomputable def modifiedFlow (N M : ℕ) : ℝ :=
  by
    classical
    exact
      if ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ M = 1 then
        0
      else if ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ M = p ^ (k - 1) then
        baseFlow N M + baseFlow N 1
      else
        baseFlow N M

noncomputable def outflow (W : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' M : ℕ, W N M

noncomputable def inflow (W : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' K : ℕ, W K N

noncomputable def erdosWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log n)

theorem outflow_modifiedFlow_eq_erdosWeight {N : ℕ} (hN : 1 < N) :
    outflow modifiedFlow N = erdosWeight N := by
      sorry
noncomputable def analyticSeries (s : ℝ) : ℝ :=
  ∑' q : { q : ℕ // 2 ≤ q },
    ArithmeticFunction.vonMangoldt q / Real.rpow ((q : ℕ) : ℝ) s

noncomputable def zetaSeries (s : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s

lemma analyticSeries_eq_neg_deriv_zetaSeries_div_zetaSeries {s : ℝ} (hs : 1 < s) :
    analyticSeries s = -deriv zetaSeries s / zetaSeries s := by
  have hs' : 1 < (s : ℂ).re := by
    simpa using hs
  let e : ℕ ≃ { q : ℕ // 2 ≤ q } :=
    { toFun := fun n => ⟨n + 2, by omega⟩
      invFun := fun q => q.1 - 2
      left_inv := by
        intro n
        simp
      right_inv := by
        rintro ⟨q, hq⟩
        apply Subtype.ext
        exact Nat.sub_add_cancel hq }
  have hzeta_complex {x : ℝ} (hx : 1 < x) :
      ((zetaSeries x : ℝ) : ℂ) = LSeries 1 (x : ℂ) := by
    have hx' : 1 < (x : ℂ).re := by
      simpa using hx
    calc
      ((zetaSeries x : ℝ) : ℂ)
          = ∑' n : ℕ, ((1 / Real.rpow (((n + 1 : ℕ) : ℝ)) x : ℝ) : ℂ) := by
              rw [zetaSeries, Complex.ofReal_tsum]
      _ = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) := by
            refine tsum_congr fun n ↦ ?_
            have hpow :
                ((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (↑n + 1 : ℂ) ^ (x : ℂ) := by
              simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) x)
            simpa using congrArg (fun z : ℂ => (1 : ℂ) / z) hpow
      _ = riemannZeta (x : ℂ) := by
            symm
            exact zeta_eq_tsum_one_div_nat_add_one_cpow hx'
      _ = LSeries 1 (x : ℂ) := by
            symm
            exact LSeries_one_eq_riemannZeta hx'
  have hzeta_event :
      zetaSeries =ᶠ[𝓝 s] fun x : ℝ => (LSeries 1 (x : ℂ)).re := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{x : ℝ | 1 < x}, (isOpen_lt continuous_const continuous_id).mem_nhds hs, ?_⟩
    intro x hx
    simpa using congrArg Complex.re (hzeta_complex hx)
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  have hL1_deriv :
      HasDerivAt (fun x : ℝ => (LSeries 1 (x : ℂ)).re) (deriv (LSeries 1) (s : ℂ)).re s := by
    simpa [LSeries_deriv habs] using (LSeries_hasDerivAt (f := 1) habs).real_of_complex
  have hzeta_deriv : deriv zetaSeries s = (deriv (LSeries 1) (s : ℂ)).re := by
    rw [Filter.EventuallyEq.deriv_eq hzeta_event]
    exact hL1_deriv.deriv
  have hzeta_val : zetaSeries s = (LSeries 1 (s : ℂ)).re := by
    simpa using congrArg Complex.re (hzeta_complex hs)
  have hzeta_pos : 0 < zetaSeries s := by
    rw [hzeta_val, LSeries_one_eq_riemannZeta hs']
    exact riemannZeta_re_pos_of_one_lt hs
  have hzeta_ne : zetaSeries s ≠ 0 := hzeta_pos.ne'
  have hanalytic_complex :
      ((analyticSeries s : ℝ) : ℂ) =
        LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
    calc
      ((analyticSeries s : ℝ) : ℂ)
          = ∑' n : ℕ,
              ((ArithmeticFunction.vonMangoldt (n + 2 : ℕ) /
                Real.rpow (((n + 2 : ℕ) : ℝ)) s : ℝ) : ℂ) := by
                  rw [analyticSeries, Complex.ofReal_tsum,
                    ← e.tsum_eq
                      (fun q : { q : ℕ // 2 ≤ q } =>
                        (((ArithmeticFunction.vonMangoldt q : ℝ) /
                          Real.rpow ((q : ℕ) : ℝ) s : ℝ) : ℂ))]
                  simp [e]
      _ = ∑' n : ℕ,
            LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) (n + 2) := by
              refine tsum_congr fun n ↦ ?_
              have hn : (n + 2 : ℕ) ≠ 0 := by omega
              rw [LSeries.term_of_ne_zero hn]
              have hpow :
                  ((((n + 2 : ℕ) : ℝ) ^ s : ℝ) : ℂ) = (↑n + 2 : ℂ) ^ (s : ℂ) := by
                simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 2 : ℕ) : ℝ))) s)
              simpa using
                congrArg
                  (fun z : ℂ => (ArithmeticFunction.vonMangoldt (n + 2 : ℕ) : ℂ) / z) hpow
      _ = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
            symm
            rw [LSeries]
            have hsum :
                LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
              simpa using ArithmeticFunction.LSeriesSummable_vonMangoldt hs'
            have htail := hsum.sum_add_tsum_nat_add 2
            have hinit :
                ∑ i ∈ Finset.range 2,
                  LSeries.term
                      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) i = 0 := by
              rw [Finset.sum_range_succ, Finset.sum_range_one]
              simp [LSeries.term_def, ArithmeticFunction.vonMangoldt_apply_one]
            simpa [hinit] using htail.symm
  have hmain_complex :
      ((analyticSeries s : ℝ) : ℂ) =
        -deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ) := by
    calc
      ((analyticSeries s : ℝ) : ℂ)
          = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) :=
            hanalytic_complex
      _ = -deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ) := by
            simpa using ArithmeticFunction.LSeries_vonMangoldt_eq hs'
  have hmain_re :
      analyticSeries s = (-deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ)).re := by
    simpa using congrArg Complex.re hmain_complex
  have hquot :
      (-deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ)).re =
        -deriv zetaSeries s / zetaSeries s := by
    rw [← hzeta_complex hs, Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, hzeta_deriv, mul_zero, zero_div, add_zero]
    field_simp [hzeta_ne]
  exact hmain_re.trans hquot

lemma neg_deriv_zetaSeries_eq_tsum_log_nat_succ_div_rpow {s : ℝ} (hs : 1 < s) :
    -deriv zetaSeries s =
      ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
  have hzeta_complex {x : ℝ} (hx : 1 < x) :
      ((zetaSeries x : ℝ) : ℂ) = LSeries 1 (x : ℂ) := by
    have hx' : 1 < (x : ℂ).re := by
      simpa using hx
    calc
      ((zetaSeries x : ℝ) : ℂ)
          = ∑' n : ℕ, ((1 / Real.rpow (((n + 1 : ℕ) : ℝ)) x : ℝ) : ℂ) := by
              rw [zetaSeries, Complex.ofReal_tsum]
      _ = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) := by
            refine tsum_congr fun n ↦ ?_
            have hpow :
                ((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (↑n + 1 : ℂ) ^ (x : ℂ) := by
              simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) x)
            simpa using congrArg (fun z : ℂ => (1 : ℂ) / z) hpow
      _ = riemannZeta (x : ℂ) := by
            symm
            exact zeta_eq_tsum_one_div_nat_add_one_cpow hx'
      _ = LSeries 1 (x : ℂ) := by
            symm
            exact LSeries_one_eq_riemannZeta hx'
  have hzeta_event :
      zetaSeries =ᶠ[𝓝 s] fun x : ℝ => (LSeries 1 (x : ℂ)).re := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{x : ℝ | 1 < x}, (isOpen_lt continuous_const continuous_id).mem_nhds hs, ?_⟩
    intro x hx
    simpa using congrArg Complex.re (hzeta_complex hx)
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  have hL1_deriv :
      HasDerivAt (fun x : ℝ => (LSeries 1 (x : ℂ)).re) (deriv (LSeries 1) (s : ℂ)).re s := by
    simpa [LSeries_deriv habs] using (LSeries_hasDerivAt (f := 1) habs).real_of_complex
  have hzeta_deriv : deriv zetaSeries s = (deriv (LSeries 1) (s : ℂ)).re := by
    rw [Filter.EventuallyEq.deriv_eq hzeta_event]
    exact hL1_deriv.deriv
  let f : ℕ → ℝ := fun n => (LSeries.term (LSeries.logMul 1) (s : ℂ) n).re
  have hsum_re_eq :
      ∑' n : ℕ, f n = (LSeries (LSeries.logMul 1) (s : ℂ)).re := by
    exact
      (Complex.hasSum_re (Summable.hasSum (LSeriesSummable_logMul_of_lt_re (f := 1) habs))).tsum_eq
  have hsum_re :
      Summable f := by
    exact
      (Complex.hasSum_re (Summable.hasSum (LSeriesSummable_logMul_of_lt_re (f := 1) habs))).summable
  have htail_eq :
      ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, f n := by
    have htail := hsum_re.sum_add_tsum_nat_add 1
    simpa [f] using htail
  have hterm_re (n : ℕ) :
      (LSeries.term (LSeries.logMul 1) (s : ℂ) (n + 1)).re =
        Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
    have hpow :
        ((((n + 1 : ℕ) : ℂ) ^ (s : ℂ))) = ((((n + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) s).symm
    have hterm :
        LSeries.term (LSeries.logMul 1) (s : ℂ) (n + 1) =
          (((Real.log (n + 1) / ((n + 1 : ℝ) ^ s) : ℝ) : ℂ)) := by
      rw [LSeries.term_of_ne_zero (show n + 1 ≠ 0 by omega), LSeries.logMul, hpow]
      have hlog : Complex.log (((n + 1 : ℕ) : ℂ)) = Real.log (n + 1) := by
        simpa using (Complex.natCast_log (n := n + 1)).symm
      rw [hlog]
      simp
    simpa using congrArg Complex.re hterm
  calc
    -deriv zetaSeries s = (-deriv (LSeries 1) (s : ℂ)).re := by
      rw [hzeta_deriv]
      simp
    _ = (LSeries (LSeries.logMul 1) (s : ℂ)).re := by
      rw [LSeries_deriv habs]
      simp
    _ = ∑' n : ℕ, f n := by
      symm
      exact hsum_re_eq
    _ = ∑' n : ℕ, f (n + 1) := by
      exact htail_eq.symm
    _ = ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
      refine tsum_congr fun n ↦ ?_
      simpa [f] using hterm_re n

noncomputable def logMesh (m : ℕ) : ℝ :=
  Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))

lemma logMesh_nonneg (m : ℕ) : 0 ≤ logMesh m := by
  unfold logMesh
  apply Real.log_nonneg
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  rw [one_le_div hpos]
  norm_num

lemma log_nat_succ_eq_sum_logMesh (n : ℕ) :
    Real.log ((n : ℝ) + 1) = ∑ m ∈ Finset.range n, logMesh m := by
  unfold logMesh
  calc
    Real.log ((n : ℝ) + 1)
        = Real.log ((n : ℝ) + 1) - Real.log 1 := by simp
    _ = ∑ m ∈ Finset.range n,
          (Real.log (((m + 1 : ℕ) : ℝ) + 1) - Real.log ((m : ℝ) + 1)) := by
          simpa using
            (Finset.sum_range_sub
              (fun m : ℕ => Real.log ((m : ℝ) + 1)) n).symm
    _ = ∑ m ∈ Finset.range n,
          Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          have h1 : 0 < (m : ℝ) + 1 := by positivity
          have h2 : 0 < (m : ℝ) + 2 := by positivity
          rw [Real.log_div h2.ne' h1.ne']
          norm_num [Nat.cast_add]
          ring_nf

lemma convexOn_rpow_of_lt_zero {p : ℝ} (hp : p < 0) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) := by
  refine (strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ)) ?_ ?_).convexOn
  · intro x hx
    exact (Real.continuousAt_rpow_const x p (Or.inl hx.ne')).continuousWithinAt
  · intro x hx
    rw [show (deriv^[2] (fun y : ℝ => y ^ p)) x = (deriv^[2] fun y : ℝ => y ^ p) x by rfl]
    rw [Real.iter_deriv_rpow_const p x 2]
    rw [descPochhammer_succ_eval, descPochhammer_succ_eval]
    have hcoeff : 0 < p * (p - 1) := by
      nlinarith
    have hpow : 0 < x ^ (p - 2) := Real.rpow_pos_of_pos hx _
    simpa using mul_pos hcoeff hpow

lemma rpow_neg_le_integral_centered {s : ℝ} (hs : 1 < s) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ (-s)) ≤
      ∫ x in (n : ℝ) - (1 / 2 : ℝ)..(n : ℝ) + (1 / 2 : ℝ), x ^ (-s) := by
  let a : ℝ := (n : ℝ) - (1 / 2 : ℝ)
  let b : ℝ := (n : ℝ) + (1 / 2 : ℝ)
  have hn_half : (1 / 2 : ℝ) < (n : ℝ) := by
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr hn_half
  have hab_lt : a < b := by
    dsimp [a, b]
    linarith
  have hconv :
      ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => x ^ (-s)) := by
    refine ⟨convex_Icc a b, ?_⟩
    intro x hx y hy u v hu hv huv
    exact (convexOn_rpow_of_lt_zero (p := -s) (by linarith)).2
      (lt_of_lt_of_le ha_pos hx.1) (lt_of_lt_of_le ha_pos hy.1) hu hv huv
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-s)) (Set.Icc a b) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    exact (Real.continuousAt_rpow_const x (-s) (Or.inl hx_pos.ne')).continuousWithinAt
  have h0 : MeasureTheory.volume (Set.uIoc a b) ≠ 0 := by
    rw [Set.uIoc_of_le hab, Real.volume_Ioc]
    have hlen : 0 < b - a := sub_pos.mpr hab_lt
    exact (ENNReal.ofReal_pos.mpr hlen).ne'
  have htop : MeasureTheory.volume (Set.uIoc a b) ≠ ⊤ := by
    rw [Set.uIoc_of_le hab, Real.volume_Ioc]
    exact (ENNReal.ofReal_ne_top : ENNReal.ofReal (b - a) ≠ ⊤)
  have huIoc_subset_Icc : Set.uIoc a b ⊆ Set.Icc a b := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    exact Set.mem_Icc_of_Ioc hx
  have hmem :
      ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.uIoc a b), x ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with x hx
    exact huIoc_subset_Icc hx
  have hid_int : MeasureTheory.IntegrableOn (fun x : ℝ => x) (Set.uIoc a b)
      MeasureTheory.volume := by
    exact continuousOn_id.integrableOn_of_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc a b))
      measurableSet_uIoc huIoc_subset_Icc htop
  have hpow_int :
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.uIoc a b) MeasureTheory.volume := by
    exact hcont.integrableOn_of_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc a b))
      measurableSet_uIoc huIoc_subset_Icc htop
  have hJ :
      ((⨍ x in a..b, x) ^ (-s)) ≤ (⨍ x in a..b, x ^ (-s)) := by
    simpa [a, b] using
      (hconv.map_set_average_le hcont isClosed_Icc h0 htop hmem hid_int hpow_int)
  have havg_id : (⨍ x in a..b, x) = (n : ℝ) := by
    rw [interval_average_eq_div, integral_id]
    dsimp [a, b]
    ring_nf
  have havg_pow : (⨍ x in a..b, x ^ (-s)) = ∫ x in a..b, x ^ (-s) := by
    rw [interval_average_eq_div]
    dsimp [a, b]
    ring_nf
  rw [havg_id] at hJ
  rw [havg_pow] at hJ
  simpa [a, b] using hJ

lemma rpow_neg_le_integral_midpoint_unit
    {s : ℝ} (hs : 1 < s) {k : ℕ} (hk : 2 ≤ k) :
    ((k : ℝ) ^ (-s))
      ≤ ∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), x ^ (-s) := by
  have hk1 : 1 ≤ k := by
    omega
  simpa using rpow_neg_le_integral_centered hs hk1

lemma sum_Ico_rpow_neg_le_midpoint_tail
    {s : ℝ} (hs : 1 < s) (m N : ℕ) :
    (∑ k ∈ Finset.Ico (m + 2) N, ((k : ℝ) ^ (-s)))
      ≤
    (1 / (s - 1)) /
      (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
  classical
  let a : ℕ → ℝ := fun k => (k : ℝ) - 1 / 2
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-s)) (Set.Ioi 0) := by
    refine continuousOn_id.rpow_const ?_
    intro x hx
    exact Or.inl (Set.mem_Ioi.mp hx).ne'
  have hinterval (k : ℕ) (hk : 2 ≤ k) :
      IntervalIntegrable (fun x : ℝ => x ^ (-s)) MeasureTheory.volume (a k) (a (k + 1)) := by
    have hpos : 0 < a k := by
      dsimp [a]
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hle : a k ≤ a (k + 1) := by
      dsimp [a]
      norm_num [Nat.cast_add]
    refine (hcont.mono ?_).intervalIntegrable
    intro x hx
    have hx' : x ∈ Set.Icc (a k) (a (k + 1)) := by
      simpa [Set.uIcc_of_le hle] using hx
    exact lt_of_lt_of_le hpos hx'.1
  by_cases hMN : m + 2 ≤ N
  · have hsum_le :
        (∑ k ∈ Finset.Ico (m + 2) N, ((k : ℝ) ^ (-s)))
          ≤
        ∑ k ∈ Finset.Ico (m + 2) N,
          ∫ x in a k..a (k + 1), x ^ (-s) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk2 : 2 ≤ k := le_trans (by omega : 2 ≤ m + 2) (Finset.mem_Ico.mp hk).1
      have ha_succ : a (k + 1) = (k : ℝ) + 1 / 2 := by
        dsimp [a]
        norm_num [Nat.cast_add]
        ring_nf
      rw [ha_succ]
      simpa [a] using rpow_neg_le_integral_midpoint_unit (s := s) hs hk2
    have htail_lt : -s < -1 := by linarith
    have hstart_pos' : 0 < ((m : ℝ) + 3 / 2) := by positivity
    have hstart_pos : 0 < a (m + 2) := by
      rw [show a (m + 2) = (m : ℝ) + 3 / 2 by
        dsimp [a]
        norm_num [Nat.cast_add]
        ring_nf]
      exact hstart_pos'
    have hsum_intervals :
        (∑ k ∈ Finset.Ico (m + 2) N,
          ∫ x in a k..a (k + 1), x ^ (-s))
          =
        ∫ x in a (m + 2)..a N, x ^ (-s) := by
      apply intervalIntegral.sum_integral_adjacent_intervals_Ico hMN
      intro k hk
      exact hinterval k (le_trans (by omega : 2 ≤ m + 2) hk.1)
    have hfinite_le_tail :
        ∫ x in a (m + 2)..a N, x ^ (-s)
          ≤ ∫ x in Set.Ioi (a (m + 2)), x ^ (-s) := by
      have hNpos : 0 < a N := by
        dsimp [a]
        have hN2 : 2 ≤ N := by omega
        have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
        linarith
      have hstart_le : a (m + 2) ≤ a N := by
        dsimp [a]
        exact sub_le_sub_right (by exact_mod_cast hMN) (1 / 2 : ℝ)
      have hint :
          IntervalIntegrable (fun x : ℝ => x ^ (-s)) MeasureTheory.volume (a (m + 2)) (a N) := by
        refine (hcont.mono ?_).intervalIntegrable
        intro x hx
        have hx' : x ∈ Set.Icc (a (m + 2)) (a N) := by
          simpa [Set.uIcc_of_le hstart_le] using hx
        exact lt_of_lt_of_le hstart_pos hx'.1
      have htailN :
          0 ≤ ∫ x in Set.Ioi (a N), x ^ (-s) := by
        rw [integral_Ioi_rpow_of_lt htail_lt hNpos]
        have hs1_pos : 0 < s - 1 := by linarith
        have hs1 : s - 1 ≠ 0 := hs1_pos.ne'
        have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs.ne'.symm
        have hpow_pos : 0 < (a N) ^ (1 - s) := Real.rpow_pos_of_pos hNpos _
        have hnonneg : 0 ≤ (a N) ^ (1 - s) / (s - 1) := by
          exact div_nonneg hpow_pos.le hs1_pos.le
        calc
          0 ≤ (a N) ^ (1 - s) / (s - 1) := hnonneg
          _ = -((a N) ^ (-s + 1)) / (-s + 1) := by
                rw [show -s + 1 = 1 - s by ring]
                field_simp [h1s, hs1]
                ring
      have hdecomp :
          (∫ x in a (m + 2)..a N, x ^ (-s))
            + ∫ x in Set.Ioi (a N), x ^ (-s)
          =
          ∫ x in Set.Ioi (a (m + 2)), x ^ (-s) := by
        exact intervalIntegral.integral_interval_add_Ioi' hint
          (integrableOn_Ioi_rpow_of_lt htail_lt hNpos)
      nlinarith [hdecomp, htailN]
    have htail_eval :
        ∫ x in Set.Ioi (a (m + 2)), x ^ (-s)
          =
        (1 / (s - 1)) /
          (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
      have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
      have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs.ne'.symm
      rw [show a (m + 2) = (m : ℝ) + 3 / 2 by
        dsimp [a]
        norm_num [Nat.cast_add]
        ring_nf]
      rw [integral_Ioi_rpow_of_lt htail_lt hstart_pos']
      calc
        -(((m : ℝ) + 3 / 2) ^ (-s + 1)) / (-s + 1)
            = (((m : ℝ) + 3 / 2) ^ (1 - s)) / (s - 1) := by
                rw [show -s + 1 = 1 - s by ring]
                field_simp [h1s, hs1]
                ring
        _ = (((m : ℝ) + 3 / 2) ^ (-(s - 1))) / (s - 1) := by
              congr 1
              ring_nf
        _ = ((((m : ℝ) + 3 / 2) ^ (s - 1))⁻¹) / (s - 1) := by
              rw [Real.rpow_neg hstart_pos'.le]
        _ = (1 / (s - 1)) / (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
              simp [div_eq_mul_inv, mul_comm]
    calc
      (∑ k ∈ Finset.Ico (m + 2) N, ((k : ℝ) ^ (-s)))
          ≤ ∑ k ∈ Finset.Ico (m + 2) N,
              ∫ x in a k..a (k + 1), x ^ (-s) := hsum_le
      _ = ∫ x in a (m + 2)..a N, x ^ (-s) := hsum_intervals
      _ ≤ ∫ x in Set.Ioi (a (m + 2)), x ^ (-s) := hfinite_le_tail
      _ = (1 / (s - 1)) / (((m : ℝ) + 3 / 2) ^ (s - 1)) := htail_eval
  · have hempty : Finset.Ico (m + 2) N = ∅ := by
      exact Finset.Ico_eq_empty_of_le (by omega)
    have hs1_pos : 0 < s - 1 := by linarith
    have hpow_pos : 0 < (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
      exact Real.rpow_pos_of_pos (by positivity) _
    have hrhs_nonneg : 0 ≤ (1 / (s - 1)) / (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
      exact div_nonneg (one_div_nonneg.mpr hs1_pos.le) hpow_pos.le
    simpa [hempty] using hrhs_nonneg

lemma logMesh_le_inv_succ (m : ℕ) :
    logMesh m ≤ 1 / ((m : ℝ) + 1) := by
  unfold logMesh
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  have hratio_pos : 0 < (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by positivity
  calc
    Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))
        ≤ (((m : ℝ) + 2) / ((m : ℝ) + 1)) - 1 :=
          Real.log_le_sub_one_of_pos hratio_pos
    _ = 1 / ((m : ℝ) + 1) := by field_simp [hpos.ne']; ring

lemma summable_logMesh_div_rpow
    {s : ℝ} (hs : 1 < s) :
    Summable fun m : ℕ =>
      logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
  have hspos : 0 < s - 1 := by linarith
  refine Summable.of_nonneg_of_le
    (fun m => by
      exact div_nonneg (logMesh_nonneg m)
        (le_of_lt (Real.rpow_pos_of_pos (by positivity) _)))
    ?_
    ((Real.summable_one_div_nat_add_rpow 1 s).2 hs)
  intro m
  have hlog := logMesh_le_inv_succ m
  have hbase1 : 0 < (m : ℝ) + 1 := by positivity
  have hbase2 : 0 < (m : ℝ) + 3 / 2 := by positivity
  have hbase_le : (m : ℝ) + 1 ≤ (m : ℝ) + 3 / 2 := by norm_num
  have hpow_le :
      ((m : ℝ) + 1) ^ (s - 1) ≤ ((m : ℝ) + 3 / 2) ^ (s - 1) := by
    exact Real.rpow_le_rpow hbase1.le hbase_le hspos.le
  have hden_pos : 0 < ((m : ℝ) + 3 / 2) ^ (s - 1) :=
    Real.rpow_pos_of_pos hbase2 _
  have hden1_pos : 0 < ((m : ℝ) + 1) ^ (s - 1) :=
    Real.rpow_pos_of_pos hbase1 _
  calc
    logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))
        ≤ (1 / ((m : ℝ) + 1)) /
            (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
          gcongr
    _ ≤ (1 / ((m : ℝ) + 1)) /
            (((m : ℝ) + 1) ^ (s - 1)) := by
          have hnum_nonneg : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
          have hrecip :
              1 / (((m : ℝ) + 3 / 2) ^ (s - 1)) ≤ 1 / (((m : ℝ) + 1) ^ (s - 1)) := by
            exact one_div_le_one_div_of_le hden1_pos hpow_le
          simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrecip hnum_nonneg
    _ = 1 / |(m : ℝ) + 1| ^ s := by
          have habs : |(m : ℝ) + 1| = (m : ℝ) + 1 := abs_of_pos hbase1
          rw [div_eq_mul_inv, one_div, ← Real.rpow_neg_one, ← Real.rpow_neg hbase1.le]
          rw [← Real.rpow_add hbase1]
          have hs_eq : (-1 : ℝ) + -(s - 1) = -s := by ring
          rw [hs_eq]
          simpa [habs, one_div] using (Real.rpow_neg hbase1.le (y := s))

lemma finite_layer_cake_bound
    {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ s))
      ≤
    ∑ m ∈ Finset.range N,
      (1 / (s - 1)) *
        (logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
  have hspos : 0 < s - 1 := by linarith
  have hspow_pos (n : ℕ) : 0 < ((n : ℝ) + 1) ^ s := by
    exact Real.rpow_pos_of_pos (by positivity) _
  calc
    (∑ n ∈ Finset.range N,
      Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ s))
        =
      ∑ n ∈ Finset.range N,
        (∑ m ∈ Finset.range n, logMesh m) / (((n : ℝ) + 1) ^ s) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [← log_nat_succ_eq_sum_logMesh n]
    _ =
      ∑ n ∈ Finset.range N,
        ∑ m ∈ Finset.range n,
          logMesh m * (((n : ℝ) + 1) ^ (-s)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
    _ =
      ∑ m ∈ Finset.range N,
        logMesh m *
          (∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s))) := by
          calc
            ∑ n ∈ Finset.range N,
              ∑ m ∈ Finset.range n, logMesh m * (((n : ℝ) + 1) ^ (-s))
                =
              ∑ m ∈ Finset.range N,
                ∑ n ∈ Finset.Ico (m + 1) N, logMesh m * (((n : ℝ) + 1) ^ (-s)) := by
                  simpa [Nat.Ico_zero_eq_range] using
                    (Finset.sum_Ico_Ico_comm' 0 N
                      (fun m n => logMesh m * (((n : ℝ) + 1) ^ (-s)))).symm
            _ =
              ∑ m ∈ Finset.range N,
                logMesh m *
                  (∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s))) := by
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    have hmN : m < N := Finset.mem_range.mp hm
                    have hshift :
                        (∑ n ∈ Finset.Ico (m + 1) N, (((n : ℝ) + 1) ^ (-s))) =
                          ∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s)) := by
                            rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
                            have hlen : N - (m + 1) = N + 1 - (m + 2) := by
                              omega
                            rw [hlen]
                            refine Finset.sum_congr rfl ?_
                            intro x hx
                            norm_num [Nat.cast_add, add_left_comm, add_comm]
                    calc
                      ∑ n ∈ Finset.Ico (m + 1) N, logMesh m * (((n : ℝ) + 1) ^ (-s))
                          = logMesh m * (∑ n ∈ Finset.Ico (m + 1) N, (((n : ℝ) + 1) ^ (-s))) := by
                              rw [Finset.mul_sum]
                      _ = logMesh m * (∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s))) := by
                              rw [hshift]
    _ ≤
      ∑ m ∈ Finset.range N,
        logMesh m *
          ((1 / (s - 1)) /
            (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          have hA : 0 ≤ logMesh m := logMesh_nonneg m
          gcongr
          exact sum_Ico_rpow_neg_le_midpoint_tail hs m (N + 1)
    _ =
      ∑ m ∈ Finset.range N,
        (1 / (s - 1)) *
          (logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring

lemma tsum_log_nat_succ_div_rpow_le_log_mesh
    {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
      ≤
    (1 / (s - 1)) *
      (∑' m : ℕ,
        Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
          (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
  have hspos : 0 < s - 1 := by linarith
  let f : ℕ → ℝ :=
    fun n => Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ s)
  let g : ℕ → ℝ :=
    fun m => logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    have hlog_arg : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      linarith
    exact div_nonneg
      (Real.log_nonneg hlog_arg)
      (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
  have hg_nonneg : ∀ m, 0 ≤ g m := by
    intro m
    dsimp [g]
    exact div_nonneg
      (logMesh_nonneg m)
      (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
  have hg_summable : Summable g := by
    simpa [g, logMesh] using summable_logMesh_div_rpow hs
  have hpartial :
      ∀ N,
        ∑ n ∈ Finset.range N, f n
          ≤ ∑ m ∈ Finset.range N, (1 / (s - 1)) * g m := by
    intro N
    simpa [f, g, logMesh] using finite_layer_cake_bound hs N
  calc
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
        = ∑' n : ℕ, f n := by simp [f]
    _ ≤ ∑' m : ℕ, (1 / (s - 1)) * g m := by
          refine Real.tsum_le_of_sum_range_le ?_ ?_
          · intro n
            exact hf_nonneg n
          · intro N
            calc
              ∑ n ∈ Finset.range N, f n
                  ≤ ∑ m ∈ Finset.range N, (1 / (s - 1)) * g m :=
                    hpartial N
              _ ≤ ∑' m : ℕ, (1 / (s - 1)) * g m := by
                    have hsg : Summable fun m => (1 / (s - 1)) * g m :=
                      hg_summable.mul_left _
                    refine hsg.sum_le_tsum (Finset.range N) ?_
                    intro m hm
                    exact mul_nonneg (by positivity) (hg_nonneg m)
    _ =
      (1 / (s - 1)) * (∑' m : ℕ, g m) := by
          rw [tsum_mul_left]
    _ =
      (1 / (s - 1)) *
        (∑' m : ℕ,
          Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
            (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
          simp [g, logMesh]

lemma tsum_log_mesh_le_one_div_sub
    {s : ℝ} (hs : 1 < s) :
    (∑' m : ℕ,
        Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
          (((m : ℝ) + 3 / 2) ^ (s - 1)))
      ≤ 1 / (s - 1) := by
        sorry
lemma one_div_sub_mul_one_div_sub_eq_one_div_sq
    {s : ℝ} (hs : 1 < s) :
    (1 / (s - 1)) * (1 / (s - 1)) = 1 / (s - 1) ^ 2 := by
  have hne : s - 1 ≠ 0 := by linarith
  field_simp [hne]

lemma tsum_log_nat_succ_div_rpow_le_one_div_sq_sub {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
      ≤ 1 / (s - 1) ^ 2 := by
  have h₁ := tsum_log_nat_succ_div_rpow_le_log_mesh (s := s) hs
  have h₂ := tsum_log_mesh_le_one_div_sub (s := s) hs
  have hpos : 0 ≤ 1 / (s - 1) := by
    have hs_sub_pos : 0 < s - 1 := by
      linarith
    exact le_of_lt (one_div_pos.mpr hs_sub_pos)
  calc
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
        ≤ (1 / (s - 1)) *
            (∑' m : ℕ,
              Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
                (((m : ℝ) + 3 / 2) ^ (s - 1))) := h₁
    _ ≤ (1 / (s - 1)) * (1 / (s - 1)) :=
        mul_le_mul_of_nonneg_left h₂ hpos
    _ = 1 / (s - 1) ^ 2 :=
        one_div_sub_mul_one_div_sub_eq_one_div_sq (s := s) hs

lemma neg_deriv_zetaSeries_le_one_div_sq_sub {s : ℝ} (hs : 1 < s) :
    -deriv zetaSeries s ≤ 1 / (s - 1) ^ 2 := by
  rw [neg_deriv_zetaSeries_eq_tsum_log_nat_succ_div_rpow hs]
  exact tsum_log_nat_succ_div_rpow_le_one_div_sq_sub hs

lemma zetaSeries_ge_one_div_sub_add_one_half {s : ℝ} (hs : 1 < s) :
    zetaSeries s ≥ 1 / (s - 1) + (1 / 2 : ℝ) := by
      sorry
lemma analyticSeries_le_two_div_sq_sub_one {s : ℝ} (hs : 1 < s) :
    analyticSeries s ≤ 2 / (s ^ 2 - 1) := by
  have hs_sub_pos : 0 < s - 1 := by
    linarith
  have hs_sub_ne : s - 1 ≠ 0 := by
    linarith
  have hs_add_ne : s + 1 ≠ 0 := by
    linarith
  have hs_sq_sub_ne : s ^ 2 - 1 ≠ 0 := by
    nlinarith
  have hζ_bound : 1 / (s - 1) + (1 / 2 : ℝ) ≤ zetaSeries s := by
    simpa using zetaSeries_ge_one_div_sub_add_one_half hs
  have hζ_lower : 0 < 1 / (s - 1) + (1 / 2 : ℝ) := by
    have hmain : 0 < 1 / (s - 1 : ℝ) := one_div_pos.mpr hs_sub_pos
    linarith
  have hζ_pos : 0 < zetaSeries s := lt_of_lt_of_le hζ_lower hζ_bound
  rw [analyticSeries_eq_neg_deriv_zetaSeries_div_zetaSeries hs]
  by_cases hnum_nonneg : 0 ≤ -deriv zetaSeries s
  · have hrecip :
        1 / zetaSeries s ≤ 1 / (1 / (s - 1) + (1 / 2 : ℝ)) :=
      one_div_le_one_div_of_le hζ_lower hζ_bound
    have hstep1 :
        (-deriv zetaSeries s) * (1 / zetaSeries s) ≤
          (-deriv zetaSeries s) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hrecip hnum_nonneg
    have hstep2 :
        (-deriv zetaSeries s) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) ≤
          (1 / (s - 1) ^ 2) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := by
      have hrecip_nonneg : 0 ≤ 1 / (1 / (s - 1) + (1 / 2 : ℝ)) := by
        positivity
      exact
        mul_le_mul_of_nonneg_right (neg_deriv_zetaSeries_le_one_div_sq_sub hs)
          hrecip_nonneg
    have hratio :
        (1 / (s - 1) ^ 2) / (1 / (s - 1) + (1 / 2 : ℝ)) = 2 / (s ^ 2 - 1) := by
      field_simp [hs_sub_ne, hs_add_ne, hs_sq_sub_ne]
      ring
    calc
      (-deriv zetaSeries s) / zetaSeries s
          = (-deriv zetaSeries s) * (1 / zetaSeries s) := by
              simp [div_eq_mul_inv]
      _ ≤ (-deriv zetaSeries s) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := hstep1
      _ ≤ (1 / (s - 1) ^ 2) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := hstep2
      _ = (1 / (s - 1) ^ 2) / (1 / (s - 1) + (1 / 2 : ℝ)) := by
            simp [div_eq_mul_inv]
      _ = 2 / (s ^ 2 - 1) := hratio
  · have hnum_nonpos : -deriv zetaSeries s ≤ 0 := le_of_not_ge hnum_nonneg
    have hleft : (-deriv zetaSeries s) / zetaSeries s ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (le_of_lt hζ_pos)
    have hs_sq_sub_pos : 0 < s ^ 2 - 1 := by
      nlinarith
    have hright : 0 ≤ 2 / (s ^ 2 - 1) := by
      exact le_of_lt (div_pos (by positivity) hs_sq_sub_pos)
    exact hleft.trans hright

lemma prime_log_term_le_one_div_add {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (s + 1) := by
  have hs_pos : 0 < s := lt_trans zero_lt_one hs
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hrpow_pos : 0 < Real.rpow (p : ℝ) s := Real.rpow_pos_of_pos hp_pos s
  have h_exp_two : (2 : ℝ) ≤ Real.exp 1 := by
    simpa [one_add_one_eq_two] using Real.add_one_le_exp 1
  have h_log_over_exp : s * Real.log p ≤ Real.rpow (p : ℝ) s / Real.exp 1 := by
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    have h := Real.exp_one_mul_le_exp (x := s * Real.log p)
    simpa [Real.rpow_def_of_pos hp_pos, mul_comm, mul_left_comm, mul_assoc] using h
  have h_main : Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (Real.exp 1 * s) := by
    apply (div_le_iff₀ hrpow_pos).2
    have h' : Real.log p ≤ (Real.rpow (p : ℝ) s / Real.exp 1) / s := by
      apply (le_div_iff₀ hs_pos).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_log_over_exp
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  have h_den : s + 1 ≤ Real.exp 1 * s := by
    calc
      s + 1 ≤ s + s := by linarith
      _ = (2 : ℝ) * s := by ring
      _ ≤ Real.exp 1 * s := by
        gcongr
  exact h_main.trans (one_div_le_one_div_of_le (by positivity) h_den)

lemma two_div_sq_sub_one_add_one_div_add_eq_one_div_sub {s : ℝ} (hs : 1 < s) :
    2 / (s ^ 2 - 1) + 1 / (s + 1) = 1 / (s - 1) := by
  have hs_sub : s - 1 ≠ 0 := by linarith
  have hs_add : s + 1 ≠ 0 := by linarith
  have hfactor : s ^ 2 - 1 = (s - 1) * (s + 1) := by ring
  rw [hfactor]
  field_simp [hs_sub, hs_add]
  ring

lemma analyticSeries_add_log_term_le_of_aux_bounds {s : ℝ} (hs : 1 < s)
    {p : ℕ} (hp : p.Prime) :
    analyticSeries s + Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (s - 1) := by
  calc
    analyticSeries s + Real.log p / Real.rpow (p : ℝ) s
        ≤ 2 / (s ^ 2 - 1) + 1 / (s + 1) := by
          exact add_le_add (analyticSeries_le_two_div_sq_sub_one hs)
            (prime_log_term_le_one_div_add hs hp)
    _ = 1 / (s - 1) := two_div_sq_sub_one_add_one_div_add_eq_one_div_sub hs

theorem analyticSeries_add_log_term_le {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    analyticSeries s + Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (s - 1) :=
  analyticSeries_add_log_term_le_of_aux_bounds hs hp

lemma inflow_modifiedFlow_le_erdosWeight_of_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : IsPrimePow N) :
    inflow modifiedFlow N ≤ erdosWeight N := by
      sorry
lemma inflow_modifiedFlow_le_erdosWeight_of_not_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : ¬ IsPrimePow N) :
    inflow modifiedFlow N ≤ erdosWeight N := by
      sorry
lemma inflow_modifiedFlow_le_erdosWeight {N : ℕ} (hN : 1 < N) :
    inflow modifiedFlow N ≤ erdosWeight N := by
  by_cases hPrimePow : IsPrimePow N
  · exact inflow_modifiedFlow_le_erdosWeight_of_isPrimePow hN hPrimePow
  · exact inflow_modifiedFlow_le_erdosWeight_of_not_isPrimePow hN hPrimePow

theorem outflow_modifiedFlow_ge_inflow_modifiedFlow {N : ℕ} (hN : 1 < N) :
    inflow modifiedFlow N ≤ outflow modifiedFlow N := by
  simpa [outflow_modifiedFlow_eq_erdosWeight hN] using
    (inflow_modifiedFlow_le_erdosWeight (N := N) hN)

theorem modifiedFlow_to_one_pos_iff_prime {N : ℕ} (hN : 1 < N) :
    0 < modifiedFlow N 1 ↔ N.Prime := by
  classical
  constructor
  · intro hpos
    have hpow2 : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k := by
      intro h
      have hbranch : ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x := by
        rcases h with ⟨p, k, hp, hk, hNk⟩
        exact ⟨p, hp, k, hk, hNk⟩
      have hzero : modifiedFlow N 1 = 0 := by
        unfold modifiedFlow
        simp [hbranch]
      simp [hzero] at hpos
    have hpow2' : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ 1 = p ^ (k - 1) := by
      rintro ⟨p, k, hp, hk, hNk, _⟩
      exact hpow2 ⟨p, k, hp, hk, hNk⟩
    have hbase : 0 < baseFlow N 1 := by
      have hbranch : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x := by
        rintro ⟨p, hp, k, hk, hNk⟩
        exact hpow2 ⟨p, k, hp, hk, hNk⟩
      have hbranch' : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x ∧ 1 = p ^ (x - 1) := by
        rintro ⟨p, hp, k, hk, hNk, hk1⟩
        exact hpow2' ⟨p, k, hp, hk, hNk, hk1⟩
      have hmf : modifiedFlow N 1 = baseFlow N 1 := by
        unfold modifiedFlow
        simp [hbranch, hbranch']
      rwa [hmf] at hpos
    have hPrimePow : IsPrimePow N := by
      by_contra hPrimePow
      have hzero : baseFlow N 1 = 0 := by
        simp only [baseFlow, if_pos hN, if_pos (one_dvd N), Nat.div_one, if_neg hPrimePow]
      simp [hzero] at hbase
    obtain ⟨p, k, hp, hk, hkpow⟩ := (isPrimePow_nat_iff N).mp hPrimePow
    have hk_not_ge_two : ¬ 2 ≤ k := by
      intro hk2
      exact hpow2 ⟨p, k, hp, hk2, hkpow.symm⟩
    have hk1 : k = 1 := by
      omega
    have hNp : N = p := by
      simpa [hk1] using hkpow.symm
    simpa [hNp] using hp
  · intro hprime
    have hpow2 : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k := by
      rintro ⟨p, k, hp, hk, hNk⟩
      exact (Nat.Prime.not_prime_pow (x := p) hk) (by simpa [hNk] using hprime)
    have hpow2' : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ 1 = p ^ (k - 1) := by
      rintro ⟨p, k, hp, hk, hNk, _⟩
      exact hpow2 ⟨p, k, hp, hk, hNk⟩
    have hmf : modifiedFlow N 1 = baseFlow N 1 := by
      have hbranch : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x := by
        rintro ⟨p, hp, k, hk, hNk⟩
        exact hpow2 ⟨p, k, hp, hk, hNk⟩
      have hbranch' : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x ∧ 1 = p ^ (x - 1) := by
        rintro ⟨p, hp, k, hk, hNk, hk1⟩
        exact hpow2' ⟨p, k, hp, hk, hNk, hk1⟩
      unfold modifiedFlow
      simp [hbranch, hbranch']
    have hlog : 0 < Real.log N := by
      exact Real.log_pos (Nat.one_lt_cast.2 hN)
    have hden : 0 < (N : ℝ) * (Real.log N) ^ 2 := by
      refine mul_pos ?_ ?_
      · exact Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one hN)
      · exact sq_pos_of_pos hlog
    have hnum : 0 < ArithmeticFunction.vonMangoldt N := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
      exact hlog
    have hbase : 0 < baseFlow N 1 := by
      rw [baseFlow, if_pos hN, if_pos (one_dvd N), Nat.div_one, if_pos hprime.isPrimePow]
      exact div_pos hnum hden
    rwa [hmf]

def primeSet : Set ℕ :=
  { p | p.Prime }

def PrimitiveSet (A : Set ℕ) : Prop :=
  (∀ ⦃a : ℕ⦄, a ∈ A → 2 ≤ a) ∧
    ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a ∣ b → a = b

def DivisibilityFlow (W : ℕ → ℕ → ℝ) : Prop :=
  (∀ m n, 0 ≤ W m n) ∧
    ∀ m n, ¬ (n ∣ m ∧ n < m) → W m n = 0

def SatisfiesFlowConjecture (W : ℕ → ℕ → ℝ) : Prop :=
  DivisibilityFlow W ∧
    (∀ r : ℕ, 2 ≤ r → erdosWeight r ≤ outflow W r) ∧
    (∀ p : ℕ, p.Prime → outflow W p = erdosWeight p) ∧
    (∀ r : ℕ, 2 ≤ r → inflow W r ≤ outflow W r) ∧
    (∀ m : ℕ, 2 ≤ m → ¬ m.Prime → W m 1 = 0)

theorem modifiedFlow_satisfies_flow_conjecture :
    SatisfiesFlowConjecture modifiedFlow := by
  classical
  have hbase_nonneg : ∀ m n : ℕ, 0 ≤ baseFlow m n := by
    intro m n
    by_cases hm : 1 < m
    · by_cases hdiv : n ∣ m
      · by_cases hpow : IsPrimePow (m / n)
        · rw [baseFlow, if_pos hm, if_pos hdiv, if_pos hpow]
          have hm0 : 0 < (m : ℝ) := by
            exact_mod_cast (lt_trans Nat.zero_lt_one hm)
          have hlog : 0 < Real.log m := by
            exact Real.log_pos (by exact_mod_cast hm)
          refine div_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
          exact le_of_lt (mul_pos hm0 (sq_pos_of_pos hlog))
        · rw [baseFlow, if_pos hm, if_pos hdiv, if_neg hpow]
      · rw [baseFlow, if_pos hm, if_neg hdiv]
    · rw [baseFlow, if_neg hm]
  have hbase_support : ∀ m n : ℕ, ¬ (n ∣ m ∧ n < m) → baseFlow m n = 0 := by
    intro m n hmn
    unfold baseFlow
    by_cases hm : 1 < m
    · by_cases hdiv : n ∣ m
      · by_cases hpow : IsPrimePow (m / n)
        · exfalso
          apply hmn
          refine ⟨hdiv, ?_⟩
          have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
          have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hdiv hm0
          have hq : 1 < m / n := IsPrimePow.one_lt hpow
          have hlt : n * 1 < n * (m / n) := Nat.mul_lt_mul_of_pos_left hq hn0
          simpa [Nat.mul_div_cancel' hdiv] using hlt
        · simp [hm, hdiv, hpow]
      · simp [hm, hdiv]
    · simp [hm]
  have hmodified_nonneg : ∀ m n : ℕ, 0 ≤ modifiedFlow m n := by
    intro m n
    unfold modifiedFlow
    split_ifs with h1 h2
    · simp
    · exact add_nonneg (hbase_nonneg m n) (hbase_nonneg m 1)
    · exact hbase_nonneg m n
  have hmodified_support : ∀ m n : ℕ, ¬ (n ∣ m ∧ n < m) → modifiedFlow m n = 0 := by
    intro m n hmn
    unfold modifiedFlow
    split_ifs with h1 h2
    · rfl
    · exfalso
      apply hmn
      rcases h2 with ⟨p, k, hp, hk, rfl, rfl⟩
      refine ⟨pow_dvd_pow p (Nat.sub_le _ _), ?_⟩
      have hklt : k - 1 < k := by
        omega
      exact Nat.pow_lt_pow_right hp.one_lt hklt
    · exact hbase_support m n hmn
  have h12 : 1 < 2 := by decide
  refine ⟨⟨hmodified_nonneg, hmodified_support⟩, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have hr' : 1 < r := lt_of_lt_of_le h12 hr
    exact le_of_eq (outflow_modifiedFlow_eq_erdosWeight hr').symm
  · intro p hp
    exact outflow_modifiedFlow_eq_erdosWeight hp.one_lt
  · intro r hr
    exact outflow_modifiedFlow_ge_inflow_modifiedFlow (lt_of_lt_of_le h12 hr)
  · intro m hm hnotprime
    have hm' : 1 < m := lt_of_lt_of_le h12 hm
    have hnotpos : ¬ 0 < modifiedFlow m 1 := by
      intro hpos
      exact hnotprime ((modifiedFlow_to_one_pos_iff_prime hm').1 hpos)
    exact le_antisymm (le_of_not_gt hnotpos) (hmodified_nonneg m 1)

noncomputable def primitiveWeightSum (A : Set ℕ) : ℝ :=
  ∑' a : A, erdosWeight (a : ℕ)

noncomputable def primeWeightSum : ℝ :=
  primitiveWeightSum primeSet

def primitiveDivisorClosure (A : Set ℕ) : Set ℕ :=
  { d | 2 ≤ d ∧ ∃ a ∈ A, d ∣ a }

def boundaryOutPairs (Ω : Set ℕ) : Set (ℕ × ℕ) :=
  { mn | mn.1 ∈ Ω ∧ mn.2 ∉ Ω ∧ mn.2 ∣ mn.1 ∧ mn.2 < mn.1 }

def boundaryInPairs (Ω : Set ℕ) : Set (ℕ × ℕ) :=
  { mn | mn.1 ∉ Ω ∧ mn.2 ∈ Ω ∧ mn.2 ∣ mn.1 ∧ mn.2 < mn.1 }

noncomputable def boundaryOutflow (W : ℕ → ℕ → ℝ) (Ω : Set ℕ) : ℝ :=
  ∑' mn : boundaryOutPairs Ω, W mn.1.1 mn.1.2

noncomputable def boundaryInflow (W : ℕ → ℕ → ℝ) (Ω : Set ℕ) : ℝ :=
  ∑' mn : boundaryInPairs Ω, W mn.1.1 mn.1.2

open Filter Asymptotics MeasureTheory
open scoped Nat.Prime

def shiftedPrimeIndicator (n : ℕ) : ℝ :=
  if (n + 1).Prime then 1 else 0

def shiftedPrimeWeightReal (x : ℝ) : ℝ :=
  (((x + 1) * Real.log (x + 1))⁻¹)

def shiftedPrimeWeightDeriv (x : ℝ) : ℝ :=
  ((((x + 1) * Real.log (x + 1)) ^ 2)⁻¹ * (-1 - Real.log (x + 1)))

def shiftedPrimeWeightBound (t : ℝ) : ℝ :=
  1 / ((t + 1) * Real.log (t + 1) ^ 2)

lemma sum_shiftedPrimeIndicator_le_primeCounting (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖ ≤ (π (n + 1) : ℝ) := by
  classical
  let s : Finset ℕ := (Finset.Icc 1 n).filter fun k => (k + 1).Prime
  have hs' : ∀ k : ℕ, ‖shiftedPrimeIndicator k‖ = if (k + 1).Prime then (1 : ℝ) else 0 := by
    intro k
    by_cases hk : (k + 1).Prime <;> simp [shiftedPrimeIndicator, hk]
  have hs : ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖ = (s.card : ℝ) := by
    rw [show (fun k : ℕ => ‖shiftedPrimeIndicator k‖) =
      fun k => if (k + 1).Prime then (1 : ℝ) else 0 from funext hs']
    simp [s]
  have hsub : s.image (fun k => k + 1) ⊆ (n + 2).primesBelow := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
    have hk_mem : k ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hk).1
    have hkprime : (k + 1).Prime := (Finset.mem_filter.mp hk).2
    rw [Nat.mem_primesBelow]
    constructor
    · have hk_le : k ≤ n := (Finset.mem_Icc.mp hk_mem).2
      omega
    · exact hkprime
  have hcard_nat : s.card ≤ ((n + 2).primesBelow).card := by
    calc
      s.card = (s.image (fun k => k + 1)).card := by
        symm
        exact Finset.card_image_of_injective s (fun a b h => Nat.succ.inj (by simpa using h))
      _ ≤ ((n + 2).primesBelow).card := Finset.card_le_card hsub
  calc
    ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖ = (s.card : ℝ) := hs
    _ ≤ (((n + 2).primesBelow).card : ℝ) := by exact_mod_cast hcard_nat
    _ = (π (n + 1) : ℝ) := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      norm_num [Nat.primeCounting]

lemma hasDerivAt_norm_shiftedPrimeWeight {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (fun t => ‖shiftedPrimeWeightReal t‖) (shiftedPrimeWeightDeriv x) x := by
      sorry
lemma locallyIntegrable_deriv_norm_shiftedPrimeWeight :
    LocallyIntegrableOn (deriv (fun t => ‖shiftedPrimeWeightReal t‖)) (Set.Ici 1) := by
      sorry
lemma summable_shiftedPrimeWeights_indicator :
    Summable (fun n : ℕ => if (n + 1).Prime then erdosWeight (n + 1) else 0) := by
      sorry
def shiftedPrimeEquiv : {n : ℕ // (n + 1).Prime} ≃ {p : ℕ // p.Prime} where
  toFun n := ⟨n.1 + 1, n.2⟩
  invFun p := ⟨p.1 - 1, by
    simpa [Nat.sub_add_cancel p.2.one_le] using p.2⟩
  left_inv n := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    simpa using Nat.succ_pred_eq_of_pos p.2.pos

lemma summable_primeWeights :
    Summable (fun p : {p : ℕ // p.Prime} => erdosWeight p.1) := by
  have hsub : Summable (fun n : {n : ℕ // (n + 1).Prime} => erdosWeight (n.1 + 1)) := by
    let F : ℕ → ℝ := fun n => if (n + 1).Prime then erdosWeight (n + 1) else 0
    have hF : Summable F := by
      simpa [F] using summable_shiftedPrimeWeights_indicator
    have hzero : ∀ n ∉ Set.range ((↑) : {n : ℕ // (n + 1).Prime} → ℕ), F n = 0 := by
      intro n hn
      have hnotprime : ¬ (n + 1).Prime := by
        intro hprime
        apply hn
        exact ⟨⟨n, hprime⟩, rfl⟩
      simp [F, hnotprime]
    have hcomp : (fun n : {n : ℕ // (n + 1).Prime} => F n) = fun n => erdosWeight (n.1 + 1) := by
      funext n
      simp [F, n.2]
    rw [← hcomp]
    exact ((Function.Injective.summable_iff
      (f := F) (g := ((↑) : {n : ℕ // (n + 1).Prime} → ℕ)) Subtype.val_injective hzero).2 hF)
  exact (Equiv.summable_iff shiftedPrimeEquiv).1 hsub

lemma primitiveDivisorClosure_spec_of_finite {A : Set ℕ} (hA : PrimitiveSet A)
    (hfin : A.Finite) :
    (primitiveDivisorClosure A).Finite ∧
      A ⊆ primitiveDivisorClosure A ∧
      ∀ {d e : ℕ}, d ∈ primitiveDivisorClosure A → 2 ≤ e → e ∣ d →
        e ∈ primitiveDivisorClosure A := by
  have hclosure_subset :
      primitiveDivisorClosure A ⊆ ⋃ a ∈ A, ((Nat.divisors a : Finset ℕ) : Set ℕ) := by
    intro d hd
    rcases (show 2 ≤ d ∧ ∃ a ∈ A, d ∣ a by simpa [primitiveDivisorClosure] using hd) with
      ⟨_, a, ha, hda⟩
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    refine Set.mem_iUnion.2 ⟨ha, ?_⟩
    have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le (by decide) (hA.1 ha))
    exact Nat.mem_divisors.mpr ⟨hda, ha0⟩
  have hclosure_fin :
      (primitiveDivisorClosure A).Finite := by
    refine (hfin.biUnion ?_).subset hclosure_subset
    intro a ha
    exact Finset.finite_toSet (Nat.divisors a)
  have hA_subset : A ⊆ primitiveDivisorClosure A := by
    intro a ha
    exact show a ∈ primitiveDivisorClosure A by
      simpa [primitiveDivisorClosure] using ⟨hA.1 ha, a, ha, dvd_rfl⟩
  refine ⟨hclosure_fin, hA_subset, ?_⟩
  intro d e hd he hed
  rcases (show 2 ≤ d ∧ ∃ a ∈ A, d ∣ a by simpa [primitiveDivisorClosure] using hd) with
    ⟨_, a, ha, hda⟩
  exact show e ∈ primitiveDivisorClosure A by
    simpa [primitiveDivisorClosure] using ⟨he, a, ha, dvd_trans hed hda⟩

lemma modifiedFlow_nonneg (m n : ℕ) : 0 ≤ modifiedFlow m n :=
  (modifiedFlow_satisfies_flow_conjecture.1.1) m n

lemma modifiedFlow_eq_zero_of_not_dvd_lt {m n : ℕ}
    (h : ¬ (n ∣ m ∧ n < m)) : modifiedFlow m n = 0 :=
  (modifiedFlow_satisfies_flow_conjecture.1.2) m n h

lemma summable_modifiedFlow_row (m : ℕ) :
    Summable (fun n : ℕ => modifiedFlow m n) := by
  classical
  refine summable_of_ne_finset_zero (s := m.divisors) ?_
  intro n hn
  apply modifiedFlow_eq_zero_of_not_dvd_lt
  intro h
  have hm0 : m ≠ 0 := by omega
  exact hn (Nat.mem_divisors.mpr ⟨h.1, hm0⟩)

lemma outflow_modifiedFlow_eq_sum_finset_add_compl (s : Finset ℕ) (m : ℕ) :
    outflow modifiedFlow m =
      (∑ n ∈ s, modifiedFlow m n) +
        ∑' n : { n // n ∉ s }, modifiedFlow m n := by
  simpa [outflow] using ((summable_modifiedFlow_row m).sum_add_tsum_subtype_compl s).symm


lemma summable_shift_rpow_neg_two : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-2 : ℝ)) := by
  have hpow : Summable (fun j : ℕ => (j : ℝ) ^ (-2 : ℝ)) := by
    exact (Real.summable_nat_rpow).2 (by norm_num)
  have hshift : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) :=
    (summable_nat_add_iff 1).2 hpow
  simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using hshift

lemma baseFlow_nonneg (m n : ℕ) : 0 ≤ baseFlow m n := by
  by_cases hm : 1 < m
  · by_cases hdiv : n ∣ m
    · by_cases hpow : IsPrimePow (m / n)
      · rw [baseFlow, if_pos hm, if_pos hdiv, if_pos hpow]
        refine div_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
        have hm0 : 0 < (m : ℝ) := by
          exact_mod_cast (lt_trans Nat.zero_lt_one hm)
        have hlog : 0 < Real.log m := by
          exact Real.log_pos (by exact_mod_cast hm)
        exact le_of_lt (mul_pos hm0 (sq_pos_of_pos hlog))
      · rw [baseFlow, if_pos hm, if_pos hdiv, if_neg hpow]
    · rw [baseFlow, if_pos hm, if_neg hdiv]
  · rw [baseFlow, if_neg hm]

lemma baseFlow_mul_primepow_eq {N p j : ℕ} (hN : 0 < N) (hp : p.Prime) :
    baseFlow (N * p ^ (j + 1)) N =
      Real.log p /
        ((((N * p ^ (j + 1) : ℕ) : ℝ)) * (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2)) := by
  have hpow_gt1 : 1 < p ^ (j + 1) := by
    exact one_lt_pow' hp.one_lt (by omega)
  have hNp : 1 < N * p ^ (j + 1) := by
    have hNge1 : 1 ≤ N := Nat.succ_le_of_lt hN
    have hmul : N < N * p ^ (j + 1) := by
      simpa using (Nat.mul_lt_mul_of_pos_left hpow_gt1 hN)
    exact lt_of_le_of_lt hNge1 hmul
  have hdvd : N ∣ N * p ^ (j + 1) := ⟨p ^ (j + 1), by simp⟩
  have hpp : IsPrimePow (p ^ (j + 1)) := by
    exact (isPrimePow_pow_iff (by omega)).2 hp.isPrimePow
  rw [baseFlow, if_pos hNp, if_pos hdvd, Nat.mul_div_right _ hN, if_pos hpp]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma baseFlow_mul_primepow_le {N p j : ℕ} (hN : 0 < N) (hp : p.Prime) :
    baseFlow (N * p ^ (j + 1)) N ≤
      (1 / (N : ℝ)) * erdosWeight p * (((j : ℝ) + 1) ^ (-2 : ℝ)) := by
  rw [baseFlow_mul_primepow_eq hN hp]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog_ge : (((j : ℝ) + 1) * Real.log p) ≤ Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) := by
    have hlogN_nonneg : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hpow0 : (((p ^ (j + 1) : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast (pow_pos hp.pos _).ne'
    have hlogmul := Real.log_mul hN0 hpow0
    have hlogpow : Real.log (((p ^ (j + 1) : ℕ) : ℝ)) = (((j : ℝ) + 1) * Real.log p) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, Real.log_rpow]
      · norm_num
      · exact_mod_cast hp.pos
    rw [show Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) =
        Real.log N + Real.log (((p ^ (j + 1) : ℕ) : ℝ)) by
      simpa [Nat.cast_mul] using hlogmul]
    rw [hlogpow]
    linarith
  have hlog_nonneg : 0 ≤ (((j : ℝ) + 1) * Real.log p) := by positivity
  have hsq_le : ((((j : ℝ) + 1) * Real.log p) ^ 2) ≤
      (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2) := by
    nlinarith
  have hA : (N : ℝ) * p ≤ (((N * p ^ (j + 1) : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.mul_le_mul_left N (Nat.le_self_pow (by omega) p))
  have hsq_nonneg : 0 ≤ ((((j : ℝ) + 1) * Real.log p) ^ 2) := by positivity
  have hB_nonneg : 0 ≤ ((((N * p ^ (j + 1) : ℕ) : ℝ))) := by positivity
  have hden_le :
      ((N : ℝ) * p) * ((((j : ℝ) + 1) * Real.log p) ^ 2) ≤
        (((N * p ^ (j + 1) : ℕ) : ℝ)) *
          (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2) := by
    exact mul_le_mul hA hsq_le hsq_nonneg hB_nonneg
  have hlogp_nonneg : 0 ≤ Real.log p := hlogp_pos.le
  have hden_pos : 0 < ((N : ℝ) * p) * ((((j : ℝ) + 1) * Real.log p) ^ 2) := by
    positivity
  calc
    Real.log p /
        ((((N * p ^ (j + 1) : ℕ) : ℝ)) * (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2))
        ≤ Real.log p / (((N : ℝ) * p) * ((((j : ℝ) + 1) * Real.log p) ^ 2)) := by
          exact div_le_div_of_nonneg_left hlogp_nonneg hden_pos hden_le
    _ = (1 / (N : ℝ)) * erdosWeight p * (((j : ℝ) + 1) ^ (-2 : ℝ)) := by
          rw [erdosWeight]
          have hsq :
              ((((j : ℝ) + 1) * Real.log p) ^ 2) =
                (((j : ℝ) + 1) ^ 2) * (Real.log p) ^ 2 := by
            ring
          have hrpow :
              (((j : ℝ) + 1) ^ (-2 : ℝ)) = ((((j : ℝ) + 1) ^ 2))⁻¹ := by
            rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity) 2]
            norm_num
          rw [hsq, hrpow]
          field_simp [hN0, hp0, hlogp_pos.ne']

lemma summable_baseFlow_col (N : ℕ) : Summable (fun K : ℕ => baseFlow K N) := by
  classical
  by_cases hN : N = 0
  · refine summable_of_ne_finset_zero (s := ∅) ?_
    intro K hK
    simp [baseFlow, hN]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let e : (Σ p : {p : ℕ // p.Prime}, ℕ) → ℕ := fun a => N * a.1.1 ^ (a.2 + 1)
    have he : Function.Injective e := by
      intro a b hab
      cases a with
      | mk ap aj =>
        cases b with
        | mk bp bj =>
          simp only [e] at hab ⊢
          have hpow : ap.1 ^ (aj + 1) = bp.1 ^ (bj + 1) := by
            exact Nat.eq_of_mul_eq_mul_left hNpos hab
          rcases ap.2.pow_inj' bp.2 (by omega) (by omega) hpow with ⟨hp, hj⟩
          have hapbp : ap = bp := by
            apply Subtype.ext
            simpa using hp
          subst hapbp
          have hajbj : aj = bj := by omega
          subst hajbj
          rfl
    have hzero : ∀ K : ℕ, K ∉ Set.range e → baseFlow K N = 0 := by
      intro K hK
      by_cases hdiv : N ∣ K
      · rcases hdiv with ⟨q, rfl⟩
        by_cases hqpp : IsPrimePow q
        · exfalso
          obtain ⟨p, k, hp, hk, hq⟩ := (isPrimePow_nat_iff q).mp hqpp
          apply hK
          refine ⟨⟨⟨p, hp⟩, k - 1⟩, ?_⟩
          simp [e, hq, show k - 1 + 1 = k by omega]
        · by_cases hNq : 1 < N * q
          · simp [baseFlow, hNq, Nat.mul_div_right q hNpos, hqpp]
          · simp [baseFlow, hNq]
      · simp [baseFlow, hdiv]
    let g : (Σ p : {p : ℕ // p.Prime}, ℕ) → ℝ :=
      fun a => (1 / (N : ℝ)) * erdosWeight a.1.1 * (((a.2 : ℝ) + 1) ^ (-2 : ℝ))
    have hg_nonneg : ∀ a, 0 ≤ g a := by
      intro a
      have hp1 : 1 < a.1.1 := a.1.2.one_lt
      have herdos_nonneg : 0 ≤ erdosWeight a.1.1 := by
        rw [erdosWeight]
        positivity
      have hrpow_nonneg : 0 ≤ (((a.2 : ℝ) + 1) ^ (-2 : ℝ)) := by positivity
      have hNinv_nonneg : 0 ≤ (1 / (N : ℝ)) := by positivity
      exact mul_nonneg (mul_nonneg hNinv_nonneg herdos_nonneg) hrpow_nonneg
    have hinner : ∀ p : {p : ℕ // p.Prime}, Summable (fun j : ℕ => g ⟨p, j⟩) := by
      intro p
      have hs : Summable (fun j : ℕ => (((j : ℝ) + 1) ^ (-2 : ℝ))) := summable_shift_rpow_neg_two
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using
        (Summable.mul_left ((1 / (N : ℝ)) * erdosWeight p.1) hs)
    have houter : Summable (fun p : {p : ℕ // p.Prime} => ∑' j : ℕ, g ⟨p, j⟩) := by
      let C : ℝ := ∑' j : ℕ, (((j : ℝ) + 1) ^ (-2 : ℝ))
      have hC : Summable (fun p : {p : ℕ // p.Prime} => ((1 / (N : ℝ)) * C) * erdosWeight p.1) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Summable.mul_left (((1 / (N : ℝ)) * C)) summable_primeWeights)
      refine hC.congr ?_
      intro p
      have htsum :
          (∑' j : ℕ, g ⟨p, j⟩) = ((1 / (N : ℝ)) * erdosWeight p.1) * C := by
        simpa [g, C, mul_assoc, mul_left_comm, mul_comm] using
          (summable_shift_rpow_neg_two.tsum_mul_left (((1 / (N : ℝ)) * erdosWeight p.1)))
      rw [htsum]
      ring
    have hg : Summable g := (summable_sigma_of_nonneg hg_nonneg).2 ⟨hinner, houter⟩
    have hbase_on_range : ∀ a, baseFlow (e a) N ≤ g a := by
      intro a
      simpa [e, g] using baseFlow_mul_primepow_le hNpos a.1.2
    have hbase_range_summable :
        Summable (fun a : (Σ p : {p : ℕ // p.Prime}, ℕ) => baseFlow (e a) N) := by
      exact Summable.of_nonneg_of_le
        (fun a => baseFlow_nonneg (e a) N)
        hbase_on_range hg
    exact
      (Function.Injective.summable_iff (f := fun K => baseFlow K N) (g := e) he hzero).1
        hbase_range_summable

lemma modifiedFlow_le_baseFlow_add_baseFlow_one (m n : ℕ) :
    modifiedFlow m n ≤ baseFlow m n + baseFlow m 1 := by
  rw [modifiedFlow]
  split_ifs <;> nlinarith [baseFlow_nonneg m n, baseFlow_nonneg m 1]

lemma summable_modifiedFlow_col (N : ℕ) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
  have hsum : Summable (fun K : ℕ => baseFlow K N + baseFlow K 1) :=
    (summable_baseFlow_col N).add (summable_baseFlow_col 1)
  exact Summable.of_nonneg_of_le
    (fun K => modifiedFlow_nonneg K N)
    (fun K => modifiedFlow_le_baseFlow_add_baseFlow_one K N)
    hsum

lemma inflow_modifiedFlow_eq_sum_finset_add_compl (s : Finset ℕ) (n : ℕ) :
    inflow modifiedFlow n =
      (∑ m ∈ s, modifiedFlow m n) +
        ∑' m : { m // m ∉ s }, modifiedFlow m n := by
  simpa [inflow] using ((summable_modifiedFlow_col n).sum_add_tsum_subtype_compl s).symm

lemma boundaryOutflow_eq_sum_compl (s : Finset ℕ) :
    boundaryOutflow modifiedFlow (↑s : Set ℕ) =
      ∑ r ∈ s, ∑' n : { n // n ∉ s }, modifiedFlow r n := by
        sorry
lemma boundaryInflow_eq_sum_compl (s : Finset ℕ) :
    boundaryInflow modifiedFlow (↑s : Set ℕ) =
      ∑ n ∈ s, ∑' m : { m // m ∉ s }, modifiedFlow m n := by
        sorry
lemma tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow {Ω : Set ℕ}
    (hΩfin : Ω.Finite) :
    (∑' r : Ω, (outflow modifiedFlow (r : ℕ) - inflow modifiedFlow (r : ℕ))) =
      boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := by
  classical
  let s : Finset ℕ := hΩfin.toFinset
  have hsΩ : (↑s : Set ℕ) = Ω := hΩfin.coe_toFinset
  rw [← hsΩ]
  have hout :
      ∑ r ∈ s, outflow modifiedFlow r =
        (∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n := by
    calc
      ∑ r ∈ s, outflow modifiedFlow r
        = ∑ r ∈ s, ((∑ n ∈ s, modifiedFlow r n) +
            ∑' n : {n // n ∉ s}, modifiedFlow r n) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [outflow_modifiedFlow_eq_sum_finset_add_compl s r]
      _ = (∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n) +
            ∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n := by
              rw [Finset.sum_add_distrib]
  have hin :
      ∑ r ∈ s, inflow modifiedFlow r =
        (∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r := by
    calc
      ∑ r ∈ s, inflow modifiedFlow r
        = ∑ r ∈ s, ((∑ m ∈ s, modifiedFlow m r) +
            ∑' m : {m // m ∉ s}, modifiedFlow m r) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [inflow_modifiedFlow_eq_sum_finset_add_compl s r]
      _ = (∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r) +
            ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r := by
              rw [Finset.sum_add_distrib]
  have hinternal :
      ∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n =
        ∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r := by
    simpa using (Finset.sum_comm (s := s) (t := s) (f := fun r n => modifiedFlow r n))
  calc
    (∑' r : (↑s : Set ℕ), (outflow modifiedFlow (r : ℕ) - inflow modifiedFlow (r : ℕ)))
      = ∑ r ∈ s, (outflow modifiedFlow r - inflow modifiedFlow r) := by
          simpa using
            (Finset.tsum_subtype' s
              (fun r => outflow modifiedFlow r - inflow modifiedFlow r))
    _ = (∑ r ∈ s, outflow modifiedFlow r) - ∑ r ∈ s, inflow modifiedFlow r := by
          rw [Finset.sum_sub_distrib]
    _ =
        ((∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n) -
        ((∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r) := by
            rw [hout, hin]
    _ = (∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n) -
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r := by
            rw [hinternal]
            ring
    _ = boundaryOutflow modifiedFlow (↑s : Set ℕ) -
          boundaryInflow modifiedFlow (↑s : Set ℕ) := by
            rw [boundaryOutflow_eq_sum_compl, boundaryInflow_eq_sum_compl]

lemma boundaryOutflow_le_primeWeightSum_of_downwardClosed {Ω : Set ℕ}
    (hΩ_ge_two : ∀ {d : ℕ}, d ∈ Ω → 2 ≤ d)
    (hΩdown : ∀ {d e : ℕ}, d ∈ Ω → 2 ≤ e → e ∣ d → e ∈ Ω) :
    boundaryOutflow modifiedFlow Ω ≤ primeWeightSum := by
  classical
  rcases modifiedFlow_satisfies_flow_conjecture with
    ⟨⟨_, hmodified_support⟩, _, hprime_outflow, _, hcomposite_to_one⟩
  have hone_not_mem : 1 ∉ Ω := by
    intro h1
    have h := hΩ_ge_two h1
    omega
  have hboundary_target_eq_one : ∀ mn : boundaryOutPairs Ω, mn.1.2 = 1 := by
    intro mn
    rcases mn with ⟨⟨m, n⟩, hmn⟩
    rcases hmn with ⟨hmΩ, hnΩ, hdiv, _⟩
    have hm2 : 2 ≤ m := hΩ_ge_two hmΩ
    have hmpos : 0 < m := by omega
    have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hdiv hmpos
    have hnle : n ≤ 1 := by
      by_contra hgt
      have hn2 : 2 ≤ n := by omega
      exact hnΩ (hΩdown hmΩ hn2 hdiv)
    have hpred : n.pred = 0 := by
      rw [Nat.pred_eq_sub_one, Nat.sub_eq_zero_of_le hnle]
    have hsucc : n.pred.succ = n := Nat.succ_pred_eq_of_pos hnpos
    rw [hpred] at hsucc
    simpa using hsucc.symm
  let eBoundaryFun : boundaryOutPairs Ω → Ω := fun mn => ⟨mn.1.1, mn.2.1⟩
  have heBoundary_bij : Function.Bijective eBoundaryFun := by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Prod.ext
      · simpa [eBoundaryFun] using congrArg Subtype.val h
      · simp [hboundary_target_eq_one a, hboundary_target_eq_one b]
    · intro m
      refine ⟨⟨(m.1, 1), ?_⟩, ?_⟩
      · refine ⟨m.2, hone_not_mem, one_dvd _, ?_⟩
        have hm2 : 2 ≤ m.1 := hΩ_ge_two m.2
        exact lt_of_lt_of_le Nat.one_lt_two hm2
      · rfl
  let eBoundary : boundaryOutPairs Ω ≃ Ω := Equiv.ofBijective eBoundaryFun heBoundary_bij
  have hprime_at_one : ∀ {p : ℕ}, p.Prime → modifiedFlow p 1 = erdosWeight p := by
    intro p hp
    have hout : outflow modifiedFlow p = modifiedFlow p 1 := by
      unfold outflow
      rw [tsum_eq_single 1]
      intro n hn
      apply hmodified_support p n
      intro h
      rcases h with ⟨hdiv, hlt⟩
      rcases (Nat.dvd_prime hp).1 hdiv with h1 | hp'
      · exact hn h1
      · subst hp'
        exact (lt_irrefl _ hlt).elim
    calc
      modifiedFlow p 1 = outflow modifiedFlow p := hout.symm
      _ = erdosWeight p := hprime_outflow p hp
  have hpointwise : ∀ m : Ω, modifiedFlow m.1 1 = if m.1.Prime then erdosWeight m.1 else 0 := by
    intro m
    by_cases hm : m.1.Prime
    · simp [hm, hprime_at_one hm]
    · have hm2 : 2 ≤ m.1 := hΩ_ge_two m.2
      simp [hm, hcomposite_to_one m.1 hm2 hm]
  let SΩ : Set {p : ℕ // p.Prime} := { p | p.1 ∈ Ω }
  let ePrimeΩFun : {m : Ω // m.1.Prime} → SΩ := fun m => ⟨⟨m.1.1, m.2⟩, m.1.2⟩
  have hePrimeΩ_bij : Function.Bijective ePrimeΩFun := by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      simpa [ePrimeΩFun] using congrArg (fun q : SΩ => q.1.1) h
    · intro p
      refine ⟨⟨⟨p.1.1, p.2⟩, p.1.2⟩, ?_⟩
      rfl
  let ePrimeΩ : {m : Ω // m.1.Prime} ≃ SΩ := Equiv.ofBijective ePrimeΩFun hePrimeΩ_bij
  have hboundary_eq :
      boundaryOutflow modifiedFlow Ω = ∑' q : SΩ, erdosWeight q.1.1 := by
    unfold boundaryOutflow
    calc
      ∑' mn : boundaryOutPairs Ω, modifiedFlow mn.1.1 mn.1.2
          = ∑' mn : boundaryOutPairs Ω, modifiedFlow mn.1.1 1 := by
              apply tsum_congr
              intro mn
              simp [hboundary_target_eq_one mn]
      _ = ∑' m : Ω, modifiedFlow m.1 1 := by
            simpa [eBoundary] using (Equiv.tsum_eq eBoundary (fun m : Ω => modifiedFlow m.1 1))
      _ = ∑' m : Ω, if m.1.Prime then erdosWeight m.1 else 0 := by
            apply tsum_congr
            intro m
            exact hpointwise m
      _ = ∑' p : {m : Ω // m.1.Prime}, erdosWeight p.1.1 := by
            symm
            simpa [Set.indicator, Set.mem_setOf_eq] using
              (tsum_subtype {m : Ω | m.1.Prime} (fun m : Ω => erdosWeight m.1))
      _ = ∑' q : SΩ, erdosWeight q.1.1 := by
            simpa [ePrimeΩ] using (Equiv.tsum_eq ePrimeΩ (fun q : SΩ => erdosWeight q.1.1))
  have hnonneg_prime : ∀ p : {p : ℕ // p.Prime}, 0 ≤ erdosWeight p.1 := by
    intro p
    have hp1 : 1 < (p : ℕ) := p.2.one_lt
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (Nat.one_lt_cast.2 hp1)
    have hden : 0 ≤ ((p : ℝ) * Real.log p) := by positivity
    simpa [erdosWeight] using one_div_nonneg.mpr hden
  calc
    boundaryOutflow modifiedFlow Ω = ∑' q : SΩ, erdosWeight q.1.1 := hboundary_eq
    _ ≤ ∑' p : {p : ℕ // p.Prime}, erdosWeight p.1 := by
          exact Summable.tsum_subtype_le (fun p : {p : ℕ // p.Prime} => erdosWeight p.1)
            SΩ hnonneg_prime summable_primeWeights
    _ = primeWeightSum := rfl
lemma boundaryOutflow_ge_boundaryInflow_add_tsum_divergence_of_subset
    {A Ω : Set ℕ} (hΩfin : Ω.Finite)
    (hΩ_ge_two : ∀ {r : ℕ}, r ∈ Ω → 2 ≤ r) (hAΩ : A ⊆ Ω) :
    boundaryInflow modifiedFlow Ω +
      (∑' a : A, (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ))) ≤
        boundaryOutflow modifiedFlow Ω := by
  classical
  let f : ℕ → ℝ := fun r => outflow modifiedFlow r - inflow modifiedFlow r
  have htwo : 1 < 2 := by decide
  have hnonneg : ∀ r ∈ Ω, 0 ≤ f r := by
    intro r hr
    exact sub_nonneg.mpr <|
      outflow_modifiedFlow_ge_inflow_modifiedFlow
        (lt_of_lt_of_le htwo (hΩ_ge_two hr))
  have hAfin : A.Finite := hΩfin.subset hAΩ
  letI := hΩfin.fintype
  letI := hAfin.fintype
  let e : A ≃ {r : Ω // (r : ℕ) ∈ A} :=
    { toFun := fun a => ⟨⟨a.1, hAΩ a.2⟩, a.2⟩
      invFun := fun r => ⟨r.1.1, r.2⟩
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hAeq :
      (∑' a : A, f (a : ℕ)) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype]
    exact Fintype.sum_equiv e (fun a : A => f (a : ℕ))
      (fun r : {s : Ω // (s : ℕ) ∈ A} => f (r : ℕ)) (by intro a; rfl)
  have hsplit :
      (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
          (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) =
        ∑' r : Ω, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype]
    simpa using
      (Fintype.sum_subtype_add_sum_subtype (fun r : Ω => (r : ℕ) ∈ A)
        (fun r : Ω => f (r : ℕ)))
  have hcompl_nonneg : 0 ≤ ∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ) := by
    rw [tsum_fintype]
    exact Finset.sum_nonneg fun r _ => by
      simpa using hnonneg (r : ℕ) r.1.2
  have hA_le_Ω :
      (∑' a : A, f (a : ℕ)) ≤ ∑' r : Ω, f (r : ℕ) := by
    calc
      ∑' a : A, f (a : ℕ) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := hAeq
      _ ≤ (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
            (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) := by
              linarith
      _ = ∑' r : Ω, f (r : ℕ) := hsplit
  have hΩboundary :
      (∑' r : Ω, f (r : ℕ)) =
        boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := by
    simpa [f] using
      tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow (Ω := Ω) hΩfin
  have hmain :
      (∑' a : A, f (a : ℕ)) ≤
        boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := by
    calc
      ∑' a : A, f (a : ℕ) ≤ ∑' r : Ω, f (r : ℕ) := hA_le_Ω
      _ = boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := hΩboundary
  linarith

lemma flow_into_primitive_member_from_outside_divisorClosure {A : Set ℕ}
    (hA : PrimitiveSet A) {a m : ℕ} (ha : a ∈ A)
    (hflow : modifiedFlow m a ≠ 0) :
    m ∉ primitiveDivisorClosure A := by
  intro hm
  rcases hm with ⟨hm_ge_two, b, hb, hm_dvd_b⟩
  have hdiv_lt : a ∣ m ∧ a < m := by
    by_contra hnot
    exact hflow (modifiedFlow_satisfies_flow_conjecture.1.2 m a hnot)
  have ha_dvd_m : a ∣ m := hdiv_lt.1
  have ha_lt_m : a < m := hdiv_lt.2
  have ha_dvd_b : a ∣ b := dvd_trans ha_dvd_m hm_dvd_b
  have hab_eq : a = b := hA.2 ha hb ha_dvd_b
  have hm_dvd_a : m ∣ a := hab_eq ▸ hm_dvd_b
  have ha_pos : 0 < a := lt_of_lt_of_le Nat.zero_lt_two (hA.1 ha)
  have hm_le_a : m ≤ a := Nat.le_of_dvd ha_pos hm_dvd_a
  exact (not_le_of_gt ha_lt_m) hm_le_a

lemma summable_modifiedFlow_col_of_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : IsPrimePow N) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
      sorry
lemma summable_modifiedFlow_col_of_not_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : ¬ IsPrimePow N) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
      sorry
lemma summable_modifiedFlow_col2 {N : ℕ} (hN : 2 ≤ N) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
  have hN' : 1 < N := lt_of_lt_of_le Nat.one_lt_two hN
  by_cases hPrimePow : IsPrimePow N
  · exact summable_modifiedFlow_col_of_isPrimePow hN' hPrimePow
  · exact summable_modifiedFlow_col_of_not_isPrimePow hN' hPrimePow

lemma primitiveWeightSum_le_primeWeightSum_of_finite {A : Set ℕ}
    (hA : PrimitiveSet A) (hfin : A.Finite) :
    primitiveWeightSum A ≤ primeWeightSum := by
      sorry
lemma primitiveWeightSum_le_primeWeightSum_of_finite_subsets {A : Set ℕ}
    (hfinite :
      ∀ A₀ : Set ℕ, A₀ ⊆ A → A₀.Finite → primitiveWeightSum A₀ ≤ primeWeightSum) :
    primitiveWeightSum A ≤ primeWeightSum := by
  classical
  have htsum : ∑' a : A, erdosWeight (a : ℕ) ≤ primeWeightSum := by
    refine Real.tsum_le_of_sum_le ?_ ?_
    · intro a
      by_cases ha : 1 < (a : ℕ)
      · have hlog : 0 < Real.log (a : ℕ) := Real.log_pos (Nat.one_lt_cast.2 ha)
        have hden : 0 < ((a : ℕ) : ℝ) * Real.log (a : ℕ) := by
          refine mul_pos ?_ hlog
          exact Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one ha)
        simpa [erdosWeight] using one_div_nonneg.mpr hden.le
      · have ha' : (a : ℕ) = 0 ∨ (a : ℕ) = 1 := by omega
        rcases ha' with h0 | h1
        · simp [erdosWeight, h0]
        · simp [erdosWeight, h1]
    · intro u
      let s : Finset ℕ := u.image (fun a : A => (a : ℕ))
      have hs_subset : (↑s : Set ℕ) ⊆ A := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
        exact a.2
      have hs_eq :
          primitiveWeightSum (↑s : Set ℕ) = ∑ n ∈ s, erdosWeight n := by
        simpa [primitiveWeightSum, s] using (Finset.tsum_subtype' s erdosWeight)
      have hu_eq : ∑ n ∈ s, erdosWeight n = ∑ a ∈ u, erdosWeight (a : ℕ) := by
        dsimp [s]
        exact
          Finset.sum_image
            (s := u)
            (g := fun a : A => (a : ℕ))
            (f := erdosWeight)
            Subtype.val_injective.injOn
      calc
        ∑ a ∈ u, erdosWeight (a : ℕ) = primitiveWeightSum (↑s : Set ℕ) := by
          rw [← hu_eq, ← hs_eq]
        _ ≤ primeWeightSum := hfinite (↑s : Set ℕ) hs_subset s.finite_toSet
  simpa [primitiveWeightSum] using htsum

theorem primitiveWeightSum_le_primeWeightSum {A : Set ℕ} (hA : PrimitiveSet A) :
    primitiveWeightSum A ≤ primeWeightSum := by
  refine primitiveWeightSum_le_primeWeightSum_of_finite_subsets ?_
  intro A₀ hA₀ hA₀fin
  have hA₀_primitive : PrimitiveSet A₀ := by
    refine ⟨?_, ?_⟩
    · intro a ha
      exact hA.1 (hA₀ ha)
    · intro a b ha hb hab
      exact hA.2 (hA₀ ha) (hA₀ hb) hab
  exact primitiveWeightSum_le_primeWeightSum_of_finite hA₀_primitive hA₀fin

theorem erdos164 :
    PrimitiveSet primeSet ∧
      primitiveWeightSum primeSet = primeWeightSum ∧
      ∀ A : Set ℕ, PrimitiveSet A → primitiveWeightSum A ≤ primitiveWeightSum primeSet := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro a ha
      have hPrime : a.Prime := by
        simpa [primeSet] using ha
      exact hPrime.two_le
    · intro a b ha hb hab
      have haPrime : a.Prime := by
        simpa [primeSet] using ha
      have hbPrime : b.Prime := by
        simpa [primeSet] using hb
      have ha_ne_one : a ≠ 1 := by
        exact ne_of_gt <| lt_of_lt_of_le (by decide : 1 < 2) haPrime.two_le
      have hEq : b = a := (hbPrime.dvd_iff_eq ha_ne_one).mp hab
      simpa using hEq.symm
  · rfl
  · intro A hA
    simpa [primitiveWeightSum, primeWeightSum, primeSet] using
      primitiveWeightSum_le_primeWeightSum hA

/-- We index from `q ≥ 2`, since
`ArithmeticFunction.vonMangoldt 1 = 0`. -/
noncomputable def series (n : ℕ) : ℝ :=
  ∑' q : { q : ℕ // 2 ≤ q },
    ArithmeticFunction.vonMangoldt q.1 /
      ((q.1 : ℝ) * Real.log ((n * q.1 : ℕ) : ℝ) * Real.log ((2 * n * q.1 : ℕ) : ℝ))

/-- The Mellin kernel suggested by the identity
`1 / (log (nq) * log (2nq))
   = (1 / log 2) * ∫_0^∞ n^{-t} (1 - 2^{-t}) q^{-t} dt`. -/
noncomputable def kernel (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) ^ (-t)) * (1 - (2 : ℝ) ^ (-t)) / Real.log (2 : ℝ)

lemma kernel_nonneg {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    0 ≤ kernel n t := by
  have hn_pos_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hn_factor_nonneg : 0 ≤ (n : ℝ) ^ (-t) := by
    exact (Real.rpow_pos_of_pos hn_pos _).le
  have htwo_lt_one : (2 : ℝ) ^ (-t) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hshift_nonneg : 0 ≤ 1 - (2 : ℝ) ^ (-t) := by
    linarith
  have hnum_nonneg : 0 ≤ ((n : ℝ) ^ (-t)) * (1 - (2 : ℝ) ^ (-t)) := by
    exact mul_nonneg hn_factor_nonneg hshift_nonneg
  exact div_nonneg hnum_nonneg hlog2.le

lemma analyticSeries_nonneg_shift (t : ℝ) :
    0 ≤ analyticSeries (1 + t) := by
  rw [analyticSeries]
  exact tsum_nonneg fun q =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
      le_of_lt <|
        Real.rpow_pos_of_pos (by
          have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
          exact_mod_cast hqnatpos) _

/-- Step 1: rewrite the original series as an integral against
`analyticSeries (1 + t)`. -/
lemma series_eq_integral {n : ℕ} (hn : 1 ≤ n) :
    series n =
      ∫ t in Set.Ioi (0 : ℝ), kernel n t * analyticSeries (1 + t) := by
        sorry
/-- The majorant uses the positive denominator `2^t - 1`. -/
lemma two_rpow_sub_one_pos {t : ℝ} (ht : 0 < t) :
    0 < (2 : ℝ) ^ t - 1 := by
  have hpow_gt_one : 1 < (2 : ℝ) ^ t := Real.one_lt_rpow (by norm_num) ht
  linarith

/-- The key algebraic simplification: once the sharp bound
`analyticSeries (1 + t) ≤ log 2 / (2^t - 1)` is inserted, the kernel collapses
exactly to `(2n)^{-t}`. -/
lemma kernel_mul_bound_eq {n : ℕ} {t : ℝ} (ht : 0 < t) :
    kernel n t * (Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1)) =
      (((2 * n : ℕ) : ℝ) ^ (-t)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hpow_pos : 0 < (2 : ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
  have hpow_ne : (2 : ℝ) ^ t ≠ 0 := hpow_pos.ne'
  have hpow_sub_ne : (2 : ℝ) ^ t - 1 ≠ 0 := (two_rpow_sub_one_pos ht).ne'
  have hratio :
      (1 - (2 : ℝ) ^ (-t)) / ((2 : ℝ) ^ t - 1) = (2 : ℝ) ^ (-t) := by
    rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))]
    field_simp [hpow_ne, hpow_sub_ne]
  calc
    kernel n t * (Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1))
        = (n : ℝ) ^ (-t) * ((1 - (2 : ℝ) ^ (-t)) / ((2 : ℝ) ^ t - 1)) := by
            rw [kernel]
            field_simp [hlog2.ne', hpow_sub_ne]
    _ = (n : ℝ) ^ (-t) * (2 : ℝ) ^ (-t) := by rw [hratio]
    _ = (2 : ℝ) ^ (-t) * (n : ℝ) ^ (-t) := by ring
    _ = (((2 * n : ℕ) : ℝ) ^ (-t)) := by
          symm
          simpa [Nat.cast_mul] using
            (Real.mul_rpow (show 0 ≤ (2 : ℝ) by positivity)
              (show 0 ≤ (n : ℝ) by positivity) (z := -t))

/-- Rewrite `(2n)^{-t}` as an exponential so that the standard integral lemma
applies. -/
lemma two_n_rpow_neg_eq_exp {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    (((2 * n : ℕ) : ℝ) ^ (-t)) =
      Real.exp (-(Real.log ((2 * n : ℕ) : ℝ) * t)) := by
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have htwon_pos : 0 < (((2 * n : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by omega) hn_pos
  rw [show -(Real.log ((2 * n : ℕ) : ℝ) * t) =
      Real.log ((2 * n : ℕ) : ℝ) * (-t) by ring]
  rw [← Real.rpow_def_of_pos htwon_pos (-t)]

/-- The terminal integral in the proof is absolutely integrable on `(0,∞)`. -/
lemma two_n_integrable {n : ℕ} (hn : 1 ≤ n) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => (((2 * n : ℕ) : ℝ) ^ (-t)))
      (Set.Ioi (0 : ℝ)) := by
  have htwon_gt_one : 1 < (2 * n : ℕ) := by
    omega
  have hlog_pos : 0 < Real.log ((2 * n : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast htwon_gt_one)
  convert (exp_neg_integrableOn_Ioi (a := (0 : ℝ)) hlog_pos) using 1
  ext t
  rw [two_n_rpow_neg_eq_exp hn t, neg_mul]

/-- The last line: the integral of `(2n)^{-t}` over `(0,∞)`
is `1 / log (2n)`. -/
lemma integral_two_n_eq {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in Set.Ioi (0 : ℝ), (((2 * n : ℕ) : ℝ) ^ (-t)) =
      1 / Real.log ((2 * n : ℕ) : ℝ) := by
  have htwon_gt_one : 1 < (2 * n : ℕ) := by
    omega
  have hlog_pos : 0 < Real.log ((2 * n : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast htwon_gt_one)
  calc
    ∫ t in Set.Ioi (0 : ℝ), (((2 * n : ℕ) : ℝ) ^ (-t))
        = ∫ t in Set.Ioi (0 : ℝ),
            Real.exp (-(Real.log ((2 * n : ℕ) : ℝ) * t)) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with t
              rw [two_n_rpow_neg_eq_exp hn t]
    _ = (Real.log ((2 * n : ℕ) : ℝ)) ^ (-1 / (1 : ℝ)) *
          Real.Gamma (1 / (1 : ℝ) + 1) := by
            simpa using
              (integral_exp_neg_mul_rpow (p := 1) zero_lt_one hlog_pos)
    _ = 1 / Real.log ((2 * n : ℕ) : ℝ) := by
          have htwo : (1 / (1 : ℝ) + 1) = 2 := by norm_num
          rw [htwo, Real.Gamma_two]
          rw [show (-1 / (1 : ℝ)) = -(1 : ℝ) by norm_num, Real.rpow_neg hlog_pos.le]
          simp [one_div]

noncomputable def etaTerm (m : ℕ) (s : ℝ) : ℝ :=
  1 / Real.rpow ((2 * m + 1 : ℕ) : ℝ) s -
    1 / Real.rpow ((2 * m + 2 : ℕ) : ℝ) s

noncomputable def etaSeries (s : ℝ) : ℝ :=
  ∑' m : ℕ, etaTerm m s

lemma zetaSeries_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt zetaSeries (deriv zetaSeries s) s := by
  have hs' : 1 < (s : ℂ).re := by
    simpa using hs
  have hzeta_complex {x : ℝ} (hx : 1 < x) :
      ((zetaSeries x : ℝ) : ℂ) = LSeries 1 (x : ℂ) := by
    have hx' : 1 < (x : ℂ).re := by
      simpa using hx
    calc
      ((zetaSeries x : ℝ) : ℂ)
          = ∑' n : ℕ, ((1 / Real.rpow (((n + 1 : ℕ) : ℝ)) x : ℝ) : ℂ) := by
              rw [zetaSeries, Complex.ofReal_tsum]
      _ = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) := by
            refine tsum_congr fun n ↦ ?_
            have hpow :
                ((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (↑n + 1 : ℂ) ^ (x : ℂ) := by
              simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) x)
            simpa using congrArg (fun z : ℂ => (1 : ℂ) / z) hpow
      _ = riemannZeta (x : ℂ) := by
            symm
            exact zeta_eq_tsum_one_div_nat_add_one_cpow hx'
      _ = LSeries 1 (x : ℂ) := by
            symm
            exact LSeries_one_eq_riemannZeta hx'
  have hzeta_event :
      zetaSeries =ᶠ[nhds s] fun x : ℝ => (LSeries 1 (x : ℂ)).re := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{x : ℝ | 1 < x},
      (isOpen_lt continuous_const continuous_id).mem_nhds (by simpa using hs), ?_⟩
    intro x hx
    simpa using congrArg Complex.re (hzeta_complex hx)
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  have hL1_deriv :
      HasDerivAt (fun x : ℝ => (LSeries 1 (x : ℂ)).re) (deriv (LSeries 1) (s : ℂ)).re s := by
    simpa [LSeries_deriv habs] using (LSeries_hasDerivAt (f := 1) habs).real_of_complex
  have hzeta_has : HasDerivAt zetaSeries (deriv (LSeries 1) (s : ℂ)).re s := by
    exact hL1_deriv.congr_of_eventuallyEq hzeta_event
  have hzeta_deriv : deriv zetaSeries s = (deriv (LSeries 1) (s : ℂ)).re := by
    rw [Filter.EventuallyEq.deriv_eq hzeta_event]
    exact hL1_deriv.deriv
  simpa [hzeta_deriv] using hzeta_has

lemma zetaSeries_term_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s) := by
  have hs' : 1 < (s : ℂ).re := by
    simpa using hs
  let full : ℕ → ℝ := fun n => if n = 0 then 0 else 1 / Real.rpow ((n : ℝ)) s
  have hLs : LSeriesSummable 1 (s : ℂ) := LSeriesSummable_one_iff.mpr hs'
  have hsum_full : Summable full := by
    simpa [full, LSeries.norm_term_eq, Real.norm_eq_abs] using hLs.norm
  have hfull_zero :
      ∀ n ∉ Set.range (fun m : ℕ => m + 1), full n = 0 := by
    intro n hn
    rcases n with _ | n
    · simp [full]
    · exfalso
      exact hn ⟨n, rfl⟩
  have hsucc_inj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)
  have hsub : Summable (full ∘ fun n : ℕ => n + 1) :=
    (Function.Injective.summable_iff hsucc_inj hfull_zero).2 hsum_full
  refine hsub.congr ?_
  intro n
  simp [full]

lemma etaSeries_eq_factor_mul_zetaSeries {s : ℝ} (hs : 1 < s) :
    etaSeries s = (1 - (2 : ℝ) ^ (1 - s)) * zetaSeries s := by
  let f : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) ^ (-s))
  have hsum : Summable f := by
    refine (zetaSeries_term_summable hs).congr ?_
    intro n
    simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s).symm
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have hodd : Summable (fun n : ℕ => f (2 * n)) :=
    hsum.comp_injective htwo_inj
  have htwo_add_one_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h)
    exact htwo_inj h'
  have heven : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hsum.comp_injective htwo_add_one_inj
  have hdecomp :
      etaSeries s = (∑' n : ℕ, f (2 * n)) - ∑' n : ℕ, f (2 * n + 1) := by
    calc
      etaSeries s = ∑' n : ℕ, (f (2 * n) - f (2 * n + 1)) := by
        rw [etaSeries]
        refine tsum_congr ?_
        intro n
        calc
          etaTerm n s
              = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) := by
                  rw [etaTerm]
                  rw [show 1 / Real.rpow (((2 * n + 1 : ℕ) : ℝ)) s =
                      (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) by
                        symm
                        simpa [one_div] using
                          (Real.rpow_neg (show 0 ≤ (((2 * n + 1 : ℕ) : ℝ)) by positivity) s)]
                  rw [show 1 / Real.rpow (((2 * n + 2 : ℕ) : ℝ)) s =
                      (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) by
                        symm
                        simpa [one_div] using
                          (Real.rpow_neg (show 0 ≤ (((2 * n + 2 : ℕ) : ℝ)) by positivity) s)]
          _ = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 1 + 1 : ℕ) : ℝ) ^ (-s)) := by
                congr 1
          _ = f (2 * n) - f (2 * n + 1) := by
                rfl
      _ = (∑' n : ℕ, f (2 * n)) - ∑' n : ℕ, f (2 * n + 1) := by
        exact (hodd.hasSum.sub heven.hasSum).tsum_eq
  have hsplit :
      (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) = zetaSeries s := by
    calc
      (∑' n : ℕ, f (2 * n)) + ∑' n : ℕ, f (2 * n + 1) = ∑' n : ℕ, f n := by
        exact tsum_even_add_odd hodd heven
      _ = ∑' n : ℕ, 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s := by
        refine tsum_congr ?_
        intro n
        simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s)
      _ = zetaSeries s := by
        simp [zetaSeries]
  have heven_eq :
      (∑' n : ℕ, f (2 * n + 1)) = (2 : ℝ) ^ (-s) * zetaSeries s := by
    have hterm :
        ∀ n : ℕ, f (2 * n + 1) = (2 : ℝ) ^ (-s) * f n := by
      intro n
      have hcast_double : (2 : ℝ) * (n : ℝ) + 1 + 1 = 2 * ((n : ℝ) + 1) := by ring
      calc
        f (2 * n + 1)
            = (((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ (-s)) := by
                simp [f, hcast_double]
        _ = (2 : ℝ) ^ (-s) * (((n + 1 : ℕ) : ℝ) ^ (-s)) := by
              simpa [Nat.cast_mul] using
                (Real.mul_rpow (show 0 ≤ (2 : ℝ) by positivity)
                  (show 0 ≤ (((n + 1 : ℕ) : ℝ)) by positivity) (z := -s))
        _ = (2 : ℝ) ^ (-s) * f n := by simp [f]
    calc
      (∑' n : ℕ, f (2 * n + 1)) = ∑' n : ℕ, (2 : ℝ) ^ (-s) * f n := by
        refine tsum_congr hterm
      _ = (2 : ℝ) ^ (-s) * ∑' n : ℕ, f n := by
        rw [tsum_mul_left]
      _ = (2 : ℝ) ^ (-s) * ∑' n : ℕ, 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s := by
        refine congrArg ((2 : ℝ) ^ (-s) * ·) ?_
        refine tsum_congr ?_
        intro n
        simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s)
      _ = (2 : ℝ) ^ (-s) * zetaSeries s := by
        simp [zetaSeries]
  calc
    etaSeries s = (∑' n : ℕ, f (2 * n)) - ∑' n : ℕ, f (2 * n + 1) := hdecomp
    _ = zetaSeries s - 2 * (∑' n : ℕ, f (2 * n + 1)) := by
          linarith [hsplit]
    _ = zetaSeries s - 2 * ((2 : ℝ) ^ (-s) * zetaSeries s) := by
          rw [heven_eq]
    _ = (1 - (2 : ℝ) ^ (1 - s)) * zetaSeries s := by
          rw [show (2 : ℝ) ^ (1 - s) = 2 * (2 : ℝ) ^ (-s) by
            have htwo_pos : 0 < (2 : ℝ) := by norm_num
            calc
              (2 : ℝ) ^ (1 - s) = (2 : ℝ) ^ (1 + (-s)) := by ring_nf
              _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-s) := by
                    simpa using (Real.rpow_add htwo_pos (1 : ℝ) (-s))
              _ = 2 * (2 : ℝ) ^ (-s) := by simp]
          ring

lemma log_nat_succ_div_rpow_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => Real.log (n + 1) / ((n + 1 : ℝ) ^ s)) := by
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  let f : ℕ → ℝ := fun n => (LSeries.term (LSeries.logMul 1) (s : ℂ) n).re
  have hsum_re : Summable f := by
    exact
      (Complex.hasSum_re (Summable.hasSum (LSeriesSummable_logMul_of_lt_re (f := 1) habs))).summable
  have htail : Summable (fun n : ℕ => f (n + 1)) := by
    exact hsum_re.comp_injective (fun a b h => Nat.succ.inj h)
  have hterm_re (n : ℕ) :
      f (n + 1) = Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
    have hpow :
        ((((n + 1 : ℕ) : ℂ) ^ (s : ℂ))) = ((((n + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) s).symm
    have hterm :
        LSeries.term (LSeries.logMul 1) (s : ℂ) (n + 1) =
          (((Real.log (n + 1) / ((n + 1 : ℝ) ^ s) : ℝ) : ℂ)) := by
      rw [LSeries.term_of_ne_zero (show n + 1 ≠ 0 by omega), LSeries.logMul, hpow]
      have hlog : Complex.log (((n + 1 : ℕ) : ℂ)) = Real.log (n + 1) := by
        simpa using (Complex.natCast_log (n := n + 1)).symm
      rw [hlog]
      simp
    simpa [f] using congrArg Complex.re hterm
  refine htail.congr ?_
  intro n
  exact hterm_re n

noncomputable def etaTermDeriv (m : ℕ) (s : ℝ) : ℝ :=
  Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-s)) -
    Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-s))

lemma etaTerm_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (etaTerm m) (etaTermDeriv m s) s := by
      sorry
lemma etaSeries_summable {s : ℝ} (hs : 1 < s) :
    Summable (fun m : ℕ => etaTerm m s) := by
  let f : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ) ^ (-s))
  have hsum : Summable f := by
    refine (zetaSeries_term_summable hs).congr ?_
    intro n
    simpa [f, one_div] using (Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) s).symm
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have htwo_add_one_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    exact htwo_inj h'
  have hodd : Summable (fun n : ℕ => f (2 * n)) :=
    hsum.comp_injective htwo_inj
  have heven : Summable (fun n : ℕ => f (2 * n + 1)) :=
    hsum.comp_injective htwo_add_one_inj
  have hcongr :
      (fun m : ℕ => etaTerm m s) = fun n : ℕ => f (2 * n) - f (2 * n + 1) := by
    funext n
    calc
      etaTerm n s
          = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) := by
              rw [etaTerm]
              rw [show 1 / Real.rpow (((2 * n + 1 : ℕ) : ℝ)) s =
                  (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) by
                    symm
                    simpa [one_div] using
                      (Real.rpow_neg (show 0 ≤ (((2 * n + 1 : ℕ) : ℝ)) by positivity) s)]
              rw [show 1 / Real.rpow (((2 * n + 2 : ℕ) : ℝ)) s =
                  (((2 * n + 2 : ℕ) : ℝ) ^ (-s)) by
                    symm
                    simpa [one_div] using
                      (Real.rpow_neg (show 0 ≤ (((2 * n + 2 : ℕ) : ℝ)) by positivity) s)]
      _ = (((2 * n + 1 : ℕ) : ℝ) ^ (-s)) - (((2 * n + 1 + 1 : ℕ) : ℝ) ^ (-s)) := by
            congr 1
      _ = f (2 * n) - f (2 * n + 1) := by
            rfl
  rw [hcongr]
  exact (hodd.hasSum.sub heven.hasSum).summable

lemma etaSeries_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt etaSeries (∑' m : ℕ, etaTermDeriv m s) s := by
  let c : ℝ := (1 + s) / 2
  have hc : 1 < c := by
    dsimp [c]
    linarith
  have hs_mem : s ∈ Set.Ioi c := by
    change c < s
    dsimp [c]
    linarith
  let g : ℕ → ℝ := fun n => Real.log (n + 1) * (((n + 1 : ℕ) : ℝ) ^ (-c))
  have hsumg : Summable g := by
    refine (log_nat_succ_div_rpow_summable hc).congr ?_
    intro n
    simpa [g, div_eq_mul_inv] using
      congrArg (fun t : ℝ => Real.log (n + 1) * t)
        ((Real.rpow_neg (show 0 ≤ ((n + 1 : ℕ) : ℝ) by positivity) c).symm)
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have htwo_add_one_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    exact htwo_inj h'
  let u : ℕ → ℝ := fun m => g (2 * m) + g (2 * m + 1)
  have hu : Summable u := by
    dsimp [u]
    exact (hsumg.comp_injective htwo_inj).add (hsumg.comp_injective htwo_add_one_inj)
  refine hasDerivAt_tsum_of_isPreconnected (u := u) hu isOpen_Ioi isPreconnected_Ioi ?_ ?_
    hs_mem (etaSeries_summable hs) hs_mem
  · intro m y hy
    exact etaTerm_hasDerivAt m y
  · intro m y hy
    have hyc : c < y := hy
    have hodd_pos : 0 < (((2 * m + 1 : ℕ) : ℝ)) := by positivity
    have heven_pos : 0 < (((2 * m + 2 : ℕ) : ℝ)) := by positivity
    have hodd_one_le' : (1 : ℝ) ≤ (((2 * m + 1 : ℕ) : ℝ)) := by
      have hnat : 1 ≤ 2 * m + 1 := by omega
      exact_mod_cast hnat
    have heven_one_le' : (1 : ℝ) ≤ (((2 * m + 2 : ℕ) : ℝ)) := by
      have hnat : 1 ≤ 2 * m + 2 := by omega
      exact_mod_cast hnat
    have hodd_log_nonneg : 0 ≤ Real.log (2 * m + 1) := by
      have hcast_odd : (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 := by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
      rw [hcast_odd] at hodd_one_le'
      have hodd_one_le : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
        exact hodd_one_le'
      exact Real.log_nonneg hodd_one_le
    have heven_log_nonneg : 0 ≤ Real.log (2 * m + 2) := by
      have hcast_even : (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 := by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
      rw [hcast_even] at heven_one_le'
      have heven_one_le : (1 : ℝ) ≤ 2 * (m : ℝ) + 2 := by
        exact heven_one_le'
      exact Real.log_nonneg heven_one_le
    have hodd_rpow :
        (((2 * m + 1 : ℕ) : ℝ) ^ (-y)) ≤ (((2 * m + 1 : ℕ) : ℝ) ^ (-c)) := by
      exact Real.rpow_le_rpow_of_exponent_le hodd_one_le'
        (by linarith)
    have heven_rpow :
        (((2 * m + 2 : ℕ) : ℝ) ^ (-y)) ≤ (((2 * m + 2 : ℕ) : ℝ) ^ (-c)) := by
      exact Real.rpow_le_rpow_of_exponent_le heven_one_le'
        (by linarith)
    calc
      ‖etaTermDeriv m y‖
          ≤ ‖Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-y))‖ +
              ‖Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-y))‖ := by
                simpa [etaTermDeriv, sub_eq_add_neg] using
                  (norm_sub_le (Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-y)))
                    (Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-y))))
      _ = Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-y)) +
            Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-y)) := by
              rw [Real.norm_of_nonneg (mul_nonneg heven_log_nonneg (by positivity))]
              rw [Real.norm_of_nonneg (mul_nonneg hodd_log_nonneg (by positivity))]
      _ ≤ Real.log (2 * m + 2) * (((2 * m + 2 : ℕ) : ℝ) ^ (-c)) +
            Real.log (2 * m + 1) * (((2 * m + 1 : ℕ) : ℝ) ^ (-c)) := by
              gcongr
      _ = u m := by
            dsimp [u, g]
            have h0 : (((2 * m : ℕ) : ℝ) + 1) = (((2 * m + 1 : ℕ) : ℝ)) := by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            have h1 : (((2 * m + 1 : ℕ) : ℝ) + 1) = (((2 * m + 2 : ℕ) : ℝ)) := by
              have hleft : (((2 * m + 1 : ℕ) : ℝ) + 1) = (m : ℝ) * 2 + 1 + 1 := by
                norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              have hmid : (m : ℝ) * 2 + 1 + 1 = (m : ℝ) * 2 + 2 := by ring
              have hright : (((2 * m + 2 : ℕ) : ℝ)) = (m : ℝ) * 2 + 2 := by
                norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              rw [hleft, hmid, hright]
            rw [h0, h1]
            have h2 : (((2 * m + 1 + 1 : ℕ) : ℝ)) = (((2 * m + 2 : ℕ) : ℝ)) := by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              ring
            rw [h2]
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            rw [add_comm]

lemma first_eta_deriv_block_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤
      Real.log (2 : ℝ) / ((2 : ℝ) ^ s) - Real.log (3 : ℝ) / ((3 : ℝ) ^ s) +
        Real.log (4 : ℝ) / ((4 : ℝ) ^ s) - Real.log (5 : ℝ) / ((5 : ℝ) ^ s) := by
  have hs_ge_one : (1 : ℝ) ≤ s := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hfive :
      Real.log (5 : ℝ) / (5 : ℝ) ^ s ≤
        ((3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
    have hratio : (5 / 3 : ℝ) ≤ (5 / 3 : ℝ) ^ s := by
      simpa using
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5 / 3) hs_ge_one)
    have hdiv :
        (5 / 3 : ℝ) ^ s = (5 : ℝ) ^ s / (3 : ℝ) ^ s := by
      simpa using
        (Real.div_rpow (show 0 ≤ (5 : ℝ) by positivity)
          (show 0 ≤ (3 : ℝ) by positivity) s)
    have h3pow_pos : 0 < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have h5pow_pos : 0 < (5 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hpow : (5 / 3 : ℝ) * (3 : ℝ) ^ s ≤ (5 : ℝ) ^ s := by
      rw [hdiv] at hratio
      exact (le_div_iff₀ h3pow_pos).mp hratio
    have hcross :
        Real.log (5 : ℝ) * (3 : ℝ) ^ s ≤
          ((3 / 5 : ℝ) * Real.log (5 : ℝ)) * (5 : ℝ) ^ s := by
      have hlog5_nonneg : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
      nlinarith
    exact (div_le_div_iff₀ h5pow_pos h3pow_pos).2 hcross
  have hgeom : 3 ≤ (3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s := by
    have hprod :
        (9 / 8 : ℝ) ≤ (3 / 2 : ℝ) ^ s * (3 / 4 : ℝ) ^ s := by
      calc
        (9 / 8 : ℝ) ≤ (9 / 8 : ℝ) ^ s := by
          simpa using
            (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9 / 8) hs_ge_one)
        _ = (3 / 2 : ℝ) ^ s * (3 / 4 : ℝ) ^ s := by
            simpa [show (9 / 8 : ℝ) = (3 / 2 : ℝ) * (3 / 4 : ℝ) by norm_num] using
              (Real.mul_rpow (show 0 ≤ (3 / 2 : ℝ) by positivity)
                (show 0 ≤ (3 / 4 : ℝ) by positivity) (z := s))
    have hsquare : 9 ≤ ((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) ^ 2 := by
      have hsq_nonneg : 0 ≤ ((3 / 2 : ℝ) ^ s - 2 * (3 / 4 : ℝ) ^ s) ^ 2 := sq_nonneg _
      nlinarith
    have hnonneg : 0 ≤ (3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s := by positivity
    nlinarith
  have hlog_bound :
      Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ) ≤ 3 * Real.log (2 : ℝ) := by
    have hpow :
        ((3 : ℝ) ^ (5 : ℝ)) * ((5 : ℝ) ^ (3 : ℝ)) ≤ (8 : ℝ) ^ (5 : ℝ) := by
      norm_num [Real.rpow_natCast]
    have hlog :
        Real.log (((3 : ℝ) ^ (5 : ℝ)) * ((5 : ℝ) ^ (3 : ℝ))) ≤
          Real.log ((8 : ℝ) ^ (5 : ℝ)) := by
      exact Real.log_le_log (by positivity) hpow
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    rw [Real.log_rpow (by norm_num : 0 < (3 : ℝ)),
      Real.log_rpow (by norm_num : 0 < (5 : ℝ)),
      Real.log_rpow (by norm_num : 0 < (8 : ℝ))] at hlog
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num [Real.rpow_natCast],
        Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
    rw [hlog8] at hlog
    nlinarith
  have hmain :
      Real.log (3 : ℝ) / (3 : ℝ) ^ s + Real.log (5 : ℝ) / (5 : ℝ) ^ s ≤
        Real.log (2 : ℝ) / (2 : ℝ) ^ s + Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
    have h3pow_pos : 0 < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have hlhs :
        Real.log (3 : ℝ) / (3 : ℝ) ^ s + Real.log (5 : ℝ) / (5 : ℝ) ^ s ≤
          (Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
      calc
        Real.log (3 : ℝ) / (3 : ℝ) ^ s + Real.log (5 : ℝ) / (5 : ℝ) ^ s
            ≤ Real.log (3 : ℝ) / (3 : ℝ) ^ s +
                ((3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
                  exact add_le_add_right hfive _
        _ = (Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s := by
              rw [add_div]
    have hlog_div :
        (Real.log (3 : ℝ) + (3 / 5 : ℝ) * Real.log (5 : ℝ)) / (3 : ℝ) ^ s ≤
          (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := by
      exact (div_le_div_iff_of_pos_right h3pow_pos).2 hlog_bound
    have hrhs :
        (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s ≤
          Real.log (2 : ℝ) / (2 : ℝ) ^ s + Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
      have hlog :
          3 * Real.log (2 : ℝ) ≤
            ((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) * Real.log (2 : ℝ) := by
        nlinarith [hgeom, hlog2]
      have hdiv :
          (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s ≤
            (((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := by
        exact (div_le_div_iff_of_pos_right h3pow_pos).2 hlog
      have h32 :
          ((3 / 2 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s =
            Real.log (2 : ℝ) / (2 : ℝ) ^ s := by
        rw [show (3 / 2 : ℝ) ^ s = (3 : ℝ) ^ s / (2 : ℝ) ^ s by
          simpa using
            (Real.div_rpow (show 0 ≤ (3 : ℝ) by positivity)
              (show 0 ≤ (2 : ℝ) by positivity) s)]
        field_simp [show (3 : ℝ) ^ s ≠ 0 by positivity, show (2 : ℝ) ^ s ≠ 0 by positivity]
      have h34 :
          (2 * (3 / 4 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s =
            Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
        rw [show (3 / 4 : ℝ) ^ s = (3 : ℝ) ^ s / (4 : ℝ) ^ s by
          simpa using
            (Real.div_rpow (show 0 ≤ (3 : ℝ) by positivity)
              (show 0 ≤ (4 : ℝ) by positivity) s)]
        rw [show Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) by
          rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num [Real.rpow_natCast],
            Real.log_rpow (by norm_num : 0 < (2 : ℝ))]]
        field_simp [show (3 : ℝ) ^ s ≠ 0 by positivity, show (4 : ℝ) ^ s ≠ 0 by positivity]
      calc
        (3 * Real.log (2 : ℝ)) / (3 : ℝ) ^ s
            ≤ (((3 / 2 : ℝ) ^ s + 2 * (3 / 4 : ℝ) ^ s) * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := hdiv
        _ = ((3 / 2 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s +
              (2 * (3 / 4 : ℝ) ^ s * Real.log (2 : ℝ)) / (3 : ℝ) ^ s := by
                rw [add_mul, add_div]
        _ = Real.log (2 : ℝ) / (2 : ℝ) ^ s + Real.log (4 : ℝ) / (4 : ℝ) ^ s := by
              rw [h32, h34]
    exact hlhs.trans (hlog_div.trans hrhs)
  nlinarith [hmain]

lemma etaSeries_deriv_eq_pair_tsum {s : ℝ} (hs : 1 < s) :
    deriv etaSeries s =
      ∑' m : ℕ,
        (Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
          Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)) := by
  let f : ℕ → ℝ := fun n => Real.log (n + 1) / ((n + 1 : ℝ) ^ s)
  have hsum : Summable f := log_nat_succ_div_rpow_summable hs
  have htwo_inj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro a b h
    have h' := congrArg (fun x : ℕ => x / 2) h
    simpa [Nat.mul_comm] using h'
  have hodd_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    exact htwo_inj h'
  have hshift_inj : Function.Injective (fun n : ℕ => 2 * n + 2) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred (congrArg Nat.pred h)
    exact htwo_inj h'
  have heven : Summable (fun n : ℕ => f (2 * n)) := hsum.comp_injective htwo_inj
  have hodd : Summable (fun n : ℕ => f (2 * n + 1)) := hsum.comp_injective hodd_inj
  have hshift : Summable (fun n : ℕ => f (2 * n + 2)) := hsum.comp_injective hshift_inj
  have hderiv0 :
      deriv etaSeries s = ∑' m : ℕ, (f (2 * m + 1) - f (2 * m)) := by
    rw [(etaSeries_hasDerivAt hs).deriv]
    refine tsum_congr ?_
    intro m
    calc
      etaTermDeriv m s
          = Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
              Real.log (2 * m + 1) / (((2 * m + 1 : ℕ) : ℝ) ^ s) := by
                rw [etaTermDeriv]
                rw [show (((2 * m + 2 : ℕ) : ℝ) ^ (-s)) =
                    ((((2 * m + 2 : ℕ) : ℝ) ^ s)⁻¹) by
                      rw [Real.rpow_neg (show 0 ≤ (((2 * m + 2 : ℕ) : ℝ)) by positivity)]]
                rw [show (((2 * m + 1 : ℕ) : ℝ) ^ (-s)) =
                    ((((2 * m + 1 : ℕ) : ℝ) ^ s)⁻¹) by
                      rw [Real.rpow_neg (show 0 ≤ (((2 * m + 1 : ℕ) : ℝ)) by positivity)]]
                simp [div_eq_mul_inv]
      _ = f (2 * m + 1) - f (2 * m) := by
            dsimp [f]
            rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 2 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
            rw [show (((2 * m : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 1 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
            rw [show (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
            rw [show (((2 * m + 1 : ℕ) : ℝ)) = 2 * (m : ℝ) + 1 by
              norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
              try ring]
  have heven_shift :
      (∑' n : ℕ, f (2 * n)) = ∑' n : ℕ, f (2 * n + 2) := by
    let g : ℕ → ℝ := fun n => f (2 * n)
    have hg : Summable g := heven
    have hg0 : g 0 = 0 := by
      dsimp [g, f]
      simp
    calc
      ∑' n : ℕ, f (2 * n) = ∑' n : ℕ, g n := by rfl
      _ = ∑ i ∈ Finset.range 1, g i + ∑' n : ℕ, g (n + 1) := by
            exact (hg.sum_add_tsum_nat_add 1).symm
      _ = ∑' n : ℕ, g (n + 1) := by simp [hg0]
      _ = ∑' n : ℕ, f (2 * n + 2) := by
            refine tsum_congr ?_
            intro n
            simp [g, Nat.mul_add, add_comm]
  calc
    deriv etaSeries s = ∑' m : ℕ, (f (2 * m + 1) - f (2 * m)) := hderiv0
    _ = (∑' m : ℕ, f (2 * m + 1)) - ∑' m : ℕ, f (2 * m) := by
          exact (hodd.hasSum.sub heven.hasSum).tsum_eq
    _ = (∑' m : ℕ, f (2 * m + 1)) - ∑' m : ℕ, f (2 * m + 2) := by
          rw [heven_shift]
    _ = ∑' m : ℕ, (f (2 * m + 1) - f (2 * m + 2)) := by
          symm
          exact (hodd.hasSum.sub hshift.hasSum).tsum_eq
    _ = ∑' m : ℕ,
          (Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
            Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)) := by
          refine tsum_congr ?_
          intro m
          dsimp [f]
          rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 2 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]
          rw [show (((2 * m + 2 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 3 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]
          rw [show (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]
          rw [show (((2 * m + 3 : ℕ) : ℝ)) = 2 * (m : ℝ) + 3 by
            norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
            try ring]

lemma eta_deriv_pair_nonneg {s : ℝ} (hs : 1 < s) {m : ℕ} (hm : 1 ≤ m) :
    0 ≤
      Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
        Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s) := by
  have hs_pos : 0 < s := by linarith
  have hinv_lt_one : 1 / s < (1 : ℝ) := by
    simpa using (one_div_lt_one_div_of_lt (show (0 : ℝ) < 1 by norm_num) hs)
  have hexp_lt_four : Real.exp (1 / s) < (4 : ℝ) := by
    have hexp_lt_three : Real.exp (1 / s) < (3 : ℝ) := by
      exact lt_trans (Real.exp_lt_exp.mpr hinv_lt_one) Real.exp_one_lt_three
    linarith
  have hanti := Real.log_div_self_rpow_antitoneOn hs_pos
  have hmem₁ : (2 * m + 2 : ℝ) ∈ Set.Ici (Real.exp s⁻¹) := by
    have h4le : (4 : ℝ) ≤ (2 * m + 2 : ℝ) := by
      exact_mod_cast (show 4 ≤ 2 * m + 2 by omega)
    simpa [one_div] using le_trans hexp_lt_four.le h4le
  have hmem₂ : (2 * m + 3 : ℝ) ∈ Set.Ici (Real.exp s⁻¹) := by
    have h4le : (4 : ℝ) ≤ (2 * m + 3 : ℝ) := by
      exact_mod_cast (show 4 ≤ 2 * m + 3 by omega)
    simpa [one_div] using le_trans hexp_lt_four.le h4le
  have hle : (2 * m + 2 : ℝ) ≤ 2 * m + 3 := by linarith
  have hcmp :
      Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s) ≤
        Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) := by
    simpa [Nat.cast_add, Nat.cast_mul, mul_comm] using hanti hmem₁ hmem₂ hle
  exact sub_nonneg.mpr hcmp

lemma etaSeries_deriv_nonneg {s : ℝ} (hs : 1 < s) :
    0 ≤ deriv etaSeries s := by
  let pair : ℕ → ℝ := fun m =>
    Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s) -
      Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)
  have hderiv : deriv etaSeries s = ∑' m : ℕ, pair m := by
    simpa [pair] using etaSeries_deriv_eq_pair_tsum hs
  let f : ℕ → ℝ := fun n => Real.log (n + 1) / ((n + 1 : ℝ) ^ s)
  have hsum : Summable f := log_nat_succ_div_rpow_summable hs
  have hodd_inj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred h
    have h'' := congrArg (fun x : ℕ => x / 2) h'
    simpa [Nat.mul_comm] using h''
  have hshift_inj : Function.Injective (fun n : ℕ => 2 * n + 2) := by
    intro a b h
    have h' : 2 * a = 2 * b := by
      simpa [Nat.succ_eq_add_one] using congrArg Nat.pred (congrArg Nat.pred h)
    have h'' := congrArg (fun x : ℕ => x / 2) h'
    simpa [Nat.mul_comm] using h''
  have hsum_pair : Summable pair := by
    have hsum1 :
        Summable (fun m : ℕ => Real.log (2 * m + 2) / (((2 * m + 2 : ℕ) : ℝ) ^ s)) := by
      refine (hsum.comp_injective hodd_inj).congr ?_
      intro m
      dsimp [f]
      rw [show (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 2 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
      rw [show (((2 * m + 2 : ℕ) : ℝ)) = 2 * (m : ℝ) + 2 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
    have hsum2 :
        Summable (fun m : ℕ => Real.log (2 * m + 3) / (((2 * m + 3 : ℕ) : ℝ) ^ s)) := by
      refine (hsum.comp_injective hshift_inj).congr ?_
      intro m
      dsimp [f]
      rw [show (((2 * m + 2 : ℕ) : ℝ) + 1) = 2 * (m : ℝ) + 3 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
      rw [show (((2 * m + 3 : ℕ) : ℝ)) = 2 * (m : ℝ) + 3 by
        norm_num [Nat.cast_add, Nat.cast_mul, mul_comm]
        try ring]
    simpa [pair] using hsum1.sub hsum2
  have htail_nonneg : 0 ≤ ∑' m : ℕ, pair (m + 2) := by
    exact tsum_nonneg fun m => eta_deriv_pair_nonneg hs (by omega)
  have hsplit :
      ∑' m : ℕ, pair m = pair 0 + pair 1 + ∑' m : ℕ, pair (m + 2) := by
    calc
      ∑' m : ℕ, pair m = ∑ i ∈ Finset.range 2, pair i + ∑' m : ℕ, pair (m + 2) := by
        simpa using (hsum_pair.sum_add_tsum_nat_add 2).symm
      _ = pair 0 + pair 1 + ∑' m : ℕ, pair (m + 2) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          simp [pair]
  have hfirst : 0 ≤ pair 0 + pair 1 := by
    dsimp [pair]
    norm_num
    nlinarith [first_eta_deriv_block_nonneg hs]
  rw [hderiv, hsplit]
  nlinarith

lemma etaSeries_pos {s : ℝ} (hs : 1 < s) :
    0 < etaSeries s := by
  have hfactor_pos : 0 < 1 - (2 : ℝ) ^ (1 - s) := by
    have hlt : (2 : ℝ) ^ (1 - s) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  have hzeta_bound : 1 / (s - 1) + (1 / 2 : ℝ) ≤ zetaSeries s := by
    simpa using zetaSeries_ge_one_div_sub_add_one_half hs
  have hzeta_pos : 0 < zetaSeries s := by
    have hs1 : 0 < s - 1 := by linarith
    have hlower : 0 < 1 / (s - 1) + (1 / 2 : ℝ) := by
      have : 0 < 1 / (s - 1 : ℝ) := one_div_pos.mpr hs1
      linarith
    exact lt_of_lt_of_le hlower hzeta_bound
  rw [etaSeries_eq_factor_mul_zetaSeries hs]
  exact mul_pos hfactor_pos hzeta_pos

lemma analyticSeries_eq_bound_sub_eta_log_deriv {s : ℝ} (hs : 1 < s) :
    analyticSeries s =
      Real.log (2 : ℝ) / ((2 : ℝ) ^ (s - 1) - 1) - deriv etaSeries s / etaSeries s := by
        sorry
lemma analyticSeries_le_bound {t : ℝ} (ht : 0 < t) :
    analyticSeries (1 + t) ≤ Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1) := by
  have hs : 1 < 1 + t := by linarith
  have hmain := analyticSeries_eq_bound_sub_eta_log_deriv hs
  have hq :
      0 ≤ deriv etaSeries (1 + t) / etaSeries (1 + t) := by
    exact div_nonneg (etaSeries_deriv_nonneg hs) (etaSeries_pos hs).le
  have hpow : ((2 : ℝ) ^ ((1 + t) - 1) - 1) = ((2 : ℝ) ^ t - 1) := by ring_nf
  rw [hmain, hpow]
  linarith

theorem main_bound_of_one_lt {n : ℕ} (hn : 1 < n) :
    series n ≤ 1 / Real.log ((2 * n : ℕ) : ℝ) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have h_nonneg :
      0 ≤ᵐ[μ] fun t : ℝ => kernel n t * analyticSeries (1 + t) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (kernel_nonneg (le_of_lt hn) ht) (analyticSeries_nonneg_shift t)
  have h_le :
      (fun t : ℝ => kernel n t * analyticSeries (1 + t)) ≤ᵐ[μ]
        (fun t : ℝ => (((2 * n : ℕ) : ℝ) ^ (-t))) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      kernel n t * analyticSeries (1 + t)
          ≤ kernel n t * (Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1)) := by
            exact mul_le_mul_of_nonneg_left (analyticSeries_le_bound ht)
              (kernel_nonneg (le_of_lt hn) ht)
      _ = (((2 * n : ℕ) : ℝ) ^ (-t)) := kernel_mul_bound_eq ht
  rw [series_eq_integral (le_of_lt hn)]
  have hmono :
      ∫ t, kernel n t * analyticSeries (1 + t) ∂μ ≤
        ∫ t, (((2 * n : ℕ) : ℝ) ^ (-t)) ∂μ := by
    exact MeasureTheory.integral_mono_of_nonneg h_nonneg (two_n_integrable (le_of_lt hn)) h_le
  calc
    ∫ t in Set.Ioi (0 : ℝ), kernel n t * analyticSeries (1 + t)
        = ∫ t, kernel n t * analyticSeries (1 + t) ∂μ := by
            rfl
    _ ≤ ∫ t, (((2 * n : ℕ) : ℝ) ^ (-t)) ∂μ := hmono
    _ = ∫ t in Set.Ioi (0 : ℝ), (((2 * n : ℕ) : ℝ) ^ (-t)) := by
          rfl
    _ = 1 / Real.log ((2 * n : ℕ) : ℝ) := integral_two_n_eq (le_of_lt hn)

theorem main_bound_of_eq_one {n : ℕ} (hn : n = 1) :
    series n ≤ 1 / Real.log ((2 * n : ℕ) : ℝ) := by
  subst hn
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have h_nonneg :
      0 ≤ᵐ[μ] fun t : ℝ => kernel 1 t * analyticSeries (1 + t) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (kernel_nonneg le_rfl ht) (analyticSeries_nonneg_shift t)
  have h_le :
      (fun t : ℝ => kernel 1 t * analyticSeries (1 + t)) ≤ᵐ[μ]
        (fun t : ℝ => (((2 * 1 : ℕ) : ℝ) ^ (-t))) := by
    filter_upwards [show ∀ᵐ t : ℝ ∂MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)),
        t ∈ Set.Ioi (0 : ℝ) from
          MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    calc
      kernel 1 t * analyticSeries (1 + t)
          ≤ kernel 1 t * (Real.log (2 : ℝ) / ((2 : ℝ) ^ t - 1)) := by
            exact mul_le_mul_of_nonneg_left (analyticSeries_le_bound ht)
              (kernel_nonneg le_rfl ht)
      _ = (((2 * 1 : ℕ) : ℝ) ^ (-t)) := by
            simpa using (kernel_mul_bound_eq (n := 1) ht)
  rw [series_eq_integral le_rfl]
  have hmono :
      ∫ t, kernel 1 t * analyticSeries (1 + t) ∂μ ≤
        ∫ t, (((2 * 1 : ℕ) : ℝ) ^ (-t)) ∂μ := by
    exact MeasureTheory.integral_mono_of_nonneg h_nonneg (two_n_integrable le_rfl) h_le
  calc
    ∫ t in Set.Ioi (0 : ℝ), kernel 1 t * analyticSeries (1 + t)
        = ∫ t, kernel 1 t * analyticSeries (1 + t) ∂μ := by
            rfl
    _ ≤ ∫ t, (((2 * 1 : ℕ) : ℝ) ^ (-t)) ∂μ := hmono
    _ = ∫ t in Set.Ioi (0 : ℝ), (((2 * 1 : ℕ) : ℝ) ^ (-t)) := by
          rfl
    _ = 1 / Real.log ((2 * 1 : ℕ) : ℝ) := by
          simpa using (integral_two_n_eq (n := 1) le_rfl)

theorem main_bound {n : ℕ} (hn : 1 ≤ n) :
    series n ≤ 1 / Real.log ((2 * n : ℕ) : ℝ) := by
  rcases Nat.eq_or_lt_of_le hn with h | h
  · exact main_bound_of_eq_one h.symm
  · exact main_bound_of_one_lt h

noncomputable def twoWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log ((2 * n : ℕ) : ℝ))

noncomputable def twoFlow (m n : ℕ) : ℝ :=
  if 0 < n then
    if n ∣ m then
      let q := m / n
      if 2 ≤ q then
        ArithmeticFunction.vonMangoldt q /
          ((m : ℝ) * Real.log m * Real.log ((2 * m : ℕ) : ℝ))
      else
        0
    else
      0
  else
    0

lemma twoFlow_nonneg (m n : ℕ) : 0 ≤ twoFlow m n := by
  unfold twoFlow
  by_cases hn : 0 < n
  · by_cases hdiv : n ∣ m
    · by_cases hq : 2 ≤ m / n
      · rcases hdiv with ⟨q, rfl⟩
        have hq' : 2 ≤ q := by simpa [Nat.mul_div_right _ hn] using hq
        have hm_gt_one : 1 < n * q := by
          exact lt_of_lt_of_le (by omega : 1 < q) (Nat.le_mul_of_pos_left q hn)
        have hm_pos_nat : 0 < n * q := Nat.mul_pos hn (by omega)
        have hm_pos : 0 < ((n * q : ℕ) : ℝ) := by
          exact_mod_cast hm_pos_nat
        have hm_mul_pos : 0 < (n : ℝ) * q := by
          exact_mod_cast hm_pos_nat
        have hlogm_pos : 0 < Real.log ((n * q : ℕ) : ℝ) := by
          exact Real.log_pos (by exact_mod_cast hm_gt_one)
        have hlogm_mul_pos : 0 < Real.log ((n : ℝ) * q) := by
          simpa [Nat.cast_mul] using hlogm_pos
        have hlog2m_pos : 0 < Real.log ((2 * (n * q) : ℕ) : ℝ) := by
          exact Real.log_pos (by exact_mod_cast (show 1 < 2 * (n * q) by omega))
        have hlog2m_mul_pos : 0 < Real.log (2 * ((n : ℝ) * q)) := by
          simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hlog2m_pos
        suffices
            0 ≤
              ArithmeticFunction.vonMangoldt q /
                (((n : ℝ) * q) * Real.log ((n : ℝ) * q) * Real.log (2 * ((n : ℝ) * q))) by
          simpa only [twoFlow, hn, dvd_mul_right, Nat.mul_div_right _ hn, hq', ↓reduceIte,
            Nat.cast_mul, Nat.cast_ofNat, ge_iff_le]
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
          le_of_lt <| mul_pos (mul_pos hm_mul_pos hlogm_mul_pos) hlog2m_mul_pos
      · simp [hn, hdiv, hq]
    · simp [hn, hdiv]
  · simp [hn]

lemma twoFlow_eq_zero_of_not_dvd_lt {m n : ℕ}
    (h : ¬ (n ∣ m ∧ n < m)) : twoFlow m n = 0 := by
  unfold twoFlow
  by_cases hn : 0 < n
  · by_cases hdiv : n ∣ m
    · by_cases hq : 2 ≤ m / n
      · exfalso
        apply h
        rcases hdiv with ⟨q, rfl⟩
        have hq' : 2 ≤ q := by simpa [Nat.mul_div_right _ hn] using hq
        refine ⟨dvd_mul_right n q, ?_⟩
        simpa using (Nat.mul_lt_mul_of_pos_left (show 1 < q by omega) hn)
      · simp [hn, hdiv, hq]
    · simp [hn, hdiv]
  · simp [hn]

lemma summable_twoFlow_row (m : ℕ) : Summable (fun n : ℕ => twoFlow m n) := by
  classical
  refine summable_of_ne_finset_zero (s := m.divisors) ?_
  intro n hn
  apply twoFlow_eq_zero_of_not_dvd_lt
  intro h
  have hm0 : m ≠ 0 := by omega
  exact hn (Nat.mem_divisors.mpr ⟨h.1, hm0⟩)

lemma twoFlow_mul_right_eq {n q : ℕ} (hn : 1 ≤ n) (hq : 2 ≤ q) :
    twoFlow (n * q) n =
      ArithmeticFunction.vonMangoldt q /
        ((((n * q : ℕ) : ℝ)) * Real.log ((n * q : ℕ) : ℝ) *
          Real.log ((2 * n * q : ℕ) : ℝ)) := by
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  simp [twoFlow, hn_pos, show n ∣ n * q by exact dvd_mul_right n q,
    Nat.mul_div_right q hn_pos, hq, Nat.mul_assoc]

lemma twoFlow_mul_le_baseFlow {n : ℕ} (hn : 1 ≤ n) (q : {q : ℕ // 2 ≤ q}) :
    twoFlow (n * q.1) n ≤ baseFlow (n * q.1) n := by
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hq_pos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
  have hlogA_pos : 0 < Real.log ((n * q.1 : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < n * q.1 by
      exact lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos)))
  have hlogB_ge :
      Real.log ((n * q.1 : ℕ) : ℝ) ≤ Real.log ((2 * n * q.1 : ℕ) : ℝ) := by
    have hA_pos : 0 < ((n * q.1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos hn_pos hq_pos)
    apply Real.log_le_log hA_pos
    exact_mod_cast (show n * q.1 ≤ 2 * n * q.1 by
      have hle : n * q.1 ≤ 2 * (n * q.1) := Nat.le_mul_of_pos_left (n * q.1) (by omega)
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle)
  by_cases hqpp : IsPrimePow q.1
  · have hbase :
      baseFlow (n * q.1) n =
        ArithmeticFunction.vonMangoldt q.1 /
          ((((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2) := by
      have hgt : 1 < n * q.1 := by
        exact lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos)
      simp [baseFlow, hgt, show n ∣ n * q.1 by exact dvd_mul_right n q.1,
        Nat.mul_div_right q.1 hn_pos, hqpp]
    rw [twoFlow_mul_right_eq hn q.2, hbase]
    have hnum_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt q.1 :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hden :
        (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2 ≤
          (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) *
            Real.log ((2 * n * q.1 : ℕ) : ℝ) := by
      have hlogA_nonneg : 0 ≤ Real.log ((n * q.1 : ℕ) : ℝ) := hlogA_pos.le
      calc
        (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2
            = (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) *
                Real.log ((n * q.1 : ℕ) : ℝ) := by ring
        _ ≤ (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) *
              Real.log ((2 * n * q.1 : ℕ) : ℝ) := by
              gcongr
    have hden_pos :
        0 < (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2 := by
      refine mul_pos ?_ ?_
      · exact_mod_cast (Nat.mul_pos hn_pos hq_pos)
      · exact sq_pos_of_pos hlogA_pos
    exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden
  · have hvm : ArithmeticFunction.vonMangoldt q.1 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
      exact hqpp
    rw [twoFlow_mul_right_eq hn q.2, hvm]
    simp [baseFlow, show 1 < n * q.1 by
      exact lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos),
      show n ∣ n * q.1 by exact dvd_mul_right n q.1,
      Nat.mul_div_right q.1 hn_pos, hqpp]

lemma summable_twoFlow_col {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun K : ℕ => twoFlow K n) := by
      sorry
lemma inflow_twoFlow_eq_one_div_mul_series {n : ℕ} (hn : 1 ≤ n) :
    inflow twoFlow n = (1 / (n : ℝ)) * series n := by
      sorry
theorem outflow_twoFlow_eq_twoWeight {n : ℕ} (hn : 1 < n) :
    outflow twoFlow n = twoWeight n := by
  have hn0_nat : n ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hn)
  have hn_cast : (1 : ℝ) < n := by
    exact_mod_cast hn
  have hlogn_pos : 0 < Real.log n := Real.log_pos hn_cast
  have hlog2n_pos : 0 < Real.log ((2 * n : ℕ) : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < 2 * n by omega))
  have hsupport : ∀ m ∉ n.divisors, twoFlow n m = 0 := by
    intro m hm
    apply twoFlow_eq_zero_of_not_dvd_lt
    intro h
    exact hm (Nat.mem_divisors.mpr ⟨h.1, hn0_nat⟩)
  rw [outflow, tsum_eq_sum (s := n.divisors) hsupport]
  calc
    ∑ m ∈ n.divisors, twoFlow n m
        = ∑ m ∈ n.divisors,
            ArithmeticFunction.vonMangoldt (n / m) /
              ((n : ℝ) * Real.log n * Real.log ((2 * n : ℕ) : ℝ)) := by
                apply Finset.sum_congr rfl
                intro m hm
                have hdiv : m ∣ n := Nat.dvd_of_mem_divisors hm
                have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hdiv (lt_trans Nat.zero_lt_one hn)
                by_cases hq : 2 ≤ n / m
                · simp [twoFlow, hm_pos, hdiv, hq]
                · have hnotpp : ¬ IsPrimePow (n / m) := by
                    intro hpp
                    exact hq (Nat.succ_le_of_lt (IsPrimePow.one_lt hpp))
                  have hvm : ArithmeticFunction.vonMangoldt (n / m) = 0 := by
                    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
                    exact hnotpp
                  simp [twoFlow, hm_pos, hdiv, hq, hvm]
    _ = ∑ d ∈ n.divisors,
          ArithmeticFunction.vonMangoldt d /
            ((n : ℝ) * Real.log n * Real.log ((2 * n : ℕ) : ℝ)) := by
              simpa using
                (Nat.sum_div_divisors n
                  (fun d : ℕ =>
                    ArithmeticFunction.vonMangoldt d /
                      ((n : ℝ) * Real.log n * Real.log ((2 * n : ℕ) : ℝ))))
    _ = (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d) /
          ((n : ℝ) * Real.log n * Real.log ((2 * n : ℕ) : ℝ)) := by
            rw [Finset.sum_div]
    _ = Real.log n / ((n : ℝ) * Real.log n * Real.log ((2 * n : ℕ) : ℝ)) := by
          rw [ArithmeticFunction.vonMangoldt_sum]
    _ = twoWeight n := by
          rw [twoWeight]
          field_simp [Nat.cast_ne_zero.mpr hn0_nat, hlogn_pos.ne', hlog2n_pos.ne']

theorem outflow_twoFlow_ge_inflow_twoFlow {n : ℕ} (hn : 1 < n) :
    inflow twoFlow n ≤ outflow twoFlow n := by
  have hn1 : 1 ≤ n := le_of_lt hn
  have hmain := main_bound (n := n) hn1
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  calc
    inflow twoFlow n = (1 / (n : ℝ)) * series n := inflow_twoFlow_eq_one_div_mul_series hn1
    _ ≤ (1 / (n : ℝ)) * (1 / Real.log ((2 * n : ℕ) : ℝ)) := by
          gcongr
    _ = twoWeight n := by
          rw [twoWeight]
          ring
    _ = outflow twoFlow n := (outflow_twoFlow_eq_twoWeight hn).symm

noncomputable def twoWeightSum (A : Set ℕ) : ℝ :=
  ∑' a : A, twoWeight (a : ℕ)

lemma outflow_twoFlow_eq_sum_finset_add_compl (s : Finset ℕ) (m : ℕ) :
    outflow twoFlow m =
      (∑ n ∈ s, twoFlow m n) +
        ∑' n : { n // n ∉ s }, twoFlow m n := by
  simpa [outflow] using ((summable_twoFlow_row m).sum_add_tsum_subtype_compl s).symm

lemma inflow_twoFlow_eq_sum_finset_add_compl (s : Finset ℕ) {n : ℕ} (hn : 1 ≤ n) :
    inflow twoFlow n =
      (∑ m ∈ s, twoFlow m n) +
        ∑' m : { m // m ∉ s }, twoFlow m n := by
  simpa [inflow] using ((summable_twoFlow_col hn).sum_add_tsum_subtype_compl s).symm

lemma boundaryOutflow_eq_sum_compl_twoFlow (s : Finset ℕ) :
    boundaryOutflow twoFlow (↑s : Set ℕ) =
      ∑ r ∈ s, ∑' n : { n // n ∉ s }, twoFlow r n := by
        sorry
lemma boundaryInflow_eq_sum_compl_twoFlow (s : Finset ℕ)
    (hs_ge_one : ∀ {n : ℕ}, n ∈ s → 1 ≤ n) :
    boundaryInflow twoFlow (↑s : Set ℕ) =
      ∑ n ∈ s, ∑' m : { m // m ∉ s }, twoFlow m n := by
        sorry
lemma tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow_twoFlow {Ω : Set ℕ}
    (hΩfin : Ω.Finite) (hΩ_ge_one : ∀ {r : ℕ}, r ∈ Ω → 1 ≤ r) :
    (∑' r : Ω, (outflow twoFlow (r : ℕ) - inflow twoFlow (r : ℕ))) =
      boundaryOutflow twoFlow Ω - boundaryInflow twoFlow Ω := by
  classical
  let s : Finset ℕ := hΩfin.toFinset
  have hsΩ : (↑s : Set ℕ) = Ω := hΩfin.coe_toFinset
  rw [← hsΩ]
  have hout :
      ∑ r ∈ s, outflow twoFlow r =
        (∑ r ∈ s, ∑ n ∈ s, twoFlow r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, twoFlow r n := by
    calc
      ∑ r ∈ s, outflow twoFlow r
        = ∑ r ∈ s, ((∑ n ∈ s, twoFlow r n) +
            ∑' n : {n // n ∉ s}, twoFlow r n) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [outflow_twoFlow_eq_sum_finset_add_compl s r]
      _ = (∑ r ∈ s, ∑ n ∈ s, twoFlow r n) +
            ∑ r ∈ s, ∑' n : {n // n ∉ s}, twoFlow r n := by
              rw [Finset.sum_add_distrib]
  have hin :
      ∑ r ∈ s, inflow twoFlow r =
        (∑ r ∈ s, ∑ m ∈ s, twoFlow m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, twoFlow m r := by
    calc
      ∑ r ∈ s, inflow twoFlow r
        = ∑ r ∈ s, ((∑ m ∈ s, twoFlow m r) +
            ∑' m : {m // m ∉ s}, twoFlow m r) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              have hrΩ : r ∈ Ω := by
                simpa [hsΩ] using (show r ∈ (↑s : Set ℕ) from hr)
              rw [inflow_twoFlow_eq_sum_finset_add_compl s (hΩ_ge_one hrΩ)]
      _ = (∑ r ∈ s, ∑ m ∈ s, twoFlow m r) +
            ∑ r ∈ s, ∑' m : {m // m ∉ s}, twoFlow m r := by
              rw [Finset.sum_add_distrib]
  have hinternal :
      ∑ r ∈ s, ∑ n ∈ s, twoFlow r n =
        ∑ r ∈ s, ∑ m ∈ s, twoFlow m r := by
    simpa using (Finset.sum_comm (s := s) (t := s) (f := fun r n => twoFlow r n))
  calc
    (∑' r : (↑s : Set ℕ), (outflow twoFlow (r : ℕ) - inflow twoFlow (r : ℕ)))
      = ∑ r ∈ s, (outflow twoFlow r - inflow twoFlow r) := by
          simpa using
            (Finset.tsum_subtype' s
              (fun r => outflow twoFlow r - inflow twoFlow r))
    _ = (∑ r ∈ s, outflow twoFlow r) - ∑ r ∈ s, inflow twoFlow r := by
          rw [Finset.sum_sub_distrib]
    _ =
        ((∑ r ∈ s, ∑ n ∈ s, twoFlow r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, twoFlow r n) -
        ((∑ r ∈ s, ∑ m ∈ s, twoFlow m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, twoFlow m r) := by
            rw [hout, hin]
    _ = (∑ r ∈ s, ∑' n : {n // n ∉ s}, twoFlow r n) -
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, twoFlow m r := by
            rw [hinternal]
            ring
    _ = boundaryOutflow twoFlow (↑s : Set ℕ) -
          boundaryInflow twoFlow (↑s : Set ℕ) := by
            rw [boundaryOutflow_eq_sum_compl_twoFlow,
              boundaryInflow_eq_sum_compl_twoFlow s (fun {n} hn =>
                hΩ_ge_one (by simpa [hsΩ] using (show n ∈ (↑s : Set ℕ) from hn)))]

lemma boundaryOutflow_le_series_one_of_downwardClosed {Ω : Set ℕ}
    (hΩ_ge_two : ∀ {d : ℕ}, d ∈ Ω → 2 ≤ d)
    (hΩdown : ∀ {d e : ℕ}, d ∈ Ω → 2 ≤ e → e ∣ d → e ∈ Ω) :
    boundaryOutflow twoFlow Ω ≤ series 1 := by
  classical
  have hone_not_mem : 1 ∉ Ω := by
    intro h1
    have h := hΩ_ge_two h1
    omega
  have hboundary_target_eq_one : ∀ mn : boundaryOutPairs Ω, mn.1.2 = 1 := by
    intro mn
    rcases mn with ⟨⟨m, n⟩, hmn⟩
    rcases hmn with ⟨hmΩ, hnΩ, hdiv, _⟩
    have hm2 : 2 ≤ m := hΩ_ge_two hmΩ
    have hmpos : 0 < m := by omega
    have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hdiv hmpos
    have hnle : n ≤ 1 := by
      by_contra hgt
      have hn2 : 2 ≤ n := by omega
      exact hnΩ (hΩdown hmΩ hn2 hdiv)
    have hpred : n.pred = 0 := by
      rw [Nat.pred_eq_sub_one, Nat.sub_eq_zero_of_le hnle]
    have hsucc : n.pred.succ = n := Nat.succ_pred_eq_of_pos hnpos
    rw [hpred] at hsucc
    simpa using hsucc.symm
  let eBoundaryFun : boundaryOutPairs Ω → Ω := fun mn => ⟨mn.1.1, mn.2.1⟩
  have heBoundary_bij : Function.Bijective eBoundaryFun := by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Prod.ext
      · simpa [eBoundaryFun] using congrArg Subtype.val h
      · simp [hboundary_target_eq_one a, hboundary_target_eq_one b]
    · intro m
      refine ⟨⟨(m.1, 1), ?_⟩, ?_⟩
      · refine ⟨m.2, hone_not_mem, one_dvd _, ?_⟩
        have hm2 : 2 ≤ m.1 := hΩ_ge_two m.2
        exact lt_of_lt_of_le Nat.one_lt_two hm2
      · rfl
  let eBoundary : boundaryOutPairs Ω ≃ Ω := Equiv.ofBijective eBoundaryFun heBoundary_bij
  have hboundary_eq :
      boundaryOutflow twoFlow Ω = ∑' m : Ω, twoFlow m.1 1 := by
    unfold boundaryOutflow
    calc
      ∑' mn : boundaryOutPairs Ω, twoFlow mn.1.1 mn.1.2
          = ∑' mn : boundaryOutPairs Ω, twoFlow mn.1.1 1 := by
              apply tsum_congr
              intro mn
              simp [hboundary_target_eq_one mn]
      _ = ∑' m : Ω, twoFlow m.1 1 := by
            simpa [eBoundary] using (Equiv.tsum_eq eBoundary (fun m : Ω => twoFlow m.1 1))
  have hnonneg : ∀ n : ℕ, 0 ≤ twoFlow n 1 := by
    intro n
    exact twoFlow_nonneg _ _
  calc
    boundaryOutflow twoFlow Ω = ∑' m : Ω, twoFlow m.1 1 := hboundary_eq
    _ ≤ ∑' n : ℕ, twoFlow n 1 := by
          exact Summable.tsum_subtype_le (fun n : ℕ => twoFlow n 1)
            Ω hnonneg (summable_twoFlow_col le_rfl)
    _ = inflow twoFlow 1 := by rw [inflow]
    _ = series 1 := by simpa using inflow_twoFlow_eq_one_div_mul_series (n := 1) le_rfl

lemma boundaryOutflow_ge_boundaryInflow_add_tsum_divergence_of_subset_twoFlow
    {A Ω : Set ℕ} (hΩfin : Ω.Finite)
    (hΩ_ge_two : ∀ {r : ℕ}, r ∈ Ω → 2 ≤ r) (hAΩ : A ⊆ Ω) :
    boundaryInflow twoFlow Ω +
      (∑' a : A, (outflow twoFlow (a : ℕ) - inflow twoFlow (a : ℕ))) ≤
        boundaryOutflow twoFlow Ω := by
  classical
  let f : ℕ → ℝ := fun r => outflow twoFlow r - inflow twoFlow r
  have hnonneg : ∀ r ∈ Ω, 0 ≤ f r := by
    intro r hr
    exact sub_nonneg.mpr <|
      outflow_twoFlow_ge_inflow_twoFlow
        (lt_of_lt_of_le Nat.one_lt_two (hΩ_ge_two hr))
  have hAfin : A.Finite := hΩfin.subset hAΩ
  letI := hΩfin.fintype
  letI := hAfin.fintype
  let e : A ≃ {r : Ω // (r : ℕ) ∈ A} :=
    { toFun := fun a => ⟨⟨a.1, hAΩ a.2⟩, a.2⟩
      invFun := fun r => ⟨r.1.1, r.2⟩
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hAeq :
      (∑' a : A, f (a : ℕ)) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype]
    exact Fintype.sum_equiv e (fun a : A => f (a : ℕ))
      (fun r : {s : Ω // (s : ℕ) ∈ A} => f (r : ℕ)) (by intro a; rfl)
  have hsplit :
      (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
          (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) =
        ∑' r : Ω, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype]
    simpa using
      (Fintype.sum_subtype_add_sum_subtype (fun r : Ω => (r : ℕ) ∈ A)
        (fun r : Ω => f (r : ℕ)))
  have hcompl_nonneg : 0 ≤ ∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ) := by
    rw [tsum_fintype]
    exact Finset.sum_nonneg fun r _ => by
      simpa using hnonneg (r : ℕ) r.1.2
  have hA_le_Ω :
      (∑' a : A, f (a : ℕ)) ≤ ∑' r : Ω, f (r : ℕ) := by
    calc
      ∑' a : A, f (a : ℕ) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := hAeq
      _ ≤ (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
            (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) := by
              linarith
      _ = ∑' r : Ω, f (r : ℕ) := hsplit
  have hΩboundary :
      (∑' r : Ω, f (r : ℕ)) =
        boundaryOutflow twoFlow Ω - boundaryInflow twoFlow Ω := by
    simpa [f] using
      tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow_twoFlow
        (Ω := Ω) hΩfin (fun {r} hr => le_trans (by decide : 1 ≤ 2) (hΩ_ge_two hr))
  have hmain :
      (∑' a : A, f (a : ℕ)) ≤
        boundaryOutflow twoFlow Ω - boundaryInflow twoFlow Ω := by
    calc
      ∑' a : A, f (a : ℕ) ≤ ∑' r : Ω, f (r : ℕ) := hA_le_Ω
      _ = boundaryOutflow twoFlow Ω - boundaryInflow twoFlow Ω := hΩboundary
  linarith

lemma flow_into_primitive_member_from_outside_divisorClosure_twoFlow {A : Set ℕ}
    (hA : PrimitiveSet A) {a m : ℕ} (ha : a ∈ A)
    (hflow : twoFlow m a ≠ 0) :
    m ∉ primitiveDivisorClosure A := by
  intro hm
  rcases hm with ⟨hm_ge_two, b, hb, hm_dvd_b⟩
  have hdiv_lt : a ∣ m ∧ a < m := by
    by_contra hnot
    exact hflow (twoFlow_eq_zero_of_not_dvd_lt hnot)
  have ha_dvd_m : a ∣ m := hdiv_lt.1
  have ha_lt_m : a < m := hdiv_lt.2
  have ha_dvd_b : a ∣ b := dvd_trans ha_dvd_m hm_dvd_b
  have hab_eq : a = b := hA.2 ha hb ha_dvd_b
  have hm_dvd_a : m ∣ a := hab_eq ▸ hm_dvd_b
  have ha_pos : 0 < a := lt_of_lt_of_le Nat.zero_lt_two (hA.1 ha)
  have hm_le_a : m ≤ a := Nat.le_of_dvd ha_pos hm_dvd_a
  exact (not_le_of_gt ha_lt_m) hm_le_a

lemma twoWeightSum_le_series_one_of_finite {A : Set ℕ}
    (hA : PrimitiveSet A) (hfin : A.Finite) :
    twoWeightSum A ≤ series 1 := by
      sorry
lemma twoWeightSum_le_series_one_of_finite_subsets {A : Set ℕ}
    (hfinite :
      ∀ A₀ : Set ℕ, A₀ ⊆ A → A₀.Finite → twoWeightSum A₀ ≤ series 1) :
    twoWeightSum A ≤ series 1 := by
  classical
  have htsum : ∑' a : A, twoWeight (a : ℕ) ≤ series 1 := by
    refine Real.tsum_le_of_sum_le ?_ ?_
    · intro a
      by_cases ha0 : (a : ℕ) = 0
      · simp [twoWeight, ha0]
      · have ha1 : 1 ≤ (a : ℕ) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero ha0)
        have hlog : 0 < Real.log ((2 * (a : ℕ) : ℕ) : ℝ) := by
          exact Real.log_pos (by exact_mod_cast (show 1 < 2 * (a : ℕ) by omega))
        have hden : 0 ≤ ((a : ℕ) : ℝ) * Real.log ((2 * (a : ℕ) : ℕ) : ℝ) := by
          positivity
        simpa [twoWeight] using one_div_nonneg.mpr hden
    · intro u
      let s : Finset ℕ := u.image (fun a : A => (a : ℕ))
      have hs_subset : (↑s : Set ℕ) ⊆ A := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
        exact a.2
      have hs_eq :
          twoWeightSum (↑s : Set ℕ) = ∑ n ∈ s, twoWeight n := by
        simpa [twoWeightSum, s] using (Finset.tsum_subtype' s twoWeight)
      have hu_eq : ∑ n ∈ s, twoWeight n = ∑ a ∈ u, twoWeight (a : ℕ) := by
        dsimp [s]
        exact
          Finset.sum_image
            (s := u)
            (g := fun a : A => (a : ℕ))
            (f := twoWeight)
            Subtype.val_injective.injOn
      calc
        ∑ a ∈ u, twoWeight (a : ℕ) = twoWeightSum (↑s : Set ℕ) := by
          rw [← hu_eq, ← hs_eq]
        _ ≤ series 1 := hfinite (↑s : Set ℕ) hs_subset s.finite_toSet
  simpa [twoWeightSum] using htsum

theorem twoWeightSum_le_series_one {A : Set ℕ} (hA : PrimitiveSet A) :
    twoWeightSum A ≤ series 1 := by
  refine twoWeightSum_le_series_one_of_finite_subsets ?_
  intro A₀ hA₀ hA₀fin
  have hA₀_primitive : PrimitiveSet A₀ := by
    refine ⟨?_, ?_⟩
    · intro a ha
      exact hA.1 (hA₀ ha)
    · intro a b ha hb hab
      exact hA.2 (hA₀ ha) (hA₀ hb) hab
  exact twoWeightSum_le_series_one_of_finite hA₀_primitive hA₀fin

/-- A natural number is `p`-rough if all of its prime divisors are at least `p`.
This is vacuously true for `1`. -/
def IsPRough (p m : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ∣ m → p ≤ q

def erdos_strong (n : ℕ) : Prop :=
  ∀ ⦃A : Set ℕ⦄, PrimitiveSet A →
    A ⊆ {m : ℕ | n ∣ m ∧ IsPRough n (m / n)} →
    primitiveWeightSum A ≤ erdosWeight n

theorem erdos_strong_of_two : erdos_strong 2 := by
  intro A hA hTwoSub
  have hEven : A ⊆ {n : ℕ | Even n} := by
    intro a ha
    exact even_iff_two_dvd.mpr (hTwoSub ha).1
  by_cases h2 : 2 ∈ A
  · have hAeq : A = {2} := by
      ext a
      constructor
      · intro ha
        have h2dvd : 2 ∣ a := even_iff_two_dvd.mp (hEven ha)
        have hEq : 2 = a := hA.2 h2 ha h2dvd
        simp [hEq]
      · intro ha
        simp at ha
        simp [ha, h2]
    rw [hAeq, primitiveWeightSum]
    simp [erdosWeight]
  · let B : Set ℕ := {n : ℕ | 2 * n ∈ A}
    have hB_primitive : PrimitiveSet B := by
      refine ⟨?_, ?_⟩
      · intro b hb
        by_cases hb1 : b = 1
        · exact False.elim <| h2 (by simpa [B, hb1] using hb)
        · have hb_pos : 0 < b := by
            have hAelt : 2 ≤ 2 * b := hA.1 hb
            omega
          have : 1 < b := by omega
          exact Nat.succ_le_of_lt this
      · intro a b ha hb hab
        have hEq : 2 * a = 2 * b := hA.2 ha hb (Nat.mul_dvd_mul_left 2 hab)
        exact Nat.eq_of_mul_eq_mul_left (by omega) hEq
    let e : B ≃ A :=
      { toFun := fun b => ⟨2 * b.1, b.2⟩
        invFun := fun a => ⟨a.1 / 2, by
          have htwo_dvd : 2 ∣ a.1 := even_iff_two_dvd.mp (hEven a.2)
          have hEq : 2 * (a.1 / 2) = a.1 := Nat.mul_div_cancel' htwo_dvd
          simp [B, hEq, a.2]⟩
        left_inv := by
          intro b
          apply Subtype.ext
          simp
        right_inv := by
          intro a
          apply Subtype.ext
          exact Nat.mul_div_cancel' (even_iff_two_dvd.mp (hEven a.2)) }
    have hWeight :
        primitiveWeightSum A = (1 / (2 : ℝ)) * twoWeightSum B := by
      calc
        primitiveWeightSum A = ∑' b : B, erdosWeight (2 * (b : ℕ)) := by
          unfold primitiveWeightSum
          simpa [e] using (Equiv.tsum_eq e (fun a : A => erdosWeight a.1)).symm
        _ = ∑' b : B, (1 / (2 : ℝ)) * twoWeight (b : ℕ) := by
              apply tsum_congr
              intro b
              have hb_pos : 0 < (b : ℕ) := lt_of_lt_of_le Nat.zero_lt_two (hB_primitive.1 b.2)
              have hb0 : ((b : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb_pos)
              have hlog : 0 < Real.log ((2 * (b : ℕ) : ℕ) : ℝ) := by
                exact Real.log_pos (by exact_mod_cast (show 1 < 2 * (b : ℕ) by
                  have : 1 < (b : ℕ) := lt_of_lt_of_le Nat.one_lt_two (hB_primitive.1 b.2)
                  omega))
              rw [erdosWeight, twoWeight, Nat.cast_mul]
              field_simp [hb0, hlog.ne']
              ring
        _ = (1 / (2 : ℝ)) * twoWeightSum B := by
              rw [twoWeightSum, tsum_mul_left]
    have hB_bound : twoWeightSum B ≤ series 1 := twoWeightSum_le_series_one hB_primitive
    have hseries : series 1 ≤ 1 / Real.log ((2 * 1 : ℕ) : ℝ) := main_bound le_rfl
    calc
      primitiveWeightSum A = (1 / (2 : ℝ)) * twoWeightSum B := hWeight
      _ ≤ (1 / (2 : ℝ)) * series 1 := by
            gcongr
      _ ≤ (1 / (2 : ℝ)) * (1 / Real.log ((2 * 1 : ℕ) : ℝ)) := by
            gcongr
      _ = erdosWeight 2 := by
            rw [erdosWeight]
            ring

/-- The common upper bound appearing throughout `B/f1.tex`. -/
noncomputable def roughLogBound (p : ℕ) : ℝ :=
  Real.log (p : ℝ) - (p : ℝ) * Real.log (1 + 1 / (p : ℝ))

/-- The harmonic/logarithmic average from equations (1) and (2) of `B/f1.tex`. -/
noncomputable def harmonicLogAverage (p : ℕ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 (p - 1), Real.log (m : ℝ) / (m : ℝ)) /
    (∑ m ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (m : ℝ))

/-- The finite Dirichlet polynomial `H_p(s) = \sum_{m=1}^{p-1} m^{-s}`. -/
noncomputable def Hp (p : ℕ) (s : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (p - 1), 1 / Real.rpow (m : ℝ) s

/-- The weighted logarithmic average from Sub-lemma 1 of `B/f1.tex`. -/
noncomputable def hpLogAverage (p : ℕ) (s : ℝ) : ℝ :=
  (∑ m ∈ Finset.Icc 1 (p - 1), Real.log (m : ℝ) / Real.rpow (m : ℝ) s) / Hp p s

/-- The sifted Euler-product factor from Sub-lemma 2 of `B/f1.tex`. -/
noncomputable def Qp (p : ℕ) (s : ℝ) : ℝ :=
  Hp p s *
    ∏ ℓ ∈ (Finset.Icc 2 (p - 1)).filter Nat.Prime,
      (1 - 1 / Real.rpow (ℓ : ℝ) s)

/-- The prime-tail series from equation (5) of `B/f1.tex`. -/
noncomputable def primeTailSeries (p : ℕ) (v : ℝ) : ℝ :=
  ∑' r : { r : ℕ // p ≤ r ∧ r.Prime },
    Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1)

/-- The rough von Mangoldt Dirichlet series `A_p(v)` from the main proof. -/
noncomputable def roughMangoldtSeries (p : ℕ) (v : ℝ) : ℝ :=
  ∑' q : { q : ℕ // 2 ≤ q ∧ IsPRough p q },
    ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + v)

/-- The left-hand side of the main inequality `(*_p)` from `B/f1.tex`. -/
noncomputable def roughKernelSeries (p n : ℕ) : ℝ :=
  ∑' q : { q : ℕ // 2 ≤ q ∧ IsPRough p q },
    ArithmeticFunction.vonMangoldt q.1 /
      ((q.1 : ℝ) * Real.log ((n * q.1 : ℕ) : ℝ) * Real.log ((p * n * q.1 : ℕ) : ℝ))

/-- The Mellin kernel from `B/f1.tex` for the rough series. -/
noncomputable def roughKernel (p n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) ^ (-t)) * (1 - (p : ℝ) ^ (-t)) / Real.log (p : ℝ)

lemma roughKernel_nonneg {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    0 ≤ roughKernel p n t := by
  have hp_cast_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpow_gt_one : 1 < (p : ℝ) ^ t := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) ht
  have hpow_pos : 0 < (p : ℝ) ^ t := lt_trans zero_lt_one hpow_gt_one
  have hratio : 1 - (p : ℝ) ^ (-t) = ((p : ℝ) ^ t - 1) / ((p : ℝ) ^ t) := by
    rw [Real.rpow_neg hp_cast_pos.le]
    field_simp [hpow_pos.ne']
  rw [roughKernel, hratio]
  refine div_nonneg ?_ hlogp.le
  refine mul_nonneg ?_ ?_
  · exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) by positivity) _
  · exact div_nonneg (sub_nonneg.mpr hpow_gt_one.le) hpow_pos.le

lemma rough_rpow_sub_one_pos {p : ℕ} (hp : p.Prime) {t : ℝ} (ht : 0 < t) :
    0 < (p : ℝ) ^ t - 1 := by
  have hpow_gt_one : 1 < (p : ℝ) ^ t := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) ht
  linarith

lemma roughKernel_mul_bound_eq {p n : ℕ} (hp : p.Prime) {t : ℝ} (ht : 0 < t) :
    roughKernel p n t * (Real.log (p : ℝ) / ((p : ℝ) ^ t - 1)) =
      (((p * n : ℕ) : ℝ) ^ (-t)) := by
  have hp_cast_pos : 0 < (p : ℝ) := by
    exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpow_pos : 0 < (p : ℝ) ^ t := Real.rpow_pos_of_pos hp_cast_pos t
  have hpow_sub_ne : (p : ℝ) ^ t - 1 ≠ 0 := (rough_rpow_sub_one_pos hp ht).ne'
  have hratio :
      (1 - (p : ℝ) ^ (-t)) / ((p : ℝ) ^ t - 1) = (p : ℝ) ^ (-t) := by
    rw [Real.rpow_neg hp_cast_pos.le]
    field_simp [hpow_pos.ne', hpow_sub_ne]
  calc
    roughKernel p n t * (Real.log (p : ℝ) / ((p : ℝ) ^ t - 1))
        = ((n : ℝ) ^ (-t)) * ((1 - (p : ℝ) ^ (-t)) / ((p : ℝ) ^ t - 1)) := by
            rw [roughKernel]
            field_simp [hlogp.ne', hpow_sub_ne]
    _ = ((n : ℝ) ^ (-t)) * (p : ℝ) ^ (-t) := by
          rw [hratio]
    _ = (((p * n : ℕ) : ℝ) ^ (-t)) := by
          have hmul :
              (((p * n : ℕ) : ℝ) ^ (-t)) = (p : ℝ) ^ (-t) * (n : ℝ) ^ (-t) := by
            simpa [Nat.cast_mul] using
              (Real.mul_rpow (show 0 ≤ (p : ℝ) by positivity)
                (show 0 ≤ (n : ℝ) by positivity) (z := -t))
          rw [hmul]
          ring

/-- Equation (1): the directly checked cases `p = 3, 5, 7`. -/
lemma harmonicLogAverage_small_cases {p : ℕ} (hp : p = 3 ∨ p = 5 ∨ p = 7) :
    harmonicLogAverage p ≤ roughLogBound p := by
  rcases hp with rfl | rfl | rfl
  · have hH3 : harmonicLogAverage 3 = Real.log 2 / 3 := by
      rw [harmonicLogAverage]
      have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by
        decide
      rw [hIcc]
      simp
      ring_nf
    have hR3 : roughLogBound 3 = 4 * Real.log 3 - 6 * Real.log 2 := by
      rw [roughLogBound]
      norm_num
      have h43 : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
        rw [show (4 / 3 : ℝ) = (4 : ℝ) / 3 by norm_num]
        rw [Real.log_div (by positivity) (by positivity)]
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
        ring
      rw [h43]
      ring
    rw [hH3, hR3]
    have hpow : 19 * Real.log 2 ≤ 12 * Real.log 3 := by
      have hlog : Real.log ((2 : ℝ) ^ 19) ≤ Real.log ((3 : ℝ) ^ 12) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · norm_num
      simpa [Real.log_pow] using hlog
    nlinarith
  · have hH5 : harmonicLogAverage 5 = (12 * Real.log 2 + 4 * Real.log 3) / 25 := by
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        calc
          Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log 2 := by
              simp [Real.log_pow]
      rw [harmonicLogAverage]
      have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by
        decide
      rw [hIcc]
      simp only [Finset.mem_insert, OfNat.one_ne_ofNat, Finset.mem_singleton, or_self,
        not_false_eq_true, Finset.sum_insert, Nat.cast_one, Real.log_one, div_one,
        Nat.reduceEqDiff, Nat.cast_ofNat, Finset.sum_singleton, zero_add, one_div, inv_one]
      ring_nf
      nlinarith [hlog4]
    have hR5 : roughLogBound 5 = 6 * Real.log 5 - 5 * Real.log 2 - 5 * Real.log 3 := by
      rw [roughLogBound]
      norm_num
      have h65 : Real.log (6 / 5 : ℝ) = Real.log 2 + Real.log 3 - Real.log 5 := by
        rw [show (6 / 5 : ℝ) = ((2 : ℝ) * 3) / 5 by norm_num]
        rw [Real.log_div (by positivity) (by positivity)]
        rw [Real.log_mul (by positivity) (by positivity)]
      rw [h65]
      ring
    rw [hH5, hR5]
    have h43 : 4 * Real.log 3 ≤ 13 * Real.log 2 := by
      have hlog : Real.log ((3 : ℝ) ^ 4) ≤ Real.log ((2 : ℝ) ^ 13) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · norm_num
      simpa [Real.log_pow] using hlog
    have h256 : 6 * Real.log 2 + 5 * Real.log 3 ≤ 6 * Real.log 5 := by
      have hlog : Real.log (((2 : ℝ) ^ 6) * ((3 : ℝ) ^ 5)) ≤ Real.log ((5 : ℝ) ^ 6) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · norm_num
      calc
        6 * Real.log 2 + 5 * Real.log 3
            = Real.log (((2 : ℝ) ^ 6) * ((3 : ℝ) ^ 5)) := by
                rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
                norm_num
        _ ≤ Real.log ((5 : ℝ) ^ 6) := hlog
        _ = 6 * Real.log 5 := by
            rw [Real.log_pow]
            norm_num
    have hleft : (12 * Real.log 2 + 4 * Real.log 3) / 25 ≤ Real.log 2 := by
      nlinarith
    have hright : Real.log 2 ≤ 6 * Real.log 5 - 5 * Real.log 2 - 5 * Real.log 3 := by
      linarith
    exact hleft.trans hright
  · have hH7 :
        harmonicLogAverage 7 =
          (70 * Real.log 2 + 30 * Real.log 3 + 12 * Real.log 5) / 147 := by
      have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        calc
          Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
          _ = 2 * Real.log 2 := by
              simp [Real.log_pow]
      have hlog6 : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
        calc
          Real.log (6 : ℝ) = Real.log ((2 : ℝ) * 3) := by norm_num
          _ = Real.log 2 + Real.log 3 := by
              rw [Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num)
                (show (3 : ℝ) ≠ 0 by norm_num)]
      rw [harmonicLogAverage]
      have hIcc : Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) := by
        decide
      rw [hIcc]
      simp only [Finset.mem_insert, OfNat.one_ne_ofNat, Finset.mem_singleton, or_self,
        not_false_eq_true, Finset.sum_insert, Nat.cast_one, Real.log_one, div_one,
        Nat.reduceEqDiff, Nat.cast_ofNat, Finset.sum_singleton, zero_add, one_div, inv_one]
      ring_nf
      nlinarith [hlog4, hlog6]
    have hR7 : roughLogBound 7 = 8 * Real.log 7 - 21 * Real.log 2 := by
      rw [roughLogBound]
      norm_num
      have h87 : Real.log (8 / 7 : ℝ) = 3 * Real.log 2 - Real.log 7 := by
        rw [show (8 / 7 : ℝ) = (8 : ℝ) / 7 by norm_num]
        rw [Real.log_div (by positivity) (by positivity)]
        rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow]
        ring
      rw [h87]
      ring
    rw [hH7, hR7]
    have h32 : 10 * Real.log 3 ≤ 16 * Real.log 2 := by
      have hlog : Real.log ((3 : ℝ) ^ 10) ≤ Real.log ((2 : ℝ) ^ 16) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · norm_num
      simpa [Real.log_pow] using hlog
    have h52 : 12 * Real.log 5 ≤ 29 * Real.log 2 := by
      have hlog : Real.log ((5 : ℝ) ^ 12) ≤ Real.log ((2 : ℝ) ^ 29) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · norm_num
      simpa [Real.log_pow] using hlog
    have h72 : 11 * Real.log 2 ≤ 4 * Real.log 7 := by
      have hlog : Real.log ((2 : ℝ) ^ 11) ≤ Real.log ((7 : ℝ) ^ 4) := by
        refine Real.log_le_log ?_ ?_
        · positivity
        · norm_num
      simpa [Real.log_pow] using hlog
    have hleft :
        (70 * Real.log 2 + 30 * Real.log 3 + 12 * Real.log 5) / 147 ≤ Real.log 2 := by
      nlinarith
    have hright : Real.log 2 ≤ 8 * Real.log 7 - 21 * Real.log 2 := by
      linarith
    exact hleft.trans hright

/-- Equation (2): the elementary bound valid for all `p ≥ 11`. -/
lemma harmonicLogAverage_le_roughLogBound_of_eleven_le {p : ℕ} (hp : 11 ≤ p) :
    harmonicLogAverage p ≤ roughLogBound p := by
  set S : ℝ := ∑ m ∈ Finset.Icc 1 (p - 1), Real.log (m : ℝ) / (m : ℝ)
  set H : ℝ := ∑ m ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (m : ℝ)
  set L : ℝ := Real.log (p : ℝ)
  have hp1 : 1 ≤ p := by omega
  have hp3 : 3 ≤ p - 1 := by omega
  have hp4 : 4 ≤ p - 1 := by omega
  have hp_pos : 0 < (p : ℝ) := by positivity
  have hden : L ≤ H := by
    calc
      L = ∫ x in (1 : ℝ)..(p : ℝ), 1 / x := by
        dsimp [L]
        rw [integral_one_div_of_pos (by norm_num) hp_pos, div_one]
      _ ≤ ∑ i ∈ Finset.range (p - 1), (1 : ℝ) / ((i + 1 : ℕ) : ℝ) := by
        have hsum :=
          (inv_antitoneOn_Icc_right (show (0 : ℝ) < 1 by norm_num)).integral_le_sum
            (x₀ := (1 : ℝ)) (a := p - 1)
        simpa [one_div, Nat.cast_add, Nat.cast_one, Nat.cast_sub hp1, add_comm, add_left_comm,
          add_assoc] using hsum
      _ = H := by
        dsimp [H]
        rw [Finset.range_eq_Ico]
        rw [Finset.sum_Ico_add' (fun i : ℕ => (1 : ℝ) / (i : ℝ)) 0 (p - 1) (c := 1)]
        simp [Finset.Ico_add_one_right_eq_Icc, one_div]
  have hanti :
      AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Icc (3 : ℝ) ((p - 1 : ℕ) : ℝ)) := by
    intro x hx y hy hxy
    exact Real.log_div_self_antitoneOn
      (le_trans Real.exp_one_lt_three.le hx.1)
      (le_trans Real.exp_one_lt_three.le hy.1)
      hxy
  have htail :
      (∑ m ∈ Finset.Icc 4 (p - 1), Real.log (m : ℝ) / (m : ℝ))
        ≤ ∫ x in (3 : ℝ)..(((p - 1 : ℕ) : ℝ)), Real.log x / x := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    rw [← Finset.sum_Ico_add' (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ)) 3 (p - 1) (c := 1)]
    exact @AntitoneOn.sum_le_integral_Ico 3 (p - 1) (fun x : ℝ => Real.log x / x) hp3
      (by simpa using hanti)
  have hS_split :
      S =
        Real.log 2 / 2 + Real.log 3 / 3 +
          ∑ m ∈ Finset.Icc 4 (p - 1), Real.log (m : ℝ) / (m : ℝ) := by
    dsimp [S]
    calc
      ∑ m ∈ Finset.Icc 1 (p - 1), Real.log (m : ℝ) / (m : ℝ)
          = ∑ m ∈ Finset.Icc 2 (p - 1), Real.log (m : ℝ) / (m : ℝ) := by
              rw [← Finset.insert_Icc_succ_left_eq_Icc (a := 1) (b := p - 1) (by omega : 1 ≤ p - 1)]
              rw [Finset.sum_insert] <;> simp
      _ = Real.log 2 / 2 + ∑ m ∈ Finset.Icc 3 (p - 1), Real.log (m : ℝ) / (m : ℝ) := by
            rw [← Finset.insert_Icc_succ_left_eq_Icc (a := 2) (b := p - 1) (by omega : 2 ≤ p - 1)]
            rw [Finset.sum_insert] <;> simp
      _ = Real.log 2 / 2 +
            (Real.log 3 / 3 + ∑ m ∈ Finset.Icc 4 (p - 1), Real.log (m : ℝ) / (m : ℝ)) := by
            rw [← Finset.insert_Icc_succ_left_eq_Icc (a := 3) (b := p - 1) (by omega : 3 ≤ p - 1)]
            rw [Finset.sum_insert] <;> simp
      _ = Real.log 2 / 2 + Real.log 3 / 3 +
            ∑ m ∈ Finset.Icc 4 (p - 1), Real.log (m : ℝ) / (m : ℝ) := by
            ring
  let F : ℝ → ℝ := fun x => (Real.log x) ^ 2 / 2
  have hab_real : (3 : ℝ) ≤ (((p - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hp3
  have hFderiv :
      ∀ x ∈ Set.uIcc (3 : ℝ) (((p - 1 : ℕ) : ℝ)), HasDerivAt F (Real.log x / x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (3 : ℝ) (((p - 1 : ℕ) : ℝ)) := by
      simpa [Set.uIcc_of_le hab_real] using hx
    have hx0 : x ≠ 0 := by
      linarith [hxIcc.1]
    simpa [F, one_div, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (((Real.hasDerivAt_log hx0).pow 2).div_const (2 : ℝ))
  have hFint :
      IntervalIntegrable (fun x : ℝ => Real.log x / x) volume (3 : ℝ) (((p - 1 : ℕ) : ℝ)) := by
    have hanti_u :
        AntitoneOn (fun x : ℝ => Real.log x / x) (Set.uIcc (3 : ℝ) (((p - 1 : ℕ) : ℝ))) := by
      simpa [Set.uIcc_of_le hab_real] using hanti
    exact hanti_u.intervalIntegrable
  have hInt :
      ∫ x in (3 : ℝ)..(((p - 1 : ℕ) : ℝ)), Real.log x / x
        = (Real.log (((p - 1 : ℕ) : ℝ))) ^ 2 / 2 - (Real.log (3 : ℝ)) ^ 2 / 2 := by
    simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt hFderiv hFint
  set c : ℝ := Real.log 2 / 2 + Real.log 3 / 3 - (Real.log 3) ^ 2 / 2
  have hlog2 : Real.log 2 ≤ (7 : ℝ) / 10 := by
    linarith [Real.log_two_lt_d9]
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    simpa using Real.exp_one_lt_three
  have hc_aux : Real.log 3 / 3 - (Real.log 3) ^ 2 / 2 ≤ -(1 : ℝ) / 6 := by
    nlinarith [le_of_lt hlog3]
  have hc : c ≤ (11 : ℝ) / 60 := by
    dsimp [c]
    nlinarith
  have hlog11_part : (2 : ℝ) / 11 ≤ Real.log ((11 : ℝ) / 9) := by
    have hpos : 0 < (11 : ℝ) / 9 := by positivity
    calc
      (2 : ℝ) / 11 = 1 - ((11 : ℝ) / 9)⁻¹ := by norm_num
      _ ≤ Real.log ((11 : ℝ) / 9) := Real.one_sub_inv_le_log_of_pos hpos
  have hlog11 : (24 : ℝ) / 11 ≤ Real.log (11 : ℝ) := by
    have hlog9 : 2 * Real.log 3 = Real.log (9 : ℝ) := by
      calc
        2 * Real.log 3 = Real.log 3 + Real.log 3 := by ring
        _ = Real.log (3 * 3 : ℝ) := by
          rw [← Real.log_mul (show (3 : ℝ) ≠ 0 by norm_num) (show (3 : ℝ) ≠ 0 by norm_num)]
        _ = Real.log (9 : ℝ) := by norm_num
    calc
      (24 : ℝ) / 11 = 2 + (2 : ℝ) / 11 := by norm_num
      _ ≤ 2 * Real.log 3 + Real.log ((11 : ℝ) / 9) := by
        nlinarith [hlog3, hlog11_part]
      _ = Real.log (11 : ℝ) := by
        rw [hlog9, ← Real.log_mul (show (9 : ℝ) ≠ 0 by norm_num)
          (show ((11 : ℝ) / 9) ≠ 0 by positivity)]
        norm_num
  have hL_lower : (24 : ℝ) / 11 ≤ L := by
    calc
      (24 : ℝ) / 11 ≤ Real.log (11 : ℝ) := hlog11
      _ ≤ L := by
        dsimp [L]
        exact Real.log_le_log (by positivity : 0 < (11 : ℝ)) (by exact_mod_cast hp)
  have hS_le :
      S ≤ L ^ 2 / 2 + c := by
    have hlog_sub_nonneg : 0 ≤ Real.log (((p - 1 : ℕ) : ℝ)) := by
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ p - 1)
    have hlog_sub_le : Real.log (((p - 1 : ℕ) : ℝ)) ≤ L := by
      dsimp [L]
      apply Real.log_le_log
      · exact_mod_cast (by omega : 0 < p - 1)
      · exact_mod_cast Nat.sub_le p 1
    have hsq : (Real.log (((p - 1 : ℕ) : ℝ))) ^ 2 ≤ L ^ 2 := by
      nlinarith
    calc
      S = Real.log 2 / 2 + Real.log 3 / 3 +
            ∑ m ∈ Finset.Icc 4 (p - 1), Real.log (m : ℝ) / (m : ℝ) := hS_split
      _ ≤ Real.log 2 / 2 + Real.log 3 / 3 +
            ∫ x in (3 : ℝ)..(((p - 1 : ℕ) : ℝ)), Real.log x / x := by
          gcongr
      _ = Real.log 2 / 2 + Real.log 3 / 3 +
            ((Real.log (((p - 1 : ℕ) : ℝ))) ^ 2 / 2 - (Real.log (3 : ℝ)) ^ 2 / 2) := by
          rw [hInt]
      _ ≤ Real.log 2 / 2 + Real.log 3 / 3 + (L ^ 2 / 2 - (Real.log 3) ^ 2 / 2) := by
          have hsq_half : (Real.log (((p - 1 : ℕ) : ℝ))) ^ 2 / 2 ≤ L ^ 2 / 2 := by
            exact div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2)
          linarith
      _ = L ^ 2 / 2 + c := by
          dsimp [c]
          ring
  have hS_main : S ≤ L ^ 2 - L := by
    calc
      S ≤ L ^ 2 / 2 + c := hS_le
      _ ≤ L ^ 2 / 2 + (11 : ℝ) / 60 := by
        gcongr
      _ ≤ L ^ 2 - L := by
        nlinarith [hL_lower]
  have hL_pos : 0 < L := by
    nlinarith [hL_lower]
  have hH_pos : 0 < H := lt_of_lt_of_le hL_pos hden
  have hfrac : S / H ≤ L - 1 := by
    apply (div_le_iff₀ hH_pos).2
    calc
      S ≤ L ^ 2 - L := hS_main
      _ = (L - 1) * L := by ring
      _ ≤ (L - 1) * H := by
        have hLm1_nonneg : 0 ≤ L - 1 := by
          nlinarith [hL_lower]
        gcongr
  have hrough : L - 1 ≤ roughLogBound p := by
    dsimp [L, roughLogBound]
    have hmul : (p : ℝ) * Real.log (1 + 1 / (p : ℝ)) ≤ 1 := by
      have hpos : 0 < 1 + 1 / (p : ℝ) := by positivity
      calc
        (p : ℝ) * Real.log (1 + 1 / (p : ℝ))
            ≤ (p : ℝ) * ((1 + 1 / (p : ℝ)) - 1) := by
              gcongr
              exact Real.log_le_sub_one_of_pos hpos
        _ = (p : ℝ) * (1 / (p : ℝ)) := by ring
        _ = 1 := by
          field_simp [show (p : ℝ) ≠ 0 by positivity]
    linarith
  simpa [harmonicLogAverage, S, H, L] using hfrac.trans hrough

lemma hpLogAverage_one_eq_harmonicLogAverage (p : ℕ) :
    hpLogAverage p 1 = harmonicLogAverage p := by
  have hnum :
      (∑ m ∈ Finset.Icc 1 (p - 1), Real.log (m : ℝ) / Real.rpow (m : ℝ) 1) =
        ∑ m ∈ Finset.Icc 1 (p - 1), Real.log (m : ℝ) / (m : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp
  have hden :
      (∑ m ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / Real.rpow (m : ℝ) 1) =
        ∑ m ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / (m : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro m hm
    simp
  rw [hpLogAverage, harmonicLogAverage, Hp, hnum, hden]

lemma hpLogAverage_antitoneOn {p : ℕ} (hp2 : 2 ≤ p) :
    AntitoneOn (hpLogAverage p) (Set.Ici (1 : ℝ)) := by
      sorry
/-- For `s > 1`, the `m^{-s}`-weighted logarithmic average is at most the harmonic one. -/
lemma hpLogAverage_le_harmonicLogAverage {p : ℕ} (hp2 : 2 ≤ p) {s : ℝ} (hs : 1 < s) :
    hpLogAverage p s ≤ harmonicLogAverage p := by
  calc
    hpLogAverage p s ≤ hpLogAverage p 1 := by
      exact hpLogAverage_antitoneOn hp2 (by simp) hs.le hs.le
    _ = harmonicLogAverage p := hpLogAverage_one_eq_harmonicLogAverage p

/-- Sub-lemma 1 of `B/f1.tex`. -/
lemma hpLogAverage_le_roughLogBound {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {s : ℝ} (hs : 1 < s) :
    hpLogAverage p s ≤ roughLogBound p := by
  refine (hpLogAverage_le_harmonicLogAverage hp.two_le hs).trans ?_
  by_cases h11 : 11 ≤ p
  · exact harmonicLogAverage_le_roughLogBound_of_eleven_le h11
  · have hp_lt : p < 11 := lt_of_not_ge h11
    have hsmall : p = 3 ∨ p = 5 ∨ p = 7 := by
      interval_cases p
      · exfalso
        exact Nat.not_prime_zero hp
      · exfalso
        exact Nat.not_prime_one hp
      · exfalso
        exact hodd rfl
      · simp
      · exfalso
        norm_num at hp
      · simp
      · exfalso
        norm_num at hp
      · simp
      · exfalso
        norm_num at hp
      · exfalso
        norm_num at hp
      · exfalso
        norm_num at hp
    exact harmonicLogAverage_small_cases hsmall

/-- The completely multiplicative weight `n ↦ n^{-s}`. -/
private noncomputable def inverseRpowHom (s : ℝ) : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ s)⁻¹
  map_one' := by simp
  map_mul' m n := by
    simp [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      mul_inv_rev, mul_comm]

/-- If `a ≤ b` and `x ≤ y`, then the mixed inverse powers satisfy the expected rearrangement
inequality. -/
private lemma inv_rpow_mul_inv_rpow_le_inv_rpow_mul_inv_rpow
    {x y : ℝ} (hxy : x ≤ y) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (((a : ℝ) ^ x)⁻¹) * (((b : ℝ) ^ y)⁻¹) ≤
      (((a : ℝ) ^ y)⁻¹) * (((b : ℝ) ^ x)⁻¹) := by
  let d : ℝ := y - x
  have hd : 0 ≤ d := sub_nonneg.mpr hxy
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  have hb0 : 0 < (b : ℝ) := lt_of_lt_of_le ha0 (by exact_mod_cast hab)
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hpow : (a : ℝ) ^ d ≤ (b : ℝ) ^ d :=
    Real.rpow_le_rpow ha0.le habR hd
  have hcommon : 0 ≤ (a : ℝ) ^ x * (b : ℝ) ^ x := by positivity
  have hden' :
      (a : ℝ) ^ d * ((a : ℝ) ^ x * (b : ℝ) ^ x) ≤
        (b : ℝ) ^ d * ((a : ℝ) ^ x * (b : ℝ) ^ x) :=
    mul_le_mul_of_nonneg_right hpow hcommon
  have hden :
      (a : ℝ) ^ y * (b : ℝ) ^ x ≤ (a : ℝ) ^ x * (b : ℝ) ^ y := by
    calc
      (a : ℝ) ^ y * (b : ℝ) ^ x
          = (a : ℝ) ^ d * ((a : ℝ) ^ x * (b : ℝ) ^ x) := by
              rw [show y = d + x by
                    dsimp [d]
                    linarith,
                Real.rpow_add ha0, mul_assoc]
      _ ≤ (b : ℝ) ^ d * ((a : ℝ) ^ x * (b : ℝ) ^ x) := hden'
      _ = (a : ℝ) ^ x * (b : ℝ) ^ y := by
            calc
              (b : ℝ) ^ d * ((a : ℝ) ^ x * (b : ℝ) ^ x)
                  = (a : ℝ) ^ x * ((b : ℝ) ^ d * (b : ℝ) ^ x) := by ring
              _ = (a : ℝ) ^ x * (b : ℝ) ^ (d + x) := by
                    rw [← Real.rpow_add hb0]
              _ = (a : ℝ) ^ x * (b : ℝ) ^ y := by
                    have hdx : d + x = y := by
                      dsimp [d]
                      linarith
                    rw [hdx]
  have hleftPos : 0 < (a : ℝ) ^ x * (b : ℝ) ^ y := by positivity
  have hrightPos : 0 < (a : ℝ) ^ y * (b : ℝ) ^ x := by positivity
  have hinv :
      ((a : ℝ) ^ x * (b : ℝ) ^ y)⁻¹ ≤ ((a : ℝ) ^ y * (b : ℝ) ^ x)⁻¹ :=
    (inv_le_inv₀ hleftPos hrightPos).2 hden
  simpa [mul_comm, mul_left_comm, mul_assoc, mul_inv_rev] using hinv

/-- Sub-lemma 2 of `B/f1.tex`. -/
lemma monotoneOn_Qp {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    MonotoneOn (Qp p) (Set.Ioi (1 : ℝ)) := by
  classical
  have hp_two_le : 2 ≤ p := hp.two_le
  have hp_gt_two : 2 < p := lt_of_le_of_ne hp_two_le (Ne.symm hodd)
  have hp_gt_one : 1 < p := lt_trans (by decide) hp_gt_two
  let S : Set p.smoothNumbers := {m | (m : ℕ) < p}
  let smallEquiv : ↥S ≃ {m : ℕ // m ∈ Finset.Icc 1 (p - 1)} :=
    { toFun := fun m => ⟨(m : ℕ), by
        have hm0 : 0 < (m : ℕ) := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers m.1.2)
        exact Finset.mem_Icc.mpr ⟨hm0, Nat.le_pred_of_lt m.2⟩⟩
      invFun := fun m => by
        have hm0 : 0 < (m : ℕ) := (Finset.mem_Icc.mp m.2).1
        have hmle : (m : ℕ) ≤ p - 1 := (Finset.mem_Icc.mp m.2).2
        have hmlt : (m : ℕ) < p := by omega
        exact ⟨⟨(m : ℕ), Nat.mem_smoothNumbers_of_lt hm0 hmlt⟩, hmlt⟩
      left_inv := by
        intro m
        ext
        rfl
      right_inv := by
        intro m
        ext
        rfl }
  haveI : Fintype ↥S := Fintype.ofEquiv {m : ℕ // m ∈ Finset.Icc 1 (p - 1)} smallEquiv.symm
  let H : ℝ → ℝ := fun s => ∑ m : ↥S, ((m : ℝ) ^ s)⁻¹
  let tail : ℝ → ℝ := fun s => ∑' m : ↥(Sᶜ), ((m : ℝ) ^ s)⁻¹
  have hprimesBelow :
      p.primesBelow = (Finset.Icc 2 (p - 1)).filter Nat.Prime := by
    ext ℓ
    constructor
    · intro hℓ
      rcases Nat.mem_primesBelow.mp hℓ with ⟨hℓlt, hℓprime⟩
      refine Finset.mem_filter.mpr ?_
      exact ⟨Finset.mem_Icc.mpr ⟨hℓprime.two_le, Nat.le_pred_of_lt hℓlt⟩, hℓprime⟩
    · intro hℓ
      rcases Finset.mem_filter.mp hℓ with ⟨hℓIcc, hℓprime⟩
      rcases Finset.mem_Icc.mp hℓIcc with ⟨_, hℓle⟩
      refine Nat.mem_primesBelow.mpr ?_
      have hℓlt : ℓ < p := by omega
      exact ⟨hℓlt, hℓprime⟩
  have hsumNat (s : ℝ) (hs : 1 < s) : Summable (inverseRpowHom s : ℕ → ℝ) := by
    simpa [inverseRpowHom] using (Real.summable_nat_rpow_inv.mpr hs)
  have hHp_tsum (s : ℝ) : Hp p s = ∑' m : ↥S, ((m : ℝ) ^ s)⁻¹ := by
    calc
      Hp p s = ∑ m ∈ Finset.Icc 1 (p - 1), ((m : ℝ) ^ s)⁻¹ := by
        simp [Hp, one_div]
      _ = ∑ m : {m : ℕ // m ∈ Finset.Icc 1 (p - 1)}, ((m : ℝ) ^ s)⁻¹ := by
          symm
          exact Finset.sum_attach (Finset.Icc 1 (p - 1)) (fun m => ((m : ℝ) ^ s)⁻¹)
      _ = ∑ m : ↥S, ((m : ℝ) ^ s)⁻¹ := by
          symm
          exact Fintype.sum_equiv smallEquiv
            (fun m : ↥S => ((m : ℝ) ^ s)⁻¹)
            (fun m : {m : ℕ // m ∈ Finset.Icc 1 (p - 1)} => ((m : ℝ) ^ s)⁻¹)
            (by intro m; rfl)
      _ = ∑' m : ↥S, ((m : ℝ) ^ s)⁻¹ := by
          rw [tsum_fintype]
  have hQformula (s : ℝ) (hs : 1 < s) :
      Qp p s = H s / (H s + tail s) := by
    have hsmoothSummable : Summable (fun m : p.smoothNumbers => ((m : ℝ) ^ s)⁻¹) :=
      (hsumNat s hs).subtype p.smoothNumbers
    have hsmoothSplit :
        ∑' m : p.smoothNumbers, ((m : ℝ) ^ s)⁻¹ =
          ∑' m : ↥S, ((m : ℝ) ^ s)⁻¹ + tail s := by
      simpa [S, tail] using (hsmoothSummable.tsum_subtype_add_tsum_subtype_compl S).symm
    have hsmoothEuler :
        (∏ ℓ ∈ (Finset.Icc 2 (p - 1)).filter Nat.Prime, (1 - ((ℓ : ℝ) ^ s)⁻¹)⁻¹) =
          ∑' m : p.smoothNumbers, ((m : ℝ) ^ s)⁻¹ := by
      rw [← hprimesBelow]
      simpa [inverseRpowHom] using
        (EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers
          (f := inverseRpowHom s) (hsumNat s hs) p)
    have hsmoothEuler' :
        ∏ ℓ ∈ (Finset.Icc 2 (p - 1)).filter Nat.Prime, (1 - 1 / Real.rpow (ℓ : ℝ) s) =
          (∑' m : p.smoothNumbers, ((m : ℝ) ^ s)⁻¹)⁻¹ := by
      apply inv_injective
      simpa [one_div, Finset.prod_inv_distrib] using hsmoothEuler
    calc
      Qp p s = Hp p s / (∑' m : p.smoothNumbers, ((m : ℝ) ^ s)⁻¹) := by
        rw [Qp, hsmoothEuler', div_eq_mul_inv]
      _ = (∑' m : ↥S, ((m : ℝ) ^ s)⁻¹) /
            ((∑' m : ↥S, ((m : ℝ) ^ s)⁻¹) + tail s) := by
        rw [hHp_tsum s, hsmoothSplit]
      _ = H s / (H s + tail s) := by
        simp [H]
  intro x hx y hy hxy
  have htailSummable (s : ℝ) (hs : 1 < s) :
      Summable (fun m : ↥(Sᶜ) => ((m : ℝ) ^ s)⁻¹) :=
    ((hsumNat s hs).subtype p.smoothNumbers).subtype Sᶜ
  have hstep (a : ↥S) :
      ((a : ℝ) ^ x)⁻¹ * tail y ≤ ((a : ℝ) ^ y)⁻¹ * tail x := by
    have ha_pos : 0 < (a : ℕ) := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers a.1.2)
    have ha_one : 1 ≤ (a : ℕ) := Nat.succ_le_of_lt ha_pos
    calc
      ((a : ℝ) ^ x)⁻¹ * tail y
          = ∑' b : ↥(Sᶜ), ((a : ℝ) ^ x)⁻¹ * ((b : ℝ) ^ y)⁻¹ := by
              change ((a : ℝ) ^ x)⁻¹ * (∑' b : ↥(Sᶜ), ((b : ℝ) ^ y)⁻¹) =
                ∑' b : ↥(Sᶜ), ((a : ℝ) ^ x)⁻¹ * ((b : ℝ) ^ y)⁻¹
              rw [tsum_mul_left]
      _ ≤ ∑' b : ↥(Sᶜ), ((a : ℝ) ^ y)⁻¹ * ((b : ℝ) ^ x)⁻¹ := by
            apply Summable.tsum_le_tsum
            · intro b
              have hb_ge : p ≤ (b : ℕ) := Nat.not_lt.mp b.2
              exact inv_rpow_mul_inv_rpow_le_inv_rpow_mul_inv_rpow hxy ha_one
                (le_trans (Nat.le_of_lt a.2) hb_ge)
            · exact Summable.mul_left _ (htailSummable y hy)
            · exact Summable.mul_left _ (htailSummable x hx)
      _ = ((a : ℝ) ^ y)⁻¹ * tail x := by
            change ∑' b : ↥(Sᶜ), ((a : ℝ) ^ y)⁻¹ * ((b : ℝ) ^ x)⁻¹ =
              ((a : ℝ) ^ y)⁻¹ * (∑' b : ↥(Sᶜ), ((b : ℝ) ^ x)⁻¹)
            rw [tsum_mul_left]
  have hcross : H x * tail y ≤ H y * tail x := by
    change (∑ m : ↥S, ((m : ℝ) ^ x)⁻¹) * tail y ≤
      (∑ m : ↥S, ((m : ℝ) ^ y)⁻¹) * tail x
    rw [Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_le_sum (fun a _ => hstep a)
  let oneSmall : ↥S := ⟨⟨1, Nat.mem_smoothNumbers_of_lt (by decide) hp_gt_one⟩, hp_gt_one⟩
  have hH_pos (s : ℝ) : 0 < H s := by
    have hterm : 0 < ((oneSmall : ℝ) ^ s)⁻¹ := by
      simp [oneSmall]
    have hle : ((oneSmall : ℝ) ^ s)⁻¹ ≤ H s := by
      simpa using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset ↥S))
          (f := fun m : ↥S => ((m : ℝ) ^ s)⁻¹)
          (fun m _ => by positivity)
          (by simp [oneSmall]))
    exact lt_of_lt_of_le hterm hle
  have htail_nonneg (s : ℝ) : 0 ≤ tail s := by
    exact tsum_nonneg (fun _ => by positivity)
  have hden_pos (s : ℝ) : 0 < H s + tail s := by
    linarith [hH_pos s, htail_nonneg s]
  have hfrac : H x / (H x + tail x) ≤ H y / (H y + tail y) := by
    refine (div_le_div_iff₀ (hden_pos x) (hden_pos y)).2 ?_
    nlinarith [hcross]
  rw [hQformula x hx, hQformula y hy]
  exact hfrac

noncomputable def blockDiff (p k j : ℕ) (s : ℝ) : ℝ :=
  1 / Real.rpow (((k + 1) * p : ℕ) : ℝ) s -
    1 / Real.rpow (((k + 1) * p + j : ℕ) : ℝ) s

lemma log_one_add_div_antitoneOn :
    AntitoneOn (fun x : ℝ => Real.log (1 + x) / x) (Set.Ioi (0 : ℝ)) := by
  have hanti :=
    strictConcaveOn_log_Ioi.concaveOn.antitoneOn_slope_gt
      (show (1 : ℝ) ∈ Set.Ioi (0 : ℝ) by norm_num)
  intro x hx y hy hxy
  have hx0' : 0 < x := hx
  have hy0' : 0 < y := hy
  have hxmem : 1 + x ∈ {z : ℝ | z ∈ Set.Ioi (0 : ℝ) ∧ 1 < z} := by
    constructor
    · change 0 < 1 + x
      linarith
    · change 1 < 1 + x
      linarith
  have hymem : 1 + y ∈ {z : ℝ | z ∈ Set.Ioi (0 : ℝ) ∧ 1 < z} := by
    constructor
    · change 0 < 1 + y
      linarith
    · change 1 < 1 + y
      linarith
  have hmain :
      slope Real.log 1 (1 + y) ≤ slope Real.log 1 (1 + x) := by
    exact hanti hxmem hymem (by linarith)
  have hx0 : x ≠ 0 := hx0'.ne'
  have hy0 : y ≠ 0 := hy0'.ne'
  simpa [slope, Real.log_one, hx0, hy0, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hmain

lemma roughLogBoundCore_monotoneOn :
    MonotoneOn
      (fun x : ℝ => Real.log x - x * Real.log (1 + 1 / x))
      (Set.Ioi (0 : ℝ)) := by
        sorry
lemma Hp_pos {p : ℕ} (hp2 : 2 ≤ p) {s : ℝ} :
    0 < Hp p s := by
  have hmem : 1 ∈ Finset.Icc 1 (p - 1) := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hle :
      (1 : ℝ) / ((1 : ℝ) ^ s) ≤ Hp p s := by
    have hle' :
        (1 : ℝ) / ((1 : ℝ) ^ s) ≤
          ∑ m ∈ Finset.Icc 1 (p - 1), (1 : ℝ) / Real.rpow (m : ℝ) s := by
      simpa using
        (Finset.single_le_sum
          (f := fun m : ℕ => (1 : ℝ) / Real.rpow (m : ℝ) s)
          (fun m hm => by
            have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
            have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm1
            exact div_nonneg (by positivity) (Real.rpow_pos_of_pos hm0 s).le)
          hmem)
    simpa [Hp] using hle'
  have hone : 0 < (1 : ℝ) / ((1 : ℝ) ^ s) := by
    simp
  exact lt_of_lt_of_le hone hle

lemma Hp_hasDerivAt {p : ℕ} {s : ℝ} :
    HasDerivAt (Hp p)
      (-(∑ m ∈ Finset.Icc 1 (p - 1), Real.log (m : ℝ) / Real.rpow (m : ℝ) s)) s := by
        sorry
lemma blockDiff_nonneg {p k j : ℕ} (hp2 : 2 ≤ p) (_hj1 : 1 ≤ j) {s : ℝ} (hs : 1 < s) :
    0 ≤ blockDiff p k j s := by
  have hs0 : 0 ≤ s := by linarith
  have hp0 : 0 < p := by omega
  have ha_pos : 0 < (((k + 1) * p : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos _) hp0
  have hab : (((k + 1) * p : ℕ) : ℝ) ≤ ((((k + 1) * p + j : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right ((k + 1) * p) j
  have hpow :
      Real.rpow (((k + 1) * p : ℕ) : ℝ) s ≤
        Real.rpow ((((k + 1) * p + j : ℕ) : ℕ) : ℝ) s := by
    exact Real.rpow_le_rpow ha_pos.le hab hs0
  exact sub_nonneg.mpr <|
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos ha_pos s) hpow

lemma blockDiff_hasDerivAt {p k j : ℕ} (hp2 : 2 ≤ p) (hj1 : 1 ≤ j) {s : ℝ} :
    HasDerivAt (blockDiff p k j)
      (-Real.log (((k + 1) * p : ℕ) : ℝ) / Real.rpow (((k + 1) * p : ℕ) : ℝ) s +
        Real.log (((k + 1) * p + j : ℕ) : ℝ) /
          Real.rpow (((k + 1) * p + j : ℕ) : ℝ) s) s := by
            sorry
lemma blockDiff_deriv_le_neg_roughLogBound_mul {p : ℕ} (hp : p.Prime)
    {t : ℝ} (ht : 1 < t) (k j : ℕ) (hj1 : 1 ≤ j) :
    (-Real.log (((k + 1) * p : ℕ) : ℝ) / Real.rpow (((k + 1) * p : ℕ) : ℝ) t +
        Real.log (((k + 1) * p + j : ℕ) : ℝ) /
          Real.rpow (((k + 1) * p + j : ℕ) : ℝ) t) ≤
      -roughLogBound p * blockDiff p k j t := by
  let a : ℕ := (k + 1) * p
  let x : ℝ := (j : ℝ) / (a : ℝ)
  have ha_pos_nat : 0 < a := by
    dsimp [a]
    exact Nat.mul_pos (Nat.succ_pos _) hp.pos
  have ha_pos : 0 < (a : ℝ) := by
    exact_mod_cast ha_pos_nat
  have ha_nonneg : 0 ≤ (a : ℝ) := ha_pos.le
  have hxa : 1 / (a : ℝ) ≤ x := by
    dsimp [x]
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    field_simp [ha_pos.ne']
    nlinarith
  have hx_pos : 0 < x := lt_of_lt_of_le (by positivity) hxa
  have h1x_pos : 0 < 1 + x := by linarith
  have h1x_one : 1 < 1 + x := by linarith
  have hb_eq :
      (((k + 1) * p + j : ℕ) : ℝ) = (a : ℝ) * (1 + x) := by
    dsimp [a, x]
    have hmul_div :
        (((k + 1) * p : ℕ) : ℝ) * ((j : ℝ) / (((k + 1) * p : ℕ) : ℝ)) = (j : ℝ) := by
      calc
        (((k + 1) * p : ℕ) : ℝ) * ((j : ℝ) / (((k + 1) * p : ℕ) : ℝ))
            = (((k + 1) * p : ℕ) : ℝ) * (j : ℝ) *
                ((((k + 1) * p : ℕ) : ℝ)⁻¹) := by
                  rw [div_eq_mul_inv]
                  ring
        _ = (j : ℝ) * ((((k + 1) * p : ℕ) : ℝ) * ((((k + 1) * p : ℕ) : ℝ)⁻¹)) := by
              ring
        _ = (j : ℝ) * 1 := by
              rw [mul_inv_cancel₀ ha_pos.ne']
        _ = (j : ℝ) := by ring
    calc
      (((k + 1) * p + j : ℕ) : ℝ) = (((k + 1) * p : ℕ) : ℝ) + (j : ℝ) := by
            rw [Nat.cast_add]
      _ = (((k + 1) * p : ℕ) : ℝ) +
            (((k + 1) * p : ℕ) : ℝ) * ((j : ℝ) / (((k + 1) * p : ℕ) : ℝ)) := by
            rw [hmul_div]
      _ = (((k + 1) * p : ℕ) : ℝ) * (1 + (j : ℝ) / (((k + 1) * p : ℕ) : ℝ)) := by
            ring
  have hlogb :
      Real.log (((k + 1) * p + j : ℕ) : ℝ) = Real.log (a : ℝ) + Real.log (1 + x) := by
    rw [hb_eq, Real.log_mul (by positivity) (by positivity)]
  have hrpowb :
      Real.rpow (((k + 1) * p + j : ℕ) : ℝ) t =
        Real.rpow (a : ℝ) t * Real.rpow (1 + x) t := by
    rw [hb_eq]
    simpa using (Real.mul_rpow ha_nonneg h1x_pos.le (z := t))
  have hblock_eq :
      blockDiff p k j t =
        (Real.rpow (a : ℝ) t)⁻¹ * (1 - (Real.rpow (1 + x) t)⁻¹) := by
    rw [blockDiff]
    change 1 / Real.rpow (a : ℝ) t - 1 / Real.rpow (((k + 1) * p + j : ℕ) : ℝ) t =
      (Real.rpow (a : ℝ) t)⁻¹ * (1 - (Real.rpow (1 + x) t)⁻¹)
    rw [hb_eq]
    rw [show Real.rpow ((a : ℝ) * (1 + x)) t =
        Real.rpow (a : ℝ) t * Real.rpow (1 + x) t by
          simpa using (Real.mul_rpow ha_nonneg h1x_pos.le (z := t))]
    field_simp [Real.rpow_pos_of_pos ha_pos t, Real.rpow_pos_of_pos h1x_pos t]
  have hderiv_eq :
      -Real.log (((k + 1) * p : ℕ) : ℝ) / Real.rpow (((k + 1) * p : ℕ) : ℝ) t +
          Real.log (((k + 1) * p + j : ℕ) : ℝ) /
            Real.rpow (((k + 1) * p + j : ℕ) : ℝ) t =
        blockDiff p k j t *
          (-Real.log (a : ℝ) +
            Real.log (1 + x) / (Real.rpow (1 + x) t - 1)) := by
    change -Real.log (a : ℝ) / Real.rpow (a : ℝ) t +
          Real.log (((k + 1) * p + j : ℕ) : ℝ) /
            Real.rpow (((k + 1) * p + j : ℕ) : ℝ) t =
        blockDiff p k j t *
          (-Real.log (a : ℝ) +
            Real.log (1 + x) / (Real.rpow (1 + x) t - 1))
    have hw_pos : 0 < Real.rpow (1 + x) t := Real.rpow_pos_of_pos h1x_pos t
    have hw_ne : Real.rpow (1 + x) t ≠ 0 := hw_pos.ne'
    have hw_sub_ne : Real.rpow (1 + x) t - 1 ≠ 0 := by
      have ht_pos : 0 < t := lt_trans zero_lt_one ht
      have hpow_gt_one : 1 < Real.rpow (1 + x) t := Real.one_lt_rpow h1x_one ht_pos
      linarith
    rw [hblock_eq, hlogb, hrpowb]
    field_simp [Real.rpow_pos_of_pos ha_pos t, hw_pos, hw_ne, hw_sub_ne]
    ring
  have ht_ge_one : 1 ≤ t := ht.le
  have hbern :
      x ≤ Real.rpow (1 + x) t - 1 := by
    have htmp :
        1 + t * x ≤ Real.rpow (1 + x) t := by
      simpa [mul_comm] using
        (one_add_mul_self_le_rpow_one_add (s := x) (by linarith) (p := t) ht_ge_one)
    have hx_le_sx : x ≤ t * x := by
      nlinarith [ht_ge_one, hx_pos.le]
    linarith
  have hfrac1 :
      Real.log (1 + x) / (Real.rpow (1 + x) t - 1) ≤ Real.log (1 + x) / x := by
    have hlog_nonneg : 0 ≤ Real.log (1 + x) := by
      exact Real.log_nonneg h1x_one.le
    have hden_pos : 0 < Real.rpow (1 + x) t - 1 := by
      have ht_pos : 0 < t := lt_trans zero_lt_one ht
      have hpow_gt_one : 1 < Real.rpow (1 + x) t := Real.one_lt_rpow h1x_one ht_pos
      linarith
    exact div_le_div_of_nonneg_left hlog_nonneg hx_pos hbern
  have hfrac2 :
      Real.log (1 + x) / x ≤ (a : ℝ) * Real.log (1 + 1 / (a : ℝ)) := by
    have hanti := log_one_add_div_antitoneOn
    have haux :
        Real.log (1 + x) / x ≤
          Real.log (1 + 1 / (a : ℝ)) / (1 / (a : ℝ)) := by
      have hia_pos : 0 < 1 / (a : ℝ) := by positivity
      exact hanti hia_pos hx_pos hxa
    simpa [div_eq_mul_inv, ha_pos.ne', mul_comm, mul_left_comm, mul_assoc] using haux
  have hcore :
      roughLogBound p ≤ Real.log (a : ℝ) - (a : ℝ) * Real.log (1 + 1 / (a : ℝ)) := by
    have hmono := roughLogBoundCore_monotoneOn
    have hpa_nat : p ≤ a := by
      dsimp [a]
      simpa [Nat.mul_comm] using Nat.le_mul_of_pos_right p (Nat.succ_pos k)
    have hpa : (p : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hpa_nat
    have hpIoi : (p : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      change 0 < (p : ℝ)
      exact_mod_cast hp.pos
    have haIoi : (a : ℝ) ∈ Set.Ioi (0 : ℝ) := by
      change 0 < (a : ℝ)
      exact_mod_cast ha_pos_nat
    simpa [roughLogBound] using hmono hpIoi haIoi hpa
  have hbracket :
      -Real.log (a : ℝ) + Real.log (1 + x) / (Real.rpow (1 + x) t - 1) ≤
        -roughLogBound p := by
    linarith [hfrac1.trans hfrac2, hcore]
  have hblock_nonneg : 0 ≤ blockDiff p k j t := blockDiff_nonneg hp.two_le hj1 ht
  rw [hderiv_eq]
  have hmul :
      blockDiff p k j t *
          (-Real.log (a : ℝ) + Real.log (1 + x) / (Real.rpow (1 + x) t - 1)) ≤
        blockDiff p k j t * (-roughLogBound p) :=
    mul_le_mul_of_nonneg_left hbracket hblock_nonneg
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

lemma blockDiff_div_Hp_antitoneOn {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {k j : ℕ} (hj1 : 1 ≤ j) :
    AntitoneOn (fun t : ℝ => blockDiff p k j t / Hp p t) (Set.Ioi (1 : ℝ)) := by
      sorry
lemma summable_blockDiff_fin_div_Hp {p : ℕ} (hp : p.Prime) {t : ℝ} (ht : 1 < t) :
    Summable (fun k : ℕ => ∑ j : Fin p, blockDiff p k j t / Hp p t) := by
  have hHp_pos : 0 < Hp p t := Hp_pos hp.two_le (s := t)
  have hHp_nonneg : 0 ≤ Hp p t := hHp_pos.le
  have hbound :
      ∀ k : ℕ,
        ∑ j : Fin p, blockDiff p k j t / Hp p t ≤
          ((p : ℝ) / Hp p t) * (1 / Real.rpow ((k + 1 : ℕ) : ℝ) t) := by
    intro k
    have hterm :
        ∀ j : Fin p,
          blockDiff p k j t / Hp p t ≤
            (1 / Hp p t) * (1 / Real.rpow (((k + 1) * p : ℕ) : ℝ) t) := by
      intro j
      have hblock_le :
          blockDiff p k j t ≤ 1 / Real.rpow (((k + 1) * p : ℕ) : ℝ) t := by
        rw [blockDiff]
        have hbase_pos : 0 < ((((k + 1) * p + j : ℕ) : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_pos_left (Nat.mul_pos (Nat.succ_pos _) hp.pos) j
        have hnonneg : 0 ≤ 1 / Real.rpow (((k + 1) * p + j : ℕ) : ℝ) t := by
          exact one_div_nonneg.mpr (Real.rpow_pos_of_pos hbase_pos t).le
        linarith
      have hHp_inv_nonneg : 0 ≤ (Hp p t)⁻¹ := inv_nonneg.mpr hHp_nonneg
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hblock_le hHp_inv_nonneg
    calc
      ∑ j : Fin p, blockDiff p k j t / Hp p t
          ≤ ∑ j : Fin p, (1 / Hp p t) * (1 / Real.rpow (((k + 1) * p : ℕ) : ℝ) t) := by
              exact Finset.sum_le_sum (fun j _ => hterm j)
      _ = (p : ℝ) * ((1 / Hp p t) * (1 / Real.rpow (((k + 1) * p : ℕ) : ℝ) t)) := by
            simp
      _ = ((p : ℝ) / Hp p t) * (1 / Real.rpow (((k + 1) * p : ℕ) : ℝ) t) := by
            ring
      _ ≤ ((p : ℝ) / Hp p t) * (1 / Real.rpow ((k + 1 : ℕ) : ℝ) t) := by
            have hk_pos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
            have hkp : (((k + 1 : ℕ) : ℝ)) ≤ ((((k + 1) * p : ℕ) : ℝ)) := by
              exact_mod_cast Nat.le_mul_of_pos_right (k + 1) hp.pos
            have ht_nonneg : 0 ≤ t := by linarith
            have hpow :
                Real.rpow ((k + 1 : ℕ) : ℝ) t ≤
                  Real.rpow ((((k + 1) * p : ℕ) : ℝ)) t := by
              exact Real.rpow_le_rpow hk_pos.le hkp ht_nonneg
            have hinv :
                1 / Real.rpow (((k + 1) * p : ℕ) : ℝ) t ≤
                  1 / Real.rpow ((k + 1 : ℕ) : ℝ) t := by
              exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hk_pos t) hpow
            have hpR_nonneg : 0 ≤ (p : ℝ) / Hp p t := by
              exact div_nonneg (by exact_mod_cast hp.pos.le) hHp_nonneg
            exact mul_le_mul_of_nonneg_left hinv hpR_nonneg
  have hsum :
      Summable (fun k : ℕ => ((p : ℝ) / Hp p t) * (1 / Real.rpow ((k + 1 : ℕ) : ℝ) t)) := by
    exact Summable.mul_left _ (by simpa using zetaSeries_term_summable (s := t) ht)
  refine Summable.of_nonneg_of_le ?_ hbound hsum
  intro k
  refine Finset.sum_nonneg ?_
  intro j hj
  by_cases hj0 : (j : ℕ) = 0
  · simp [blockDiff, hj0]
  · exact div_nonneg
      (blockDiff_nonneg hp.two_le (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)) ht) hHp_nonneg

lemma zetaSeries_eq_Hp_add_blockTail {p : ℕ} (hp : p.Prime) {t : ℝ} (ht : 1 < t) :
    zetaSeries t = Hp p t + ∑' k : ℕ, ∑ j : Fin p,
      1 / Real.rpow ((((k + 1) * p + j : ℕ) : ℕ) : ℝ) t := by
        sorry
lemma tsum_blockDiff_fin_div_Hp_eq_formula {p : ℕ} (hp : p.Prime) {t : ℝ} (ht : 1 < t) :
    (∑' k : ℕ, ∑ j : Fin p, blockDiff p k j t / Hp p t) =
      1 - ((1 - Real.rpow (p : ℝ) (1 - t)) * zetaSeries t) / Hp p t := by
        sorry
lemma eulerFactor_hasDerivAt {ℓ : ℕ} (hℓprime : ℓ.Prime) {s : ℝ} :
    HasDerivAt (fun t : ℝ => 1 - 1 / Real.rpow (ℓ : ℝ) t)
      (Real.log (ℓ : ℝ) / Real.rpow (ℓ : ℝ) s) s := by
        sorry
lemma one_sub_hasDerivAt {s : ℝ} :
    HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
      sorry
lemma primeEulerProduct_hasDerivAt {p : ℕ} {s : ℝ} (hs : 1 < s) :
    HasDerivAt
      (fun t : ℝ =>
        ∏ ℓ ∈ (Finset.Icc 2 (p - 1)).filter Nat.Prime, (1 - 1 / Real.rpow (ℓ : ℝ) t))
      ((∏ ℓ ∈ (Finset.Icc 2 (p - 1)).filter Nat.Prime, (1 - 1 / Real.rpow (ℓ : ℝ) s)) *
        (∑ ℓ ∈ (Finset.Icc 2 (p - 1)).filter Nat.Prime,
          Real.log (ℓ : ℝ) / (Real.rpow (ℓ : ℝ) s - 1))) s := by
            sorry
lemma summable_vonMangoldt_div_rpow_if {v : ℝ} (hv : 0 < v) {P : ℕ → Prop}
    [DecidablePred P]
    (hP : ∀ {q : ℕ}, P q → 2 ≤ q) :
    Summable (fun q : ℕ =>
      if _hq : P q then
        ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v)
      else
        0) := by
  have hvhalf : 0 < v / 2 := by
    linarith
  have hmajorant : Summable (fun q : ℕ => (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹)) := by
    have hbase : Summable (fun q : ℕ => (((q : ℝ) ^ (1 + v / 2))⁻¹)) := by
      exact (Real.summable_nat_rpow_inv).2 (by linarith)
    exact hbase.mul_left (2 / v)
  refine Summable.of_nonneg_of_le
    (f := fun q : ℕ => (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹)) ?_ ?_ hmajorant
  · intro q
    by_cases hq : P q
    · have hqpos : 0 < (q : ℝ) := by
        exact_mod_cast lt_of_lt_of_le zero_lt_two (hP hq)
      have hqpow : 0 < Real.rpow (q : ℝ) (1 + v) := Real.rpow_pos_of_pos hqpos _
      simpa [hq] using
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hqpow.le :
          0 ≤ ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v))
    · simp [hq]
  · intro q
    by_cases hq : P q
    · have hq2 : 2 ≤ q := hP hq
      have hq0 : 0 ≤ (q : ℝ) := by positivity
      have hqpos : 0 < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_two hq2
      have hqpow : 0 < Real.rpow (q : ℝ) (1 + v) := Real.rpow_pos_of_pos hqpos _
      have hlog : ArithmeticFunction.vonMangoldt q ≤ Real.log (q : ℝ) := by
        simpa using ArithmeticFunction.vonMangoldt_le_log (n := q)
      have hlog' : Real.log (q : ℝ) ≤ (q : ℝ) ^ (v / 2) / (v / 2) :=
        Real.log_le_rpow_div hq0 hvhalf
      have hmain :
          ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v) ≤
            (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹) := by
        have h1 :
            ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v) ≤
              Real.log (q : ℝ) / Real.rpow (q : ℝ) (1 + v) :=
          div_le_div_of_nonneg_right hlog hqpow.le
        refine h1.trans ?_
        have h2 :
            Real.log (q : ℝ) / Real.rpow (q : ℝ) (1 + v) ≤
              ((q : ℝ) ^ (v / 2) / (v / 2)) / Real.rpow (q : ℝ) (1 + v) :=
          div_le_div_of_nonneg_right hlog' hqpow.le
        refine h2.trans ?_
        have hcalc :
            ((q : ℝ) ^ (v / 2) / (v / 2)) / Real.rpow (q : ℝ) (1 + v) =
              (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹) := by
          have hsplit :
              Real.rpow (q : ℝ) (1 + v) = (q : ℝ) ^ (1 + v / 2) * (q : ℝ) ^ (v / 2) := by
            simpa [show (1 + v : ℝ) = (1 + v / 2) + (v / 2) by ring] using
              (Real.rpow_add hqpos (1 + v / 2) (v / 2))
          rw [hsplit]
          field_simp [hv.ne', hqpos.ne']
        exact le_of_eq hcalc
      simpa [hq] using hmain
    · have hcoef : 0 ≤ 2 / v := by positivity
      have hpow : 0 ≤ (((q : ℝ) ^ (1 + v / 2))⁻¹) := by positivity
      simpa [hq] using (mul_nonneg hcoef hpow :
        0 ≤ (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹))

lemma tsum_vonMangoldt_prime_powers_div_rpow {s : ℝ} (hs : 1 < s) (r : Nat.Primes) :
    (∑' k : ℕ,
      ArithmeticFunction.vonMangoldt ((r : ℕ) ^ (k + 1)) /
        Real.rpow ((((r : ℕ) ^ (k + 1) : ℕ) : ℝ)) s) =
      Real.log (r : ℝ) / (Real.rpow (r : ℝ) s - 1) := by
  let a : ℝ := (Real.rpow (r : ℝ) s)⁻¹
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hr1 : 1 < (r : ℝ) := by exact_mod_cast r.2.one_lt
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hrpow0 : 0 < Real.rpow (r : ℝ) s := Real.rpow_pos_of_pos (by positivity) _
  have hrpow1 : 1 < Real.rpow (r : ℝ) s := Real.one_lt_rpow hr1 hs0
  have ha0 : 0 ≤ a := by
    exact inv_nonneg.mpr hrpow0.le
  have ha1 : a < 1 := by
    exact (inv_lt_one₀ hrpow0).2 hrpow1
  have hpowden (k : ℕ) :
      Real.rpow ((((r : ℕ) ^ (k + 1) : ℕ) : ℝ)) s =
      (Real.rpow (r : ℝ) s) ^ (k + 1) := by
    rw [Nat.cast_pow]
    conv_lhs => rw [← Real.rpow_natCast]
    calc
      (Real.rpow (r : ℝ) (((k + 1 : ℕ) : ℝ))).rpow s =
          Real.rpow (r : ℝ) ((((k + 1 : ℕ) : ℝ) * s)) := by
            symm
            exact Real.rpow_mul hr0 (((k + 1 : ℕ) : ℝ)) s
      _ = Real.rpow (r : ℝ) (s * (((k + 1 : ℕ) : ℝ))) := by ring_nf
      _ = Real.rpow (Real.rpow (r : ℝ) s) (((k + 1 : ℕ) : ℝ)) := by
            exact Real.rpow_mul hr0 s (((k + 1 : ℕ) : ℝ))
      _ = (Real.rpow (r : ℝ) s) ^ (k + 1) := by
            exact Real.rpow_natCast (Real.rpow (r : ℝ) s) (k + 1)
  calc
    ∑' k : ℕ, ArithmeticFunction.vonMangoldt ((r : ℕ) ^ (k + 1)) /
        Real.rpow ((((r : ℕ) ^ (k + 1) : ℕ) : ℝ)) s
        = ∑' k : ℕ, Real.log (r : ℝ) * a ^ (k + 1) := by
            apply tsum_congr
            intro k
            rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k)]
            rw [ArithmeticFunction.vonMangoldt_apply_prime r.2]
            rw [hpowden k, div_eq_mul_inv, inv_pow]
    _ = Real.log (r : ℝ) * ∑' k : ℕ, a ^ (k + 1) := by
          rw [tsum_mul_left]
    _ = Real.log (r : ℝ) * (a * ∑' k : ℕ, a ^ k) := by
          congr 1
          calc
            ∑' k : ℕ, a ^ (k + 1) = ∑' k : ℕ, a * a ^ k := by
              apply tsum_congr
              intro k
              rw [pow_succ']
            _ = a * ∑' k : ℕ, a ^ k := by
              rw [tsum_mul_left]
    _ = Real.log (r : ℝ) * (a * (1 - a)⁻¹) := by
          rw [tsum_geometric_of_lt_one ha0 ha1]
    _ = Real.log (r : ℝ) / (Real.rpow (r : ℝ) s - 1) := by
          have hgeom : a * (1 - a)⁻¹ = 1 / (Real.rpow (r : ℝ) s - 1) := by
            dsimp [a]
            field_simp [hrpow0.ne']
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun t : ℝ => Real.log (r : ℝ) * t) hgeom

lemma summable_primeTailSeries_terms {p : ℕ} (_hp : p.Prime) {v : ℝ} (hv : 0 < v) :
    Summable (fun r : ℕ =>
      if _hr : p ≤ r ∧ r.Prime then
        Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1)
      else
        0) := by
  have hvhalf : 0 < v / 2 := by
    linarith
  have hmajorant : Summable (fun r : ℕ => (4 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹)) := by
    have hbase : Summable (fun r : ℕ => (((r : ℝ) ^ (1 + v / 2))⁻¹)) := by
      exact (Real.summable_nat_rpow_inv).2 (by linarith)
    exact hbase.mul_left (4 / v)
  refine Summable.of_nonneg_of_le
    (f := fun r : ℕ => (4 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹)) ?_ ?_ hmajorant
  · intro r
    by_cases hr : p ≤ r ∧ r.Prime
    · have hr1 : 1 < (r : ℝ) := by exact_mod_cast hr.2.one_lt
      have hs0 : 0 < 1 + v := by linarith
      have hpow_gt_one : 1 < Real.rpow (r : ℝ) (1 + v) := Real.one_lt_rpow hr1 hs0
      have hlog_nonneg : 0 ≤ Real.log (r : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast hr.2.one_lt.le)
      simpa [hr] using
        (div_nonneg hlog_nonneg (by linarith : 0 ≤ Real.rpow (r : ℝ) (1 + v) - 1))
    · simp [hr]
  · intro r
    by_cases hr : p ≤ r ∧ r.Prime
    · have hr0 : 0 ≤ (r : ℝ) := by positivity
      have hrpos : 0 < (r : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_two hr.2.two_le
      have hr1 : 1 < (r : ℝ) := by exact_mod_cast hr.2.one_lt
      have hs0 : 0 < 1 + v := by linarith
      have hs_nonneg : 0 ≤ 1 + v := by linarith
      have hpow_pos : 0 < Real.rpow (r : ℝ) (1 + v) := Real.rpow_pos_of_pos hrpos (1 + v)
      have hpow_gt_one : 1 < Real.rpow (r : ℝ) (1 + v) := Real.one_lt_rpow hr1 hs0
      have hpow_ge_two : (2 : ℝ) ≤ Real.rpow (r : ℝ) (1 + v) := by
        have htwo_le : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.2.two_le
        calc
          (2 : ℝ) = Real.rpow (2 : ℝ) 1 := by simp
          _ ≤ Real.rpow (2 : ℝ) (1 + v) := by
              exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ ≤ Real.rpow (r : ℝ) (1 + v) := by
              exact Real.rpow_le_rpow (by positivity) htwo_le hs_nonneg
      have hden_pos : 0 < Real.rpow (r : ℝ) (1 + v) - 1 := by
        linarith
      have hinv_le : 1 / (Real.rpow (r : ℝ) (1 + v) - 1) ≤ 2 / Real.rpow (r : ℝ) (1 + v) := by
        have hhalf : Real.rpow (r : ℝ) (1 + v) / 2 ≤ Real.rpow (r : ℝ) (1 + v) - 1 := by
          nlinarith
        have hhalf_pos : 0 < Real.rpow (r : ℝ) (1 + v) / 2 := by
          positivity
        have htmp := one_div_le_one_div_of_le hhalf_pos hhalf
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using htmp
      have hterm_le :
          Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) ≤
            2 * (Real.log (r : ℝ) / Real.rpow (r : ℝ) (1 + v)) := by
        have hlog_nonneg : 0 ≤ Real.log (r : ℝ) := by
          exact Real.log_nonneg (by exact_mod_cast hr.2.one_lt.le)
        calc
          Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1)
              = Real.log (r : ℝ) * (1 / (Real.rpow (r : ℝ) (1 + v) - 1)) := by
                  rw [div_eq_mul_inv, one_div]
          _ ≤ Real.log (r : ℝ) * (2 / Real.rpow (r : ℝ) (1 + v)) := by
                exact mul_le_mul_of_nonneg_left hinv_le hlog_nonneg
          _ = 2 * (Real.log (r : ℝ) / Real.rpow (r : ℝ) (1 + v)) := by
                ring
      have hlog' : Real.log (r : ℝ) ≤ (r : ℝ) ^ (v / 2) / (v / 2) :=
        Real.log_le_rpow_div hr0 hvhalf
      have hmain0 :
          Real.log (r : ℝ) / Real.rpow (r : ℝ) (1 + v) ≤
            (2 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹) := by
        have h2 :
            Real.log (r : ℝ) / Real.rpow (r : ℝ) (1 + v) ≤
              ((r : ℝ) ^ (v / 2) / (v / 2)) / Real.rpow (r : ℝ) (1 + v) :=
          div_le_div_of_nonneg_right hlog' hpow_pos.le
        refine h2.trans ?_
        have hsplit :
            Real.rpow (r : ℝ) (1 + v) = (r : ℝ) ^ (1 + v / 2) * (r : ℝ) ^ (v / 2) := by
          simpa [show (1 + v : ℝ) = (1 + v / 2) + (v / 2) by ring] using
            (Real.rpow_add hrpos (1 + v / 2) (v / 2))
        have hcalc :
            ((r : ℝ) ^ (v / 2) / (v / 2)) / Real.rpow (r : ℝ) (1 + v) =
              (2 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹) := by
          rw [hsplit]
          field_simp [hv.ne', hrpos.ne']
        exact le_of_eq hcalc
      have hmain1 :
          2 * (Real.log (r : ℝ) / Real.rpow (r : ℝ) (1 + v)) ≤
            2 * ((2 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹)) := by
        exact mul_le_mul_of_nonneg_left hmain0 (by positivity)
      calc
        (if hr : p ≤ r ∧ r.Prime then
            Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1)
          else
            0)
            = Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) := by
                simp [hr]
        _ ≤ 2 * (Real.log (r : ℝ) / Real.rpow (r : ℝ) (1 + v)) := hterm_le
        _ ≤ 2 * ((2 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹)) := hmain1
        _ = (4 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹) := by ring
    · have hcoef : 0 ≤ 4 / v := by positivity
      have hpow : 0 ≤ (((r : ℝ) ^ (1 + v / 2))⁻¹) := by positivity
      simpa [hr] using (mul_nonneg hcoef hpow :
        0 ≤ (4 / v) * (((r : ℝ) ^ (1 + v / 2))⁻¹))

/-- Equation (5): the Euler-Rankin prime-tail estimate. -/
lemma primeTailSeries_le_roughLogBound {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {v : ℝ} (hv : 0 < v) :
    primeTailSeries p v ≤ Real.log (p : ℝ) / (Real.rpow (p : ℝ) v - 1) := by
      sorry
/-- The auxiliary bound `A_p(v) ≤ log p / (p^v - 1)` used in the main proof. -/
lemma roughMangoldtSeries_le_roughLogBound {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {v : ℝ} (hv : 0 < v) :
    roughMangoldtSeries p v ≤ Real.log (p : ℝ) / (Real.rpow (p : ℝ) v - 1) := by
  classical
  let f : ℕ → ℝ := fun q =>
    if hq : 2 ≤ q ∧ IsPRough p q then
      ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v)
    else
      0
  have hrough_eq : roughMangoldtSeries p v = ∑' q : ℕ, f q := by
    calc
      roughMangoldtSeries p v
          = ∑' q : { q : ℕ // 2 ≤ q ∧ IsPRough p q }, f q := by
              apply tsum_congr
              intro q
              simp [f, q.2]
      _ = ∑' q : ℕ, f q := by
            apply tsum_subtype_eq_of_support_subset
            intro q hq
            by_contra hq'
            have hzero : f q = 0 := by
              dsimp [f]
              split_ifs with h
              · exact (hq' h).elim
              · rfl
            exact hq hzero
  have hvhalf : 0 < v / 2 := by
    linarith
  have hfsum_majorant : Summable (fun q : ℕ => (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹)) := by
    have hbase : Summable (fun q : ℕ => (((q : ℝ) ^ (1 + v / 2))⁻¹)) := by
      exact (Real.summable_nat_rpow_inv).2 (by linarith)
    exact hbase.mul_left (2 / v)
  have hfsum : Summable f := by
    refine Summable.of_nonneg_of_le
      (f := fun q : ℕ => (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹)) ?_ ?_ hfsum_majorant
    · intro q
      by_cases hq : 2 ≤ q ∧ IsPRough p q
      · have hqpos : 0 < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_two hq.1
        have hqpow : 0 < Real.rpow (q : ℝ) (1 + v) := Real.rpow_pos_of_pos hqpos _
        simpa [f, hq] using
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hqpow.le :
            0 ≤ ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v))
      · have hf : f q = 0 := by
          dsimp [f]
          by_cases h : 2 ≤ q ∧ IsPRough p q
          · exact (hq h).elim
          · simp [h]
        rw [hf]
    · intro q
      by_cases hq : 2 ≤ q ∧ IsPRough p q
      · have hq0 : 0 ≤ (q : ℝ) := by positivity
        have hqpos : 0 < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_two hq.1
        have hqpow : 0 < Real.rpow (q : ℝ) (1 + v) := Real.rpow_pos_of_pos hqpos _
        have hlog : ArithmeticFunction.vonMangoldt q ≤ Real.log (q : ℝ) := by
          simpa using ArithmeticFunction.vonMangoldt_le_log (n := q)
        have hlog' : Real.log (q : ℝ) ≤ (q : ℝ) ^ (v / 2) / (v / 2) :=
          Real.log_le_rpow_div hq0 hvhalf
        have hmain :
            ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v) ≤
              (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹) := by
          have h1 :
              ArithmeticFunction.vonMangoldt q / Real.rpow (q : ℝ) (1 + v) ≤
                Real.log (q : ℝ) / Real.rpow (q : ℝ) (1 + v) :=
            div_le_div_of_nonneg_right hlog hqpow.le
          refine h1.trans ?_
          have h2 :
              Real.log (q : ℝ) / Real.rpow (q : ℝ) (1 + v) ≤
                ((q : ℝ) ^ (v / 2) / (v / 2)) / Real.rpow (q : ℝ) (1 + v) :=
            div_le_div_of_nonneg_right hlog' hqpow.le
          refine h2.trans ?_
          have hcalc :
              ((q : ℝ) ^ (v / 2) / (v / 2)) / Real.rpow (q : ℝ) (1 + v) =
                (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹) := by
            have hsplit :
                Real.rpow (q : ℝ) (1 + v) = (q : ℝ) ^ (1 + v / 2) * (q : ℝ) ^ (v / 2) := by
              simpa [show (1 + v : ℝ) = (1 + v / 2) + (v / 2) by ring] using
                (Real.rpow_add hqpos (1 + v / 2) (v / 2))
            rw [hsplit]
            field_simp [hv.ne', hqpos.ne']
          exact le_of_eq hcalc
        simpa [f, hq] using hmain
      · have hcoef : 0 ≤ 2 / v := by positivity
        have hpow : 0 ≤ (((q : ℝ) ^ (1 + v / 2))⁻¹) := by positivity
        simpa [f, hq] using (mul_nonneg hcoef hpow :
          0 ≤ (2 / v) * (((q : ℝ) ^ (1 + v / 2))⁻¹))
  have hfsupport : Function.support f ⊆ {n : ℕ | IsPrimePow n} := by
    intro q hq
    by_contra hprimepow
    have : f q = 0 := by
      by_cases hcond : 2 ≤ q ∧ IsPRough p q
      · simp [f, hcond, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hprimepow]
      · simp [f, hcond]
    exact hq this
  have hrough_expanded :
      roughMangoldtSeries p v =
        ∑' (r : Nat.Primes) (k : ℕ), f ((r : ℕ) ^ (k + 1)) := by
    rw [hrough_eq, tsum_eq_tsum_primes_of_support_subset_prime_powers hfsum hfsupport]
  have hrough_pow_iff (r : Nat.Primes) (k : ℕ) :
      IsPRough p ((r : ℕ) ^ (k + 1)) ↔ p ≤ (r : ℕ) := by
    constructor
    · intro h
      exact h r r.2 (dvd_pow_self _ (Nat.succ_ne_zero k))
    · intro hpr q hq hqdiv
      have hqr : q = (r : ℕ) := Nat.prime_eq_prime_of_dvd_pow hq r.2 hqdiv
      exact hqr ▸ hpr
  have hinner (r : Nat.Primes) :
      (∑' k : ℕ, f ((r : ℕ) ^ (k + 1))) =
        if p ≤ (r : ℕ) then Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) else 0 := by
    by_cases hpr : p ≤ (r : ℕ)
    · let a : ℝ := (Real.rpow (r : ℝ) (1 + v))⁻¹
      have hr0 : 0 ≤ (r : ℝ) := by positivity
      have hr1 : 1 < (r : ℝ) := by exact_mod_cast r.2.one_lt
      have hv1 : 0 < 1 + v := by linarith
      have hrpow0 : 0 < Real.rpow (r : ℝ) (1 + v) := Real.rpow_pos_of_pos (by positivity) _
      have hrpow1 : 1 < Real.rpow (r : ℝ) (1 + v) := Real.one_lt_rpow hr1 hv1
      have ha0 : 0 ≤ a := by
        exact inv_nonneg.mpr hrpow0.le
      have ha1 : a < 1 := by
        exact (inv_lt_one₀ hrpow0).2 hrpow1
      have hpowden (k : ℕ) :
          Real.rpow ((((r : ℕ) ^ (k + 1) : ℕ) : ℝ)) (1 + v) =
            (Real.rpow (r : ℝ) (1 + v)) ^ (k + 1) := by
        rw [Nat.cast_pow]
        conv_lhs => rw [← Real.rpow_natCast]
        calc
          (Real.rpow (r : ℝ) (((k + 1 : ℕ) : ℝ))).rpow (1 + v) =
              Real.rpow (r : ℝ) ((((k + 1 : ℕ) : ℝ) * (1 + v))) := by
                symm
                exact Real.rpow_mul hr0 (((k + 1 : ℕ) : ℝ)) (1 + v)
          _ = Real.rpow (r : ℝ) ((1 + v) * (((k + 1 : ℕ) : ℝ))) := by ring_nf
          _ = Real.rpow (Real.rpow (r : ℝ) (1 + v)) (((k + 1 : ℕ) : ℝ)) := by
                simpa using (Real.rpow_mul hr0 (1 + v) (((k + 1 : ℕ) : ℝ)))
          _ = (Real.rpow (r : ℝ) (1 + v)) ^ (k + 1) := by
                simpa using (Real.rpow_natCast (Real.rpow (r : ℝ) (1 + v)) (k + 1))
      have hcond (k : ℕ) : 2 ≤ (r : ℕ) ^ (k + 1) ∧ IsPRough p ((r : ℕ) ^ (k + 1)) := by
        refine ⟨le_trans r.2.two_le (Nat.le_pow (Nat.succ_pos _)), (hrough_pow_iff r k).2 hpr⟩
      rw [if_pos hpr]
      calc
        ∑' k : ℕ, f ((r : ℕ) ^ (k + 1)) = ∑' k : ℕ, Real.log (r : ℝ) * a ^ (k + 1) := by
          apply tsum_congr
          intro k
          have hkcond : 2 ≤ (r : ℕ) ^ (k + 1) ∧ IsPRough p ((r : ℕ) ^ (k + 1)) := hcond k
          have hkf :
              f ((r : ℕ) ^ (k + 1)) =
                ArithmeticFunction.vonMangoldt ((r : ℕ) ^ (k + 1)) /
                  Real.rpow ((((r : ℕ) ^ (k + 1) : ℕ) : ℝ)) (1 + v) := by
                simp [f, hkcond]
          rw [hkf]
          rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k)]
          rw [ArithmeticFunction.vonMangoldt_apply_prime r.2]
          rw [hpowden k, div_eq_mul_inv, inv_pow]
        _ = Real.log (r : ℝ) * ∑' k : ℕ, a ^ (k + 1) := by
          rw [tsum_mul_left]
        _ = Real.log (r : ℝ) * (a * ∑' k : ℕ, a ^ k) := by
          congr 1
          calc
            ∑' k : ℕ, a ^ (k + 1) = ∑' k : ℕ, a * a ^ k := by
              apply tsum_congr
              intro k
              rw [pow_succ']
            _ = a * ∑' k : ℕ, a ^ k := by
              rw [tsum_mul_left]
        _ = Real.log (r : ℝ) * (a * (1 - a)⁻¹) := by
          rw [tsum_geometric_of_lt_one ha0 ha1]
        _ = Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) := by
          have hgeom : a * (1 - a)⁻¹ = 1 / (Real.rpow (r : ℝ) (1 + v) - 1) := by
            dsimp [a]
            field_simp [hrpow0.ne']
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun t : ℝ => Real.log (r : ℝ) * t) hgeom
    · have hzero (k : ℕ) : f ((r : ℕ) ^ (k + 1)) = 0 := by
        by_cases hcond : 2 ≤ (r : ℕ) ^ (k + 1) ∧ IsPRough p ((r : ℕ) ^ (k + 1))
        · exfalso
          exact hpr ((hrough_pow_iff r k).1 hcond.2)
        · simp [f, hcond]
      rw [if_neg hpr]
      simp [hzero]
  let g : ℕ → ℝ := fun r =>
    if hr : p ≤ r ∧ r.Prime then
      Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1)
    else
      0
  have hprime_nat :
      (∑' r : Nat.Primes,
          if p ≤ (r : ℕ) then Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) else 0) =
        ∑' r : ℕ, g r := by
    let h : ℕ → ℝ := fun r =>
      if hr : r.Prime then
        if p ≤ r then Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) else 0
      else
        0
    calc
      (∑' r : Nat.Primes,
          if p ≤ (r : ℕ) then Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) else 0)
          =
        ∑' r : { r : ℕ // r.Prime },
          if p ≤ (r : ℕ) then Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) else 0 := by
            rfl
      _ =
        ∑' r : { r : ℕ // r.Prime }, h r := by
              apply tsum_congr
              intro r
              simp [h, r.2]
      _ = ∑' r : ℕ, h r := by
              apply tsum_subtype_eq_of_support_subset
              intro r hr
              by_contra hr'
              have hzero : h r = 0 := by
                by_cases hprime : r.Prime
                · exact (hr' hprime).elim
                · simp [h, hprime]
              exact hr hzero
      _ = ∑' r : ℕ, g r := by
            apply tsum_congr
            intro r
            by_cases hrp : r.Prime
            · by_cases hpr' : p ≤ r
              · simp [g, h, hrp, hpr']
              · simp [g, h, hrp, hpr']
            · simp [g, h, hrp]
  have hprime_eq : primeTailSeries p v = ∑' r : ℕ, g r := by
    calc
      primeTailSeries p v
          = ∑' r : { r : ℕ // p ≤ r ∧ r.Prime }, g r := by
              apply tsum_congr
              intro r
              simp [g, r.2]
      _ = ∑' r : ℕ, g r := by
            apply tsum_subtype_eq_of_support_subset
            intro r hr
            by_contra hr'
            have hzero : g r = 0 := by
              dsimp [g]
              split_ifs with h
              · exact (hr' h).elim
              · rfl
            exact hr hzero
  calc
    roughMangoldtSeries p v = ∑' (r : Nat.Primes) (k : ℕ), f ((r : ℕ) ^ (k + 1)) := hrough_expanded
    _ = ∑' r : Nat.Primes,
          (if p ≤ (r : ℕ) then Real.log (r : ℝ) / (Real.rpow (r : ℝ) (1 + v) - 1) else 0) := by
        apply tsum_congr
        intro r
        exact hinner r
    _ = ∑' r : ℕ, g r := hprime_nat
    _ = primeTailSeries p v := hprime_eq.symm
    _ ≤ Real.log (p : ℝ) / (Real.rpow (p : ℝ) v - 1) := primeTailSeries_le_roughLogBound hp hodd hv

lemma one_lt_mul_of_one_le_of_two_le {a b : ℕ} (ha : 1 ≤ a) (hb : 2 ≤ b) :
    1 < a * b := by
  have hmul : 2 ≤ a * b := by
    calc
      2 = 1 * 2 := by norm_num
      _ ≤ a * b := Nat.mul_le_mul ha hb
  exact lt_of_lt_of_le (by decide : 1 < 2) hmul

lemma one_lt_mul_mul_of_two_le_of_one_le_of_two_le {a b c : ℕ}
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 2 ≤ c) :
    1 < a * b * c := by
  have hab_lt : 1 < a * b := by
    simpa [Nat.mul_comm] using one_lt_mul_of_one_le_of_two_le hb ha
  have hab_le : 1 ≤ a * b := le_of_lt hab_lt
  simpa [Nat.mul_assoc] using one_lt_mul_of_one_le_of_two_le hab_le hc

/-- The model kernel `X^{-t}` is integrable on `(0,\infty)` as soon as `X > 1`. -/
lemma integrableOn_rpow_neg_Ioi {X : ℝ} (hX : 1 < X) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.rpow X (-t)) (Set.Ioi (0 : ℝ)) := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  refine (MeasureTheory.IntegrableOn.congr_fun
    (integrableOn_exp_mul_Ioi (a := -Real.log X) (by linarith [Real.log_pos hX]) 0)
    ?_ measurableSet_Ioi)
  intro t ht
  change Real.exp ((-Real.log X) * t) = Real.rpow X (-t)
  simp [Real.rpow_def_of_pos hX0]

/-- The basic Laplace integral `\int_0^\infty X^{-t} dt = 1 / \log X` for `X > 1`. -/
lemma integral_rpow_neg_Ioi {X : ℝ} (hX : 1 < X) :
    ∫ t in Set.Ioi (0 : ℝ), Real.rpow X (-t) = 1 / Real.log X := by
  have hX0 : 0 < X := lt_trans zero_lt_one hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  calc
    ∫ t in Set.Ioi (0 : ℝ), Real.rpow X (-t)
      = ∫ t in Set.Ioi (0 : ℝ), Real.exp ((-Real.log X) * t) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t ht
          change Real.rpow X (-t) = Real.exp ((-Real.log X) * t)
          simp [Real.rpow_def_of_pos hX0]
    _ = -Real.exp ((-Real.log X) * 0) / (-Real.log X) := by
          simpa using integral_exp_mul_Ioi (a := -Real.log X)
            (by linarith [Real.log_pos hX]) (0 : ℝ)
    _ = 1 / Real.log X := by
          simp

lemma summable_log_div_rpow_on_ge_two {s : ℝ} (hs : 1 < s) :
    Summable (fun q : { q : ℕ // 2 ≤ q } =>
      Real.log (q.1 : ℝ) / Real.rpow (q.1 : ℝ) s) := by
        sorry
lemma summable_roughMangoldtTerm {p : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (fun q : { q : ℕ // 2 ≤ q ∧ IsPRough p q } =>
      ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
        sorry
/-- Main result `(*_p)` from `B/f1.tex`. -/
theorem roughKernelSeries_le_main_bound {p n : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hn : 1 ≤ n) (hnrough : IsPRough p n) :
    roughKernelSeries p n ≤ 1 / Real.log ((p * n : ℕ) : ℝ) := by
  let _ := hnrough
  let α := { q : ℕ // 2 ≤ q ∧ IsPRough p q }
  let term : α → ℝ := fun q =>
    ArithmeticFunction.vonMangoldt q.1 /
      ((q.1 : ℝ) * Real.log ((n * q.1 : ℕ) : ℝ) * Real.log ((p * n * q.1 : ℕ) : ℝ))
  let diffInt : α → ℝ → ℝ := fun q t =>
    (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (p : ℝ))) *
      (Real.rpow (((n * q.1 : ℕ) : ℝ)) (-t) -
        Real.rpow (((p * n * q.1 : ℕ) : ℝ)) (-t))
  have hp1 : 1 < p := hp.one_lt
  have hlogp_pos : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp1)
  have hterm_nonneg : ∀ q : α, 0 ≤ term q := by
    intro q
    have hnq : 1 < n * q.1 := by
      exact one_lt_mul_of_one_le_of_two_le hn q.2.1
    have hpnq : 1 < p * n * q.1 := by
      exact one_lt_mul_mul_of_two_le_of_one_le_of_two_le hp.two_le hn q.2.1
    dsimp [term]
    have hq0 : 0 < (q.1 : ℝ) := by
      have hq0n : 0 < q.1 := by omega
      exact_mod_cast hq0n
    have hlog_nq_pos : 0 < Real.log ((n * q.1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hnq)
    have hlog_pnq_pos : 0 < Real.log ((p * n * q.1 : ℕ) : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hpnq)
    refine div_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
    exact mul_nonneg (mul_nonneg hq0.le hlog_nq_pos.le) hlog_pnq_pos.le
  have hsum_bound : ∀ u : Finset α, Finset.sum u term ≤ 1 / Real.log ((p * n : ℕ) : ℝ) := by
    intro u
    have hdiff_integrable : ∀ q : α, MeasureTheory.IntegrableOn (diffInt q) (Set.Ioi (0 : ℝ)) := by
      intro q
      have hnq : 1 < n * q.1 := by
        exact one_lt_mul_of_one_le_of_two_le hn q.2.1
      have hpnq : 1 < p * n * q.1 := by
        exact one_lt_mul_mul_of_two_le_of_one_le_of_two_le hp.two_le hn q.2.1
      dsimp [diffInt]
      refine ((integrableOn_rpow_neg_Ioi (by exact_mod_cast hnq)).sub
        (integrableOn_rpow_neg_Ioi (by exact_mod_cast hpnq))).const_mul _
    have hsum_eq_integral :
        Finset.sum u term = ∫ t in Set.Ioi (0 : ℝ), Finset.sum u (fun q => diffInt q t) := by
      calc
        Finset.sum u term = Finset.sum u (fun q => ∫ t in Set.Ioi (0 : ℝ), diffInt q t) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          dsimp [term, diffInt]
          have hnq : 1 < n * q.1 := by
            exact one_lt_mul_of_one_le_of_two_le hn q.2.1
          have hpnq : 1 < p * n * q.1 := by
            exact one_lt_mul_mul_of_two_le_of_one_le_of_two_le hp.two_le hn q.2.1
          have hlog_nq_ne : Real.log ((n * q.1 : ℕ) : ℝ) ≠ 0 := by
            apply Real.log_ne_zero_of_pos_of_ne_one
            · positivity
            · exact_mod_cast hnq.ne'
          have hlog_pnq_ne : Real.log ((p * n * q.1 : ℕ) : ℝ) ≠ 0 := by
            apply Real.log_ne_zero_of_pos_of_ne_one
            · positivity
            · exact_mod_cast hpnq.ne'
          have hlog_mul :
              Real.log ((p * n * q.1 : ℕ) : ℝ) =
                Real.log (p : ℝ) + Real.log ((n * q.1 : ℕ) : ℝ) := by
            rw [show ((p * n * q.1 : ℕ) : ℝ) = (p : ℝ) * ((n * q.1 : ℕ) : ℝ) by
              norm_num [Nat.cast_mul, mul_assoc]]
            rw [Real.log_mul (show (p : ℝ) ≠ 0 by positivity)
              (show (((n * q.1 : ℕ) : ℝ)) ≠ 0 by positivity)]
          have hInt :
              ∫ t in Set.Ioi (0 : ℝ), diffInt q t
                = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (p : ℝ))) *
                    ((∫ t in Set.Ioi (0 : ℝ), Real.rpow (((n * q.1 : ℕ) : ℝ)) (-t)) -
                      ∫ t in Set.Ioi (0 : ℝ), Real.rpow (((p * n * q.1 : ℕ) : ℝ)) (-t)) := by
            rw [integral_const_mul]
            rw [integral_sub
              (integrableOn_rpow_neg_Ioi (by exact_mod_cast hnq))
              (integrableOn_rpow_neg_Ioi (by exact_mod_cast hpnq))]
          calc
            term q
                = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (p : ℝ))) *
                  (1 / Real.log ((n * q.1 : ℕ) : ℝ) -
                    1 / Real.log ((p * n * q.1 : ℕ) : ℝ)) := by
                dsimp [term]
                rw [hlog_mul]
                field_simp [hlogp_pos.ne', hlog_nq_ne, hlog_pnq_ne]
                ring
            _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (p : ℝ))) *
                  ((∫ t in Set.Ioi (0 : ℝ), Real.rpow (((n * q.1 : ℕ) : ℝ)) (-t)) -
                    ∫ t in Set.Ioi (0 : ℝ), Real.rpow (((p * n * q.1 : ℕ) : ℝ)) (-t)) := by
                rw [integral_rpow_neg_Ioi (by exact_mod_cast hnq),
                  integral_rpow_neg_Ioi (by exact_mod_cast hpnq)]
            _ = ∫ t in Set.Ioi (0 : ℝ), diffInt q t := hInt.symm
        _ = ∫ t in Set.Ioi (0 : ℝ), Finset.sum u (fun q => diffInt q t) := by
            rw [integral_finsetSum u (fun q hq => hdiff_integrable q)]
    have hleft_integrable :
        MeasureTheory.IntegrableOn (fun t : ℝ => Finset.sum u (fun q => diffInt q t))
          (Set.Ioi (0 : ℝ)) := by
      simpa [MeasureTheory.IntegrableOn] using
        integrable_finsetSum u (fun q hq => hdiff_integrable q)
    have hpn : 1 < p * n := by
      simpa [Nat.mul_comm] using one_lt_mul_of_one_le_of_two_le hn hp.two_le
    have hright_integrable :
        MeasureTheory.IntegrableOn
          (fun t : ℝ => (((p * n : ℕ) : ℝ) ^ (-t))) (Set.Ioi (0 : ℝ)) :=
      integrableOn_rpow_neg_Ioi (by exact_mod_cast hpn)
    have hpoint :
        ∀ t ∈ Set.Ioi (0 : ℝ),
          Finset.sum u (fun q => diffInt q t) ≤ (((p * n : ℕ) : ℝ) ^ (-t)) := by
      intro t ht
      have ht0 : 0 < t := ht
      have hsum_term := summable_roughMangoldtTerm (p := p) ht0
      have hpartial_le :
        Finset.sum u (fun q =>
          ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) ≤
          roughMangoldtSeries p t := by
        simpa [roughMangoldtSeries] using
          hsum_term.sum_le_tsum u (fun q hq => by
            exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.rpow_nonneg (show 0 ≤ (q.1 : ℝ) by positivity) _))
      have hker_nonneg : 0 ≤ roughKernel p n t := roughKernel_nonneg hp hn ht0
      have hdiff_factor :
          ∀ q : α,
            roughKernel p n t *
                (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) =
              diffInt q t := by
        intro q
        have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2.1
        have hqpos : 0 < (q.1 : ℝ) := by
          exact_mod_cast hqnatpos
        have hq_rpow : Real.rpow (q.1 : ℝ) (1 + t) = (q.1 : ℝ) * Real.rpow (q.1 : ℝ) t := by
          simpa using (Real.rpow_add hqpos (1 : ℝ) t)
        have hnq_rpow :
            (((n * q.1 : ℕ) : ℝ)) ^ (-t) = (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) := by
          simpa [Nat.cast_mul] using
            (Real.mul_rpow (show 0 ≤ (n : ℝ) by positivity)
              (show 0 ≤ (q.1 : ℝ) by positivity) (z := -t))
        have hpnq_rpow :
            (((p * n * q.1 : ℕ) : ℝ)) ^ (-t) =
              (p : ℝ) ^ (-t) * (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) := by
          calc
            (((p * n * q.1 : ℕ) : ℝ)) ^ (-t)
                = (p : ℝ) ^ (-t) * (((n * q.1 : ℕ) : ℝ)) ^ (-t) := by
                    simpa [Nat.cast_mul, mul_assoc] using
                      (Real.mul_rpow (show 0 ≤ (p : ℝ) by positivity)
                        (show 0 ≤ (((n * q.1 : ℕ) : ℝ)) by positivity) (z := -t))
            _ = (p : ℝ) ^ (-t) * ((n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t)) := by
                  rw [hnq_rpow]
            _ = (p : ℝ) ^ (-t) * (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) := by
                  ring
        calc
          roughKernel p n t *
              (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
              = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (p : ℝ))) *
                  ((n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t) -
                    (p : ℝ) ^ (-t) * (n : ℝ) ^ (-t) * (q.1 : ℝ) ^ (-t)) := by
                  rw [roughKernel, hq_rpow, div_eq_mul_inv, Real.rpow_neg (le_of_lt hqpos),
                    Real.rpow_eq_pow]
                  field_simp [hlogp_pos.ne', (Real.rpow_pos_of_pos hqpos t).ne']
          _ = (ArithmeticFunction.vonMangoldt q.1 / ((q.1 : ℝ) * Real.log (p : ℝ))) *
                ((((n * q.1 : ℕ) : ℝ)) ^ (-t) - (((p * n * q.1 : ℕ) : ℝ)) ^ (-t)) := by
                rw [hnq_rpow, hpnq_rpow]
          _ = diffInt q t := by
                rfl
      calc
        Finset.sum u (fun q => diffInt q t)
            = Finset.sum u (fun q =>
                roughKernel p n t *
                  (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))) := by
                refine Finset.sum_congr rfl ?_
                intro q hq
                symm
                exact hdiff_factor q
        _ = roughKernel p n t *
              Finset.sum u (fun q =>
                ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
                rw [Finset.mul_sum]
        _ ≤ roughKernel p n t * roughMangoldtSeries p t := by
                exact mul_le_mul_of_nonneg_left hpartial_le hker_nonneg
        _ ≤ roughKernel p n t *
              (Real.log (p : ℝ) / ((p : ℝ) ^ t - 1)) := by
                exact mul_le_mul_of_nonneg_left
                  (roughMangoldtSeries_le_roughLogBound hp hodd ht0) hker_nonneg
        _ = (((p * n : ℕ) : ℝ) ^ (-t)) := roughKernel_mul_bound_eq hp ht0
    calc
      Finset.sum u term
          = ∫ t in Set.Ioi (0 : ℝ), Finset.sum u (fun q => diffInt q t) := hsum_eq_integral
      _ ≤ ∫ t in Set.Ioi (0 : ℝ), (((p * n : ℕ) : ℝ) ^ (-t)) := by
            exact setIntegral_mono_on hleft_integrable hright_integrable measurableSet_Ioi hpoint
      _ = 1 / Real.log ((p * n : ℕ) : ℝ) := integral_rpow_neg_Ioi (by exact_mod_cast hpn)
  simpa [roughKernelSeries, α, term] using Real.tsum_le_of_sum_le hterm_nonneg hsum_bound

lemma isPRough_one (p : ℕ) : IsPRough p 1 := by
  intro q hq hqdiv
  exact False.elim (hq.ne_one (Nat.dvd_one.mp hqdiv))

lemma isPRough_of_dvd {p m n : ℕ} (hm : IsPRough p m) (hdiv : n ∣ m) :
    IsPRough p n := by
  intro q hq hqdiv
  exact hm q hq (dvd_trans hqdiv hdiv)

/-- The quotient-side weight used in the proof of `B/d2.tex`. -/
noncomputable def roughWeight (p n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log ((p * n : ℕ) : ℝ))

/-- The quotient-side divisibility flow from `B/d2.tex`. -/
noncomputable def roughFlow (p m n : ℕ) : ℝ :=
  by
    classical
    exact
      if 0 < n then
        if n ∣ m then
          let q := m / n
          if IsPRough p n ∧ 2 ≤ q ∧ IsPRough p q then
            ArithmeticFunction.vonMangoldt q /
              ((m : ℝ) * Real.log m * Real.log ((p * m : ℕ) : ℝ))
          else
            0
        else
          0
      else
        0

noncomputable def roughWeightSum (p : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : A, roughWeight p (a : ℕ)

lemma roughFlow_nonneg {p m n : ℕ} (hp : p.Prime) :
    0 ≤ roughFlow p m n := by
  classical
  unfold roughFlow
  by_cases hn : 0 < n
  · by_cases hdiv : n ∣ m
    · let q := m / n
      by_cases hq : IsPRough p n ∧ 2 ≤ q ∧ IsPRough p q
      · rcases hdiv with ⟨r, rfl⟩
        have hnrough' : IsPRough p n := hq.1
        have hq' : 2 ≤ r := by
          simpa [q, Nat.mul_div_right _ hn] using hq.2.1
        have hroughr : IsPRough p r := by
          simpa [q, Nat.mul_div_right _ hn] using hq.2.2
        have hm_gt_one : 1 < n * r := by
          exact lt_of_lt_of_le (by omega : 1 < r) (Nat.le_mul_of_pos_left r hn)
        have hm_pos_nat : 0 < n * r := Nat.mul_pos hn (by omega)
        have hm_mul_pos : 0 < (n : ℝ) * r := by
          exact_mod_cast hm_pos_nat
        have hlogm_pos : 0 < Real.log ((n * r : ℕ) : ℝ) := by
          exact Real.log_pos (by exact_mod_cast hm_gt_one)
        have hlogm_mul_pos : 0 < Real.log ((n : ℝ) * r) := by
          simpa [Nat.cast_mul] using hlogm_pos
        have hlogpm_pos : 0 < Real.log ((p * (n * r) : ℕ) : ℝ) := by
          exact Real.log_pos (by
            exact_mod_cast (show 1 < p * (n * r) by
              exact lt_of_lt_of_le hm_gt_one (Nat.le_mul_of_pos_left (n * r) hp.pos)))
        have hlogpm_mul_pos : 0 < Real.log ((p : ℝ) * ((n : ℝ) * r)) := by
          simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hlogpm_pos
        simpa [hn, q, hnrough', hq', hroughr, Nat.mul_div_right _ hn,
          Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
            le_of_lt <| mul_pos (mul_pos hm_mul_pos hlogm_mul_pos) hlogpm_mul_pos)
      · simp [hn, hdiv, q, hq]
    · simp [hn, hdiv]
  · simp [hn]

lemma roughFlow_eq_zero_of_not_dvd_lt {p m n : ℕ}
    (h : ¬ (n ∣ m ∧ n < m)) : roughFlow p m n = 0 := by
  classical
  unfold roughFlow
  by_cases hn : 0 < n
  · by_cases hdiv : n ∣ m
    · let q := m / n
      by_cases hq : IsPRough p n ∧ 2 ≤ q ∧ IsPRough p q
      · exfalso
        apply h
        rcases hdiv with ⟨r, rfl⟩
        have hq' : 2 ≤ r := by
          simpa [q, Nat.mul_div_right _ hn] using hq.2.1
        refine ⟨dvd_mul_right n r, ?_⟩
        simpa using (Nat.mul_lt_mul_of_pos_left (show 1 < r by omega) hn)
      · simp [hn, hdiv, q, hq]
    · simp [hn, hdiv]
  · simp [hn]

lemma summable_roughFlow_row (p m : ℕ) : Summable (fun n : ℕ => roughFlow p m n) := by
  classical
  refine summable_of_ne_finset_zero (s := m.divisors) ?_
  intro n hn
  apply roughFlow_eq_zero_of_not_dvd_lt
  intro h
  have hm0 : m ≠ 0 := by omega
  exact hn (Nat.mem_divisors.mpr ⟨h.1, hm0⟩)

lemma roughFlow_mul_right_eq {p n q : ℕ} (hn : 1 ≤ n) (hnrough : IsPRough p n)
    (hq : 2 ≤ q) (hqrough : IsPRough p q) :
    roughFlow p (n * q) n =
      ArithmeticFunction.vonMangoldt q /
        ((((n * q : ℕ) : ℝ)) * Real.log ((n * q : ℕ) : ℝ) *
          Real.log ((p * n * q : ℕ) : ℝ)) := by
  classical
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  unfold roughFlow
  have hqpair : 2 ≤ q ∧ IsPRough p q := ⟨hq, hqrough⟩
  simp [hn_pos, show n ∣ n * q by exact dvd_mul_right n q,
    Nat.mul_div_right q hn_pos, hnrough, hqpair, Nat.mul_left_comm, Nat.mul_comm]

lemma roughFlow_mul_le_baseFlow {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hnrough : IsPRough p n) (q : {q : ℕ // 2 ≤ q ∧ IsPRough p q}) :
    roughFlow p (n * q.1) n ≤ baseFlow (n * q.1) n := by
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hq_pos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2.1
  have hlogA_pos : 0 < Real.log ((n * q.1 : ℕ) : ℝ) := by
    exact Real.log_pos (by
      exact_mod_cast (show 1 < n * q.1 by
        exact lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos)))
  have hlogB_ge :
      Real.log ((n * q.1 : ℕ) : ℝ) ≤ Real.log ((p * n * q.1 : ℕ) : ℝ) := by
    have hA_pos : 0 < ((n * q.1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos hn_pos hq_pos)
    apply Real.log_le_log hA_pos
    exact_mod_cast (show n * q.1 ≤ p * n * q.1 by
      have hle : n * q.1 ≤ p * (n * q.1) := Nat.le_mul_of_pos_left (n * q.1) hp.pos
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle)
  by_cases hqpp : IsPrimePow q.1
  · have hbase :
      baseFlow (n * q.1) n =
        ArithmeticFunction.vonMangoldt q.1 /
          ((((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2) := by
      have hgt : 1 < n * q.1 := by
        exact lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos)
      simp [baseFlow, hgt, show n ∣ n * q.1 by exact dvd_mul_right n q.1,
        Nat.mul_div_right q.1 hn_pos, hqpp]
    rw [roughFlow_mul_right_eq hn hnrough q.2.1 q.2.2, hbase]
    have hnum_nonneg : 0 ≤ ArithmeticFunction.vonMangoldt q.1 :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hden :
        (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2 ≤
          (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) *
            Real.log ((p * n * q.1 : ℕ) : ℝ) := by
      have hlogA_nonneg : 0 ≤ Real.log ((n * q.1 : ℕ) : ℝ) := hlogA_pos.le
      calc
        (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2
            = (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) *
                Real.log ((n * q.1 : ℕ) : ℝ) := by ring
        _ ≤ (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) *
              Real.log ((p * n * q.1 : ℕ) : ℝ) := by
              gcongr
    have hden_pos :
        0 < (((n * q.1 : ℕ) : ℝ)) * Real.log ((n * q.1 : ℕ) : ℝ) ^ 2 := by
      refine mul_pos ?_ ?_
      · exact_mod_cast (Nat.mul_pos hn_pos hq_pos)
      · exact sq_pos_of_pos hlogA_pos
    exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden
  · have hvm : ArithmeticFunction.vonMangoldt q.1 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
      exact hqpp
    rw [roughFlow_mul_right_eq hn hnrough q.2.1 q.2.2, hvm]
    simp [baseFlow, show 1 < n * q.1 by
      exact lt_of_lt_of_le (by omega : 1 < q.1) (Nat.le_mul_of_pos_left q.1 hn_pos),
      show n ∣ n * q.1 by exact dvd_mul_right n q.1,
      Nat.mul_div_right q.1 hn_pos, hqpp]

lemma summable_roughFlow_col {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hnrough : IsPRough p n) :
    Summable (fun K : ℕ => roughFlow p K n) := by
      sorry
lemma inflow_roughFlow_eq_one_div_mul_roughKernelSeries {p n : ℕ} (hp : p.Prime)
    (hn : 1 ≤ n) (hnrough : IsPRough p n) :
    inflow (roughFlow p) n = (1 / (n : ℝ)) * roughKernelSeries p n := by
      sorry
theorem outflow_roughFlow_eq_roughWeight {p n : ℕ} (hp : p.Prime) (hn : 1 < n)
    (hnrough : IsPRough p n) :
    outflow (roughFlow p) n = roughWeight p n := by
  have hn0_nat : n ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hn)
  have hn_cast : (1 : ℝ) < n := by
    exact_mod_cast hn
  have hlogn_pos : 0 < Real.log n := Real.log_pos hn_cast
  have hlogpn_pos : 0 < Real.log ((p * n : ℕ) : ℝ) := by
    exact Real.log_pos (by
      exact_mod_cast (show 1 < p * n by
        exact lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p (lt_trans Nat.zero_lt_one hn))))
  have hsupport : ∀ m ∉ n.divisors, roughFlow p n m = 0 := by
    intro m hm
    apply roughFlow_eq_zero_of_not_dvd_lt
    intro h
    exact hm (Nat.mem_divisors.mpr ⟨h.1, hn0_nat⟩)
  rw [outflow, tsum_eq_sum (s := n.divisors) hsupport]
  calc
    ∑ m ∈ n.divisors, roughFlow p n m
        = ∑ m ∈ n.divisors,
            ArithmeticFunction.vonMangoldt (n / m) /
              ((n : ℝ) * Real.log n * Real.log ((p * n : ℕ) : ℝ)) := by
                apply Finset.sum_congr rfl
                intro m hm
                have hdiv : m ∣ n := Nat.dvd_of_mem_divisors hm
                have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hdiv (lt_trans Nat.zero_lt_one hn)
                have hmrough : IsPRough p m := isPRough_of_dvd hnrough hdiv
                have hqrough : IsPRough p (n / m) := by
                  rcases hdiv with ⟨q, rfl⟩
                  have hqdiv : q ∣ m * q := by
                    simp
                  simpa [Nat.mul_div_right _ hm_pos] using isPRough_of_dvd hnrough hqdiv
                by_cases hq : 2 ≤ n / m
                · have hcond :
                      IsPRough p m ∧ 2 ≤ n / m ∧ IsPRough p (n / m) :=
                      ⟨hmrough, hq, hqrough⟩
                  simp [roughFlow, hm_pos, hdiv, hcond]
                · have hnotpp : ¬ IsPrimePow (n / m) := by
                    intro hpp
                    exact hq (Nat.succ_le_of_lt (IsPrimePow.one_lt hpp))
                  have hvm : ArithmeticFunction.vonMangoldt (n / m) = 0 := by
                    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
                    exact hnotpp
                  have hcond :
                      ¬ (IsPRough p m ∧ 2 ≤ n / m ∧ IsPRough p (n / m)) := by
                    intro hcond
                    exact hq hcond.2.1
                  simp [roughFlow, hm_pos, hdiv, hcond, hvm]
    _ = ∑ d ∈ n.divisors,
          ArithmeticFunction.vonMangoldt d /
            ((n : ℝ) * Real.log n * Real.log ((p * n : ℕ) : ℝ)) := by
              simpa using
                (Nat.sum_div_divisors n
                  (fun d : ℕ =>
                    ArithmeticFunction.vonMangoldt d /
                      ((n : ℝ) * Real.log n * Real.log ((p * n : ℕ) : ℝ))))
    _ = (∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d) /
          ((n : ℝ) * Real.log n * Real.log ((p * n : ℕ) : ℝ)) := by
            rw [Finset.sum_div]
    _ = Real.log n / ((n : ℝ) * Real.log n * Real.log ((p * n : ℕ) : ℝ)) := by
          rw [ArithmeticFunction.vonMangoldt_sum]
    _ = roughWeight p n := by
          rw [roughWeight]
          field_simp [Nat.cast_ne_zero.mpr hn0_nat, hlogn_pos.ne', hlogpn_pos.ne']

lemma inflow_roughFlow_le_roughWeight_of_bound {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hnrough : IsPRough p n)
    (hbound : roughKernelSeries p n ≤ 1 / Real.log ((p * n : ℕ) : ℝ)) :
    inflow (roughFlow p) n ≤ roughWeight p n := by
  calc
    inflow (roughFlow p) n = (1 / (n : ℝ)) * roughKernelSeries p n :=
      inflow_roughFlow_eq_one_div_mul_roughKernelSeries hp hn hnrough
    _ ≤ (1 / (n : ℝ)) * (1 / Real.log ((p * n : ℕ) : ℝ)) := by
          gcongr
    _ = roughWeight p n := by
          rw [roughWeight]
          ring

lemma outflow_roughFlow_eq_sum_finset_add_compl (s : Finset ℕ) (m : ℕ) :
    outflow (roughFlow p) m =
      (∑ n ∈ s, roughFlow p m n) +
        ∑' n : { n // n ∉ s }, roughFlow p m n := by
  simpa [outflow] using ((summable_roughFlow_row p m).sum_add_tsum_subtype_compl s).symm

lemma inflow_roughFlow_eq_sum_finset_add_compl (p : ℕ) (s : Finset ℕ) {n : ℕ}
    (hp : p.Prime) (hn : 1 ≤ n) (hnrough : IsPRough p n) :
    inflow (roughFlow p) n =
      (∑ m ∈ s, roughFlow p m n) +
        ∑' m : { m // m ∉ s }, roughFlow p m n := by
  simpa [inflow] using ((summable_roughFlow_col hp hn hnrough).sum_add_tsum_subtype_compl s).symm

lemma boundaryOutflow_eq_sum_compl_roughFlow (p : ℕ) (s : Finset ℕ) (hp : p.Prime) :
    boundaryOutflow (roughFlow p) (↑s : Set ℕ) =
      ∑ r ∈ s, ∑' n : { n // n ∉ s }, roughFlow p r n := by
        sorry
lemma boundaryInflow_eq_sum_compl_roughFlow (p : ℕ) (s : Finset ℕ) (hp : p.Prime)
    (hs_ge_one : ∀ {n : ℕ}, n ∈ s → 1 ≤ n)
    (hs_rough : ∀ {n : ℕ}, n ∈ s → IsPRough p n) :
    boundaryInflow (roughFlow p) (↑s : Set ℕ) =
      ∑ n ∈ s, ∑' m : { m // m ∉ s }, roughFlow p m n := by
        sorry
lemma tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow_roughFlow {p : ℕ}
    {Ω : Set ℕ} (hp : p.Prime) (hΩfin : Ω.Finite)
    (hΩ_ge_one : ∀ {r : ℕ}, r ∈ Ω → 1 ≤ r)
    (hΩrough : ∀ {r : ℕ}, r ∈ Ω → IsPRough p r) :
    (∑' r : Ω, (outflow (roughFlow p) (r : ℕ) - inflow (roughFlow p) (r : ℕ))) =
      boundaryOutflow (roughFlow p) Ω - boundaryInflow (roughFlow p) Ω := by
  classical
  let s : Finset ℕ := hΩfin.toFinset
  have hsΩ : (↑s : Set ℕ) = Ω := hΩfin.coe_toFinset
  rw [← hsΩ]
  have hout :
      ∑ r ∈ s, outflow (roughFlow p) r =
        (∑ r ∈ s, ∑ n ∈ s, roughFlow p r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, roughFlow p r n := by
    calc
      ∑ r ∈ s, outflow (roughFlow p) r
        = ∑ r ∈ s, ((∑ n ∈ s, roughFlow p r n) +
            ∑' n : {n // n ∉ s}, roughFlow p r n) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [outflow_roughFlow_eq_sum_finset_add_compl (p := p) s r]
      _ = (∑ r ∈ s, ∑ n ∈ s, roughFlow p r n) +
            ∑ r ∈ s, ∑' n : {n // n ∉ s}, roughFlow p r n := by
              rw [Finset.sum_add_distrib]
  have hin :
      ∑ r ∈ s, inflow (roughFlow p) r =
        (∑ r ∈ s, ∑ m ∈ s, roughFlow p m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, roughFlow p m r := by
    calc
      ∑ r ∈ s, inflow (roughFlow p) r
        = ∑ r ∈ s, ((∑ m ∈ s, roughFlow p m r) +
            ∑' m : {m // m ∉ s}, roughFlow p m r) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              have hrΩ : r ∈ Ω := by
                simpa [hsΩ] using (show r ∈ (↑s : Set ℕ) from hr)
              rw [inflow_roughFlow_eq_sum_finset_add_compl p s hp (hΩ_ge_one hrΩ) (hΩrough hrΩ)]
      _ = (∑ r ∈ s, ∑ m ∈ s, roughFlow p m r) +
            ∑ r ∈ s, ∑' m : {m // m ∉ s}, roughFlow p m r := by
              rw [Finset.sum_add_distrib]
  have hinternal :
      ∑ r ∈ s, ∑ n ∈ s, roughFlow p r n =
        ∑ r ∈ s, ∑ m ∈ s, roughFlow p m r := by
    simpa using (Finset.sum_comm (s := s) (t := s) (f := fun r n => roughFlow p r n))
  calc
    (∑' r : (↑s : Set ℕ), (outflow (roughFlow p) (r : ℕ) - inflow (roughFlow p) (r : ℕ)))
      = ∑ r ∈ s, (outflow (roughFlow p) r - inflow (roughFlow p) r) := by
          simpa using
            (Finset.tsum_subtype' s
              (fun r => outflow (roughFlow p) r - inflow (roughFlow p) r))
    _ = (∑ r ∈ s, outflow (roughFlow p) r) - ∑ r ∈ s, inflow (roughFlow p) r := by
          rw [Finset.sum_sub_distrib]
    _ =
        ((∑ r ∈ s, ∑ n ∈ s, roughFlow p r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, roughFlow p r n) -
        ((∑ r ∈ s, ∑ m ∈ s, roughFlow p m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, roughFlow p m r) := by
            rw [hout, hin]
    _ = (∑ r ∈ s, ∑' n : {n // n ∉ s}, roughFlow p r n) -
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, roughFlow p m r := by
            rw [hinternal]
            ring
    _ = boundaryOutflow (roughFlow p) (↑s : Set ℕ) -
          boundaryInflow (roughFlow p) (↑s : Set ℕ) := by
            rw [boundaryOutflow_eq_sum_compl_roughFlow p s hp,
              boundaryInflow_eq_sum_compl_roughFlow p s hp
                (fun {n} hn => hΩ_ge_one (by simpa [hsΩ] using (show n ∈ (↑s : Set ℕ) from hn)))
                (fun {n} hn => hΩrough (by simpa [hsΩ] using (show n ∈ (↑s : Set ℕ) from hn)))]

lemma boundaryOutflow_roughFlow_le_one_div_log_of_downwardClosed {p : ℕ} (hp : p.Prime)
    (hbound : roughKernelSeries p 1 ≤ 1 / Real.log (p : ℝ)) {Ω : Set ℕ}
    (hΩ_ge_two : ∀ {d : ℕ}, d ∈ Ω → 2 ≤ d)
    (hΩrough : ∀ {d : ℕ}, d ∈ Ω → IsPRough p d)
    (hΩdown : ∀ {d e : ℕ}, d ∈ Ω → 2 ≤ e → e ∣ d → e ∈ Ω) :
    boundaryOutflow (roughFlow p) Ω ≤ 1 / Real.log (p : ℝ) := by
      sorry
lemma boundaryOutflow_ge_boundaryInflow_add_tsum_divergence_of_subset_roughFlow
    {p : ℕ} {A Ω : Set ℕ} (hp : p.Prime)
    (hbound : ∀ {n : ℕ}, 1 ≤ n → IsPRough p n →
      roughKernelSeries p n ≤ 1 / Real.log ((p * n : ℕ) : ℝ))
    (hΩfin : Ω.Finite)
    (hΩ_ge_two : ∀ {r : ℕ}, r ∈ Ω → 2 ≤ r)
    (hΩrough : ∀ {r : ℕ}, r ∈ Ω → IsPRough p r)
    (hAΩ : A ⊆ Ω) :
    boundaryInflow (roughFlow p) Ω +
      (∑' a : A, (outflow (roughFlow p) (a : ℕ) - inflow (roughFlow p) (a : ℕ))) ≤
        boundaryOutflow (roughFlow p) Ω := by
  classical
  let f : ℕ → ℝ := fun r => outflow (roughFlow p) r - inflow (roughFlow p) r
  have hnonneg : ∀ r ∈ Ω, 0 ≤ f r := by
    intro r hr
    have hr_lt : 1 < r := lt_of_lt_of_le Nat.one_lt_two (hΩ_ge_two hr)
    have hin_le :
        inflow (roughFlow p) r ≤ outflow (roughFlow p) r := by
      calc
        inflow (roughFlow p) r ≤ roughWeight p r := by
          exact inflow_roughFlow_le_roughWeight_of_bound hp (le_of_lt hr_lt) (hΩrough hr)
            (hbound (le_of_lt hr_lt) (hΩrough hr))
        _ = outflow (roughFlow p) r := (outflow_roughFlow_eq_roughWeight hp hr_lt (hΩrough hr)).symm
    exact sub_nonneg.mpr hin_le
  have hAfin : A.Finite := hΩfin.subset hAΩ
  letI := hΩfin.fintype
  letI := hAfin.fintype
  let e : A ≃ {r : Ω // (r : ℕ) ∈ A} :=
    { toFun := fun a => ⟨⟨a.1, hAΩ a.2⟩, a.2⟩
      invFun := fun r => ⟨r.1.1, r.2⟩
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hAeq :
      (∑' a : A, f (a : ℕ)) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype]
    exact Fintype.sum_equiv e (fun a : A => f (a : ℕ))
      (fun r : {s : Ω // (s : ℕ) ∈ A} => f (r : ℕ)) (by intro a; rfl)
  have hsplit :
      (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
          (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) =
        ∑' r : Ω, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype]
    simpa using
      (Fintype.sum_subtype_add_sum_subtype (fun r : Ω => (r : ℕ) ∈ A)
        (fun r : Ω => f (r : ℕ)))
  have hcompl_nonneg : 0 ≤ ∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ) := by
    rw [tsum_fintype]
    exact Finset.sum_nonneg fun r _ => by
      simpa using hnonneg (r : ℕ) r.1.2
  have hA_le_Ω :
      (∑' a : A, f (a : ℕ)) ≤ ∑' r : Ω, f (r : ℕ) := by
    calc
      ∑' a : A, f (a : ℕ) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := hAeq
      _ ≤ (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
            (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) := by
              linarith
      _ = ∑' r : Ω, f (r : ℕ) := hsplit
  have hΩboundary :
      (∑' r : Ω, f (r : ℕ)) =
        boundaryOutflow (roughFlow p) Ω - boundaryInflow (roughFlow p) Ω := by
    simpa [f] using
      tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow_roughFlow hp hΩfin
        (fun {r} hr => le_trans (by decide : 1 ≤ 2) (hΩ_ge_two hr)) hΩrough
  have hmain :
      (∑' a : A, f (a : ℕ)) ≤
        boundaryOutflow (roughFlow p) Ω - boundaryInflow (roughFlow p) Ω := by
    calc
      ∑' a : A, f (a : ℕ) ≤ ∑' r : Ω, f (r : ℕ) := hA_le_Ω
      _ = boundaryOutflow (roughFlow p) Ω - boundaryInflow (roughFlow p) Ω := hΩboundary
  linarith

lemma flow_into_primitive_member_from_outside_divisorClosure_roughFlow {p : ℕ} {A : Set ℕ}
    (hA : PrimitiveSet A) {a m : ℕ} (ha : a ∈ A)
    (hflow : roughFlow p m a ≠ 0) :
    m ∉ primitiveDivisorClosure A := by
  intro hm
  rcases hm with ⟨hm_ge_two, b, hb, hm_dvd_b⟩
  have hdiv_lt : a ∣ m ∧ a < m := by
    by_contra hnot
    exact hflow (roughFlow_eq_zero_of_not_dvd_lt hnot)
  have ha_dvd_m : a ∣ m := hdiv_lt.1
  have ha_lt_m : a < m := hdiv_lt.2
  have ha_dvd_b : a ∣ b := dvd_trans ha_dvd_m hm_dvd_b
  have hab_eq : a = b := hA.2 ha hb ha_dvd_b
  have hm_dvd_a : m ∣ a := hab_eq ▸ hm_dvd_b
  have ha_pos : 0 < a := lt_of_lt_of_le Nat.zero_lt_two (hA.1 ha)
  have hm_le_a : m ≤ a := Nat.le_of_dvd ha_pos hm_dvd_a
  exact (not_le_of_gt ha_lt_m) hm_le_a

lemma roughWeightSum_le_one_div_log_of_finite {p : ℕ} (hp : p.Prime)
    (hbound : ∀ {n : ℕ}, 1 ≤ n → IsPRough p n →
      roughKernelSeries p n ≤ 1 / Real.log ((p * n : ℕ) : ℝ))
    {A : Set ℕ} (hA : PrimitiveSet A)
    (hArough : ∀ {a : ℕ}, a ∈ A → IsPRough p a) (hfin : A.Finite) :
    roughWeightSum p A ≤ 1 / Real.log (p : ℝ) := by
      sorry
theorem roughWeightSum_le_one_div_log {p : ℕ} (hp : p.Prime)
    (hbound : ∀ {n : ℕ}, 1 ≤ n → IsPRough p n →
      roughKernelSeries p n ≤ 1 / Real.log ((p * n : ℕ) : ℝ))
    {A : Set ℕ} (hA : PrimitiveSet A)
    (hArough : ∀ {a : ℕ}, a ∈ A → IsPRough p a) :
    roughWeightSum p A ≤ 1 / Real.log (p : ℝ) := by
  classical
  have htsum : ∑' a : A, roughWeight p (a : ℕ) ≤ 1 / Real.log (p : ℝ) := by
    refine Real.tsum_le_of_sum_le ?_ ?_
    · intro a
      have ha2 : 2 ≤ (a : ℕ) := hA.1 a.2
      have hlog : 0 < Real.log ((p * (a : ℕ) : ℕ) : ℝ) := by
        exact Real.log_pos (by
          exact_mod_cast (show 1 < p * (a : ℕ) by
            exact lt_of_lt_of_le hp.one_lt
              (Nat.le_mul_of_pos_right p (lt_of_lt_of_le Nat.zero_lt_two ha2))))
      have hden : 0 ≤ ((a : ℕ) : ℝ) * Real.log ((p * (a : ℕ) : ℕ) : ℝ) := by
        positivity
      simpa [roughWeight] using one_div_nonneg.mpr hden
    · intro u
      let s : Finset ℕ := u.image (fun a : A => (a : ℕ))
      have hs_subset : (↑s : Set ℕ) ⊆ A := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
        exact a.2
      have hs_rough : ∀ {n : ℕ}, n ∈ (↑s : Set ℕ) → IsPRough p n := by
        intro n hn
        exact hArough (hs_subset hn)
      have hs_primitive : PrimitiveSet (↑s : Set ℕ) := by
        refine ⟨?_, ?_⟩
        · intro a ha
          exact hA.1 (hs_subset ha)
        · intro a b ha hb hab
          exact hA.2 (hs_subset ha) (hs_subset hb) hab
      have hs_eq :
          roughWeightSum p (↑s : Set ℕ) = ∑ n ∈ s, roughWeight p n := by
        simpa [roughWeightSum, s] using (Finset.tsum_subtype' s (roughWeight p))
      have hu_eq : ∑ n ∈ s, roughWeight p n = ∑ a ∈ u, roughWeight p (a : ℕ) := by
        dsimp [s]
        exact
          Finset.sum_image
            (s := u)
            (g := fun a : A => (a : ℕ))
            (f := roughWeight p)
            Subtype.val_injective.injOn
      calc
        ∑ a ∈ u, roughWeight p (a : ℕ) = roughWeightSum p (↑s : Set ℕ) := by
          rw [← hu_eq, ← hs_eq]
        _ ≤ 1 / Real.log (p : ℝ) := by
          exact roughWeightSum_le_one_div_log_of_finite hp hbound hs_primitive hs_rough
            s.finite_toSet
  simpa [roughWeightSum] using htsum

theorem erdos_strong_on_pRough_multiples_of_prime_of_bound {p : ℕ} (hp : p.Prime)
    (hbound : ∀ {n : ℕ}, 1 ≤ n → IsPRough p n →
      roughKernelSeries p n ≤ 1 / Real.log ((p * n : ℕ) : ℝ))
    {A : Set ℕ} (hA : PrimitiveSet A)
    (hA_sub : A ⊆ {m : ℕ | p ∣ m ∧ IsPRough p (m / p)}) :
    primitiveWeightSum A ≤ erdosWeight p := by
  by_cases hp_mem : p ∈ A
  · have hAeq : A = {p} := by
      ext a
      constructor
      · intro ha
        have hpdvd : p ∣ a := (hA_sub ha).1
        have hEq : p = a := hA.2 hp_mem ha hpdvd
        simp [hEq]
      · intro ha
        simp at ha
        simp [ha, hp_mem]
    rw [hAeq, primitiveWeightSum]
    simp [erdosWeight]
  · let B : Set ℕ := {n : ℕ | p * n ∈ A}
    have hp_pos : 0 < p := hp.pos
    have hB_primitive : PrimitiveSet B := by
      refine ⟨?_, ?_⟩
      · intro b hb
        by_cases hb1 : b = 1
        · exact False.elim <| hp_mem (by simpa [B, hb1] using hb)
        · have hAelt : 2 ≤ p * b := hA.1 (by simpa [B] using hb)
          have hb0 : b ≠ 0 := by
            intro hb0
            simp [hb0] at hAelt
          have hb_pos : 0 < b := Nat.pos_of_ne_zero hb0
          have : 1 < b := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hb0, hb1⟩
          exact Nat.succ_le_of_lt this
      · intro a b ha hb hab
        have hEq : p * a = p * b := hA.2 ha hb (Nat.mul_dvd_mul_left p hab)
        exact Nat.eq_of_mul_eq_mul_left hp_pos hEq
    have hB_rough : ∀ {b : ℕ}, b ∈ B → IsPRough p b := by
      intro b hb
      have hbA : p * b ∈ A := by simpa [B] using hb
      have hsub := hA_sub hbA
      simpa [Nat.mul_div_right _ hp_pos] using hsub.2
    let e : B ≃ A :=
      { toFun := fun b => ⟨p * b.1, b.2⟩
        invFun := fun a => ⟨a.1 / p, by
          have hsub := hA_sub a.2
          have hEq : p * (a.1 / p) = a.1 := Nat.mul_div_cancel' hsub.1
          simp [B, hEq, a.2]⟩
        left_inv := by
          intro b
          apply Subtype.ext
          simp [Nat.mul_div_right _ hp_pos]
        right_inv := by
          intro a
          apply Subtype.ext
          exact Nat.mul_div_cancel' (hA_sub a.2).1 }
    have hWeight :
        primitiveWeightSum A = (1 / (p : ℝ)) * roughWeightSum p B := by
      calc
        primitiveWeightSum A = ∑' b : B, erdosWeight (p * (b : ℕ)) := by
          unfold primitiveWeightSum
          simpa [e] using (Equiv.tsum_eq e (fun a : A => erdosWeight a.1)).symm
        _ = ∑' b : B, (1 / (p : ℝ)) * roughWeight p (b : ℕ) := by
              apply tsum_congr
              intro b
              have hb_pos : 0 < (b : ℕ) := lt_of_lt_of_le Nat.zero_lt_two (hB_primitive.1 b.2)
              have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
              have hb0 : ((b : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb_pos)
              have hlog : 0 < Real.log ((p * (b : ℕ) : ℕ) : ℝ) := by
                exact Real.log_pos (by
                  exact_mod_cast (show 1 < p * (b : ℕ) by
                    exact lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p hb_pos)))
              rw [erdosWeight, roughWeight, Nat.cast_mul]
              field_simp [hp0, hb0, hlog.ne']
        _ = (1 / (p : ℝ)) * roughWeightSum p B := by
              rw [roughWeightSum, tsum_mul_left]
    have hB_bound : roughWeightSum p B ≤ 1 / Real.log (p : ℝ) := by
      exact roughWeightSum_le_one_div_log hp hbound hB_primitive (fun {b} hb => hB_rough hb)
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    calc
      primitiveWeightSum A = (1 / (p : ℝ)) * roughWeightSum p B := hWeight
      _ ≤ (1 / (p : ℝ)) * (1 / Real.log (p : ℝ)) := by
            gcongr
      _ = erdosWeight p := by
            rw [erdosWeight]
            field_simp [Nat.cast_ne_zero.mpr hp.ne_zero, hlogp.ne']

theorem erdos_strong_on_pRough_multiples_of_odd_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {A : Set ℕ} (hA : PrimitiveSet A)
    (hA_sub : A ⊆ {m : ℕ | p ∣ m ∧ IsPRough p (m / p)}) :
    primitiveWeightSum A ≤ erdosWeight p := by
  exact erdos_strong_on_pRough_multiples_of_prime_of_bound hp
    (fun {n} hn hnrough => roughKernelSeries_le_main_bound hp hodd hn hnrough) hA hA_sub

theorem erdos_strong_of_prime {p : ℕ} (hp : p.Prime) : erdos_strong p := by
  intro A hA hA_sub
  by_cases htwo : p = 2
  · subst htwo
    exact erdos_strong_of_two hA hA_sub
  · exact erdos_strong_on_pRough_multiples_of_odd_prime hp htwo hA hA_sub

lemma erdosWeight_nonneg_of_prime {p : ℕ} (hp : p.Prime) :
    0 ≤ erdosWeight p := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (Nat.one_lt_cast.2 hp.one_lt)
  have hden : 0 ≤ ((p : ℝ) * Real.log p) := by positivity
  simpa [erdosWeight] using one_div_nonneg.mpr hden

lemma finset_sum_le_primeWeightSum {s : Finset ℕ}
    (hs : PrimitiveSet (↑s : Set ℕ)) :
    ∑ n ∈ s, erdosWeight n ≤ primeWeightSum := by
  classical
  let P : Finset ℕ := s.image Nat.minFac
  have hPprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
    have hn_ne_one : n ≠ 1 := by
      exact ne_of_gt <| lt_of_lt_of_le (by decide : 1 < 2) (hs.1 hn)
    exact Nat.minFac_prime hn_ne_one
  have hfiber_le : ∀ p ∈ P, ∑ n ∈ s with Nat.minFac n = p, erdosWeight n ≤ erdosWeight p := by
    intro p hp
    have hp' : p.Prime := hPprime p hp
    have hs_p_primitive : PrimitiveSet (↑(s.filter fun n => Nat.minFac n = p) : Set ℕ) := by
      constructor
      · intro a ha
        exact hs.1 (Finset.mem_filter.mp ha).1
      · intro a b ha hb hab
        exact hs.2 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
    have hs_p_subset :
        (↑(s.filter fun n => Nat.minFac n = p) : Set ℕ) ⊆
          {m : ℕ | p ∣ m ∧ IsPRough p (m / p)} := by
      intro m hm
      have hm_mem : m ∈ s := (Finset.mem_filter.mp hm).1
      have hm_minFac : Nat.minFac m = p := (Finset.mem_filter.mp hm).2
      have hm_ne_one : m ≠ 1 := by
        exact ne_of_gt <| lt_of_lt_of_le (by decide : 1 < 2) (hs.1 hm_mem)
      have hpdiv : p ∣ m := by
        rw [← hm_minFac]
        exact Nat.minFac_dvd m
      refine ⟨hpdiv, ?_⟩
      intro q hq hqdiv
      have hqdivm : q ∣ m := dvd_trans hqdiv (Nat.div_dvd_of_dvd hpdiv)
      calc
        p = Nat.minFac m := hm_minFac.symm
        _ ≤ q := Nat.minFac_le_of_dvd hq.two_le hqdivm
    have hstrong := erdos_strong_of_prime hp'
    have hsum_eq :
        primitiveWeightSum (↑(s.filter fun n => Nat.minFac n = p) : Set ℕ) =
          ∑ n ∈ s with Nat.minFac n = p, erdosWeight n := by
      simpa [primitiveWeightSum] using
        (Finset.tsum_subtype' (s.filter fun n => Nat.minFac n = p) erdosWeight)
    calc
      ∑ n ∈ s with Nat.minFac n = p, erdosWeight n
          = primitiveWeightSum (↑(s.filter fun n => Nat.minFac n = p) : Set ℕ) := by
              rw [hsum_eq]
      _ ≤ erdosWeight p := hstrong hs_p_primitive hs_p_subset
  have hpartition :
      ∑ p ∈ P, ∑ n ∈ s with Nat.minFac n = p, erdosWeight n = ∑ n ∈ s, erdosWeight n := by
    simpa [P] using
      (Finset.sum_fiberwise_of_maps_to
        (s := s) (t := P) (g := Nat.minFac)
        (h := fun n hn => Finset.mem_image_of_mem Nat.minFac hn)
        (f := erdosWeight))
  have hprime_sum_le :
      ∑ p ∈ P, erdosWeight p ≤ primeWeightSum := by
    let S : Set {p : ℕ // p.Prime} := {q | q.1 ∈ P}
    let ePFun : {n : ℕ // n ∈ P} → S := fun n => ⟨⟨n.1, hPprime n.1 n.2⟩, n.2⟩
    have heP_bij : Function.Bijective ePFun := by
      constructor
      · intro a b hab
        rcases a with ⟨a, ha⟩
        rcases b with ⟨b, hb⟩
        simp [ePFun] at hab
        subst b
        rfl
      · intro q
        refine ⟨⟨q.1.1, q.2⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        rfl
    let eP : {n : ℕ // n ∈ P} ≃ S := Equiv.ofBijective ePFun heP_bij
    have hP_eq :
        ∑ p ∈ P, erdosWeight p = ∑' q : S, erdosWeight q.1.1 := by
      calc
        ∑ p ∈ P, erdosWeight p = ∑' n : {n : ℕ // n ∈ P}, erdosWeight n.1 := by
          simpa using (Finset.tsum_subtype' P erdosWeight).symm
        _ = ∑' q : S, erdosWeight q.1.1 := by
          simpa [eP] using
            (Equiv.tsum_eq eP (fun q : S => erdosWeight q.1.1))
    have hnonneg_prime : ∀ q : {p : ℕ // p.Prime}, 0 ≤ erdosWeight q.1 := by
      intro q
      exact erdosWeight_nonneg_of_prime q.2
    calc
      ∑ p ∈ P, erdosWeight p = ∑' q : S, erdosWeight q.1.1 := hP_eq
      _ ≤ ∑' q : {p : ℕ // p.Prime}, erdosWeight q.1 := by
            exact
              Summable.tsum_subtype_le
                (fun q : {p : ℕ // p.Prime} => erdosWeight q.1)
                S hnonneg_prime summable_primeWeights
      _ = primeWeightSum := rfl
  calc
    ∑ n ∈ s, erdosWeight n = ∑ p ∈ P, ∑ n ∈ s with Nat.minFac n = p, erdosWeight n := by
      rw [← hpartition]
    _ ≤ ∑ p ∈ P, erdosWeight p := by
      exact Finset.sum_le_sum hfiber_le
    _ ≤ primeWeightSum := hprime_sum_le

lemma primitiveWeightSum_le_primeWeightSum_of_finite_alt {A : Set ℕ}
    (hA : PrimitiveSet A) (hfin : A.Finite) :
    primitiveWeightSum A ≤ primeWeightSum := by
  classical
  let s : Finset ℕ := hfin.toFinset
  have hsA : (↑s : Set ℕ) = A := by
    simp [s]
  have hs_primitive : PrimitiveSet (↑s : Set ℕ) := by
    simpa [hsA] using hA
  calc
    primitiveWeightSum A = ∑ n ∈ s, erdosWeight n := by
      rw [← hsA]
      simpa [primitiveWeightSum, s] using (Finset.tsum_subtype' s erdosWeight)
    _ ≤ primeWeightSum := finset_sum_le_primeWeightSum hs_primitive

theorem erdos164_alt :
    PrimitiveSet primeSet ∧
      primitiveWeightSum primeSet = primeWeightSum ∧
      ∀ A : Set ℕ, PrimitiveSet A → primitiveWeightSum A ≤ primitiveWeightSum primeSet := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro a ha
      have hPrime : a.Prime := by
        simpa [primeSet] using ha
      exact hPrime.two_le
    · intro a b ha hb hab
      have haPrime : a.Prime := by
        simpa [primeSet] using ha
      have hbPrime : b.Prime := by
        simpa [primeSet] using hb
      have ha_ne_one : a ≠ 1 := by
        exact ne_of_gt <| lt_of_lt_of_le (by decide : 1 < 2) haPrime.two_le
      have hEq : b = a := (hbPrime.dvd_iff_eq ha_ne_one).mp hab
      simpa using hEq.symm
  · rfl
  · intro A hA
    simpa [primeWeightSum] using
      (primitiveWeightSum_le_primeWeightSum_of_finite_subsets (A := A) <| by
        intro A₀ hA₀ hA₀fin
        have hA₀_primitive : PrimitiveSet A₀ := by
          constructor
          · intro a ha
            exact hA.1 (hA₀ ha)
          · intro a b ha hb hab
            exact hA.2 (hA₀ ha) (hA₀ hb) hab
        exact primitiveWeightSum_le_primeWeightSum_of_finite_alt hA₀_primitive hA₀fin)

#print axioms erdos164
-- 'Erdos164.erdos164' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_strong_of_two
-- 'Erdos164.erdos_strong_of_two' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_strong_of_prime
-- 'Erdos164.erdos_strong_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos164_alt
-- 'Erdos164.erdos164_alt' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos164
