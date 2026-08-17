/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.TwoLargeForest

/-!
# Uniform sampled forests in the compact cover range

This module packages the probabilistic part of the DKM two-large-cover
argument.  If the degree-controlling cover has size `c = alpha * sqrt n`
with `alpha` in a fixed compact subinterval of `(0, infinity)`, the bounded
internal graph has sampled linear forests of size
`(1 / alpha - rho) * sqrt n`, apart from an arbitrarily small proportion of
all samples.  The proof uses the unconditional asymptotic linear-arboricity
theorem and the sharp bipartite squared-degree estimate.
-/

namespace Erdos622
namespace CompactBoundedForest

open Filter Finset Real Set
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- A transfer below the `64K` square-root threshold is at most one
sixty-fourth of a cover above the `K` threshold, after normalization. -/
lemma small_transfer_ratio
    {n K d c : ℕ} (hK : 0 < K)
    (hd : d ≤ sqrtCoverThreshold (64 * K) n)
    (hc : sqrtCoverThreshold K n ≤ c) :
    (d : ℝ) / Real.sqrt n ≤ ((c : ℝ) / Real.sqrt n) / 64 := by
  have hK64 : 0 < 64 * K := Nat.mul_pos (by norm_num) hK
  have hd' : d ≤ Nat.sqrt n / (64 * K) := by
    simpa [sqrtCoverThreshold] using hd
  have hmul : 64 * d * K ≤ Nat.sqrt n := by
    have := (Nat.le_div_iff_mul_le hK64).mp hd'
    nlinarith
  have h64d : 64 * d ≤ Nat.sqrt n / K :=
    (Nat.le_div_iff_mul_le hK).2 (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul)
  have hnat : 64 * d ≤ c := h64d.trans (by
    simpa [sqrtCoverThreshold] using hc)
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hsqrt : 0 < Real.sqrt n :=
      Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hn)
    have hreal : (64 : ℝ) * d ≤ c := by exact_mod_cast hnat
    rw [show (c : ℝ) / Real.sqrt n / 64 =
      ((c : ℝ) / 64) / Real.sqrt n by ring]
    rw [div_le_div_iff_of_pos_right hsqrt]
    nlinarith

/-- Convert the good balancing-intersection event into the real deviation
bound used by the shifted compact window. -/
lemma balancing_transfer_deviation
    {n d : ℕ} {sigma : ℝ} {T S : Finset (Fin (2 * n))}
    (hsigma : 0 ≤ sigma) (hTcard : T.card = d)
    (hnot : ¬ sigma / 2 * (Nat.sqrt n : ℝ) ≤
      |SamplingSuitable.intersectionCount T S - (T.card : ℝ) / 2|) :
    |(((2 * (S ∩ T).card : ℕ) : ℝ) - (d : ℝ))| ≤
      sigma * Real.sqrt n := by
  have hsmall :
      |((S ∩ T).card : ℝ) - (d : ℝ) / 2| <
        sigma / 2 * (Nat.sqrt n : ℝ) := by
    rw [← hTcard]
    simpa [SamplingSuitable.intersectionCount] using lt_of_not_ge hnot
  have hsqrtFloor : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
    Real.nat_sqrt_le_real_sqrt
  have hsmall' :
      |((S ∩ T).card : ℝ) - (d : ℝ) / 2| <
        sigma / 2 * Real.sqrt n :=
    hsmall.trans_le (mul_le_mul_of_nonneg_left hsqrtFloor (by positivity))
  have heq :
      (((2 * (S ∩ T).card : ℕ) : ℝ) - (d : ℝ)) =
        2 * (((S ∩ T).card : ℝ) - (d : ℝ) / 2) := by
    push_cast
    ring
  rw [heq, abs_mul]
  norm_num
  nlinarith

/-- The scalar capacity calculation underlying the compact sampled-forest
estimate.  The hypotheses called `hlargeDegree` and `hsmallLoss` are the two
uniform conditions which become automatic as `n` tends to infinity. -/
private lemma compact_capacity
    {eta M rho : ℝ} {n c d e : ℕ}
    (heta : 0 < eta) (hM : 0 < M) (hrho : 0 < rho)
    (hetaM : eta ≤ M) (hrhoM : rho * M < 1)
    (hn : 0 < n)
    (hcLower : eta * Real.sqrt n ≤ c)
    (hcUpper : (c : ℝ) ≤ M * Real.sqrt n)
    (hdUpper : (d : ℝ) ≤ M * Real.sqrt n)
    (hedge : n ≤ e + d)
    (hlargeDegree : 3 / 2 + rho * eta / 64 ≤
      3 * (rho * eta / 64) * c)
    (hsmallLoss : M * Real.sqrt n ≤ rho * eta * n / 4) :
    let theta := rho * eta / 64
    let q := c + 1
    let Dsample := Nat.ceil ((1 / 2 + theta) * q)
    let r := Nat.ceil
      ((1 / ((c : ℝ) / Real.sqrt n) - rho) * Real.sqrt n)
    (r : ℝ) * ((1 + theta) * (Dsample : ℝ) / 2) +
        theta * n ≤ (e : ℝ) / 4 := by
  dsimp only
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrtSq : (Real.sqrt n) ^ 2 = n :=
    Real.sq_sqrt (by positivity)
  have hcposR : (0 : ℝ) < c := by
    have : 0 < eta * Real.sqrt n := mul_pos heta hsqrt
    exact this.trans_le hcLower
  have hcpos : 0 < c := by exact_mod_cast hcposR
  have htheta : 0 < rho * eta / 64 := by positivity
  have hxlt : rho * eta < 1 :=
    (mul_le_mul_of_nonneg_left hetaM hrho.le).trans_lt hrhoM
  have hthetale : rho * eta / 64 ≤ 1 / 64 := by linarith
  have halphaPos : 0 < (c : ℝ) / Real.sqrt n :=
    div_pos hcposR hsqrt
  have halphaUpper : (c : ℝ) / Real.sqrt n ≤ M := by
    rw [div_le_iff₀ hsqrt]
    exact hcUpper
  have hMInv : 1 / M ≤ 1 / ((c : ℝ) / Real.sqrt n) := by
    exact one_div_le_one_div_of_le halphaPos halphaUpper
  have hrhoInv : rho < 1 / M := by
    rw [lt_div_iff₀ hM]
    exact hrhoM
  have htargetNonneg :
      0 ≤ (1 / ((c : ℝ) / Real.sqrt n) - rho) * Real.sqrt n := by
    have : rho ≤ 1 / ((c : ℝ) / Real.sqrt n) :=
      hrhoInv.le.trans hMInv
    positivity
  have hrUpper :
      (Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
          Real.sqrt n) : ℝ) <
        (1 / ((c : ℝ) / Real.sqrt n) - rho) *
          Real.sqrt n + 1 :=
    Nat.ceil_lt_add_one htargetNonneg
  have htargetMul :
      ((1 / ((c : ℝ) / Real.sqrt n) - rho) * Real.sqrt n) * c =
        n - rho * c * Real.sqrt n := by
    field_simp [ne_of_gt hcposR, ne_of_gt hsqrt]
    nlinarith
  have hcsqrt : eta * n ≤ (c : ℝ) * Real.sqrt n := by
    calc
      eta * n = eta * (Real.sqrt n) ^ 2 := by rw [hsqrtSq]
      _ = (eta * Real.sqrt n) * Real.sqrt n := by ring
      _ ≤ (c : ℝ) * Real.sqrt n :=
        mul_le_mul_of_nonneg_right hcLower hsqrt.le
  have hcSmall : (c : ℝ) ≤ rho * eta * n / 4 :=
    hcUpper.trans hsmallLoss
  have hdSmall : (d : ℝ) ≤ rho * eta * n / 4 :=
    hdUpper.trans hsmallLoss
  have hrc :
      (Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
          Real.sqrt n) : ℝ) * c ≤
        (1 - 3 * (rho * eta) / 4) * n := by
    have hmul := mul_lt_mul_of_pos_right hrUpper hcposR
    rw [add_mul, htargetMul] at hmul
    have hrhocsqrt : rho * eta * n ≤
        rho * ((c : ℝ) * Real.sqrt n) :=
      by simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hcsqrt hrho.le
    nlinarith
  have hDceil :
      (Nat.ceil ((1 / 2 + rho * eta / 64) * ((c : ℝ) + 1)) : ℝ) <
        (1 / 2 + rho * eta / 64) * ((c : ℝ) + 1) + 1 := by
    apply Nat.ceil_lt_add_one
    positivity
  have hDsample :
      (Nat.ceil ((1 / 2 + rho * eta / 64) * ((c : ℝ) + 1)) : ℝ) ≤
        (1 / 2 + 4 * (rho * eta / 64)) * c := by
    calc
      _ ≤ (1 / 2 + rho * eta / 64) * ((c : ℝ) + 1) + 1 :=
        hDceil.le
      _ ≤ (1 / 2 + 4 * (rho * eta / 64)) * c := by
        nlinarith
  have hcoefficient :
      (1 + rho * eta / 64) *
          (1 / 2 + 4 * (rho * eta / 64)) / 2 ≤
        1 / 4 + 3 * (rho * eta / 64) := by
    nlinarith [sq_nonneg (rho * eta / 64)]
  have hcost :
      (Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
            Real.sqrt n) : ℝ) *
          ((1 + rho * eta / 64) *
            (Nat.ceil ((1 / 2 + rho * eta / 64) *
              ((c : ℝ) + 1)) : ℝ) / 2) ≤
        (1 / 4 + 3 * (rho * eta / 64)) *
          (1 - 3 * (rho * eta) / 4) * n := by
    calc
      _ ≤ (Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
              Real.sqrt n) : ℝ) *
            (((1 + rho * eta / 64) *
              (1 / 2 + 4 * (rho * eta / 64)) / 2) * c) := by
          have hscale : 0 ≤
              (Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
                Real.sqrt n) : ℝ) * ((1 + rho * eta / 64) / 2) := by
            positivity
          have hm := mul_le_mul_of_nonneg_left hDsample hscale
          nlinarith
      _ ≤ (Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
              Real.sqrt n) : ℝ) *
            ((1 / 4 + 3 * (rho * eta / 64)) * c) := by
          gcongr
      _ = (1 / 4 + 3 * (rho * eta / 64)) *
            ((Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
              Real.sqrt n) : ℝ) * c) := by ring
      _ ≤ (1 / 4 + 3 * (rho * eta / 64)) *
            ((1 - 3 * (rho * eta) / 4) * n) := by
          gcongr
      _ = _ := by ring
  have hcost' :
      (Nat.ceil ((1 / ((c : ℝ) / Real.sqrt n) - rho) *
            Real.sqrt n) : ℝ) *
          ((1 + rho * eta / 64) *
            (Nat.ceil ((1 / 2 + rho * eta / 64) *
              ((c : ℝ) + 1)) : ℝ) / 2) ≤
        (1 / 4 - 9 * (rho * eta) / 64) * n := by
    calc
      _ ≤ (1 / 4 + 3 * (rho * eta / 64)) *
          (1 - 3 * (rho * eta) / 4) * n := hcost
      _ ≤ (1 / 4 - 9 * (rho * eta) / 64) * n := by
        have hnR : (0 : ℝ) ≤ n := by positivity
        have :
            (1 / 4 + 3 * (rho * eta / 64)) *
                (1 - 3 * (rho * eta) / 4) ≤
              1 / 4 - 9 * (rho * eta) / 64 := by
          calc
            (1 / 4 + 3 * (rho * eta / 64)) *
                (1 - 3 * (rho * eta) / 4) =
              (1 / 4 - 9 * (rho * eta) / 64) -
                9 * (rho * eta) ^ 2 / 256 := by ring
            _ ≤ 1 / 4 - 9 * (rho * eta) / 64 :=
              sub_le_self _ (by positivity)
        exact mul_le_mul_of_nonneg_right this hnR
  have hedgeR : (n : ℝ) ≤ e + d := by exact_mod_cast hedge
  calc
    _ ≤ (1 / 4 - 9 * (rho * eta) / 64) * n +
        rho * eta / 64 * n := by
      simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
        add_le_add_right hcost' (rho * eta / 64 * n)
    _ ≤ ((n : ℝ) - d) / 4 := by
      have hdQuarter : (d : ℝ) / 4 ≤ rho * eta * n / 16 := by
        calc
          (d : ℝ) / 4 ≤ (rho * eta * n / 4) / 4 := by gcongr
          _ = rho * eta * n / 16 := by ring
      have hdEighth : (d : ℝ) / 4 ≤ rho * eta * n / 8 := by
        calc
          (d : ℝ) / 4 ≤ rho * eta * n / 16 := hdQuarter
          _ ≤ rho * eta * n / 8 := by
            have : 0 ≤ rho * eta * n := by positivity
            have hm := mul_le_mul_of_nonneg_left
              (show (1 : ℝ) / 16 ≤ 1 / 8 by norm_num) this
            simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_comm,
              mul_left_comm] using hm
      calc
        (1 / 4 - 9 * (rho * eta) / 64) * n +
            rho * eta / 64 * n =
          (n : ℝ) / 4 - rho * eta * n / 8 := by ring
        _ ≤ (n : ℝ) / 4 - d / 4 := sub_le_sub_left hdEighth _
        _ = ((n : ℝ) - d) / 4 := by ring
    _ ≤ (e : ℝ) / 4 := by linarith

/-- Uniform compact-cover sampled-Alon estimate.  Here `C` controls the
ambient maximum degree (`q = |C|+1`), while `D` is the small bipartition
class and also accounts for the loss in the edge lower bound.  The returned
integer `r` is at least the desired real capacity. -/
theorem eventually_compact_bounded_sample_forest
    {eta M rho delta : ℝ}
    (heta : 0 < eta) (hM : 0 < M) (hrho : 0 < rho)
    (hdelta : 0 < delta) (hetaM : eta ≤ M)
    (hrhoM : rho * M < 1) :
    ∀ᶠ n : ℕ in atTop, ∀
      (C D E : Finset (Fin (2 * n)))
      (J : SimpleGraph (Fin (2 * n))),
      eta * Real.sqrt n ≤ C.card →
      (C.card : ℝ) ≤ M * Real.sqrt n →
      (D.card : ℝ) ≤ M * Real.sqrt n →
      J.IsBipartiteWith (D : Set (Fin (2 * n))) (E : Set (Fin (2 * n))) →
      (∀ v, J.degree v ≤ C.card + 1) →
      n ≤ J.edgeFinset.card + D.card →
      ∃ r : ℕ,
        (1 / ((C.card : ℝ) / Real.sqrt n) - rho) * Real.sqrt n ≤ r ∧
        ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (J.induce (S : Set (Fin (2 * n))))
              Finset.univ r).card : ℝ)) ≤
          delta * (2 : ℝ) ^ (2 * n) := by
  let theta : ℝ := rho * eta / 64
  have htheta : 0 < theta := by dsimp [theta]; positivity
  obtain ⟨D₀, hAlon⟩ :=
    TwoLargeForest.eventually_containsLinearForestWith_induce htheta
  have hmajorant := TwoLargeForest.compactLAFailureMajorant_tendsto_zero
    heta hM (show 0 < 2 * theta by positivity) htheta
  have hmajorantSmall : ∀ᶠ n : ℕ in atTop,
      TwoLargeForest.compactLAFailureMajorant eta M (2 * theta) theta n ≤
        delta := by
    have hevent := hmajorant.eventually (Iio_mem_nhds hdelta)
    filter_upwards [hevent] with n hn
    exact hn.le
  have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hx : 0 < rho * eta := mul_pos hrho heta
  have hlarge : ∀ᶠ n : ℕ in atTop,
      3 / 2 + theta ≤ 3 * theta * (eta * Real.sqrt n) ∧
      M * Real.sqrt n ≤ rho * eta * n / 4 ∧
      (D₀ : ℝ) ≤ (1 / 2 + theta) * (eta * Real.sqrt n) := by
    have hfirst := hsqrtTop.eventually_ge_atTop
      ((3 / 2 + theta) / (3 * theta * eta))
    have hsecond := hsqrtTop.eventually_ge_atTop (4 * M / (rho * eta))
    have hthird := hsqrtTop.eventually_ge_atTop
      ((D₀ : ℝ) / ((1 / 2 + theta) * eta))
    filter_upwards [hfirst, hsecond, hthird,
      eventually_gt_atTop (0 : ℕ)] with n hn1 hn2 hn3 hnpos
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
    have hsqrtSq : (Real.sqrt n) ^ 2 = n :=
      Real.sq_sqrt (by positivity)
    constructor
    · have hcoef : 0 < 3 * theta * eta := by positivity
      calc
        3 / 2 + theta =
            ((3 / 2 + theta) / (3 * theta * eta)) *
              (3 * theta * eta) := by field_simp
        _ ≤ Real.sqrt n * (3 * theta * eta) :=
          mul_le_mul_of_nonneg_right hn1 hcoef.le
        _ = 3 * theta * (eta * Real.sqrt n) := by ring
    constructor
    · have hcoef : 0 < rho * eta := hx
      calc
        M * Real.sqrt n ≤
            (rho * eta / 4 * Real.sqrt n) * Real.sqrt n := by
          have := mul_le_mul_of_nonneg_right hn2 hsqrt.le
          field_simp at this ⊢
          nlinarith
        _ = rho * eta * (Real.sqrt n) ^ 2 / 4 := by ring
        _ = rho * eta * n / 4 := by rw [hsqrtSq]
    · have hcoef : 0 < (1 / 2 + theta) * eta := by positivity
      calc
        (D₀ : ℝ) =
            ((D₀ : ℝ) / ((1 / 2 + theta) * eta)) *
              ((1 / 2 + theta) * eta) := by field_simp
        _ ≤ Real.sqrt n * ((1 / 2 + theta) * eta) :=
          mul_le_mul_of_nonneg_right hn3 hcoef.le
        _ = (1 / 2 + theta) * (eta * Real.sqrt n) := by ring
  filter_upwards [hmajorantSmall, hlarge,
    eventually_gt_atTop (0 : ℕ)] with n hmajor hnlarge hn
  intro C D E J hcLower hcUpper hdUpper hbip hdegree hedge
  let q : ℕ := C.card + 1
  let Dsample : ℕ := Nat.ceil ((1 / 2 + theta) * q)
  let r : ℕ := Nat.ceil
    ((1 / ((C.card : ℝ) / Real.sqrt n) - rho) * Real.sqrt n)
  refine ⟨r, ?_, ?_⟩
  · dsimp [r]
    exact Nat.le_ceil _
  have hq : 0 < q := by dsimp [q]; omega
  have hD₀ : D₀ ≤ Dsample := by
    have hDreal : (D₀ : ℝ) ≤
        (1 / 2 + theta) * q := by
      calc
        (D₀ : ℝ) ≤ (1 / 2 + theta) * (eta * Real.sqrt n) :=
          hnlarge.2.2
        _ ≤ (1 / 2 + theta) * C.card := by gcongr
        _ ≤ (1 / 2 + theta) * q := by
          dsimp [q]
          gcongr
          exact Nat.le_succ _
    exact_mod_cast hDreal.trans (Nat.le_ceil _)
  have hdegreeMargin : ∀ v,
      (J.degree v : ℝ) / 2 + theta * q ≤ Dsample := by
    intro v
    have hv : (J.degree v : ℝ) ≤ q := by
      exact_mod_cast hdegree v
    have hceil : (1 / 2 + theta) * q ≤ (Dsample : ℝ) := by
      dsimp [Dsample]
      exact Nat.le_ceil _
    linarith
  have hcapacity :
      (r : ℝ) * ((1 + theta) * (Dsample : ℝ) / 2) +
          theta * n ≤ (J.edgeFinset.card : ℝ) / 4 := by
    exact compact_capacity heta hM hrho hetaM hrhoM hn hcLower hcUpper
      hdUpper hedge
      (hnlarge.1.trans (by gcongr)) hnlarge.2.1
  have hedgePos : 0 < J.edgeFinset.card := by
    by_contra he0
    have hezero : J.edgeFinset.card = 0 := Nat.eq_zero_of_not_pos he0
    rw [hezero, zero_add] at hedge
    have hdSmall : (D.card : ℝ) ≤ rho * eta * n / 4 :=
      hdUpper.trans hnlarge.2.1
    have hedgeR : (n : ℝ) ≤ D.card := by exact_mod_cast hedge
    have hxlt : rho * eta < 1 :=
      (mul_le_mul_of_nonneg_left hetaM hrho.le).trans_lt hrhoM
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  have hvariancePos :
      0 < ∑ v : Fin (2 * n), (J.degree v : ℝ) ^ 2 := by
    have hsumPos : 0 < ∑ v : Fin (2 * n), J.degree v := by
      rw [J.sum_degrees_eq_twice_card_edges]
      omega
    have hsumPosR : 0 < ∑ v : Fin (2 * n), (J.degree v : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hsumPos
    refine hsumPosR.trans_le (Finset.sum_le_sum fun v _ ↦ ?_)
    have : (J.degree v : ℝ) ≤ (J.degree v : ℝ) ^ 2 := by
      by_cases hv : J.degree v = 0
      · simp [hv]
      · have hvone : (1 : ℝ) ≤ J.degree v := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hv
        nlinarith [show (0 : ℝ) ≤ J.degree v by positivity]
    exact this
  let variance : ℝ :=
    2 * M * (M + 1) ^ 2 * n * Real.sqrt n
  have hvariance :
      (∑ v : Fin (2 * n), (J.degree v : ℝ) ^ 2) ≤ variance := by
    have hraw :=
      TwoLargeForest.sum_degree_sq_le_bipartite_left_card_mul_sq
        J D E q hbip hdegree
    have hsqrt : 1 ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hn
    have hqUpper : (q : ℝ) ≤ (M + 1) * Real.sqrt n := by
      dsimp [q]
      push_cast
      nlinarith [hcUpper]
    calc
      _ ≤ 2 * (D.card : ℝ) * (q : ℝ) ^ 2 := hraw
      _ ≤ 2 * (M * Real.sqrt n) *
          ((M + 1) * Real.sqrt n) ^ 2 := by gcongr
      _ = variance := by
        dsimp [variance]
        calc
          2 * (M * Real.sqrt n) * ((M + 1) * Real.sqrt n) ^ 2 =
              2 * M * (M + 1) ^ 2 * (Real.sqrt n) ^ 2 * Real.sqrt n := by
            ring
          _ = 2 * M * (M + 1) ^ 2 * n * Real.sqrt n := by
            rw [Real.sq_sqrt (by positivity)]
  have hnotGood :=
    TwoLargeForest.not_isInducedLinearArboricityGood_count_le_of_variance_bound
      J hq (show 0 < theta * q by positivity)
      (show 0 ≤ theta * n by positivity) hdegree hdegreeMargin hcapacity
      hvariancePos hvariance
  have hsub :
      (Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (J.induce (S : Set (Fin (2 * n))))
              Finset.univ r) ⊆
        (Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ TwoLargeForest.IsInducedLinearArboricityGood
              J S theta Dsample r) := by
    intro S hS
    have hm := Finset.mem_filter.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨hm.1, ?_⟩
    intro hgood
    exact hm.2 (hAlon (Fin (2 * n)) J S Dsample r hD₀ hgood)
  have hcard :
      (((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (J.induce (S : Set (Fin (2 * n))))
              Finset.univ r)).card : ℝ) ≤
        (((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ TwoLargeForest.IsInducedLinearArboricityGood
              J S theta Dsample r)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have htail :
      (((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ TwoLargeForest.IsInducedLinearArboricityGood
              J S theta Dsample r)).card : ℝ) ≤
        TwoLargeForest.compactLAFailureMajorant eta M (2 * theta) theta n *
          (2 : ℝ) ^ (2 * n) := by
    calc
      _ ≤ (Fintype.card (Fin (2 * n)) : ℝ) *
            (2 * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) *
              exp (-2 * (theta * q) ^ 2 / q)) +
          2 * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) *
            exp (-2 * (theta * n) ^ 2 / variance) := hnotGood
      _ ≤ TwoLargeForest.compactLAFailureMajorant eta M
            (2 * theta) theta n * (2 : ℝ) ^ (2 * n) := by
        simp only [Fintype.card_fin]
        have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
        have hsqrtSq : (Real.sqrt n) ^ 2 = n :=
          Real.sq_sqrt (by positivity)
        have hqR : (0 : ℝ) < q := by exact_mod_cast hq
        have hdegreeExp :
            exp (-2 * (theta * q) ^ 2 / q) ≤
              exp (-(((2 * theta) ^ 2 * eta / 2) * Real.sqrt n)) := by
          apply Real.exp_le_exp.mpr
          have hqLower : eta * Real.sqrt n ≤ (q : ℝ) := by
            calc
              eta * Real.sqrt n ≤ C.card := hcLower
              _ ≤ q := by dsimp [q]; norm_num
          field_simp [ne_of_gt hqR]
          nlinarith [sq_nonneg theta]
        have hvarianceDef :
            variance = 2 * M * (M + 1) ^ 2 * n * Real.sqrt n := rfl
        have hedgeExp :
            exp (-2 * (theta * n) ^ 2 / variance) =
              exp (-(theta ^ 2 / (M * (M + 1) ^ 2)) *
                Real.sqrt n) := by
          congr 1
          rw [hvarianceDef]
          have hMne : M ≠ 0 := hM.ne'
          have hMone : M + 1 ≠ 0 := by positivity
          have hnR : (n : ℝ) ≠ 0 := by positivity
          field_simp [hMne, hMone, hnR, ne_of_gt hsqrt]
          rw [hsqrtSq]
        rw [hedgeExp]
        unfold TwoLargeForest.compactLAFailureMajorant
        push_cast
        have hp : 0 ≤ (2 : ℝ) ^ (2 * n) := by positivity
        rw [show
          (2 * n : ℝ) *
                (2 * (2 : ℝ) ^ (2 * n) *
                  exp (-2 * (theta * q) ^ 2 / q)) +
              2 * (2 : ℝ) ^ (2 * n) *
                exp (-(theta ^ 2 / (M * (M + 1) ^ 2)) * Real.sqrt n) =
            (4 * (n : ℝ) * exp (-2 * (theta * q) ^ 2 / q) +
              2 * exp (-(theta ^ 2 / (M * (M + 1) ^ 2)) * Real.sqrt n)) *
              (2 : ℝ) ^ (2 * n) by ring]
        apply mul_le_mul_of_nonneg_right _ hp
        have hdegreeTerm :
            4 * (n : ℝ) * exp (-2 * (theta * q) ^ 2 / q) ≤
              4 * (n : ℝ) *
                exp (-((2 * theta) ^ 2 * eta / 2) * Real.sqrt n) := by
          have hm := mul_le_mul_of_nonneg_left hdegreeExp
            (show 0 ≤ 4 * (n : ℝ) by positivity)
          simpa only [neg_mul] using hm
        exact add_le_add hdegreeTerm le_rfl
  exact hcard.trans (htail.trans (mul_le_mul_of_nonneg_right hmajor (by positivity)))

/-- Forward-orientation package used by the final two-large-cover argument.
The minimum-cover mechanism supplies the left supported forest, while the
bounded graph `JB` supplied by `OrientedBoundedInternal` supplies the right
supported forest.  Both conclusions are already expressed in ambient
coordinates, so no further support bookkeeping is needed downstream. -/
theorem eventually_forward_oriented_matching_and_forest
    {L : ℕ} (hL : 0 < L) {eta M eps rho delta : ℝ}
    (heta : 0 < eta) (hM : 0 < M)
    (heps : 0 < eps) (hepsHalf : eps < 1 / 2)
    (hrho : 0 < rho) (hdelta : 0 < delta)
    (hetaM : eta ≤ M) (hrhoM : rho * M < 1) :
    ∀ᶠ n : ℕ in atTop, ∀
      (G : SimpleGraph (Fin (2 * n)))
      (A B C D : Finset (Fin (2 * n))),
      IsMinimumVertexCoverOn G A C →
      sqrtCoverThreshold L n ≤ C.card →
      eta * Real.sqrt n ≤ C.card →
      (C.card : ℝ) ≤ M * Real.sqrt n →
      (D.card : ℝ) ≤ M * Real.sqrt n →
      BoundedInternal.OrientedBoundedInternal G A B C D →
      ∃ left right : ℕ,
        left = Nat.floor ((1 / 4 - eps) * (C.card : ℝ)) ∧
        (1 / ((C.card : ℝ) / Real.sqrt n) - rho) * Real.sqrt n ≤
          right ∧
        ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S A) left).card : ℝ)) ≤
          delta * (2 : ℝ) ^ (2 * n) ∧
        ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S B) right).card : ℝ)) ≤
          delta * (2 : ℝ) ^ (2 * n) := by
  have hmatching := eventually_minimumCoverOn_ambient_randomMatching_count_le
    hL heps hepsHalf hdelta
  have hforest := eventually_compact_bounded_sample_forest
    heta hM hrho hdelta hetaM hrhoM
  filter_upwards [hmatching, hforest] with n hnMatching hnForest
  intro G A B C D hC hthreshold hcLower hcUpper hdUpper horiented
  rcases horiented with
    ⟨JA, JB, hJAG, hJBG, hJAsupp, hJBsupp, hJAbip, hJBbip,
      hJAdegree, hJBdegree, hJAedge, hJBedge⟩
  let left : ℕ := Nat.floor ((1 / 4 - eps) * (C.card : ℝ))
  have hmatchingCount := hnMatching (Fin (2 * n)) G A C hC hthreshold
  have hleftSub :
      (Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S A) left) ⊆
        (Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S
              ((1 / 4 - eps) * C.card)) := by
    intro S hS
    have hm := Finset.mem_filter.mp hS
    by_cases hthresholdNonneg :
        0 ≤ (1 / 4 - eps) * (C.card : ℝ)
    · apply Finset.mem_filter.mpr
      refine ⟨hm.1, ?_⟩
      intro hhigh
      apply hm.2
      apply RandomCover.HasMatchingAtLeast.induce_internalGraph
      obtain ⟨N, hNmatching, hNS, hNcard⟩ := hhigh
      refine ⟨N, hNmatching, hNS, ?_⟩
      exact (Nat.floor_le hthresholdNonneg).trans hNcard
    · have hleftZero : left = 0 := by
        dsimp [left]
        rw [Nat.floor_eq_zero]
        have : (1 / 4 - eps) * (C.card : ℝ) < 0 :=
          lt_of_not_ge hthresholdNonneg
        linarith
      have hzero :
          ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
            (restrictedPart S A) left := by
        rw [hleftZero]
        exact ContainsLinearForestWith.zero _ _
      exact (hm.2 hzero).elim
  have hleftCount :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
        fun S : Finset (Fin (2 * n)) ↦
          ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
            (restrictedPart S A) left).card : ℝ)) ≤
        delta * (2 : ℝ) ^ (2 * n) := by
    have hcard :
        ((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S A) left)).card ≤
          ((Finset.univ : Finset (Fin (2 * n))).powerset.filter
            (fun S : Finset (Fin (2 * n)) ↦
              ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S
                ((1 / 4 - eps) * C.card))).card :=
      Finset.card_le_card hleftSub
    calc
      _ ≤ (((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ RandomCover.HasMatchingAtLeast (internalGraph G A) S
              ((1 / 4 - eps) * C.card))).card : ℝ) := by
        exact_mod_cast hcard
      _ ≤ delta * (2 : ℝ) ^ (2 * n) := by
        simpa only [Fintype.card_fin] using hmatchingCount
  obtain ⟨right, hrightCapacity, hrightInternalCount⟩ :=
    hnForest C D (B \ D) JB hcLower hcUpper hdUpper hJBbip hJBdegree hJBedge
  have hrightSub :
      (Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S B) right) ⊆
        (Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
              Finset.univ right) := by
    intro S hS
    have hm := Finset.mem_filter.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨hm.1, ?_⟩
    intro hJBforest
    exact hm.2 (ContainsLinearForestWith.mono_induce_of_support
      hJBG hJBsupp hJBforest)
  have hrightCount :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
        fun S : Finset (Fin (2 * n)) ↦
          ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
            (restrictedPart S B) right).card : ℝ)) ≤
        delta * (2 : ℝ) ^ (2 * n) := by
    have hcard :
        ((Finset.univ : Finset (Fin (2 * n))).powerset.filter
          (fun S : Finset (Fin (2 * n)) ↦
            ¬ ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S B) right)).card ≤
          ((Finset.univ : Finset (Fin (2 * n))).powerset.filter
            (fun S : Finset (Fin (2 * n)) ↦
              ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
                Finset.univ right)).card :=
      Finset.card_le_card hrightSub
    apply le_trans _ hrightInternalCount
    exact_mod_cast hcard
  exact ⟨left, right, rfl, hrightCapacity, hleftCount, hrightCount⟩

end

end CompactBoundedForest
end Erdos622
