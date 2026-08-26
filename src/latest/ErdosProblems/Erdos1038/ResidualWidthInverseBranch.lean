import ErdosProblems.Erdos1038.ResidualWidthSeries
import Mathlib.Analysis.Analytic.Binomial

/-!
# Analytic residual inverse branch

This module evaluates the positive formal Lagrange series on the real
increasing branch.  The convergence argument is coefficientwise: evaluation
at a larger point below the first critical point supplies a geometric
majorant, so no appeal to Pringsheim's theorem is needed.
-/

set_option warningAsError false

open scoped BigOperators Real ENNReal NNReal Topology
open Finset Set Filter

namespace Erdos1038

noncomputable section

/-- The positive binomial factor appearing in the Lagrange kernel. -/
def lagrangePhiValue {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (y : ℝ) : ℝ :=
  ∏ i, 1 / (1 - y / d i) ^ (a i)

lemma hasSum_coeff_lagrangeFactorSeries_mul_pow
    (a d x : ℝ) (hd : 0 < d) (hx : |x| < d) :
    HasSum
      (fun r ↦ PowerSeries.coeff r
        (PowerSeries.lagrangeFactorSeries a d) * x ^ r)
      (1 / (1 - x / d) ^ a) := by
  have hnorm : ‖x / d‖ < 1 := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hd]
    exact (div_lt_one hd).2 hx
  have hball : x / d ∈ Metric.eball (0 : ℝ) 1 := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    exact_mod_cast hnorm
  have h :=
    (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a).hasSum hball
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] at h
  apply h.congr_fun
  intro r
  rw [PowerSeries.coeff_lagrangeFactorSeries,
    ← PowerSeries.real_multichoose_eq_ascPochhammer_div,
    Ring.multichoose_eq]
  simp only [div_eq_mul_inv, mul_pow]
  ring

private lemma hasSum_coeff_mul_mul_pow_of_nonneg
    (f g : PowerSeries ℝ) (x F G : ℝ)
    (hf : HasSum (fun n ↦ PowerSeries.coeff n f * x ^ n) F)
    (hg : HasSum (fun n ↦ PowerSeries.coeff n g * x ^ n) G)
    (hf0 : ∀ n, 0 ≤ PowerSeries.coeff n f * x ^ n)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g * x ^ n) :
    HasSum (fun n ↦ PowerSeries.coeff n (f * g) * x ^ n) (F * G) := by
  let u : ℕ → ℝ := fun n ↦ PowerSeries.coeff n f * x ^ n
  let v : ℕ → ℝ := fun n ↦ PowerSeries.coeff n g * x ^ n
  have huv : Summable (fun p : ℕ × ℕ ↦ u p.1 * v p.2) :=
    hf.summable.mul_of_nonneg hg.summable hf0 hg0
  have hcauchy : Summable
      (fun n ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, u p.1 * v p.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul huv
  have hsum :
      (∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, u p.1 * v p.2) = F * G := by
    rw [← hf.tsum_eq, ← hg.tsum_eq]
    exact (hf.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      hg.summable huv).symm
  rw [← hsum]
  apply hcauchy.hasSum.congr_fun
  intro n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [u, v]
  rw [← hpn, pow_add]
  ring

private lemma hasSum_coeff_mul_mul_pow_of_abs
    (f g : PowerSeries ℝ) (x F G : ℝ)
    (hf : HasSum (fun n ↦ PowerSeries.coeff n f * x ^ n) F)
    (hg : HasSum (fun n ↦ PowerSeries.coeff n g * x ^ n) G)
    (hfAbs : Summable (fun n ↦
      ‖PowerSeries.coeff n f * x ^ n‖))
    (hgAbs : Summable (fun n ↦
      ‖PowerSeries.coeff n g * x ^ n‖)) :
    HasSum (fun n ↦ PowerSeries.coeff n (f * g) * x ^ n) (F * G) := by
  let u : ℕ → ℝ := fun n ↦ PowerSeries.coeff n f * x ^ n
  let v : ℕ → ℝ := fun n ↦ PowerSeries.coeff n g * x ^ n
  have huv : Summable (fun p : ℕ × ℕ ↦ u p.1 * v p.2) := by
    exact summable_mul_of_summable_norm hfAbs hgAbs
  have hcauchy : Summable
      (fun n ↦ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, u p.1 * v p.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul huv
  have hsum :
      (∑' n, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, u p.1 * v p.2) = F * G := by
    rw [← hf.tsum_eq, ← hg.tsum_eq]
    exact (hf.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal
      hg.summable huv).symm
  rw [← hsum]
  apply hcauchy.hasSum.congr_fun
  intro n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [u, v]
  rw [← hpn, pow_add]
  ring

private lemma coeff_pow_nonneg (g : PowerSeries ℝ)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g) (k n : ℕ) :
    0 ≤ PowerSeries.coeff n (g ^ k) := by
  rw [PowerSeries.coeff_pow]
  apply Finset.sum_nonneg
  intro l hl
  apply Finset.prod_nonneg
  intro i hi
  exact hg0 (l i)

private lemma hasSum_coeff_pow_mul_pow_of_nonneg
    (g : PowerSeries ℝ) (x y : ℝ)
    (hg : HasSum (fun n ↦ PowerSeries.coeff n g * x ^ n) y)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g)
    (hx0 : 0 ≤ x) (k : ℕ) :
    HasSum (fun n ↦ PowerSeries.coeff n (g ^ k) * x ^ n) (y ^ k) := by
  induction k with
  | zero =>
      apply (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).congr_fun
      intro n
      by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      apply hasSum_coeff_mul_mul_pow_of_nonneg
      · exact ih
      · exact hg
      · intro n
        exact mul_nonneg (coeff_pow_nonneg g hg0 k n) (pow_nonneg hx0 n)
      · intro n
        exact mul_nonneg (hg0 n) (pow_nonneg hx0 n)

private lemma summable_norm_coeff_pow_mul_pow
    (g : PowerSeries ℝ) (x yAbs : ℝ)
    (hgAbs : HasSum
      (fun n ↦ PowerSeries.coeff n g * |x| ^ n) yAbs)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g) (k : ℕ) :
    Summable (fun n ↦ ‖PowerSeries.coeff n (g ^ k) * x ^ n‖) := by
  have hpos := hasSum_coeff_pow_mul_pow_of_nonneg
    g |x| yAbs hgAbs hg0 (abs_nonneg x) k
  simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (coeff_pow_nonneg g hg0 k _)] using! hpos.summable

private lemma hasSum_coeff_pow_mul_pow_of_abs
    (g : PowerSeries ℝ) (x y yAbs : ℝ)
    (hg : HasSum (fun n ↦ PowerSeries.coeff n g * x ^ n) y)
    (hgAbs : HasSum
      (fun n ↦ PowerSeries.coeff n g * |x| ^ n) yAbs)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g) (k : ℕ) :
    HasSum (fun n ↦ PowerSeries.coeff n (g ^ k) * x ^ n) (y ^ k) := by
  have hgNorm : Summable
      (fun n ↦ ‖PowerSeries.coeff n g * x ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (hg0 _)] using! hgAbs.summable
  induction k with
  | zero =>
      apply (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).congr_fun
      intro n
      by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact hasSum_coeff_mul_mul_pow_of_abs (g ^ k) g x (y ^ k) y
        ih hg (summable_norm_coeff_pow_mul_pow g x yAbs hgAbs hg0 k) hgNorm

private lemma coeff_subst_nonneg (f g : PowerSeries ℝ)
    (hgConst : PowerSeries.constantCoeff g = 0)
    (hf0 : ∀ n, 0 ≤ PowerSeries.coeff n f)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (f.subst g) := by
  let hgSubst : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hgConst
  rw [PowerSeries.coeff_subst' hgSubst]
  apply finsum_nonneg
  intro d
  simp only [smul_eq_mul]
  exact mul_nonneg (hf0 d) (coeff_pow_nonneg g hg0 d n)

set_option maxHeartbeats 800000 in
/-- Evaluation commutes with substitution for absolutely summable
nonnegative real power series. -/
private theorem hasSum_coeff_subst_mul_pow_of_nonneg
    (f g : PowerSeries ℝ) (x y F : ℝ)
    (hgConst : PowerSeries.constantCoeff g = 0)
    (hf : HasSum (fun n ↦ PowerSeries.coeff n f * y ^ n) F)
    (hg : HasSum (fun n ↦ PowerSeries.coeff n g * x ^ n) y)
    (hf0 : ∀ n, 0 ≤ PowerSeries.coeff n f)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g)
    (hx0 : 0 ≤ x) :
    HasSum (fun n ↦ PowerSeries.coeff n (f.subst g) * x ^ n) F := by
  let A : ℕ → ℕ → ℝ := fun d n ↦
    PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) * x ^ n
  have hpow (d : ℕ) :
      HasSum (fun n ↦ PowerSeries.coeff n (g ^ d) * x ^ n) (y ^ d) :=
    hasSum_coeff_pow_mul_pow_of_nonneg g x y hg hg0 hx0 d
  have hA0 : ∀ d n, 0 ≤ A d n := by
    intro d n
    exact mul_nonneg
      (mul_nonneg (hf0 d) (coeff_pow_nonneg g hg0 d n))
      (pow_nonneg hx0 n)
  have hfiber (d : ℕ) :
      HasSum (fun n ↦ A d n) (PowerSeries.coeff d f * y ^ d) := by
    simpa only [A, mul_assoc] using! (hpow d).mul_left (PowerSeries.coeff d f)
  have houter : Summable (fun d ↦ ∑' n, A d n) := by
    convert! hf.summable using 1
    funext d
    exact (hfiber d).tsum_eq
  have hfamily : Summable (fun p : ℕ × ℕ ↦ A p.1 p.2) := by
    apply (summable_prod_of_nonneg (fun p ↦ hA0 p.1 p.2)).2
    exact ⟨fun d ↦ (hfiber d).summable, houter⟩
  have hproduct : HasSum (fun p : ℕ × ℕ ↦ A p.1 p.2) F := by
    have htotal : (∑' p : ℕ × ℕ, A p.1 p.2) = F := by
      rw [hfamily.tsum_prod]
      simp_rw [(hfiber _).tsum_eq]
      exact hf.tsum_eq
    rw [← htotal]
    exact hfamily.hasSum
  have hswap : HasSum (fun p : ℕ × ℕ ↦ A p.2 p.1) F := by
    exact ((Equiv.prodComm ℕ ℕ).hasSum_iff).2 hproduct
  have hsigma : HasSum (fun p : Σ _n : ℕ, ℕ ↦ A p.2 p.1) F := by
    exact ((Equiv.sigmaEquivProd ℕ ℕ).hasSum_iff).2 hswap
  let hgSubst : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hgConst
  have hinner (n : ℕ) :
      HasSum (fun d ↦ A d n)
        (PowerSeries.coeff n (f.subst g) * x ^ n) := by
    let base : ℕ → ℝ := fun d ↦
      PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
    have hbase : (Function.support base).Finite := by
      simpa only [base, smul_eq_mul] using!
        PowerSeries.coeff_subst_finite' hgSubst f n
    have hsupport : (Function.support fun d ↦ A d n).Finite := by
      apply hbase.subset
      intro d hd
      apply Function.mem_support.mpr
      intro hzero
      apply Function.mem_support.mp hd
      dsimp only [A, base] at hzero ⊢
      rw [hzero, zero_mul]
    have hsummable : Summable (fun d ↦ A d n) :=
      summable_of_finite_support hsupport
    have htsum : (∑' d, A d n) =
        PowerSeries.coeff n (f.subst g) * x ^ n := by
      rw [tsum_eq_finsum hsupport, PowerSeries.coeff_subst' hgSubst]
      change (∑ᶠ d, base d * x ^ n) = (∑ᶠ d, base d) * x ^ n
      exact (finsum_mul' base (x ^ n) hbase).symm
    rw [← htsum]
    exact hsummable.hasSum
  exact hsigma.sigma hinner

set_option maxHeartbeats 800000 in
private theorem hasSum_coeff_subst_mul_pow_of_abs
    (f g : PowerSeries ℝ) (x y yAbs F : ℝ)
    (hgConst : PowerSeries.constantCoeff g = 0)
    (hf : HasSum (fun n ↦ PowerSeries.coeff n f * y ^ n) F)
    (hfAbs : Summable
      (fun n ↦ PowerSeries.coeff n f * yAbs ^ n))
    (hg : HasSum (fun n ↦ PowerSeries.coeff n g * x ^ n) y)
    (hgAbs : HasSum
      (fun n ↦ PowerSeries.coeff n g * |x| ^ n) yAbs)
    (hf0 : ∀ n, 0 ≤ PowerSeries.coeff n f)
    (hg0 : ∀ n, 0 ≤ PowerSeries.coeff n g) :
    HasSum (fun n ↦ PowerSeries.coeff n (f.subst g) * x ^ n) F := by
  let A : ℕ → ℕ → ℝ := fun d n ↦
    PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) * x ^ n
  let B : ℕ → ℕ → ℝ := fun d n ↦
    PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) * |x| ^ n
  have hpow (d : ℕ) :
      HasSum (fun n ↦ PowerSeries.coeff n (g ^ d) * x ^ n) (y ^ d) :=
    hasSum_coeff_pow_mul_pow_of_abs g x y yAbs hg hgAbs hg0 d
  have hpowAbs (d : ℕ) :
      HasSum (fun n ↦ PowerSeries.coeff n (g ^ d) * |x| ^ n)
        (yAbs ^ d) :=
    hasSum_coeff_pow_mul_pow_of_nonneg
      g |x| yAbs hgAbs hg0 (abs_nonneg x) d
  have hfiber (d : ℕ) :
      HasSum (fun n ↦ A d n) (PowerSeries.coeff d f * y ^ d) := by
    simpa only [A, mul_assoc] using! (hpow d).mul_left (PowerSeries.coeff d f)
  have hfiberAbs (d : ℕ) :
      HasSum (fun n ↦ B d n) (PowerSeries.coeff d f * yAbs ^ d) := by
    simpa only [B, mul_assoc] using!
      (hpowAbs d).mul_left (PowerSeries.coeff d f)
  have hB0 : ∀ d n, 0 ≤ B d n := by
    intro d n
    exact mul_nonneg
      (mul_nonneg (hf0 d) (coeff_pow_nonneg g hg0 d n))
      (pow_nonneg (abs_nonneg x) n)
  have houterAbs : Summable (fun d ↦ ∑' n, B d n) := by
    convert! hfAbs using 1
    funext d
    exact (hfiberAbs d).tsum_eq
  have hBfamily : Summable (fun p : ℕ × ℕ ↦ B p.1 p.2) := by
    apply (summable_prod_of_nonneg (fun p ↦ hB0 p.1 p.2)).2
    exact ⟨fun d ↦ (hfiberAbs d).summable, houterAbs⟩
  have hfamily : Summable (fun p : ℕ × ℕ ↦ A p.1 p.2) := by
    apply hBfamily.of_norm_bounded
    intro p
    dsimp only [A, B]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
      abs_of_nonneg (hf0 p.1),
      abs_of_nonneg (coeff_pow_nonneg g hg0 p.1 p.2)]
  have hproduct : HasSum (fun p : ℕ × ℕ ↦ A p.1 p.2) F := by
    have htotal : (∑' p : ℕ × ℕ, A p.1 p.2) = F := by
      rw [hfamily.tsum_prod]
      simp_rw [(hfiber _).tsum_eq]
      exact hf.tsum_eq
    rw [← htotal]
    exact hfamily.hasSum
  have hswap : HasSum (fun p : ℕ × ℕ ↦ A p.2 p.1) F := by
    exact ((Equiv.prodComm ℕ ℕ).hasSum_iff).2 hproduct
  have hsigma : HasSum (fun p : Σ _n : ℕ, ℕ ↦ A p.2 p.1) F := by
    exact ((Equiv.sigmaEquivProd ℕ ℕ).hasSum_iff).2 hswap
  let hgSubst : PowerSeries.HasSubst g :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hgConst
  have hinner (n : ℕ) :
      HasSum (fun d ↦ A d n)
        (PowerSeries.coeff n (f.subst g) * x ^ n) := by
    let base : ℕ → ℝ := fun d ↦
      PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
    have hbase : (Function.support base).Finite := by
      simpa only [base, smul_eq_mul] using!
        PowerSeries.coeff_subst_finite' hgSubst f n
    have hsupport : (Function.support fun d ↦ A d n).Finite := by
      apply hbase.subset
      intro d hd
      apply Function.mem_support.mpr
      intro hzero
      apply Function.mem_support.mp hd
      dsimp only [A, base] at hzero ⊢
      rw [hzero, zero_mul]
    have hsummable : Summable (fun d ↦ A d n) :=
      summable_of_finite_support hsupport
    have htsum : (∑' d, A d n) =
        PowerSeries.coeff n (f.subst g) * x ^ n := by
      rw [tsum_eq_finsum hsupport, PowerSeries.coeff_subst' hgSubst]
      change (∑ᶠ d, base d * x ^ n) = (∑ᶠ d, base d) * x ^ n
      exact (finsum_mul' base (x ^ n) hbase).symm
    rw [← htsum]
    exact hsummable.hasSum
  exact hsigma.sigma hinner

lemma coeff_lagrangeFactorSeries_pos (a d : ℝ)
    (ha : 0 < a) (hd : 0 < d) (r : ℕ) :
    0 < PowerSeries.coeff r (PowerSeries.lagrangeFactorSeries a d) := by
  rw [PowerSeries.coeff_lagrangeFactorSeries]
  exact mul_pos
    (div_pos (ascPochhammer_pos r a ha)
      (Nat.cast_pos.mpr (Nat.factorial_pos r)))
    (pow_pos (inv_pos.mpr hd) r)

lemma coeff_prod_lagrangeFactorSeries_nonneg
    {iota : Type*} [Fintype iota] (s : Finset iota)
    (a d : iota → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (hd : ∀ i ∈ s, 0 < d i) (r : ℕ) :
    0 ≤ PowerSeries.coeff r
      (∏ i ∈ s, PowerSeries.lagrangeFactorSeries (a i) (d i)) := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
      simp only [Finset.prod_empty, PowerSeries.coeff_one]
      split <;> positivity
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, PowerSeries.coeff_mul]
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg
        (coeff_lagrangeFactorSeries_pos (a i) (d i)
          (ha i (Finset.mem_insert_self i s))
          (hd i (Finset.mem_insert_self i s)) p.1).le
        (ih (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj)) p.2)

lemma hasSum_coeff_prod_lagrangeFactorSeries_mul_pow
    {iota : Type*} [Fintype iota] (s : Finset iota)
    (a d : iota → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (hd : ∀ i ∈ s, 0 < d i) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : ∀ i ∈ s, x < d i) :
    HasSum
      (fun r ↦ PowerSeries.coeff r
        (∏ i ∈ s, PowerSeries.lagrangeFactorSeries (a i) (d i)) * x ^ r)
      (∏ i ∈ s, 1 / (1 - x / d i) ^ (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).congr_fun
      intro r
      by_cases hr : r = 0 <;> simp [PowerSeries.coeff_one, hr]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      apply hasSum_coeff_mul_mul_pow_of_nonneg
      · exact hasSum_coeff_lagrangeFactorSeries_mul_pow
          (a i) (d i) x (hd i (Finset.mem_insert_self i s))
          (by rw [abs_of_nonneg hx0]; exact hx i (Finset.mem_insert_self i s))
      · exact ih
          (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))
      · intro r
        exact mul_nonneg
          (coeff_lagrangeFactorSeries_pos (a i) (d i)
            (ha i (Finset.mem_insert_self i s))
            (hd i (Finset.mem_insert_self i s)) r).le
          (pow_nonneg hx0 r)
      · intro r
        exact mul_nonneg
          (coeff_prod_lagrangeFactorSeries_nonneg s a d
            (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
            (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj)) r)
          (pow_nonneg hx0 r)

private lemma hasSum_coeff_prod_lagrangeFactorSeries_mul_pow_of_abs
    {iota : Type*} [Fintype iota] (s : Finset iota)
    (a d : iota → ℝ) (ha : ∀ i ∈ s, 0 < a i)
    (hd : ∀ i ∈ s, 0 < d i) {x : ℝ}
    (hx : ∀ i ∈ s, |x| < d i) :
    HasSum
      (fun r ↦ PowerSeries.coeff r
        (∏ i ∈ s, PowerSeries.lagrangeFactorSeries (a i) (d i)) * x ^ r)
      (∏ i ∈ s, 1 / (1 - x / d i) ^ (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      apply (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).congr_fun
      intro r
      by_cases hr : r = 0 <;> simp [PowerSeries.coeff_one, hr]
  | @insert i s hi ih =>
      have hai : 0 < a i := ha i (Finset.mem_insert_self i s)
      have hdi : 0 < d i := hd i (Finset.mem_insert_self i s)
      have hxi : |x| < d i := hx i (Finset.mem_insert_self i s)
      have hfac := hasSum_coeff_lagrangeFactorSeries_mul_pow
        (a i) (d i) x hdi hxi
      have hfacAbs := hasSum_coeff_lagrangeFactorSeries_mul_pow
        (a i) (d i) |x| hdi (by simpa using! hxi)
      have hfacNorm : Summable (fun r ↦
          ‖PowerSeries.coeff r
            (PowerSeries.lagrangeFactorSeries (a i) (d i)) * x ^ r‖) := by
        simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_pos (coeff_lagrangeFactorSeries_pos (a i) (d i) hai hdi _)]
          using! hfacAbs.summable
      have hiActual := ih
        (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))
      have hiAbs := hasSum_coeff_prod_lagrangeFactorSeries_mul_pow
        s a d
        (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj))
        (abs_nonneg x)
        (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))
      have hiNorm : Summable (fun r ↦
          ‖PowerSeries.coeff r
            (∏ j ∈ s, PowerSeries.lagrangeFactorSeries (a j) (d j)) *
              x ^ r‖) := by
        simpa only [Real.norm_eq_abs, abs_mul, abs_pow,
          abs_of_nonneg (coeff_prod_lagrangeFactorSeries_nonneg s a d
            (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
            (fun j hj ↦ hd j (Finset.mem_insert_of_mem hj)) _)]
          using! hiAbs.summable
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact hasSum_coeff_mul_mul_pow_of_abs _ _ x _ _
        hfac hiActual hfacNorm hiNorm

theorem hasSum_coeff_lagrangePhi_pow_mul_pow
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : ∀ i, x < d i) :
    HasSum
      (fun r ↦ PowerSeries.coeff r
        ((PowerSeries.lagrangePhi a d) ^ n) * x ^ r)
      ((lagrangePhiValue a d x) ^ n) := by
  classical
  rw [PowerSeries.lagrangePhi_pow]
  have h := hasSum_coeff_prod_lagrangeFactorSeries_mul_pow
    (Finset.univ : Finset iota) (fun i ↦ (n : ℝ) * a i) d
    (fun i hi ↦ mul_pos (Nat.cast_pos.mpr hn) (ha i))
    (fun i hi ↦ hd i) hx0 (fun i hi ↦ hx i)
  convert! h using 1
  rw [lagrangePhiValue, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [one_div_pow]
  congr 1
  change ((1 - x / d i) ^ a i) ^ n =
    (1 - x / d i) ^ ((n : ℝ) * a i)
  have hbase : 0 ≤ 1 - x / d i :=
    sub_nonneg.mpr ((div_le_one (hd i)).2 (hx i).le)
  rw [show (n : ℝ) * a i = a i * (n : ℝ) by ring,
    Real.rpow_mul_natCast hbase]

theorem hasSum_coeff_lagrangePhi_mul_pow_of_abs_lt
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {x : ℝ} (hx : ∀ i, |x| < d i) :
    HasSum
      (fun r ↦ PowerSeries.coeff r (PowerSeries.lagrangePhi a d) * x ^ r)
      (lagrangePhiValue a d x) := by
  classical
  rw [← pow_one (PowerSeries.lagrangePhi a d),
    PowerSeries.lagrangePhi_pow]
  simpa only [Nat.cast_one, one_mul, lagrangePhiValue] using!
    hasSum_coeff_prod_lagrangeFactorSeries_mul_pow_of_abs
      (Finset.univ : Finset iota) a d
      (fun i hi ↦ ha i) (fun i hi ↦ hd i)
      (fun i hi ↦ hx i)

lemma coeff_lagrangePhi_pow_nonneg
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {n : ℕ} (hn : 0 < n) (r : ℕ) :
    0 ≤ PowerSeries.coeff r ((PowerSeries.lagrangePhi a d) ^ n) := by
  classical
  rw [PowerSeries.lagrangePhi_pow]
  exact coeff_prod_lagrangeFactorSeries_nonneg Finset.univ
    (fun i ↦ (n : ℝ) * a i) d
    (fun i hi ↦ mul_pos (Nat.cast_pos.mpr hn) (ha i))
    (fun i hi ↦ hd i) r

lemma lagrangePhiValue_pos
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    {x : ℝ} (hd : d ∈ positiveCoordinates iota)
    (hx : ∀ i, x < d i) :
    0 < lagrangePhiValue a d x := by
  classical
  unfold lagrangePhiValue
  apply Finset.prod_pos
  intro i hi
  apply div_pos zero_lt_one
  apply Real.rpow_pos_of_pos
  exact sub_pos.mpr ((div_lt_one (hd i)).2 (hx i))

theorem coeff_lagrangePhi_pow_mul_pow_le
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : ∀ i, x < d i) :
    PowerSeries.coeff (n - 1) ((PowerSeries.lagrangePhi a d) ^ n) *
        x ^ (n - 1) ≤
      (lagrangePhiValue a d x) ^ n := by
  have hsum := hasSum_coeff_lagrangePhi_pow_mul_pow a d ha hd hn hx0 hx
  have hle := hsum.summable.le_tsum (n - 1) (fun r hr ↦
    mul_nonneg (coeff_lagrangePhi_pow_nonneg a d ha hd hn r)
      (pow_nonneg hx0 r))
  rwa [hsum.tsum_eq] at hle

/-- Below any positive comparison point on the increasing branch, the
formal inverse series is dominated by a geometric series. -/
theorem summable_lagrangeInversePowerSeries_of_lt
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {s z : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hz0 : 0 ≤ z) (hz : z < s / lagrangePhiValue a d s) :
    Summable (fun n ↦ PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n) := by
  let phi := lagrangePhiValue a d s
  let q := z * phi / s
  have hphi : 0 < phi := lagrangePhiValue_pos a d hd hsd
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hzphi : z * phi < s := by
    rw [lt_div_iff₀ hphi] at hz
    exact hz
  have hq1 : q < 1 := by
    exact (div_lt_one hs).2 hzphi
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hmajorant : Summable (fun n ↦ s * q ^ n) :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left s
  apply hmajorant.of_nonneg_of_le
  · intro n
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      rw [PowerSeries.coeff_lagrangeInversePowerSeries a d hn]
      exact mul_nonneg
        (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
          (coeff_lagrangePhi_pow_nonneg a d ha hd hn (n - 1)))
        (pow_nonneg hz0 n)
  · intro n
    by_cases hn0 : n = 0
    · subst n
      simp [hs.le]
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      let c := PowerSeries.coeff (n - 1)
        ((PowerSeries.lagrangePhi a d) ^ n)
      have hc0 : 0 ≤ c :=
        coeff_lagrangePhi_pow_nonneg a d ha hd hn (n - 1)
      have hcBound : c * s ^ (n - 1) ≤ phi ^ n := by
        exact coeff_lagrangePhi_pow_mul_pow_le a d ha hd hn hs.le hsd
      have hinv : (n : ℝ)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0))
      rw [PowerSeries.coeff_lagrangeInversePowerSeries a d hn]
      change (n : ℝ)⁻¹ * c * z ^ n ≤ s * q ^ n
      calc
        (n : ℝ)⁻¹ * c * z ^ n ≤ c * z ^ n := by
          have hinner : (n : ℝ)⁻¹ * c ≤ c := by
            simpa using! mul_le_mul_of_nonneg_right hinv hc0
          exact mul_le_mul_of_nonneg_right hinner (pow_nonneg hz0 n)
        _ = (c * s ^ (n - 1)) * (z ^ n / s ^ (n - 1)) := by
          field_simp [hs.ne']
        _ ≤ phi ^ n * (z ^ n / s ^ (n - 1)) := by
          exact mul_le_mul_of_nonneg_right hcBound (by positivity)
        _ = s * q ^ n := by
          dsimp [q]
          calc
            phi ^ n * (z ^ n / s ^ (n - 1)) =
                (z * phi) ^ n / s ^ (n - 1) := by
              rw [mul_pow]
              ring
            _ = s * ((z * phi) ^ n / s ^ n) := by
              rw [show n = (n - 1) + 1 by omega, pow_succ s (n - 1)]
              field_simp
              simp
            _ = s * (z * phi / s) ^ n := by rw [div_pow]

lemma coeff_lagrangeInversePowerSeries_nonneg
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota) (n : ℕ) :
    0 ≤ PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries a d) := by
  by_cases hn0 : n = 0
  · subst n
    rw [PowerSeries.coeff_zero_lagrangeInversePowerSeries]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rw [PowerSeries.coeff_lagrangeInversePowerSeries a d hn]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (coeff_lagrangePhi_pow_nonneg a d ha hd hn (n - 1))

/-- Value of the positive formal inverse at a real argument. -/
def lagrangeInverseValue {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) (z : ℝ) : ℝ :=
  ∑' n, PowerSeries.coeff n
    (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n

/-- Whenever the positive inverse series converges and its value remains
inside the coordinate box, evaluation of the formal Lagrange equation gives
the real fixed-point equation. -/
theorem lagrangeInverseValue_fixedPoint_of_summable
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {z : ℝ} (hz0 : 0 ≤ z)
    (hsum : Summable (fun n ↦ PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n))
    (hvalue : ∀ i, lagrangeInverseValue a d z < d i) :
    lagrangeInverseValue a d z =
      z * lagrangePhiValue a d (lagrangeInverseValue a d z) := by
  let w := PowerSeries.lagrangeInversePowerSeries a d
  let phi := PowerSeries.lagrangePhi a d
  let W := lagrangeInverseValue a d z
  have hw0 : ∀ n, 0 ≤ PowerSeries.coeff n w := by
    intro n
    exact coeff_lagrangeInversePowerSeries_nonneg a d ha hd n
  have hW0 : 0 ≤ W := by
    dsimp only [W, lagrangeInverseValue]
    exact tsum_nonneg (fun n ↦ mul_nonneg (hw0 n) (pow_nonneg hz0 n))
  have hwSum : HasSum
      (fun n ↦ PowerSeries.coeff n w * z ^ n) W := by
    simpa only [w, W, lagrangeInverseValue] using! hsum.hasSum
  have hphi0 : ∀ n, 0 ≤ PowerSeries.coeff n phi := by
    intro n
    simpa only [phi, pow_one] using!
      coeff_lagrangePhi_pow_nonneg a d ha hd (n := 1) zero_lt_one n
  have hphiSum : HasSum
      (fun n ↦ PowerSeries.coeff n phi * W ^ n)
      (lagrangePhiValue a d W) := by
    simpa only [phi, pow_one] using!
      hasSum_coeff_lagrangePhi_pow_mul_pow a d ha hd
        (n := 1) zero_lt_one hW0 hvalue
  have hwConst : PowerSeries.constantCoeff w = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_zero_lagrangeInversePowerSeries a d
  have hcomp : HasSum
      (fun n ↦ PowerSeries.coeff n (phi.subst w) * z ^ n)
      (lagrangePhiValue a d W) := by
    exact hasSum_coeff_subst_mul_pow_of_nonneg phi w z W
      (lagrangePhiValue a d W) hwConst hphiSum hwSum hphi0 hw0 hz0
  have hX : HasSum
      (fun n ↦ PowerSeries.coeff n (PowerSeries.X : PowerSeries ℝ) * z ^ n)
      z := by
    apply (hasSum_ite_eq (1 : ℕ) z).congr_fun
    intro n
    rw [PowerSeries.coeff_X]
    by_cases hn : n = 1
    · subst n
      simp
    · simp [hn]
  have hsubst0 : ∀ n, 0 ≤ PowerSeries.coeff n (phi.subst w) := by
    intro n
    exact coeff_subst_nonneg phi w hwConst hphi0 hw0 n
  have hrhs : HasSum
      (fun n ↦ PowerSeries.coeff n
        (PowerSeries.X * phi.subst w) * z ^ n)
      (z * lagrangePhiValue a d W) := by
    apply hasSum_coeff_mul_mul_pow_of_nonneg
    · exact hX
    · exact hcomp
    · intro n
      exact mul_nonneg (by rw [PowerSeries.coeff_X]; split <;> positivity)
        (pow_nonneg hz0 n)
    · intro n
      exact mul_nonneg (hsubst0 n) (pow_nonneg hz0 n)
  have hwFormal : w = PowerSeries.X * phi.subst w := by
    exact PowerSeries.lagrangeInversePowerSeries_fixedPoint a d
  have hrhs' : HasSum
      (fun n ↦ PowerSeries.coeff n w * z ^ n)
      (z * lagrangePhiValue a d W) := by
    rw [hwFormal]
    exact hrhs
  exact hwSum.unique hrhs'

/-- Absolute convergence on the positive radius evaluates the same formal
inverse on the negative radius and preserves its fixed-point equation. -/
theorem lagrangeInverseValue_neg_fixedPoint_of_pos_summable
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {z : ℝ} (hz0 : 0 ≤ z)
    (hsum : Summable (fun n ↦ PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n))
    (hvalue : ∀ i, lagrangeInverseValue a d z < d i) :
    Summable (fun n ↦ PowerSeries.coeff n
        (PowerSeries.lagrangeInversePowerSeries a d) * (-z) ^ n) ∧
      lagrangeInverseValue a d (-z) =
        (-z) * lagrangePhiValue a d (lagrangeInverseValue a d (-z)) := by
  let w := PowerSeries.lagrangeInversePowerSeries a d
  let phi := PowerSeries.lagrangePhi a d
  let Wpos := lagrangeInverseValue a d z
  let Wneg := lagrangeInverseValue a d (-z)
  have hw0 : ∀ n, 0 ≤ PowerSeries.coeff n w := by
    intro n
    exact coeff_lagrangeInversePowerSeries_nonneg a d ha hd n
  have hphi0 : ∀ n, 0 ≤ PowerSeries.coeff n phi := by
    intro n
    simpa only [phi, pow_one] using!
      coeff_lagrangePhi_pow_nonneg a d ha hd (n := 1) zero_lt_one n
  have hWpos0 : 0 ≤ Wpos := by
    dsimp only [Wpos, lagrangeInverseValue]
    exact tsum_nonneg (fun n ↦ mul_nonneg (hw0 n) (pow_nonneg hz0 n))
  have hnegNorm : Summable (fun n ↦
      ‖PowerSeries.coeff n w * (-z) ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (hw0 _), abs_of_nonneg hz0] using! hsum
  have hsumNeg : Summable
      (fun n ↦ PowerSeries.coeff n w * (-z) ^ n) :=
    hnegNorm.of_norm
  have hWnegAbs : |Wneg| ≤ Wpos := by
    have hnorm := norm_tsum_le_tsum_norm hnegNorm
    simpa only [Wneg, Wpos, lagrangeInverseValue, Real.norm_eq_abs,
      abs_mul, abs_pow, abs_neg, abs_of_nonneg (hw0 _),
      abs_of_nonneg hz0] using! hnorm
  have hWnegD (i : iota) : |Wneg| < d i :=
    hWnegAbs.trans_lt (hvalue i)
  have hwConst : PowerSeries.constantCoeff w = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_zero_lagrangeInversePowerSeries a d
  have hwPos : HasSum (fun n ↦ PowerSeries.coeff n w * |(-z)| ^ n) Wpos := by
    simpa only [abs_neg, abs_of_nonneg hz0, w, Wpos,
      lagrangeInverseValue] using! hsum.hasSum
  have hwNeg : HasSum (fun n ↦ PowerSeries.coeff n w * (-z) ^ n) Wneg := by
    simpa only [w, Wneg, lagrangeInverseValue] using! hsumNeg.hasSum
  have hphiPos : HasSum (fun n ↦ PowerSeries.coeff n phi * Wpos ^ n)
      (lagrangePhiValue a d Wpos) := by
    simpa only [phi, pow_one] using!
      hasSum_coeff_lagrangePhi_pow_mul_pow a d ha hd
        (n := 1) zero_lt_one hWpos0 hvalue
  have hphiNeg : HasSum (fun n ↦ PowerSeries.coeff n phi * Wneg ^ n)
      (lagrangePhiValue a d Wneg) := by
    simpa only [phi] using!
      hasSum_coeff_lagrangePhi_mul_pow_of_abs_lt a d ha hd hWnegD
  have hcompNeg : HasSum
      (fun n ↦ PowerSeries.coeff n (phi.subst w) * (-z) ^ n)
      (lagrangePhiValue a d Wneg) := by
    exact hasSum_coeff_subst_mul_pow_of_abs phi w (-z) Wneg Wpos
      (lagrangePhiValue a d Wneg) hwConst hphiNeg hphiPos.summable
      hwNeg hwPos hphi0 hw0
  have hcompPos : HasSum
      (fun n ↦ PowerSeries.coeff n (phi.subst w) * z ^ n)
      (lagrangePhiValue a d Wpos) := by
    exact hasSum_coeff_subst_mul_pow_of_nonneg phi w z Wpos
      (lagrangePhiValue a d Wpos) hwConst hphiPos
      (by simpa only [w, Wpos, lagrangeInverseValue] using! hsum.hasSum)
      hphi0 hw0 hz0
  have hsubst0 : ∀ n, 0 ≤ PowerSeries.coeff n (phi.subst w) := by
    intro n
    exact coeff_subst_nonneg phi w hwConst hphi0 hw0 n
  have hcompNorm : Summable (fun n ↦
      ‖PowerSeries.coeff n (phi.subst w) * (-z) ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (hsubst0 _), abs_of_nonneg hz0] using! hcompPos.summable
  have hXneg : HasSum
      (fun n ↦ PowerSeries.coeff n (PowerSeries.X : PowerSeries ℝ) *
        (-z) ^ n) (-z) := by
    apply (hasSum_ite_eq (1 : ℕ) (-z)).congr_fun
    intro n
    rw [PowerSeries.coeff_X]
    by_cases hn : n = 1
    · subst n
      simp
    · simp [hn]
  have hXnorm : Summable (fun n ↦
      ‖PowerSeries.coeff n (PowerSeries.X : PowerSeries ℝ) *
        (-z) ^ n‖) := hXneg.summable.norm
  have hrhs : HasSum
      (fun n ↦ PowerSeries.coeff n
        (PowerSeries.X * phi.subst w) * (-z) ^ n)
      ((-z) * lagrangePhiValue a d Wneg) :=
    hasSum_coeff_mul_mul_pow_of_abs _ _ (-z) _ _
      hXneg hcompNeg hXnorm hcompNorm
  have hwFormal : w = PowerSeries.X * phi.subst w :=
    PowerSeries.lagrangeInversePowerSeries_fixedPoint a d
  have hrhs' : HasSum
      (fun n ↦ PowerSeries.coeff n w * (-z) ^ n)
      ((-z) * lagrangePhiValue a d Wneg) := by
    rw [hwFormal]
    exact hrhs
  exact ⟨hsumNeg, hwNeg.unique hrhs'⟩

theorem abs_lagrangeInverseValue_neg_le_pos
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {z : ℝ} (hz0 : 0 ≤ z)
    (hsum : Summable (fun n ↦ PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n)) :
    |lagrangeInverseValue a d (-z)| ≤ lagrangeInverseValue a d z := by
  let w := PowerSeries.lagrangeInversePowerSeries a d
  have hw0 : ∀ n, 0 ≤ PowerSeries.coeff n w := by
    intro n
    exact coeff_lagrangeInversePowerSeries_nonneg a d ha hd n
  have hnorm : Summable (fun n ↦
      ‖PowerSeries.coeff n w * (-z) ^ n‖) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
      abs_of_nonneg (hw0 _), abs_of_nonneg hz0] using! hsum
  have hle := norm_tsum_le_tsum_norm hnorm
  simpa only [lagrangeInverseValue, w, Real.norm_eq_abs,
    abs_mul, abs_pow, abs_neg, abs_of_nonneg (hw0 _),
    abs_of_nonneg hz0] using! hle

/-- A comparison point satisfying `z < s / Φ(s)` lies strictly above the
positive inverse-series value.  The proof uses continuity of the positive
series and rules out a first crossing by the fixed-point equation. -/
theorem lagrangeInverseValue_lt_comparison
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {s z : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hz0 : 0 ≤ z) (hz : z < s / lagrangePhiValue a d s) :
    lagrangeInverseValue a d z < s := by
  let w := PowerSeries.lagrangeInversePowerSeries a d
  let c : ℕ → ℝ := fun n ↦ PowerSeries.coeff n w
  have hc0 : ∀ n, 0 ≤ c n := by
    intro n
    exact coeff_lagrangeInversePowerSeries_nonneg a d ha hd n
  have hsum : Summable (fun n ↦ c n * z ^ n) := by
    exact summable_lagrangeInversePowerSeries_of_lt a d ha hd hs hsd hz0 hz
  have hcont : ContinuousOn (lagrangeInverseValue a d) (Icc 0 z) := by
    unfold lagrangeInverseValue
    apply continuousOn_tsum
    · intro n
      fun_prop
    · simpa only [c, w] using! hsum
    · intro n t ht
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hc0 n) (pow_nonneg ht.1 n))]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ht.1 ht.2 n) (hc0 n)
  have hzero : lagrangeInverseValue a d 0 = 0 := by
    unfold lagrangeInverseValue
    rw [show (fun n ↦ PowerSeries.coeff n
        (PowerSeries.lagrangeInversePowerSeries a d) * 0 ^ n) =
        (fun _ ↦ 0) by
      funext n
      by_cases hn : n = 0
      · subst n
        rw [PowerSeries.coeff_zero_lagrangeInversePowerSeries]
        simp
      · rw [zero_pow hn, mul_zero]]
    exact tsum_zero
  by_contra hlt
  have hsValue : s ≤ lagrangeInverseValue a d z := le_of_not_gt hlt
  have hsBetween : s ∈ Icc
      (lagrangeInverseValue a d 0) (lagrangeInverseValue a d z) := by
    rw [hzero]
    exact ⟨hs.le, hsValue⟩
  obtain ⟨t, ht, htValue⟩ :=
    intermediate_value_Icc hz0 hcont hsBetween
  have hsumt : Summable (fun n ↦ c n * t ^ n) := by
    apply hsum.of_nonneg_of_le
    · intro n
      exact mul_nonneg (hc0 n) (pow_nonneg ht.1 n)
    · intro n
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ht.1 ht.2 n) (hc0 n)
  have hfixed := lagrangeInverseValue_fixedPoint_of_summable
    a d ha hd ht.1 (by simpa only [c, w] using! hsumt)
    (fun i ↦ by rw [htValue]; exact hsd i)
  rw [htValue] at hfixed
  have hphi : 0 < lagrangePhiValue a d s :=
    lagrangePhiValue_pos a d hd hsd
  have htEq : t = s / lagrangePhiValue a d s := by
    apply (eq_div_iff hphi.ne').2
    exact hfixed.symm
  rw [htEq] at ht
  exact (not_le_of_gt hz) ht.2

/-- On every subcritical comparison interval, the inverse value satisfies the
real Lagrange fixed-point equation and stays inside the coordinate box. -/
theorem lagrangeInverseValue_fixedPoint_of_lt
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {s z : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hz0 : 0 ≤ z) (hz : z < s / lagrangePhiValue a d s) :
    lagrangeInverseValue a d z =
      z * lagrangePhiValue a d (lagrangeInverseValue a d z) := by
  have hsum := summable_lagrangeInversePowerSeries_of_lt
    a d ha hd hs hsd hz0 hz
  apply lagrangeInverseValue_fixedPoint_of_summable a d ha hd hz0 hsum
  intro i
  exact (lagrangeInverseValue_lt_comparison
    a d ha hd hs hsd hz0 hz).trans (hsd i)

private theorem sum_range_lagrangeInversePowerSeries_le_at_boundary
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {s z : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hz : z = s / lagrangePhiValue a d s) (N : ℕ) :
    ∑ n ∈ Finset.range N, PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n ≤ s := by
  let w := PowerSeries.lagrangeInversePowerSeries a d
  let c : ℕ → ℝ := fun n ↦ PowerSeries.coeff n w
  let q : ℕ → ℝ := fun m ↦ (m : ℝ) / ((m : ℝ) + 1)
  let t : ℕ → ℝ := fun m ↦ q m * z
  have hc0 : ∀ n, 0 ≤ c n := by
    intro n
    exact coeff_lagrangeInversePowerSeries_nonneg a d ha hd n
  have hphi : 0 < lagrangePhiValue a d s :=
    lagrangePhiValue_pos a d hd hsd
  have hzpos : 0 < z := by
    rw [hz]
    exact div_pos hs hphi
  have hq0 (m : ℕ) : 0 ≤ q m := by
    dsimp only [q]
    positivity
  have hq1 (m : ℕ) : q m < 1 := by
    dsimp only [q]
    rw [div_lt_one (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    linarith
  have ht0 (m : ℕ) : 0 ≤ t m :=
    mul_nonneg (hq0 m) hzpos.le
  have htz (m : ℕ) : t m < z := by
    exact mul_lt_of_lt_one_left hzpos (hq1 m)
  have htend : Tendsto t atTop (𝓝 z) := by
    have hqend : Tendsto q atTop (𝓝 (1 : ℝ)) := by
      exact tendsto_natCast_div_add_atTop (1 : ℝ)
    simpa only [t, one_mul] using! hqend.mul_const z
  have hlimit : Tendsto
      (fun m ↦ ∑ n ∈ Finset.range N, c n * (t m) ^ n)
      atTop (𝓝 (∑ n ∈ Finset.range N, c n * z ^ n)) := by
    apply tendsto_finsetSum
    intro n hn
    exact tendsto_const_nhds.mul (htend.pow n)
  apply le_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun m ↦ by
    have hsumt : Summable (fun n ↦ c n * (t m) ^ n) := by
      exact summable_lagrangeInversePowerSeries_of_lt
        a d ha hd hs hsd (ht0 m) (by simpa only [hz] using! htz m)
    calc
      (∑ n ∈ Finset.range N, c n * (t m) ^ n) ≤
          ∑' n, c n * (t m) ^ n := by
        exact Summable.sum_le_tsum _
          (fun n hn ↦ mul_nonneg (hc0 n) (pow_nonneg (ht0 m) n)) hsumt
      _ = lagrangeInverseValue a d (t m) := by
        rfl
      _ ≤ s := (lagrangeInverseValue_lt_comparison
        a d ha hd hs hsd (ht0 m) (by simpa only [hz] using! htz m)).le

/-- Abel-type endpoint convergence for the positive inverse series.  Interior
values are bounded by `s`; passing finite partial sums to the endpoint shows
that the boundary coefficient series is summable as well. -/
theorem summable_lagrangeInversePowerSeries_at_boundary
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {s z : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hz : z = s / lagrangePhiValue a d s) :
    Summable (fun n ↦ PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries a d) * z ^ n) := by
  have hz0 : 0 ≤ z := by
    rw [hz]
    exact (div_pos hs (lagrangePhiValue_pos a d hd hsd)).le
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg
      (coeff_lagrangeInversePowerSeries_nonneg a d ha hd n)
      (pow_nonneg hz0 n)
  · exact sum_range_lagrangeInversePowerSeries_le_at_boundary
      a d ha hd hs hsd hz

/-- The endpoint inverse value is bounded by its comparison point. -/
theorem lagrangeInverseValue_le_at_boundary
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {s z : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hz : z = s / lagrangePhiValue a d s) :
    lagrangeInverseValue a d z ≤ s := by
  have hz0 : 0 ≤ z := by
    rw [hz]
    exact (div_pos hs (lagrangePhiValue_pos a d hd hsd)).le
  unfold lagrangeInverseValue
  exact Real.tsum_le_of_sum_range_le
    (fun n ↦ mul_nonneg
      (coeff_lagrangeInversePowerSeries_nonneg a d ha hd n)
      (pow_nonneg hz0 n))
    (sum_range_lagrangeInversePowerSeries_le_at_boundary
      a d ha hd hs hsd hz)

/-- The real fixed-point equation remains valid at the positive boundary. -/
theorem lagrangeInverseValue_fixedPoint_at_boundary
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (ha : ∀ i, 0 < a i) (hd : d ∈ positiveCoordinates iota)
    {s z : ℝ} (hs : 0 < s) (hsd : ∀ i, s < d i)
    (hz : z = s / lagrangePhiValue a d s) :
    lagrangeInverseValue a d z =
      z * lagrangePhiValue a d (lagrangeInverseValue a d z) := by
  have hsum := summable_lagrangeInversePowerSeries_at_boundary
    a d ha hd hs hsd hz
  have hz0 : 0 ≤ z := by
    rw [hz]
    exact (div_pos hs (lagrangePhiValue_pos a d hd hsd)).le
  apply lagrangeInverseValue_fixedPoint_of_summable a d ha hd
    hz0 hsum
  intro i
  exact (lagrangeInverseValue_le_at_boundary
    a d ha hd hs hsd hz).trans_lt (hsd i)

lemma inverseMonomial_nat_mul
    {iota : Type*} [Fintype iota] (a d : iota → ℝ) (n : ℕ) :
    inverseMonomial (fun i ↦ (n : ℝ) * a i) d =
      (inverseMonomial a d) ^ n := by
  rw [inverseMonomial, inverseMonomial, ← Real.exp_nat_mul]
  congr 1
  rw [mul_neg, Finset.mul_sum]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (hd : d ∈ positiveCoordinates iota) (n : ℕ) :
    scaledLagrangeCoefficient a n d =
      PowerSeries.coeff n (PowerSeries.lagrangeInversePowerSeries a d) *
        (inverseMonomial a d) ^ n := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [scaledLagrangeCoefficient, scaledLagrangeTerm,
      scaledLagrangePrefactor]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rw [scaledLagrangeCoefficient_eq_mul_coeff_phi_pow a d hd hn]
    rw [← PowerSeries.coeff_lagrangeInversePowerSeries a d hn]
    rw [inverseMonomial_nat_mul]
    ring

/-- Exact odd part of the inverse series. -/
def inverseWidthSeries {iota : Type*} [Fintype iota]
    (a d : iota → ℝ) : ℝ :=
  2 * ∑' j, scaledLagrangeCoefficient a (2 * j + 1) d

/-- Exact directional odd series at a reference coordinate vector. -/
def inverseWidthSeriesDirectional {iota : Type*} [Fintype iota]
    (a reference target : iota → ℝ) : ℝ :=
  2 * ∑' j, scaledLagrangeCoefficientDirectional a (2 * j + 1)
    reference target

lemma summable_odd_scaledLagrangeCoefficient
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (hsum : Summable (fun n ↦ scaledLagrangeCoefficient a n d)) :
    Summable (fun j ↦ scaledLagrangeCoefficient a (2 * j + 1) d) := by
  have hinj : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro m n hmn
    have hmul : 2 * m = 2 * n := Nat.add_right_cancel hmn
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
  simpa only [Function.comp_apply] using! hsum.comp_injective hinj

/-- Finite odd truncations converge to the exact odd inverse width whenever
the coefficient series is summable. -/
theorem tendsto_inverseWidthOddTruncation
    {iota : Type*} [Fintype iota] (a d : iota → ℝ)
    (hsum : Summable (fun n ↦ scaledLagrangeCoefficient a n d)) :
    Tendsto (fun m ↦ inverseWidthOddTruncation a m d) atTop
      (𝓝 (inverseWidthSeries a d)) := by
  have hodd := summable_odd_scaledLagrangeCoefficient a d hsum
  have hshift : Tendsto (fun m : ℕ ↦ m + 1) atTop atTop := by
    exact tendsto_add_atTop_nat 1
  have hpartial := hodd.hasSum.tendsto_sum_nat.comp hshift
  simpa only [inverseWidthOddTruncation, inverseWidthSeries] using!
    hpartial.const_mul (2 : ℝ)

theorem tendsto_inverseWidthOddTruncationDirectional
    {iota : Type*} [Fintype iota]
    (a reference target : iota → ℝ)
    (hsum : Summable (fun j ↦ scaledLagrangeCoefficientDirectional a
      (2 * j + 1) reference target)) :
    Tendsto (fun m ↦ inverseWidthOddTruncationDirectional a m
      reference target) atTop
      (𝓝 (inverseWidthSeriesDirectional a reference target)) := by
  have hshift : Tendsto (fun m : ℕ ↦ m + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hpartial := hsum.hasSum.tendsto_sum_nat.comp hshift
  simpa only [inverseWidthOddTruncationDirectional,
    inverseWidthSeriesDirectional] using! hpartial.const_mul (2 : ℝ)

/-- Passage of the finite convex supporting inequalities to the exact odd
series.  The analytic layer only has to supply the three indicated
summability facts. -/
theorem inverseWidthSeries_supporting_of_summable
    {iota : Type*} [Fintype iota] (a : iota → ℝ)
    (ha : ∀ i, 0 < a i) {reference target : iota → ℝ}
    (href : reference ∈ positiveCoordinates iota)
    (htarget : target ∈ positiveCoordinates iota)
    (hsumReference : Summable (fun n ↦
      scaledLagrangeCoefficient a n reference))
    (hsumTarget : Summable (fun n ↦
      scaledLagrangeCoefficient a n target))
    (hsumDirectional : Summable (fun j ↦
      scaledLagrangeCoefficientDirectional a (2 * j + 1)
        reference target)) :
    inverseWidthSeries a reference +
        inverseWidthSeriesDirectional a reference target ≤
      inverseWidthSeries a target := by
  apply le_of_tendsto_of_tendsto
    ((tendsto_inverseWidthOddTruncation a reference hsumReference).add
      (tendsto_inverseWidthOddTruncationDirectional
        a reference target hsumDirectional))
    (tendsto_inverseWidthOddTruncation a target hsumTarget)
  exact Filter.Eventually.of_forall fun m ↦
    inverseWidthOddTruncation_supporting a ha m href htarget

/-! ## Residual-configuration specialization -/

lemma lagrangePhiValue_residual
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k y : ℝ} (hy : y < residualMinLocation C) :
    lagrangePhiValue (residualLagrangeAlpha C k) C.location y =
      Real.exp (-(1 / k) *
        ∑ i, C.weight i * Real.log (1 - y / C.location i)) := by
  classical
  have hbase (i : iota) : 0 < 1 - y / C.location i := by
    rw [sub_pos, div_lt_one (residual_locations_mem_positiveCoordinates C i)]
    exact hy.trans_le (residualMinLocation_le_location C i)
  unfold lagrangePhiValue
  calc
    (∏ i, 1 / (1 - y / C.location i) ^
        (residualLagrangeAlpha C k i)) =
        ∏ i, Real.exp (-(Real.log (1 - y / C.location i) *
          residualLagrangeAlpha C k i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Real.rpow_def_of_pos (hbase i), one_div, ← Real.exp_neg]
    _ = Real.exp (∑ i, -(Real.log (1 - y / C.location i) *
          residualLagrangeAlpha C k i)) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(1 / k) *
        ∑ i, C.weight i * Real.log (1 - y / C.location i)) := by
      congr 1
      simp only [residualLagrangeAlpha, div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The residual inverse map is exactly `y / Φ(y)` for the Lagrange
kernel attached to the empirical weights. -/
theorem residualPsi_eq_div_lagrangePhiValue
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k y : ℝ} (hy : y < residualMinLocation C) :
    residualPsi C k y =
      y / lagrangePhiValue
        (residualLagrangeAlpha C k) C.location y := by
  rw [lagrangePhiValue_residual C hy]
  unfold residualPsi
  conv_rhs =>
    rw [div_eq_mul_inv, ← Real.exp_neg]
  congr 1
  ring_nf

/-- The Lagrange scale monomial is the residual zero-potential level. -/
lemma inverseMonomial_residualLagrangeAlpha
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    (k : ℝ) :
    inverseMonomial (residualLagrangeAlpha C k) C.location =
      residualScale C k := by
  rw [inverseMonomial, residualScale]
  congr 1
  simp only [residualLagrangeAlpha, div_eq_mul_inv]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Equation (4.16) is the inverse-series coefficient already multiplied by
the residual scale to the corresponding power. -/
theorem residual_scaledLagrangeCoefficient_eq
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k : ℝ} (n : ℕ) :
    scaledLagrangeCoefficient (residualLagrangeAlpha C k) n C.location =
      PowerSeries.coeff n (PowerSeries.lagrangeInversePowerSeries
        (residualLagrangeAlpha C k) C.location) *
          (residualScale C k) ^ n := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [scaledLagrangeCoefficient, scaledLagrangeTerm,
      scaledLagrangePrefactor]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rw [scaledLagrangeCoefficient_eq_mul_coeff_phi_pow
      (residualLagrangeAlpha C k) C.location
      (residual_locations_mem_positiveCoordinates C) hn]
    rw [← PowerSeries.coeff_lagrangeInversePowerSeries
      (residualLagrangeAlpha C k) C.location hn]
    rw [inverseMonomial_nat_mul, inverseMonomial_residualLagrangeAlpha]
    ring

theorem lagrangeInverseValue_residualScale_eq_tsum_scaled
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    (k : ℝ) :
    lagrangeInverseValue (residualLagrangeAlpha C k) C.location
        (residualScale C k) =
      ∑' n, scaledLagrangeCoefficient
        (residualLagrangeAlpha C k) n C.location := by
  unfold lagrangeInverseValue
  apply tsum_congr
  intro n
  exact (residual_scaledLagrangeCoefficient_eq C n).symm

/-- Separation, including the contact endpoint, guarantees convergence of
the residual inverse series at the zero-potential scale. -/
theorem summable_residual_lagrangeInverseSeries_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    Summable (fun n ↦ PowerSeries.coeff n
      (PowerSeries.lagrangeInversePowerSeries
        (residualLagrangeAlpha C k) C.location) *
          (residualScale C k) ^ n) := by
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hpsi : residualPsi C k yc =
      yc / lagrangePhiValue
        (residualLagrangeAlpha C k) C.location yc := by
    exact residualPsi_eq_div_lagrangePhiValue C hyc.2
  rcases residual_strictSeparation_or_contact C hk hsep with
      hstrict | hcontact
  · apply summable_lagrangeInversePowerSeries_of_lt
      (residualLagrangeAlpha C k) C.location
      (residualLagrangeAlpha_pos C hk)
      (residual_locations_mem_positiveCoordinates C)
      hyc.1 (fun i ↦ hyc.2.trans_le (residualMinLocation_le_location C i))
      (residualScale_pos C k).le
    rw [← hpsi]
    exact hstrict
  · apply summable_lagrangeInversePowerSeries_at_boundary
      (residualLagrangeAlpha C k) C.location
      (residualLagrangeAlpha_pos C hk)
      (residual_locations_mem_positiveCoordinates C)
      hyc.1 (fun i ↦ hyc.2.trans_le (residualMinLocation_le_location C i))
    exact hcontact.trans hpsi

theorem summable_residual_scaledLagrangeCoefficient_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    Summable (fun n ↦ scaledLagrangeCoefficient
      (residualLagrangeAlpha C k) n C.location) := by
  apply (summable_residual_lagrangeInverseSeries_of_separation
    C hk hsep).congr
  intro n
  exact (residual_scaledLagrangeCoefficient_eq C n).symm

theorem tendsto_residualInverseWidthOddTruncation_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    Tendsto (fun m ↦ residualInverseWidthOddTruncation
      C k m C.location) atTop
      (𝓝 (inverseWidthSeries
        (residualLagrangeAlpha C k) C.location)) := by
  simpa only [residualInverseWidthOddTruncation] using!
    tendsto_inverseWidthOddTruncation
      (residualLagrangeAlpha C k) C.location
      (summable_residual_scaledLagrangeCoefficient_of_separation C hk hsep)

/-- The exact odd series is the difference between the positive and negative
real inverse branches. -/
theorem inverseWidthSeries_residual_eq_inverseValue_sub_neg
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    inverseWidthSeries (residualLagrangeAlpha C k) C.location =
      lagrangeInverseValue (residualLagrangeAlpha C k) C.location
          (residualScale C k) -
        lagrangeInverseValue (residualLagrangeAlpha C k) C.location
          (-residualScale C k) := by
  let c : ℕ → ℝ := fun n ↦ scaledLagrangeCoefficient
    (residualLagrangeAlpha C k) n C.location
  have hsum : Summable c :=
    summable_residual_scaledLagrangeCoefficient_of_separation C hk hsep
  have hinjEven : Function.Injective (fun j : ℕ ↦ 2 * j) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmn
  have hinjOdd : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel hmn)
  have hEven : Summable (fun j ↦ c (2 * j)) := by
    simpa only [Function.comp_apply] using! hsum.comp_injective hinjEven
  have hOdd : Summable (fun j ↦ c (2 * j + 1)) := by
    simpa only [Function.comp_apply] using! hsum.comp_injective hinjOdd
  let signed : ℕ → ℝ := fun n ↦ (-1 : ℝ) ^ n * c n
  have hSignedEven : Summable (fun j ↦ signed (2 * j)) := by
    simpa only [signed, pow_mul, neg_one_sq, one_pow, one_mul] using! hEven
  have hSignedOdd : Summable (fun j ↦ signed (2 * j + 1)) := by
    simpa [signed, pow_add, pow_mul] using! hOdd.neg
  have hsplit :
      (∑' j, c (2 * j)) + (∑' j, c (2 * j + 1)) = ∑' n, c n :=
    tsum_even_add_odd hEven hOdd
  have hsplitSigned :
      (∑' j, signed (2 * j)) + (∑' j, signed (2 * j + 1)) =
        ∑' n, signed n :=
    tsum_even_add_odd hSignedEven hSignedOdd
  have hpos : lagrangeInverseValue
      (residualLagrangeAlpha C k) C.location (residualScale C k) =
        ∑' n, c n := by
    exact lagrangeInverseValue_residualScale_eq_tsum_scaled C k
  have hneg : lagrangeInverseValue
      (residualLagrangeAlpha C k) C.location (-residualScale C k) =
        ∑' n, signed n := by
    unfold lagrangeInverseValue
    apply tsum_congr
    intro n
    change PowerSeries.coeff n (PowerSeries.lagrangeInversePowerSeries
        (residualLagrangeAlpha C k) C.location) *
          (-residualScale C k) ^ n =
      (-1 : ℝ) ^ n * scaledLagrangeCoefficient
        (residualLagrangeAlpha C k) n C.location
    rw [show -residualScale C k =
      (-1 : ℝ) * residualScale C k by ring, mul_pow]
    rw [residual_scaledLagrangeCoefficient_eq C n]
    ring
  have hsignedEven : (∑' j, signed (2 * j)) = ∑' j, c (2 * j) := by
    apply tsum_congr
    intro j
    simp [signed, pow_mul]
  have hsignedOdd : (∑' j, signed (2 * j + 1)) =
      -∑' j, c (2 * j + 1) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    simp [signed, pow_add, pow_mul]
  rw [inverseWidthSeries, hpos, hneg, ← hsplit, ← hsplitSigned,
    hsignedEven, hsignedOdd]
  ring

/-- The convergent inverse value lies on the increasing side of the unique
critical point. -/
theorem residual_lagrangeInverseValue_le_critical_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    lagrangeInverseValue (residualLagrangeAlpha C k) C.location
        (residualScale C k) ≤ residualCriticalPoint C k hk := by
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hpsi : residualPsi C k yc =
      yc / lagrangePhiValue
        (residualLagrangeAlpha C k) C.location yc := by
    exact residualPsi_eq_div_lagrangePhiValue C hyc.2
  rcases residual_strictSeparation_or_contact C hk hsep with
      hstrict | hcontact
  · exact (lagrangeInverseValue_lt_comparison
      (residualLagrangeAlpha C k) C.location
      (residualLagrangeAlpha_pos C hk)
      (residual_locations_mem_positiveCoordinates C)
      hyc.1 (fun i ↦ hyc.2.trans_le (residualMinLocation_le_location C i))
      (residualScale_pos C k).le (by rw [← hpsi]; exact hstrict)).le
  · apply lagrangeInverseValue_le_at_boundary
      (residualLagrangeAlpha C k) C.location
      (residualLagrangeAlpha_pos C hk)
      (residual_locations_mem_positiveCoordinates C)
      hyc.1 (fun i ↦ hyc.2.trans_le (residualMinLocation_le_location C i))
    exact hcontact.trans hpsi

theorem residual_lagrangeInverseValue_fixedPoint_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    lagrangeInverseValue (residualLagrangeAlpha C k) C.location
        (residualScale C k) =
      residualScale C k * lagrangePhiValue
        (residualLagrangeAlpha C k) C.location
        (lagrangeInverseValue (residualLagrangeAlpha C k) C.location
          (residualScale C k)) := by
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hpsi : residualPsi C k yc =
      yc / lagrangePhiValue
        (residualLagrangeAlpha C k) C.location yc := by
    exact residualPsi_eq_div_lagrangePhiValue C hyc.2
  rcases residual_strictSeparation_or_contact C hk hsep with
      hstrict | hcontact
  · apply lagrangeInverseValue_fixedPoint_of_lt
      (residualLagrangeAlpha C k) C.location
      (residualLagrangeAlpha_pos C hk)
      (residual_locations_mem_positiveCoordinates C)
      hyc.1 (fun i ↦ hyc.2.trans_le (residualMinLocation_le_location C i))
      (residualScale_pos C k).le
    rw [← hpsi]
    exact hstrict
  · apply lagrangeInverseValue_fixedPoint_at_boundary
      (residualLagrangeAlpha C k) C.location
      (residualLagrangeAlpha_pos C hk)
      (residual_locations_mem_positiveCoordinates C)
      hyc.1 (fun i ↦ hyc.2.trans_le (residualMinLocation_le_location C i))
    exact hcontact.trans hpsi

/-- The residual Lagrange sum is the nonnegative root of the exact inverse
map equation at the zero-potential scale. -/
theorem residualPsi_lagrangeInverseValue_eq_scale_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    residualPsi C k
        (lagrangeInverseValue (residualLagrangeAlpha C k) C.location
          (residualScale C k)) =
      residualScale C k := by
  let W := lagrangeInverseValue (residualLagrangeAlpha C k) C.location
    (residualScale C k)
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hWle : W ≤ yc :=
    residual_lagrangeInverseValue_le_critical_of_separation C hk hsep
  have hWd (i : iota) : W < C.location i :=
    hWle.trans_lt (hyc.2.trans_le (residualMinLocation_le_location C i))
  have hphiW : 0 < lagrangePhiValue
      (residualLagrangeAlpha C k) C.location W :=
    lagrangePhiValue_pos _ _ (residual_locations_mem_positiveCoordinates C) hWd
  have hfixed : W = residualScale C k * lagrangePhiValue
      (residualLagrangeAlpha C k) C.location W :=
    residual_lagrangeInverseValue_fixedPoint_of_separation C hk hsep
  rw [residualPsi_eq_div_lagrangePhiValue C
    (hWle.trans_lt hyc.2)]
  exact (div_eq_iff hphiW.ne').2 hfixed

theorem residualPsi_strictMonoOn_nonpos
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k : ℝ} (hk : 0 < k) :
    StrictMonoOn (residualPsi C k) (Iic 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic 0)
  · exact (continuousOn_residualPsi_Iio C hk.ne').mono fun y hy ↦
      hy.trans_lt (residualMinLocation_pos C)
  · rw [interior_Iic]
    intro y hy
    have hyMin : y < residualMinLocation C :=
      hy.trans (residualMinLocation_pos C)
    rw [(hasDerivAt_residualPsi C hk.ne' hyMin).deriv]
    have hbalance : residualCriticalBalance C y ≤ 0 := by
      unfold residualCriticalBalance
      apply Finset.sum_nonpos
      intro i hi
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (C.weight_pos i).le hy.le)
        (residual_location_sub_pos C hyMin i).le
    exact mul_pos (Real.exp_pos _) (by
      have hdiv : residualCriticalBalance C y / k ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hbalance hk.le
      linarith)

/-- The negative evaluation of the same convergent inverse series is the
negative-side zero-potential root. -/
theorem residualPsi_lagrangeInverseValue_neg_eq_neg_scale_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    residualPsi C k
        (lagrangeInverseValue (residualLagrangeAlpha C k) C.location
          (-residualScale C k)) =
      -residualScale C k := by
  let a := residualLagrangeAlpha C k
  let R := residualScale C k
  let Wpos := lagrangeInverseValue a C.location R
  let Wneg := lagrangeInverseValue a C.location (-R)
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hsum := summable_residual_lagrangeInverseSeries_of_separation C hk hsep
  have hWposLe : Wpos ≤ yc :=
    residual_lagrangeInverseValue_le_critical_of_separation C hk hsep
  have hWposD (i : iota) : Wpos < C.location i :=
    hWposLe.trans_lt (hyc.2.trans_le (residualMinLocation_le_location C i))
  have hneg := lagrangeInverseValue_neg_fixedPoint_of_pos_summable
    a C.location (residualLagrangeAlpha_pos C hk)
    (residual_locations_mem_positiveCoordinates C)
    (residualScale_pos C k).le hsum hWposD
  have hWnegAbs : |Wneg| ≤ Wpos :=
    abs_lagrangeInverseValue_neg_le_pos a C.location
      (residualLagrangeAlpha_pos C hk)
      (residual_locations_mem_positiveCoordinates C)
      (residualScale_pos C k).le hsum
  have hWnegD (i : iota) : Wneg < C.location i :=
    (le_abs_self Wneg).trans hWnegAbs |>.trans_lt (hWposD i)
  have hphi : 0 < lagrangePhiValue a C.location Wneg :=
    lagrangePhiValue_pos a C.location
      (residual_locations_mem_positiveCoordinates C) hWnegD
  have hfixed : Wneg = (-R) * lagrangePhiValue a C.location Wneg :=
    hneg.2
  rw [residualPsi_eq_div_lagrangePhiValue C
    ((hWnegD (residualMinIndex C)).trans_le
      (by rw [location_residualMinIndex C]))]
  exact (div_eq_iff hphi.ne').2 hfixed

theorem residual_lagrangeInverseValue_neg_lt_zero_of_separation
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    {k b : ℝ} (hk : 0 < k) (hsep : IsResidualSeparationPoint C k b) :
    lagrangeInverseValue (residualLagrangeAlpha C k) C.location
      (-residualScale C k) < 0 := by
  let Wneg := lagrangeInverseValue (residualLagrangeAlpha C k) C.location
    (-residualScale C k)
  have hpsi := residualPsi_lagrangeInverseValue_neg_eq_neg_scale_of_separation
    C hk hsep
  rw [residualPsi] at hpsi
  have hexp : 0 < Real.exp ((1 / k) *
      ∑ i, C.weight i * Real.log (1 - Wneg / C.location i)) :=
    Real.exp_pos _
  have hR : 0 < residualScale C k := residualScale_pos C k
  nlinarith

/-- At contact, the endpoint value of the Lagrange series is exactly the
critical point; this is the analytic contact certificate. -/
theorem residual_lagrangeInverseValue_eq_critical_of_contact
    {iota : Type*} [Fintype iota] (C : ResidualConfiguration iota)
    (k : ℝ) (hk : 0 < k)
    (hcontact : residualScale C k =
      residualPsi C k (residualCriticalPoint C k hk)) :
    lagrangeInverseValue (residualLagrangeAlpha C k) C.location
        (residualScale C k) = residualCriticalPoint C k hk := by
  let W := lagrangeInverseValue (residualLagrangeAlpha C k) C.location
    (residualScale C k)
  let yc := residualCriticalPoint C k hk
  have hyc := residualCriticalPoint_mem_Ioo C k hk
  have hsep : IsResidualSeparationPoint C k yc := by
    refine ⟨hyc.1, fun i ↦
      hyc.2.trans_le (residualMinLocation_le_location C i), ?_⟩
    exact (residualPotential_nonneg_iff_scale_le_psi_of_pos
      C hk hyc.1 hyc.2).2 hcontact.le
  have hWle : W ≤ yc :=
    residual_lagrangeInverseValue_le_critical_of_separation C hk hsep
  have hpsiW : residualPsi C k W = residualScale C k :=
    residualPsi_lagrangeInverseValue_eq_scale_of_separation C hk hsep
  have hW0 : 0 ≤ W := by
    unfold W lagrangeInverseValue
    exact tsum_nonneg fun n ↦ mul_nonneg
      (coeff_lagrangeInversePowerSeries_nonneg _ _
        (residualLagrangeAlpha_pos C hk)
        (residual_locations_mem_positiveCoordinates C) n)
      (pow_nonneg (residualScale_pos C k).le n)
  apply (residualPsi_strictMonoOn_left C k hk).injOn
    ⟨hW0, hWle⟩ ⟨hyc.1.le, le_rfl⟩
  rw [hpsiW, hcontact]

end

end Erdos1038
