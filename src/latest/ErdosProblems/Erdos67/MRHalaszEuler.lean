import ErdosProblems.Erdos67.EulerQuantitative
import ErdosProblems.Erdos67.HalaszCpowDeficit
import ErdosProblems.Erdos67.HalaszLocalEuler
import ErdosProblems.Erdos67.MRTMajorArc

/-!
# Euler-product suppression for the complex Halász argument

This file proves the Euler-product half of the complex Halász mean-value
theorem.  The key quantity is the loss in the real part of the linear Euler
term, relative to the zeta Euler product.  A finite amount of such loss on
the primes up to `X` suppresses the complete Dirichlet series by the
exponential of that loss, with an absolute prime-square error.

All statements below are unconditional consequences of the Euler product;
there is no mean-value theorem packaged as an assumption.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace Erdos67.MRHalaszEuler

noncomputable section

open Erdos67.EulerResidue
open Erdos67.EulerQuantitative

/-- The vertical point used in Halász's argument. -/
def halaszPoint (X : ℕ) (t : ℝ) : ℂ :=
  (taoExponent X : ℂ) + Complex.I * (t : ℂ)

@[simp]
theorem halaszPoint_re (X : ℕ) (t : ℝ) :
    (halaszPoint X t).re = taoExponent X := by
  simp [halaszPoint]

/-- The logarithm of one Euler factor for a completely multiplicative
unit-circle-valued coefficient. -/
def eulerLogTerm (h : ℕ →*₀ ℂ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  -Complex.log (1 - h p * (p : ℂ) ^ (-s))

/-- The loss in the real part of the linear Euler term relative to zeta. -/
def linearEulerDeficit (h : ℕ →*₀ ℂ) (s : ℂ)
    (p : Nat.Primes) : ℝ :=
  ‖(p : ℂ) ^ (-s)‖ - (h p * (p : ℂ) ^ (-s)).re

/-- The finite Euler loss on primes up to `X`. -/
def finiteLinearEulerDeficit (h : ℕ →*₀ ℂ) (s : ℂ)
    (X : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE X,
    (‖(p : ℂ) ^ (-s)‖ - (h p * (p : ℂ) ^ (-s)).re)

theorem linearEulerDeficit_nonneg {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (s : ℂ) (p : Nat.Primes) :
    0 ≤ linearEulerDeficit h s p := by
  unfold linearEulerDeficit
  have hre : (h p * (p : ℂ) ^ (-s)).re ≤
      ‖h p * (p : ℂ) ^ (-s)‖ := Complex.re_le_norm _
  rw [norm_mul, hh p.prop.ne_zero, one_mul] at hre
  linarith

theorem finiteLinearEulerDeficit_nonneg {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) (s : ℂ) (X : ℕ) :
    0 ≤ finiteLinearEulerDeficit h s X := by
  unfold finiteLinearEulerDeficit
  apply Finset.sum_nonneg
  intro p hp
  exact linearEulerDeficit_nonneg hh s
    ⟨p, (Nat.mem_primesLE.mp hp).2⟩

/-- The Euler logarithm is absolutely summable to the right of one. -/
theorem summable_eulerLogTerm {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    Summable (eulerLogTerm h s) := by
  have hraw : Summable (fun p : Nat.Primes ↦
      h p * (p : ℂ) ^ (-s)) := by
    have hnat := (summable_norm_weightedSummandHom hh hs).of_norm
    have hsub := hnat.subtype Nat.Prime
    refine hsub.congr ?_
    intro p
    change weightedSummandHom h _ p = _
    exact weightedSummandHom_apply h _ p
  change Summable (fun p : Nat.Primes ↦
    -Complex.log (1 - h p * (p : ℂ) ^ (-s)))
  exact hraw.clog_one_sub.neg

theorem summable_primeCpowNorm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ ‖(p : ℂ) ^ (-s)‖) := by
  have hnat := summable_riemannZetaSummand hs
  have hsub := hnat.subtype Nat.Prime
  refine hsub.congr ?_
  intro p
  simp only [Function.comp_apply, riemannZetaSummandHom,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]

theorem summable_primeCpowNorm_sq {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ ‖(p : ℂ) ^ (-s)‖ ^ 2) := by
  have hbase := summable_primeCpowNorm hs
  refine hbase.of_nonneg_of_le (fun p ↦ sq_nonneg _) ?_
  intro p
  have hpPos : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast p.prop.one_le
  have hnorm : ‖(p : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hpPos]
    have hexp : (-s).re ≤ 0 := by simp; linarith
    simpa using Real.rpow_le_one_of_one_le_of_nonpos hpOne hexp
  nlinarith [norm_nonneg ((p : ℂ) ^ (-s))]

theorem summable_linearEulerDeficit {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    Summable (linearEulerDeficit h s) := by
  have hraw : Summable (fun p : Nat.Primes ↦
      h p * (p : ℂ) ^ (-s)) := by
    have hnat := (summable_norm_weightedSummandHom hh hs).of_norm
    have hsub := hnat.subtype Nat.Prime
    refine hsub.congr ?_
    intro p
    change weightedSummandHom h _ p = _
    exact weightedSummandHom_apply h _ p
  have hre : Summable (fun p : Nat.Primes ↦
      (h p * (p : ℂ) ^ (-s)).re) := by
    refine hraw.norm.of_norm_bounded ?_
    intro p
    simpa only [Real.norm_eq_abs] using
      Complex.abs_re_le_norm (h p * (p : ℂ) ^ (-s))
  exact (summable_primeCpowNorm hs).sub hre

/-- A finite prime prefix is bounded by the complete nonnegative Euler
deficit. -/
theorem finiteLinearEulerDeficit_le_tsum {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    finiteLinearEulerDeficit h s X ≤
      ∑' p : Nat.Primes, linearEulerDeficit h s p := by
  let e : {p // p ∈ Nat.primesLE X} ↪ Nat.Primes :=
    ⟨fun p ↦ ⟨p, (Nat.mem_primesLE.mp p.property).2⟩,
      by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : Nat.Primes ↦ (z : ℕ)) hab⟩
  let S : Finset Nat.Primes := Finset.univ.map e
  have hsum : ∑ p ∈ S, linearEulerDeficit h s p =
      finiteLinearEulerDeficit h s X := by
    unfold S finiteLinearEulerDeficit
    rw [Finset.sum_map]
    change (∑ p : {p // p ∈ Nat.primesLE X},
      linearEulerDeficit h s (e p)) = _
    calc
      (∑ p : {p // p ∈ Nat.primesLE X},
          linearEulerDeficit h s (e p)) =
          ∑ p : {p // p ∈ Nat.primesLE X},
            (‖(p : ℂ) ^ (-s)‖ -
              (h p * (p : ℂ) ^ (-s)).re) := by
            apply Finset.sum_congr rfl
            intro p hp
            rfl
      _ = _ := (Finset.sum_subtype (Nat.primesLE X)
        (fun _ ↦ Iff.rfl)
        (fun p ↦ ‖(p : ℂ) ^ (-s)‖ -
          (h p * (p : ℂ) ^ (-s)).re)).symm
  rw [← hsum]
  exact (summable_linearEulerDeficit hh hs).sum_le_tsum S
    (fun p hp ↦ linearEulerDeficit_nonneg hh s p)

/-- On the Halász line, the finite Euler loss dominates a fixed absolute
multiple of the usual pretentious distance. -/
theorem exp_neg_one_mul_pretentiousDistSq_le_finiteLinearEulerDeficit
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {X : ℕ} (hX : 1 < X) (t : ℝ) :
    Real.exp (-1) * pretentiousDistSq h (archimedeanTwist t) X ≤
      finiteLinearEulerDeficit h (halaszPoint X t) X := by
  have hsets : Nat.primesLE X = primesUpTo X := by
    ext p
    rw [Nat.mem_primesLE, mem_primesUpTo]
    tauto
  rw [pretentiousDistSq, finiteLinearEulerDeficit, hsets,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := (mem_primesUpTo.mp hp)
  have hz : (h p * conj (archimedeanTwist t p)).re ≤ 1 := by
    calc
      (h p * conj (archimedeanTwist t p)).re ≤
          ‖h p * conj (archimedeanTwist t p)‖ := Complex.re_le_norm _
      _ = 1 := by
        rw [norm_mul, norm_conj, hh hp'.1.ne_zero,
          norm_archimedeanTwist hp'.1.pos, one_mul]
  have hlocal :=
    Erdos67.HalaszCpowDeficit.exp_neg_one_mul_pretentiousTerm_le_prime_cpow_deficit
      ⟨p, hp'.1⟩ hX hp'.2 (h p) t hz
  simpa only [pretentiousTerm, halaszPoint, taoExponent,
    inv_eq_one_div] using hlocal

/-- The norm of the Dirichlet series is the exponential of the real part
of its complete Euler logarithm. -/
theorem norm_LSeries_eq_exp_re_tsum {h : ℕ →*₀ ℂ}
    (hh : HasUnitNorm h) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries h s‖ = Real.exp ((∑' p : Nat.Primes, eulerLogTerm h s p).re) := by
  rw [← weightedEulerProduct_exp_log hh hs]
  exact Complex.norm_exp _

/-- A general summable pointwise majorant for the Euler logarithm gives a
majorant for the complete Dirichlet series. -/
theorem norm_LSeries_le_exp_tsum_of_local
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {s : ℂ} (hs : 1 < s.re) {G : Nat.Primes → ℝ}
    (hG : Summable G)
    (hlocal : ∀ p : Nat.Primes, (eulerLogTerm h s p).re ≤ G p) :
    ‖LSeries h s‖ ≤ Real.exp (∑' p : Nat.Primes, G p) := by
  rw [norm_LSeries_eq_exp_re_tsum hh hs]
  apply Real.exp_le_exp.mpr
  rw [Complex.re_tsum (summable_eulerLogTerm hh hs)]
  have hRe : Summable (fun p : Nat.Primes ↦
      (eulerLogTerm h s p).re) := by
    refine (summable_eulerLogTerm hh hs).norm.of_norm_bounded ?_
    intro p
    simpa only [Real.norm_eq_abs] using
      Complex.abs_re_le_norm (eulerLogTerm h s p)
  exact Summable.tsum_le_tsum hlocal
    hRe hG

/-- The complete Euler-product suppression bound.  The first term is the
zeta-sized prime mass, the second is the finite nonpretentious loss, and the
last is the absolutely summable prime-square error. -/
theorem norm_LSeries_le_exp_primeMass_sub_deficit_add_square
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    ‖LSeries h s‖ ≤
      Real.exp ((∑' p : Nat.Primes, ‖(p : ℂ) ^ (-s)‖) -
        finiteLinearEulerDeficit h s X +
          ∑' p : Nat.Primes, ‖(p : ℂ) ^ (-s)‖ ^ 2) := by
  let G : Nat.Primes → ℝ := fun p ↦
    ‖(p : ℂ) ^ (-s)‖ - linearEulerDeficit h s p +
      ‖(p : ℂ) ^ (-s)‖ ^ 2
  have hG : Summable G :=
    ((summable_primeCpowNorm hs).sub
      (summable_linearEulerDeficit hh hs)).add
        (summable_primeCpowNorm_sq hs)
  have hlocal : ∀ p : Nat.Primes, (eulerLogTerm h s p).re ≤ G p := by
    intro p
    have h := Erdos67.HalaszLocalEuler.neg_log_primeEulerFactor_re_le
      hh hs p.prop
    unfold eulerLogTerm G linearEulerDeficit
    linarith
  have hbase := norm_LSeries_le_exp_tsum_of_local hh hs hG hlocal
  refine hbase.trans (Real.exp_le_exp.mpr ?_)
  change (∑' p : Nat.Primes,
      (‖(p : ℂ) ^ (-s)‖ - linearEulerDeficit h s p +
        ‖(p : ℂ) ^ (-s)‖ ^ 2)) ≤ _
  rw [((summable_primeCpowNorm hs).sub
      (summable_linearEulerDeficit hh hs)).tsum_add
        (summable_primeCpowNorm_sq hs),
    (summable_primeCpowNorm hs).tsum_sub
      (summable_linearEulerDeficit hh hs)]
  have hprefix := finiteLinearEulerDeficit_le_tsum hh hs X
  linarith

/-- The prime norm mass on the Halász line is at most the logarithm of
zeta at its real part. -/
theorem tsum_primeCpowNorm_halaszPoint_le_logZeta
    {X : ℕ} (hX : 1 < X) (t : ℝ) :
    (∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖) ≤
      Real.log (riemannZeta (taoExponent X : ℂ)).re := by
  have heq : (∑' p : Nat.Primes,
      ‖(p : ℂ) ^ (-halaszPoint X t)‖) =
      ∑' p : Nat.Primes, (p : ℝ) ^ (-taoExponent X) := by
    apply tsum_congr
    intro p
    exact Erdos67.HalaszCpowDeficit.norm_prime_cpow_neg_sigma_add_I_mul
      p (taoExponent X) t
  rw [heq]
  exact tsum_primes_rpow_le_log_riemannZeta (one_lt_taoExponent hX)

/-- The prime-square remainder on the Halász line is bounded by the
absolute Euler constant already used in the Section 4 estimates. -/
theorem tsum_primeCpowNorm_sq_halaszPoint_le_constant
    {X : ℕ} (hX : 1 < X) (t : ℝ) :
    (∑' p : Nat.Primes, ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) ≤
      primeQuadraticConstant := by
  have hu : 1 < taoExponent X := one_lt_taoExponent hX
  have heq : (∑' p : Nat.Primes,
      ‖(p : ℂ) ^ (-halaszPoint X t)‖ ^ 2) =
      ∑' p : Nat.Primes, ((p : ℝ) ^ (-taoExponent X)) ^ 2 := by
    apply tsum_congr
    intro p
    unfold halaszPoint
    rw [Erdos67.HalaszCpowDeficit.norm_prime_cpow_neg_sigma_add_I_mul]
  rw [heq]
  have hsum : Summable (fun p : Nat.Primes ↦
      ((p : ℝ) ^ (-taoExponent X)) ^ 2) := by
    have hc := summable_primeCpowNorm_sq
      (s := (taoExponent X : ℂ)) (by simpa using hu)
    refine hc.congr ?_
    intro p
    rw [norm_prime_cpow_neg_real]
  have hnonneg : 0 ≤
      ∑' p : Nat.Primes, ((p : ℝ) ^ (-taoExponent X)) ^ 2 :=
    tsum_nonneg fun p ↦ sq_nonneg _
  have htwo := tsum_primeQuadraticError_le_constant hu
  rw [hsum.tsum_mul_left] at htwo
  linarith

/-- Quantitative Euler suppression by the finite pretentious distance.
This is the exact Euler-product estimate fed into the Perron/Halász
integral argument. -/
theorem norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {X : ℕ} (hX : 1 < X) (t : ℝ) :
    ‖LSeries h (halaszPoint X t)‖ ≤
      Real.exp
        (Real.log (riemannZeta (taoExponent X : ℂ)).re -
          Real.exp (-1) * pretentiousDistSq h (archimedeanTwist t) X +
          primeQuadraticConstant) := by
  have hs : 1 < (halaszPoint X t).re := by
    rw [halaszPoint_re]
    exact one_lt_taoExponent hX
  have hbase := norm_LSeries_le_exp_primeMass_sub_deficit_add_square
    hh hs X
  refine hbase.trans (Real.exp_le_exp.mpr ?_)
  have hprime := tsum_primeCpowNorm_halaszPoint_le_logZeta hX t
  have hdist :=
    exp_neg_one_mul_pretentiousDistSq_le_finiteLinearEulerDeficit hh hX t
  have hsquare := tsum_primeCpowNorm_sq_halaszPoint_le_constant hX t
  linarith

/-- The Euler-product bound in the uniform form required on a major arc:
archimedean nonpretentiousness replaces the finite distance by its prescribed
lower bound, uniformly for all frequencies in the truncation range. -/
theorem norm_LSeries_halaszPoint_le_of_archimedeanNonpretentious
    {h : ℕ →*₀ ℂ} (hh : HasUnitNorm h)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious h A X)
    {t : ℝ} (ht : |t| ≤ X) :
    ‖LSeries h (halaszPoint X t)‖ ≤
      Real.exp
        (Real.log (riemannZeta (taoExponent X : ℂ)).re -
          Real.exp (-1) * (A : ℝ) + primeQuadraticConstant) := by
  refine
    (norm_LSeries_halaszPoint_le_exp_logZeta_sub_pretentiousDistSq
      hh hX t).trans (Real.exp_le_exp.mpr ?_)
  have hdist := hnonpret t ht
  have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  nlinarith

end

end Erdos67.MRHalaszEuler
