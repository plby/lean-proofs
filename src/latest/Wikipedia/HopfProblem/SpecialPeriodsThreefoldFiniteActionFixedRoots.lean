import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionExponentialCore
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite vertical parameters are actual real times

The exact integral kernel of the already constructed normalized
exponential implies that every finite-order multiplicative parameter
comes from real time. The standard nonidentity `n`-th root is exhibited
inside Mathlib's literal subgroup `rootsOfUnity n ℂ` for every `n ≥ 2`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed

open VerticalAction.Exponential

theorem normalizedExponential_nat_mul (s : ℂ) (n : ℕ) :
    normalizedExponential ((n : ℂ) * s) = normalizedExponential s ^ n := by
  have h := normalizedExponentialAddHom.map_nsmul n s
  change normalizedExponential (n • s) = normalizedExponential s ^ n at h
  simpa only [nsmul_eq_mul] using h

/-- Every finite-order parameter of the original complex multiplicative
group has a real lift under the actual normalized exponential. -/
theorem exists_real_parameter_of_isOfFinOrder (u : ℂˣ) (hu : IsOfFinOrder u) :
    ∃ s : ℝ, normalizedExponential (s : ℂ) = u := by
  obtain ⟨t, ht⟩ := normalizedExponential_surjective u
  obtain ⟨n, hn, hp⟩ := hu.exists_pow_eq_one
  have he : normalizedExponential ((n : ℂ) * t) = 1 := by
    rw [normalizedExponential_nat_mul, ht, hp]
  obtain ⟨k, hk⟩ := (normalizedExponential_eq_one_iff _).mp he
  have him : (n : ℝ) * t.im = 0 := by
    simpa only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
      Complex.intCast_im, zero_mul, add_zero] using congrArg Complex.im hk
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ht0 : t.im = 0 := (mul_eq_zero.mp him).resolve_left hn0
  have hreal : (t.re : ℂ) = t := by
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im, ht0]
  exact ⟨t.re, hreal ▸ ht⟩

/-- A nonidentity finite-order parameter has a nonintegral real lift. -/
theorem exists_noninteger_real_parameter (u : ℂˣ) (hu : u ≠ 1)
    (hfin : IsOfFinOrder u) :
    ∃ s : ℝ, normalizedExponential (s : ℂ) = u ∧ ¬ ∃ k : ℤ, s = (k : ℝ) := by
  obtain ⟨s, hs⟩ := exists_real_parameter_of_isOfFinOrder u hfin
  refine ⟨s, hs, ?_⟩
  rintro ⟨k, rfl⟩
  apply hu
  exact hs.symm.trans (by simpa only [Complex.ofReal_intCast] using normalizedExponential_int k)

/-- The actual real time `1/n`, used only when `n ≥ 2`. -/
def generatorTime (n : ℕ) : ℝ := 1 / (n : ℝ)

theorem generatorTime_pos {n : ℕ} (hn : 0 < n) : 0 < generatorTime n :=
  one_div_pos.mpr (by exact_mod_cast hn)

theorem generatorTime_lt_one {n : ℕ} (hn : 2 ≤ n) : generatorTime n < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn)
  exact (div_lt_one hn0).mpr hn1

theorem generatorTime_not_integer {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ k : ℤ, generatorTime n = (k : ℝ) := by
  rintro ⟨k, hk⟩
  have hp := generatorTime_pos (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hl := generatorTime_lt_one hn
  rw [hk] at hp hl
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hp
  have hk1 : k < (1 : ℤ) := by exact_mod_cast hl
  omega

/-- A specific actual parameter in the `n`-th roots-of-unity subgroup. -/
def standardRoot (n : ℕ) : ℂˣ := normalizedExponential (generatorTime n : ℂ)

theorem standardRoot_pow {n : ℕ} (hn : 0 < n) : standardRoot n ^ n = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hr : (n : ℝ) * generatorTime n = 1 := by
    simp only [generatorTime, one_div, mul_inv_cancel₀ hn0]
  have hc : (n : ℂ) * (generatorTime n : ℂ) = 1 := by exact_mod_cast hr
  rw [standardRoot, ← normalizedExponential_nat_mul, hc]
  simpa only [Int.cast_one] using normalizedExponential_int 1

theorem standardRoot_ne_one {n : ℕ} (hn : 2 ≤ n) : standardRoot n ≠ 1 := by
  intro he
  obtain ⟨k, hk⟩ := (normalizedExponential_eq_one_iff _).mp he
  apply generatorTime_not_integer hn
  exact ⟨k, by simpa only [Complex.ofReal_re, Complex.intCast_re] using congrArg Complex.re hk⟩

theorem standardRoot_mem {n : ℕ} (hn : 0 < n) : standardRoot n ∈ rootsOfUnity n ℂ :=
  (mem_rootsOfUnity n _).mpr (standardRoot_pow hn)

theorem standardRoot_isOfFinOrder {n : ℕ} (hn : 0 < n) : IsOfFinOrder (standardRoot n) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, standardRoot_pow hn⟩

/-- This is the actual finite subgroup of the usual complex units. -/
theorem rootsOfUnity_finite {n : ℕ} (hn : 0 < n) : Finite (rootsOfUnity n ℂ) := by
  let : NeZero n := ⟨hn.ne'⟩
  infer_instance

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed
