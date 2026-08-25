import PrimeNumberTheoremAnd.Wiener

/-!
# Character-weighted prime distribution

The already proved PNT in arithmetic progressions and character orthogonality
give cancellation of the character-twisted Mangoldt sum. No prime-distribution
statement is assumed in this module.
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem character_sum_by_residues {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (w : ℕ → ℂ) (X : ℕ) :
    (∑ n ∈ Finset.range X, χ n * w n) =
      ∑ a : ZMod q, χ a * ∑ n ∈ Finset.range X, if n % q = a.val then w n else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  symm
  rw [Finset.sum_eq_single (n : ZMod q)]
  · simp only [ZMod.val_natCast, ite_true]
  · intro a _ ha
    have hne : n % q ≠ a.val := by
      intro h
      apply ha
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast] using h.symm
    rw [if_neg hne, mul_zero]
  · simp

theorem twistedMangoldt_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.range X, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) / (X : ℂ))
      atTop (𝓝 0) := by
  have hterm (a : ZMod q) :
      Tendsto (fun X : ℕ => χ a *
        ((∑ n ∈ Finset.range X,
          if n % q = a.val then (ArithmeticFunction.vonMangoldt n : ℂ) else 0) / (X : ℂ)))
        atTop (𝓝 (χ a * ((1 / (q.totient : ℝ) : ℝ) : ℂ))) := by
    by_cases ha : IsUnit a
    · have hcop : a.val.Coprime q := (ZMod.isUnit_iff_coprime a.val q).mp (by simpa using ha)
      have hAP := WeakPNT_AP (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) hcop (ZMod.val_lt a)
      have hc : Tendsto (fun X : ℕ =>
          ((cumsum (fun n => if n % q = a.val then ArithmeticFunction.vonMangoldt n else 0) X /
            (X : ℝ) : ℝ) : ℂ)) atTop (𝓝 ((1 / (q.totient : ℝ) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hAP
      have hm := hc.const_mul (χ a)
      simpa only [cumsum, Complex.ofReal_div, Complex.ofReal_natCast,
        Complex.ofReal_sum, apply_ite, Complex.ofReal_zero] using hm
    · have hzero : χ a = 0 := χ.map_nonunit ha
      simp only [hzero, zero_mul]
      exact tendsto_const_nhds
  have hsum := tendsto_finsetSum Finset.univ (fun a _ => hterm a)
  have horth : (∑ a : ZMod q, χ a * ((1 / (q.totient : ℝ) : ℝ) : ℂ)) = 0 := by
    rw [← Finset.sum_mul, χ.sum_eq_zero_of_ne_one hχ, zero_mul]
  rw [horth] at hsum
  apply hsum.congr'
  apply Filter.Eventually.of_forall
  intro X
  dsimp only
  rw [character_sum_by_residues χ (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) X,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem realTwistedMangoldt_div_tendsto_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (fun X : ℕ =>
      (∑ n ∈ Finset.range X, (χ n).re * ArithmeticFunction.vonMangoldt n) / (X : ℝ))
      atTop (𝓝 0) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (twistedMangoldt_div_tendsto_zero χ hχ)
  simpa only [Function.comp_def, Complex.zero_re, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using h

end Bernays
