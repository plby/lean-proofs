import ErdosProblems.Erdos157.CharacterPositivity
import ErdosProblems.Erdos157.PolynomialInverseRoots

/-! An explicit elementary zero-free region for polynomial characters. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial ElementaryCharacterBound

theorem rootSum_div {m : ℕ} (α : Fin m → ℂ) (q : ℝ) (z : ℂ) :
    rootSum (fun i => α i / (q : ℂ)) z = rootSum α (z / (q : ℂ)) := by
  unfold rootSum
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  ring

theorem rootSum_inverseRootAt (p : ℂ[X]) (hp : p.coeff 0 = 1)
    (z : ℂ) (hz : p.eval z ≠ 0) :
    rootSum (inverseRootAt p) z = (z * (p.derivative.eval z / p.eval z)).re := by
  have h := congrArg Complex.re (inverseRoots_logDerivative p hp z hz)
  simpa only [Complex.re_sum, rootSum] using h.symm

theorem squaredPhase_div_pos (z : ℂ) (q : ℝ) (hq : 0 < q) :
    squaredPhase (z / (q : ℂ)) = squaredPhase z / (q : ℂ) := by
  by_cases hz : z = 0
  · simp [hz, squaredPhase]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  unfold squaredPhase
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, Complex.ofReal_div]
  field_simp

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

/-- The elementary inverse-root bound for a character with nonprincipal square. -/
theorem norm_inverseRoot_lt_explicit (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    (j : Fin (lPolynomial g χ).roots.toList.length) :
    ‖inverseRootAt (lPolynomial g χ) j‖ <
      (Fintype.card K : ℝ) * (1 - 1 / (100 * (g.natDegree : ℝ))) := by
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  let p := lPolynomial g χ
  let p2 := lPolynomial g (χ ^ 2)
  let α := fun i => inverseRootAt p i / (q : ℂ)
  let β := fun i => inverseRootAt p2 i / (q : ℂ)
  have hm := lPolynomial_root_count_lt g hg χ hχ
  have hn := lPolynomial_root_count_lt g hg (χ ^ 2) hχ2
  have hH : 1 ≤ g.natDegree := by omega
  have hα : ∀ i, ‖α i‖ ≤ 1 := by
    intro i
    dsimp only [α]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    exact (div_le_one hq).mpr (lPolynomial_inverseRoot_norm_le g hg χ hχ i)
  have hβ : ∀ i, ‖β i‖ ≤ 1 := by
    intro i
    dsimp only [β]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    exact (div_le_one hq).mpr (lPolynomial_inverseRoot_norm_le g hg (χ ^ 2) hχ2 i)
  have hpositive : ∀ z : ℂ, ‖z‖ < 1 →
      0 ≤ 3 * (‖z‖ / (1 - ‖z‖)) + 4 * rootSum α z + rootSum β (squaredPhase z) := by
    intro z hz
    have hscale : q * ‖z / (q : ℂ)‖ = ‖z‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
      exact mul_div_cancel₀ _ hq.ne'
    have hsmall : q * ‖z / (q : ℂ)‖ < 1 := by rwa [hscale]
    have hlt : ‖z / (q : ℂ)‖ < 1 / q :=
      (lt_div_iff₀ hq).mpr (by simpa only [mul_comm] using hsmall)
    obtain ⟨r, hrz, hrq⟩ := exists_between hlt
    have hr : 0 < r := (norm_nonneg _).trans_lt hrz
    have hqr : (Fintype.card K : ℝ) * r < 1 := by
      have := (lt_div_iff₀ hq).mp hrq
      simpa only [q, mul_comm] using this
    have hfirst : rootSum α z =
        ((z / (q : ℂ)) * (p.derivative.eval (z / (q : ℂ)) / p.eval (z / (q : ℂ)))).re := by
      rw [show rootSum α z = rootSum (inverseRootAt p) (z / (q : ℂ)) from rootSum_div _ q z]
      exact rootSum_inverseRootAt p (lPolynomial_constantCoeff g hg χ hχ) _
        (lPolynomial_eval_ne_zero g hg χ hχ _ hsmall)
    have hsecond : rootSum β (squaredPhase z) =
        (squaredPhase (z / (q : ℂ)) *
          (p2.derivative.eval (squaredPhase (z / (q : ℂ))) /
            p2.eval (squaredPhase (z / (q : ℂ))))).re := by
      rw [show rootSum β (squaredPhase z) =
          rootSum (inverseRootAt p2) (squaredPhase z / (q : ℂ)) from rootSum_div _ q _]
      rw [← squaredPhase_div_pos z q hq]
      apply rootSum_inverseRootAt p2 (lPolynomial_constantCoeff g hg (χ ^ 2) hχ2)
      apply lPolynomial_eval_ne_zero g hg (χ ^ 2) hχ2
      rwa [norm_squaredPhase]
    have h := euler_logDerivative_positivity g hg χ hχ hχ2 r hr hqr (z / (q : ℂ)) hrz
    change 0 ≤ 3 * (q * ‖z / (q : ℂ)‖ / (1 - q * ‖z / (q : ℂ)‖)) +
      4 * ((z / (q : ℂ)) * (p.derivative.eval (z / (q : ℂ)) / p.eval (z / (q : ℂ)))).re +
      (squaredPhase (z / (q : ℂ)) *
        (p2.derivative.eval (squaredPhase (z / (q : ℂ))) /
          p2.eval (squaredPhase (z / (q : ℂ))))).re at h
    rwa [hscale, ← hfirst, ← hsecond] at h
  have hroot := norm_root_lt_of_euler_positivity hH α β
    (by dsimp only [p]; omega) (by dsimp only [p2]; omega) hα hβ hpositive j
  dsimp only [α] at hroot
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] at hroot
  have := (div_lt_iff₀ hq).mp hroot
  simpa only [p, q, mul_comm] using this

/-- Odd-order unit groups satisfy the nonquadratic hypothesis automatically. -/
theorem norm_inverseRoot_lt_of_odd_units (g : K[X]) (hg : g.Monic)
    (hodd : Odd (Nat.card (AdjoinRoot g)ˣ))
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1)
    (j : Fin (lPolynomial g χ).roots.toList.length) :
    ‖inverseRootAt (lPolynomial g χ) j‖ <
      (Fintype.card K : ℝ) * (1 - 1 / (100 * (g.natDegree : ℝ))) := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  let : Fintype (AdjoinRoot g)ˣ := Fintype.ofFinite _
  have hχ2 := character_sq_ne_one
    (by simpa only [Nat.card_eq_fintype_card] using hodd) χ hχ
  exact norm_inverseRoot_lt_explicit g hg χ hχ hχ2 j

/-- Explicit power-sum error term, using only the elementary zero-free region. -/
theorem norm_inverseRoot_powerSum_le (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1) (d : ℕ) :
    ‖∑ j, inverseRootAt (lPolynomial g χ) j ^ d‖ ≤
      (g.natDegree : ℝ) * (Fintype.card K : ℝ) ^ d *
        Real.exp (-(d : ℝ) / (100 * (g.natDegree : ℝ))) := by
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  let p := lPolynomial g χ
  let α := fun j => inverseRootAt p j / (q : ℂ)
  have hm := lPolynomial_root_count_lt g hg χ hχ
  have hH : 1 ≤ g.natDegree := by omega
  have hα : ∀ j, ‖α j‖ ≤ 1 - 1 / (100 * (g.natDegree : ℝ)) := by
    intro j
    dsimp only [α]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    have h := (norm_inverseRoot_lt_explicit g hg χ hχ hχ2 j).le
    simpa only [q, mul_comm] using h
  have hbound := norm_rootPowerSum_le hH α hα d
  have hsum : (∑ j, inverseRootAt p j ^ d) = (q : ℂ) ^ d * ∑ j, α j ^ d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [α]
    rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hqC)]
  have hmreal : (p.roots.toList.length : ℝ) ≤ g.natDegree := by exact_mod_cast hm.le
  change ‖∑ j, inverseRootAt p j ^ d‖ ≤ _
  rw [hsum, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  calc
    _ ≤ q ^ d * ((p.roots.toList.length : ℝ) *
        Real.exp (-(d : ℝ) / (100 * (g.natDegree : ℝ)))) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ q ^ d * ((g.natDegree : ℝ) *
        Real.exp (-(d : ℝ) / (100 * (g.natDegree : ℝ)))) := by
      gcongr
    _ = _ := by dsimp only [q]; ring

end Erdos157.Elementary.PolynomialCharacters
