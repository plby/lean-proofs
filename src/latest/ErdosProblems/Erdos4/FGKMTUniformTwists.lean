import ErdosProblems.Erdos4.FGKMTExceptionalDecay
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormula

/-!
# Uniform primitive character estimates after prime excision

The constants and endpoint threshold are chosen before the modulus bound.
One omitted prime works for every endpoint whose square-root-logarithmic
height exceeds that modulus bound.
-/

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

theorem exists_uniform_twisted_sum :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ X₀ : ℕ,
      ∀ Q : ℕ, 2 ≤ Q → ∃ B : ℕ, B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X₀ ≤ x → (Q : ℝ) ≤ siegelWalfiszHeight x →
          ∀ χ : PrimitiveCharacter, χ.modulus ≤ Q → χ.modulus.Coprime B →
            ‖twistedChebyshevSum x χ.modulus χ.character‖ ≤
              C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨K, _hK, hformula⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le
  obtain ⟨M, A, hM, _hA, _hcard, hnonexceptional⟩ :=
    exists_nat_card_dirichletExceptionalLFunctionZerosFinset_le_one_and_norm_dirichletNonexceptionalZeroKernelSum_le
  obtain ⟨U, hU, hexc⟩ := exists_uniform_prime_excision
  let cE : ℝ := 1 / (4 * (U : ℝ) ^ 2)
  let cN : ℝ := 1 / (8 * (M : ℝ) ^ 2)
  let c : ℝ := min cE (min cN (1 / 2))
  let C : ℝ := (K : ℝ) + 96 * (A : ℝ) + 2
  have hcE : 0 < cE := by
    have hUr : (0 : ℝ) < U := by exact_mod_cast (by omega : 0 < U)
    unfold cE
    positivity
  have hcN : 0 < cN := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    unfold cN
    positivity
  have hc : 0 < c := lt_min hcE (lt_min hcN (by norm_num))
  have hC : 0 < C := by unfold C; positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (eventually_siegelWalfiszHeight_conditions 1 (by norm_num) M hM)
  refine ⟨C, c, hC, hc, X₀, ?_⟩
  intro Q hQ
  obtain ⟨B, hBQ, hB, hfree⟩ := hexc Q hQ
  refine ⟨B, hBQ, hB, ?_⟩
  intro x hxX hQheight χ hχQ hcop
  obtain ⟨hx, hxlog, hheightTwo, hheightX, _hlogHeight, hfour, htwo⟩ := hX₀ x hxX
  have hxReal : (4 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hu : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have hqHeight : (χ.modulus : ℝ) ≤ siegelWalfiszHeight x :=
    (by exact_mod_cast hχQ : (χ.modulus : ℝ) ≤ Q).trans hQheight
  have hF := (hformula χ.modulus χ.character (siegelWalfiszHeight x) hheightTwo x hx hheightX).trans
    (mul_dirichletExplicitFormulaErrorScale_siegelWalfiszHeight_le
      (K : ℝ) (Nat.cast_nonneg K) hxlog hqHeight hfour)
  have hN := (hnonexceptional χ.modulus χ.character (x : ℝ) (siegelWalfiszHeight x)
    hxReal hheightTwo hheightX).trans
    (dirichletNonexceptionalSiegelWalfiszEnvelope_le A M hM hxlog hqHeight htwo)
  have hE := (exceptional_kernel_le_after_excision hM hfree χ hχQ hcop
    (by linarith : (1 : ℝ) ≤ x) (siegelWalfiszHeight x)).trans
    (mul_le_mul_of_nonneg_left (exceptional_power_decay hU hQ hxpos hxlog hQheight) (by norm_num))
  have hcEle : c ≤ cE := min_le_left _ _
  have hcNle : c ≤ cN := (min_le_right _ _).trans (min_le_left _ _)
  have hcHalf : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hF' :
      ‖twistedChebyshevSum x χ.modulus χ.character -
        dirichletExplicitFormulaMainZeroTerms χ.character (x : ℝ) (siegelWalfiszHeight x)‖ ≤
      (K : ℝ) * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
    apply hF.trans
    gcongr
  have hN' : ‖dirichletNonexceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x)‖ ≤
      96 * (A : ℝ) * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
    apply hN.trans
    gcongr
  have hE' : ‖dirichletExceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x)‖ ≤
      2 * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
    apply hE.trans
    gcongr
  have hmain : dirichletExplicitFormulaMainZeroTerms χ.character (x : ℝ) (siegelWalfiszHeight x) =
      -(dirichletNonexceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x) +
        dirichletExceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x)) := by
    rw [dirichletExplicitFormulaMainZeroTerms,
      dirichletNontrivialZeroKernelSum_eq_nonexceptional_add_exceptional M, if_neg χ.nonprincipal]
    ring
  have htriangle := norm_sub_le
    (twistedChebyshevSum x χ.modulus χ.character -
      dirichletExplicitFormulaMainZeroTerms χ.character (x : ℝ) (siegelWalfiszHeight x))
    (dirichletNonexceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x) +
      dirichletExceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x))
  have heq : (twistedChebyshevSum x χ.modulus χ.character -
      dirichletExplicitFormulaMainZeroTerms χ.character (x : ℝ) (siegelWalfiszHeight x)) -
      (dirichletNonexceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x) +
        dirichletExceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x)) =
      twistedChebyshevSum x χ.modulus χ.character := by rw [hmain]; ring
  rw [heq] at htriangle
  have hadd := norm_add_le
    (dirichletNonexceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x))
    (dirichletExceptionalZeroKernelSum M χ.character (x : ℝ) (siegelWalfiszHeight x))
  unfold C
  nlinarith

end Erdos4.FGKMT
