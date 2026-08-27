/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSmallConductorFormula
import ErdosProblems.Erdos4b.FGKMTSmallConductorScale

/-!
# Effective small-conductor character sums with one excluded prime

The constants and endpoint threshold precede the conductor cutoff. For that
cutoff one exceptional prime is selected once, and the same prime works at
every eligible endpoint. No bound with a varying logarithmic exponent is used.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem exists_exceptionalPrime_effective_twistedSum_bound :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ Q : ℕ, 2 ≤ Q → ∃ B : ℕ, 1 ≤ B ∧ B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X0 ≤ x → (Q : ℝ) ^ 2 ≤ siegelWalfiszHeight x →
          ∀ (q : ℕ) [NeZero q], 1 < q → q ≤ Q →
            ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive → q.Coprime B →
              ‖twistedChebyshevSum x q chi‖ ≤
                C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨A, K, N, hA, hK, _hN, hformula⟩ :=
    exists_exceptionalPrime_twistedSum_formula_bound
  let cN : ℝ := 1 / (16 * (A : ℝ) ^ 2)
  let c : ℝ := min (1 / 2) cN
  let C : ℝ := (K : ℝ) + 96 * N
  have hApos : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hcN : 0 < cN := by dsimp [cN]; positivity
  have hc : 0 < c := lt_min (by norm_num) hcN
  have hC : 0 < C := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    dsimp [C]
    positivity
  have hconditions := eventually_siegelWalfiszHeight_conditions 1 zero_lt_one A hA
  have hextra := eventually_log_le_exp_mul_sqrtLog hcN
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (hconditions.and hextra)
  refine ⟨C, c, hC, hc, X0, ((hX0 X0 le_rfl).1).1, ?_⟩
  intro Q hQ
  obtain ⟨B, hBpos, hBQ, hB, hbound⟩ := hformula Q hQ
  refine ⟨B, hBpos, hBQ, hB, ?_⟩
  intro x hxX hQheight q _ hq hqQ chi hprimitive hcop
  obtain ⟨⟨hx, hlog, hheightTwo, hheightX, _hlogHeight, hfour, hsquare⟩, hlogAbsorb⟩ :=
    hX0 x hxX
  have hqQsq : q ≤ Q ^ 2 := hqQ.trans (by nlinarith)
  have hqheight : (q : ℝ) ≤ siegelWalfiszHeight x :=
    (show (q : ℝ) ≤ (Q : ℝ) ^ 2 by exact_mod_cast hqQsq).trans hQheight
  have hraw := hbound q hq hqQ chi hprimitive hcop x (siegelWalfiszHeight x)
    hx hlog hheightTwo hheightX
  have hrem := mul_dirichletExplicitFormulaErrorScale_siegelWalfiszHeight_le
    (K : ℝ) (Nat.cast_nonneg _) hlog hqheight hfour
  have hzero := smallConductorZeroEnvelope_le N A hA hQ hqQ hlog hQheight
    hsquare hlogAbsorb
  have hcHalf : c ≤ (1 / 2 : ℝ) := min_le_left _ _
  have hcNc : c ≤ cN := min_le_right _ _
  have hremCommon :
      (K : ℝ) * ((x : ℝ) * Real.exp
        (-(1 / 2 : ℝ) * Real.sqrt (Real.log (x : ℝ)))) ≤
      (K : ℝ) * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
    gcongr
  have hzeroCommon :
      96 * (N : ℝ) * ((x : ℝ) * Real.exp
        (-cN * Real.sqrt (Real.log (x : ℝ)))) ≤
      96 * (N : ℝ) * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by
    gcongr
  calc
    _ ≤ _ := hraw
    _ ≤ (K : ℝ) * ((x : ℝ) * Real.exp
        (-(1 / 2 : ℝ) * Real.sqrt (Real.log (x : ℝ)))) +
        96 * (N : ℝ) * ((x : ℝ) * Real.exp
          (-cN * Real.sqrt (Real.log (x : ℝ)))) := add_le_add hrem hzero
    _ ≤ (K : ℝ) * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) +
        96 * (N : ℝ) * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
      add_le_add hremCommon hzeroCommon
    _ = _ := by dsimp [C]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_exceptionalPrime_effective_twistedSum_bound
