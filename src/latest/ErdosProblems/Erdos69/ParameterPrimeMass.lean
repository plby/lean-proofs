import ErdosProblems.Erdos69.CutoffBounds
import ErdosProblems.Erdos69.PrimeMassBounds

/-! # Reciprocal-prime mass in the chosen parameter regime -/

open Filter
open scoped BigOperators Topology

namespace Erdos69.Elementary

theorem primeReciprocalSum_lower {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (x : ℕ) (hx : 2 ≤ x) : Real.log (Real.log (x : ℝ)) - C ≤ primeReciprocalSum x := by
  linarith [(abs_le.mp (hC x hx)).1]

theorem primeReciprocalSum_upper {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (x : ℕ) (hx : 2 ≤ x) : primeReciprocalSum x ≤ Real.log (Real.log (x : ℝ)) + C := by
  linarith [(abs_le.mp (hC x hx)).2]

theorem smallPrime_reciprocal_upper {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (m : ℕ) : primeReciprocalSum (smallPrimeCutoff m) ≤
      (fluctuationScale m : ℝ) * (Real.log 2 + C + 1) := by
  have hu := primeReciprocalSum_upper hC _ (smallPrimeCutoff_ge_two m)
  rw [log_log_smallPrimeCutoff] at hu
  have hB : (1 : ℝ) ≤ fluctuationScale m := by exact_mod_cast fluctuationScale_pos m
  nlinarith [log_log_two_nonpos]

theorem excludedPrime_reciprocal_upper {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    (m : ℕ) : primeReciprocalSum (excludedPrimeCutoff m) ≤
      (patternSize m : ℝ) ^ 3 * Real.log 2 + C := by
  have hu := primeReciprocalSum_upper hC _ (excludedPrimeCutoff_ge_two m)
  have hp : 0 < Real.log (excludedPrimeCutoff m : ℝ) :=
    Real.log_pos (by exact_mod_cast excludedPrimeCutoff_ge_two m)
  have hlog := Real.log_le_sub_one_of_pos hp
  rw [log_excludedPrimeCutoff] at hlog hu
  linarith

theorem construction_primeFactor_reciprocal_le {m : ℕ} (hm : 0 < m) :
    (∑ p ∈ (constructionModulus m).primeFactors, (1 : ℝ) / p) ≤
      primeReciprocalSum (excludedPrimeCutoff m) + 1 / Real.log 2 := by
  have h := reciprocal_primeFactors_le_cutoff (constructionModulus m) (excludedPrimeCutoff m)
    (constructionModulus_pos m) (by have hp := excludedPrimeCutoff_ge_two m; omega)
  apply h.trans
  apply add_le_add le_rfl
  have hp : (0 : ℝ) < excludedPrimeCutoff m := by
    exact_mod_cast (show 0 < excludedPrimeCutoff m by have h := excludedPrimeCutoff_ge_two m; omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  calc
    Real.log (constructionModulus m : ℝ) / ((excludedPrimeCutoff m : ℝ) * Real.log 2) ≤
        (excludedPrimeCutoff m : ℝ) / ((excludedPrimeCutoff m : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_right (log_constructionModulus_le_excluded hm) (by positivity)
    _ = _ := by field_simp

theorem goodPrime_mass_parameter_lower {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C)
    {m : ℕ} (hm : 0 < m) :
    ((fluctuationScale m : ℝ) - 2 * (patternSize m : ℝ) ^ 3) * Real.log 2 +
      Real.log (Real.log 2) - 3 * C - 1 / Real.log 2 ≤
        ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
          (1 : ℝ) / p := by
  have hl := goodPrime_reciprocal_lower (constructionModulus m) (excludedPrimeCutoff m)
    (smallPrimeCutoff m) (constructionModulus_pos m)
  have hs := primeReciprocalSum_lower hC _ (smallPrimeCutoff_ge_two m)
  rw [log_log_smallPrimeCutoff] at hs
  have he := excludedPrime_reciprocal_upper hC m
  have hf := construction_primeFactor_reciprocal_le hm
  linarith

theorem eventually_goodPrime_mass_ge_quarter {C : ℝ}
    (hC : ∀ x : ℕ, 2 ≤ x → |primeReciprocalSum x - Real.log (Real.log (x : ℝ))| ≤ C) :
    ∀ᶠ m : ℕ in atTop, (fluctuationScale m : ℝ) / 4 ≤
      ∑ p ∈ goodPrimes (constructionModulus m) (excludedPrimeCutoff m) (smallPrimeCutoff m),
        (1 : ℝ) / p := by
  let D := 3 * C + 1 / Real.log 2 - Real.log (Real.log 2)
  have hB : Tendsto (fun m ↦ (fluctuationScale m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_fluctuationScale
  filter_upwards [eventually_ge_atTop (1 : ℕ), hB.eventually (eventually_ge_atTop (8 * D))]
    with m hm hlarge
  have hm0 : 0 < m := by omega
  have hN : (8 : ℝ) ≤ patternSize m := by
    have hn := patternSize_ge_thirtysix hm0
    exact_mod_cast (show 8 ≤ patternSize m by omega)
  have hBcast : (fluctuationScale m : ℝ) = (patternSize m : ℝ) ^ 4 := by
    simp [fluctuationScale]
  have hsmall : 8 * (patternSize m : ℝ) ^ 3 ≤ fluctuationScale m := by
    rw [hBcast]
    have h := mul_le_mul_of_nonneg_right hN (by positivity : 0 ≤ (patternSize m : ℝ) ^ 3)
    nlinarith
  have hpos : 0 ≤ (fluctuationScale m : ℝ) - 2 * (patternSize m : ℝ) ^ 3 := by
    nlinarith [show (0 : ℝ) ≤ (patternSize m : ℝ) ^ 3 by positivity]
  have hhalf := mul_le_mul_of_nonneg_right half_le_log_two hpos
  have hl := goodPrime_mass_parameter_lower hC hm0
  dsimp [D] at hlarge
  nlinarith

end Erdos69.Elementary
