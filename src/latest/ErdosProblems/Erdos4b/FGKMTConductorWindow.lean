/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTVaughanCubeRange
import ErdosProblems.Erdos4b.FGKMTSqrtLogGrowth
import ErdosProblems.Erdos4b.FGKMTPrimePrefixEnvelope

/-!
# Effective prime progression saving on a uniform conductor window

The same excluded prime works for every endpoint in the displayed window.
The explicit Vaughan and prime-power remainders are absorbed on the actual
prime-counting scale, with all constants preceding the cutoff and endpoint.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter BoundedGaps.Maynard

theorem div_log_fifth_le_expDecay {x R : ℕ} {a : ℝ}
    (hR : Real.exp ((a / 2) * Real.sqrt (Real.log (x : ℝ))) ≤ R)
    (hlog : Real.log (x : ℝ) ^ 5 ≤
      Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ)))) :
    (x : ℝ) / R * Real.log (x : ℝ) ^ 5 ≤
      (x : ℝ) * Real.exp (-(a / 4) * Real.sqrt (Real.log (x : ℝ))) := by
  let u := Real.sqrt (Real.log (x : ℝ))
  have hfrac : (x : ℝ) / R ≤ (x : ℝ) / Real.exp ((a / 2) * u) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg x) (Real.exp_pos _) hR
  calc
    _ ≤ ((x : ℝ) / Real.exp ((a / 2) * u)) * Real.exp ((a / 4) * u) :=
      mul_le_mul hfrac hlog (pow_nonneg (Real.log_natCast_nonneg x) _) (by positivity)
    _ = (x : ℝ) * (Real.exp (-((a / 2) * u)) * Real.exp ((a / 4) * u)) := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem smallConductorLogFactor_le_expDecay {C c : ℝ} (hC : 0 ≤ C)
    {x L : ℕ} (hL : 1 ≤ L) (hLx : L ≤ x) (hlog : 1 ≤ Real.log (x : ℝ))
    (habsorb : Real.log (x : ℝ) ≤
      Real.exp ((c / 2) * Real.sqrt (Real.log (x : ℝ)))) :
    (4 * (1 + Real.log (L : ℝ))) *
        (C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) ≤
      8 * C * ((x : ℝ) * Real.exp (-(c / 2) * Real.sqrt (Real.log (x : ℝ)))) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogL : Real.log (L : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hLpos (by exact_mod_cast hLx)
  let u := Real.sqrt (Real.log (x : ℝ))
  calc
    _ ≤ (4 * (2 * Real.log (x : ℝ))) * (C * ((x : ℝ) * Real.exp (-c * u))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log (L : ℝ) ≤
          2 * Real.log (x : ℝ)) (by norm_num)) (by positivity)
    _ = 8 * C * ((x : ℝ) * (Real.log (x : ℝ) * Real.exp (-c * u))) := by ring
    _ ≤ 8 * C * ((x : ℝ) * (Real.exp ((c / 2) * u) * Real.exp (-c * u))) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 3; ring

theorem exists_effective_primePrefix_bound_on_conductor_window :
    ∃ D a d : ℝ, 0 < D ∧ 0 < a ∧ 0 < d ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ R : ℕ, 2 ≤ R → ∃ B : ℕ, 1 ≤ B ∧ B ≤ R ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X0 ≤ x →
          Real.exp ((a / 2) * Real.sqrt (Real.log (x : ℝ))) ≤ R →
          (R : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
          ∀ L : ℕ, R ≤ L → (L : ℝ) ≤ vaughanCubeRoot x →
            coprimePrimeDiscrepancyPrefixSum B L x ≤
              D * ((x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨C, a, c, hC, ha, hc, Xs, hXs, henv⟩ :=
    exists_exceptionalPrime_primePrefixEnvelope_bound
  obtain ⟨K, hK, hKbound⟩ := exists_primeProgressionVaughanRemainder_le_pow_log
  let d : ℝ := min (a / 4) (c / 2)
  let D : ℝ := (8 * C + 2 * K) * (Real.log 2)⁻¹
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdA : d ≤ a / 4 := min_le_left _ _
  have hdC : d ≤ c / 2 := min_le_right _ _
  have hinv : 0 < (Real.log 2)⁻¹ := inv_pos.mpr (Real.log_pos one_lt_two)
  have hD : 0 < D := by dsimp [D]; positivity
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hready : ∀ᶠ x : ℕ in atTop, 4 ≤ x ∧ 1 ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ Real.exp ((c / 2) * Real.sqrt (Real.log (x : ℝ))) ∧
      Real.log (x : ℝ) ^ 5 ≤ Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) ∧
      (x : ℝ) ^ (5 / 6 : ℝ) * Real.log (x : ℝ) ^ 6 ≤
        (x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by
    filter_upwards [eventually_ge_atTop (4 : ℕ),
      hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_log_pow_le_exp_mul_sqrtLog 1 (by positivity : 0 < c / 2),
      eventually_log_pow_le_exp_mul_sqrtLog 5 (by positivity : 0 < a / 4),
      eventually_rpow_log_pow_le_expDecay (5 / 6) d 6 (by norm_num)] with
      x hx hlog h1 h5 h6
    exact ⟨hx, hlog, by simpa only [pow_one] using h1, h5, h6⟩
  obtain ⟨Xg, hXg⟩ := eventually_atTop.mp hready
  let X0 := max Xs Xg
  refine ⟨D, a, d, hD, ha, hd, X0, hXs.trans (le_max_left _ _), ?_⟩
  intro R hR
  obtain ⟨B, hBpos, hBR, hB, hbound⟩ := henv R hR
  refine ⟨B, hBpos, hBR, hB, ?_⟩
  intro x hx hRlower hRupper L hRL hL
  have hxXs : Xs ≤ x := (le_max_left _ _).trans hx
  have hxXg : Xg ≤ x := (le_max_right _ _).trans hx
  obtain ⟨hx4, hlog, hlogAbsorb, hlog5, hpower⟩ := hXg x hxXg
  have hx1 : 1 ≤ x := by omega
  have hR1 : 1 ≤ R := by omega
  have hL1 : 1 ≤ L := hR1.trans hRL
  have hLsqrt := hL.trans (vaughanCubeRoot_le_sqrt hx1)
  have hLx : L ≤ x := by
    exact_mod_cast hLsqrt.trans
      (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast hx1)))
  let E := (x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ)))
  have hAcompare : (x : ℝ) * Real.exp (-(a / 4) * Real.sqrt (Real.log (x : ℝ))) ≤ E := by
    dsimp [E]
    gcongr
  have hCcompare : (x : ℝ) * Real.exp (-(c / 2) * Real.sqrt (Real.log (x : ℝ))) ≤ E := by
    dsimp [E]
    gcongr
  have hfirst : (x : ℝ) / R * Real.log (x : ℝ) ^ 5 ≤ E :=
    (div_log_fifth_le_expDecay hRlower hlog5).trans hAcompare
  have hrem : primeProgressionVaughanRemainder L R x ≤ 2 * K * E := by
    calc
      _ ≤ K * ((x : ℝ) / R * Real.log (x : ℝ) ^ 5 +
          (x : ℝ) ^ (5 / 6 : ℝ) * Real.log (x : ℝ) ^ 6) :=
        hKbound x L R hx1 hlog hR1 hRL hL
      _ ≤ K * (E + E) := mul_le_mul_of_nonneg_left (add_le_add hfirst hpower) hK.le
      _ = _ := by ring
  have hsmall : (4 * (1 + Real.log (L : ℝ))) *
      (C * ((x : ℝ) * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) ≤ 8 * C * E :=
    (smallConductorLogFactor_le_expDecay hC.le hL1 hLx hlog hlogAbsorb).trans
      (mul_le_mul_of_nonneg_left hCcompare (by positivity))
  calc
    _ ≤ _ := hbound x hxXs hRupper L hRL hLsqrt
    _ ≤ (Real.log 2)⁻¹ * (8 * C * E + 2 * K * E) :=
      mul_le_mul_of_nonneg_left (add_le_add hsmall hrem) hinv.le
    _ = D * E := by dsimp [D]; ring

theorem exists_effective_primeProgression_bound_on_conductor_window :
    ∃ D a d : ℝ, 0 < D ∧ 0 < a ∧ 0 < d ∧ ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ R : ℕ, 2 ≤ R → ∃ B : ℕ, 1 ≤ B ∧ B ≤ R ∧ (B = 1 ∨ B.Prime) ∧
        ∀ x : ℕ, X0 ≤ x →
          Real.exp ((a / 2) * Real.sqrt (Real.log (x : ℝ))) ≤ R →
          (R : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
          ∀ L : ℕ, R ≤ L → (L : ℝ) ≤ vaughanCubeRoot x →
            coprimeModulusDiscrepancySum B L x ≤
              D * ((x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨D, a, d, hD, ha, hd, X0, hX0, hwindow⟩ :=
    exists_effective_primePrefix_bound_on_conductor_window
  refine ⟨D, a, d, hD, ha, hd, X0, hX0, ?_⟩
  intro R hR
  obtain ⟨B, hBpos, hBR, hB, hbound⟩ := hwindow R hR
  refine ⟨B, hBpos, hBR, hB, ?_⟩
  intro x hx hRlower hRupper L hRL hL
  exact (coprimeModulusDiscrepancySum_le_prefix le_rfl B L).trans
    (hbound x hx hRlower hRupper L hRL hL)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.div_log_fifth_le_expDecay
#print axioms Erdos4b.FGKMT.smallConductorLogFactor_le_expDecay
#print axioms Erdos4b.FGKMT.exists_effective_primePrefix_bound_on_conductor_window
#print axioms Erdos4b.FGKMT.exists_effective_primeProgression_bound_on_conductor_window
