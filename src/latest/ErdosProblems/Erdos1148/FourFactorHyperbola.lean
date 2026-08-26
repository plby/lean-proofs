import ErdosProblems.Erdos1148.BiquadraticBoundary

/-! # A uniform four-factor hyperbola estimate -/

namespace Erdos1148.DukeArithmetic

theorem exists_fourFactor_hyperbola_error_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (q r u : ℕ), 0 < q → 0 < r → 0 < u →
      ∀ (χ : DirichletCharacter ℝ q) (ψ : DirichletCharacter ℝ r)
        (ρ : DirichletCharacter ℝ u), χ ≠ 1 → ψ ≠ 1 → ρ ≠ 1 →
        ∀ (s : ℝ), 1 / 2 ≤ s → s < 1 → ∀ (N : ℕ), 0 < N →
          ‖weightedArithmeticPartialSum
              (realZetaConvolution χ * (realCharacterArithmetic ψ * realCharacterArithmetic ρ))
              s (N * N) -
            ((realZetaRegularized s * realDirichletValue χ s) *
                (realDirichletValue ψ s * realDirichletValue ρ s) +
              ((N * N : ℕ) : ℝ) ^ (1 - s) / (1 - s) * realDirichletValue χ 1 *
                (realDirichletValue ψ 1 * realDirichletValue ρ 1))‖ ≤
            K * ((q : ℝ) * r * u / (1 - s)) * (N : ℝ) ^ (13 / 8 - 2 * s) := by
  obtain ⟨D, hDpos, hD⟩ := exists_weighted_divisor_sum_bound
  refine ⟨108 * D + 640, by positivity, ?_⟩
  intro q r u hq hr hu χ ψ ρ hχ hψ hρ s hs hs1 N hN
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  let : NeZero r := ⟨Nat.ne_zero_of_lt hr⟩
  let : NeZero u := ⟨Nat.ne_zero_of_lt hu⟩
  let A := realZetaConvolution χ
  let B := realCharacterArithmetic ψ * realCharacterArithmetic ρ
  let W := (N : ℝ) ^ (13 / 8 - 2 * s)
  let Q := (q : ℝ) * r * u / (1 - s)
  have hd : 0 < 1 - s := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNN : N ≤ N * N := by nlinarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hW0 : 0 ≤ W := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hru : (1 : ℝ) ≤ (r : ℝ) * u := by exact_mod_cast Nat.mul_pos hr hu
  have hqδ : (1 : ℝ) ≤ (q : ℝ) / (1 - s) := by
    apply (le_div_iff₀ hd).mpr
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hQq : (q : ℝ) / (1 - s) ≤ Q := by
    dsimp [Q]
    rw [div_le_div_iff_of_pos_right hd]
    nlinarith [Nat.cast_nonneg (α := ℝ) q]
  have hQru : (r : ℝ) * u ≤ Q := by
    have h := mul_le_mul_of_nonneg_right hqδ (show (0 : ℝ) ≤ (r : ℝ) * u by positivity)
    calc
      _ ≤ (q : ℝ) / (1 - s) * ((r : ℝ) * u) := by simpa only [one_mul] using h
      _ = Q := by dsimp [Q]; ring
  have hscale : ((N * N : ℕ) : ℝ) ^ (1 / 2 - s) * (N : ℝ) ^ (5 / 8 : ℝ) = W := by
    rw [Nat.cast_mul, rpow_biquadratic_strip hN0]
  have hsmall : (N : ℝ) ^ (3 / 2 - 2 * s) ≤ W :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hAw := hD A (realZetaConvolution_norm_le_card_divisors χ) N hN
  have hBw := hD B (realCharacterConvolution_norm_le_card_divisors ψ ρ) N hN
  have hconst := norm_hyperbola_constant_strip_error_le A (weightedArithmeticPartialSum B s)
    s (realDirichletValue ψ s * realDirichletValue ρ s) hNN
    (show (0 : ℝ) ≤ 32 * r * u by positivity)
    (fun y hy => realCharacterConvolution_floor_error_le ψ ρ hψ hρ hs hs1.le hy) hAw
  have hres := norm_hyperbola_residue_strip_error_le B (weightedArithmeticPartialSum A s)
    s (realZetaRegularized s * realDirichletValue χ s) (realDirichletValue χ 1) hNN
    (show 0 ≤ 76 * ((q : ℝ) / (1 - s)) by positivity)
    (fun y hy => realZetaConvolution_floor_error_le χ hχ hs hs1 hy) hBw
  have hresScale : 76 * ((q : ℝ) / (1 - s)) * D *
      ((N * N : ℕ) : ℝ) ^ (1 / 2 - s) * (N : ℝ) ^ (5 / 8 : ℝ) ≤ 76 * Q * D * W := by
    calc
      _ = 76 * ((q : ℝ) / (1 - s)) * D * W := by rw [← hscale]; ring
      _ ≤ _ := by gcongr
  have hconstScale : 32 * r * u * D *
      ((N * N : ℕ) : ℝ) ^ (1 / 2 - s) * (N : ℝ) ^ (5 / 8 : ℝ) ≤ 32 * Q * D * W := by
    calc
      _ = 32 * ((r : ℝ) * u) * D * W := by rw [← hscale]; ring
      _ ≤ _ := by gcongr
  have hcross := (biquadratic_cross_error_le χ ψ ρ hχ hψ hρ hs hs1 hN).trans
    (mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 608 * Q by positivity))
  have htail := (biquadratic_residue_tail_error_le χ ψ ρ hχ hψ hρ hs1 hN).trans
    (mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 32 * Q by positivity))
  have h := norm_hyperbola_error_le (hres.trans hresScale) (hconst.trans hconstScale) hcross htail
  have hdecomp := weighted_convolution_hyperbola A B s hNN hNN le_rfl
    (by nlinarith : N * N < (N + 1) * (N + 1))
  change ‖weightedArithmeticPartialSum (A * B) s (N * N) - _‖ ≤ _
  rw [hdecomp]
  convert h using 1
  · congr 1
    ring
  · dsimp only [Q, W]
    ring

end Erdos1148.DukeArithmetic
