import ErdosProblems.Erdos1148.FourFactorScale

/-! # A fixed real zero gives a positive lower bound for the four-factor residue term -/

namespace Erdos1148.DukeArithmetic

theorem exists_fixedZero_residue_scale {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {β : ℝ}
    (hβ : 15 / 16 ≤ β) (hβ1 : β < 1) (hzero : realDirichletValue χ β = 0) :
    ∃ M : ℕ, 0 < M ∧ ∀ (r : ℕ), 0 < r → ∀ (ψ : DirichletCharacter ℝ r),
      ψ ≠ 1 → productDirichletCharacter χ ψ ≠ 1 →
        (1 : ℝ) / 2 ≤ ((M : ℝ) * q * r) ^ (16 * (1 - β)) / (1 - β) *
          realDirichletValue χ 1 *
            (realDirichletValue ψ 1 * realDirichletValue (productDirichletCharacter χ ψ) 1) := by
  obtain ⟨K, hK, hApprox⟩ := exists_fourFactor_hyperbola_error_bound
  obtain ⟨M, hM, hsize⟩ := exists_fourFactor_scale hK (by linarith : 0 < 1 - β)
  refine ⟨M, hM, ?_⟩
  intro r hr ψ hψ hprod
  let : NeZero r := ⟨Nat.ne_zero_of_lt hr⟩
  let N := (M * q * r) ^ 8
  have hN : 0 < N := Nat.pow_pos (Nat.mul_pos (Nat.mul_pos hM (NeZero.pos q)) hr)
  have h := hApprox q r (q * r) (NeZero.pos q) hr (Nat.mul_pos (NeZero.pos q) hr)
    χ ψ (productDirichletCharacter χ ψ) hχ hψ hprod β (by linarith) hβ1 N hN
  have herr := h.trans (fourFactor_error_at_scaled_power hK hβ hβ1 hM (NeZero.pos q) hr hsize)
  rw [← realBiquadraticConvolution_grouped, hzero, mul_zero, zero_mul, zero_add,
    Real.norm_eq_abs] at herr
  have hle := (le_abs_self _).trans herr
  have hpos := one_le_weighted_realBiquadraticConvolution χ ψ β (Nat.mul_pos hN hN)
  have hmain : (1 : ℝ) / 2 ≤ ((N * N : ℕ) : ℝ) ^ (1 - β) / (1 - β) *
      realDirichletValue χ 1 *
        (realDirichletValue ψ 1 * realDirichletValue (productDirichletCharacter χ ψ) 1) := by
    linarith
  have hp : ((N * N : ℕ) : ℝ) ^ (1 - β) = ((M : ℝ) * q * r) ^ (16 * (1 - β)) := by
    dsimp [N]
    rw [show (M * q * r) ^ 8 * (M * q * r) ^ 8 = (M * q * r) ^ 16 by ring,
      Nat.cast_pow, Nat.cast_mul, Nat.cast_mul, ← Real.rpow_natCast_mul (by positivity)]
    norm_num only [Nat.cast_ofNat]
  rwa [hp] at hmain

end Erdos1148.DukeArithmetic
