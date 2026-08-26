import ErdosProblems.Erdos1148.FixedZeroResidue
import ErdosProblems.Erdos1148.RealDirichletLogPower

/-! # An ineffective uniform lower bound from one fixed real zero -/

namespace Erdos1148.DukeArithmetic

theorem exists_fixedZero_lower_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {β ε : ℝ}
    (hβ : 15 / 16 ≤ β) (hβ1 : β < 1) (hzero : realDirichletValue χ β = 0)
    (hε : 0 < ε) (hβε : 32 * (1 - β) ≤ ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ), 0 < r → ∀ (ψ : DirichletCharacter ℝ r),
      ψ ≠ 1 → productDirichletCharacter χ ψ ≠ 1 →
        c * (r : ℝ) ^ (-ε) ≤ realDirichletValue ψ 1 := by
  obtain ⟨M, hM, hresidue⟩ := exists_fixedZero_residue_scale χ hχ hβ hβ1 hzero
  let a := ε / 2
  let e := 16 * (1 - β)
  let B := ((M : ℝ) * q) ^ e / (1 - β) * realDirichletValue χ 1 * ((q : ℝ) ^ a / a + 3)
  have ha : 0 < a := half_pos hε
  have hd : 0 < 1 - β := by linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hχpos := realDirichletValue_one_pos χ hχ
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨1 / (2 * B), by positivity, ?_⟩
  intro r hr ψ hψ hprod
  let : NeZero r := ⟨Nat.ne_zero_of_lt hr⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hψpos := realDirichletValue_one_pos ψ hψ
  have hmain := hresidue r hr ψ hψ hprod
  have hlog := productDirichletValue_one_le_rpow χ ψ hprod ha
  have he : e + a ≤ ε := by dsimp [e, a]; linarith
  have hupper : ((M : ℝ) * q * r) ^ e / (1 - β) * realDirichletValue χ 1 *
      (realDirichletValue ψ 1 * realDirichletValue (productDirichletCharacter χ ψ) 1) ≤
      B * (r : ℝ) ^ ε * realDirichletValue ψ 1 := by
    calc
      _ ≤ ((M : ℝ) * q * r) ^ e / (1 - β) * realDirichletValue χ 1 *
          (realDirichletValue ψ 1 * (((q : ℝ) ^ a / a + 3) * (r : ℝ) ^ a)) := by
        gcongr
      _ = B * (r : ℝ) ^ (e + a) * realDirichletValue ψ 1 := by
        dsimp only [B]
        rw [Real.mul_rpow (mul_nonneg hM0.le hq0.le) hr0.le, Real.rpow_add hr0]
        ring
      _ ≤ _ := by
        gcongr
  have hLB : (1 / 2 : ℝ) / (B * (r : ℝ) ^ ε) ≤ realDirichletValue ψ 1 := by
    apply (div_le_iff₀ (mul_pos hB (Real.rpow_pos_of_pos hr0 _))).mpr
    have h := hmain.trans hupper
    simpa only [mul_comm (realDirichletValue ψ 1), mul_assoc] using h
  convert hLB using 1
  rw [Real.rpow_neg hr0.le]
  ring

end Erdos1148.DukeArithmetic
