import Util.Linnik.ZeroRepulsion
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldCrossLevelCharacters

/-!
# Exceptional-zero repulsion across conductors

Lift two characters to their least common multiple.  Its size is at most
the product of the conductors, so the same absolute repulsion estimate
applies to an entire primitive family without a loss in its cardinality.
-/

namespace Linnik

open Complex BoundedGaps.Maynard

theorem log_lcm_height_le_twice
    {q₁ q Q : ℕ} [NeZero q₁] [NeZero q] (hq₁ : q₁ ≤ Q) (hq : q ≤ Q)
    {T : ℝ} (hT : 0 ≤ T) {rho : ℂ} (hrho : |rho.im| ≤ T) :
    Real.log ((Nat.lcm q₁ q : ℝ) * (|rho.im| + 2)) ≤
      2 * Real.log ((Q : ℝ) * (T + 2)) := by
  have hQ : (1 : ℝ) ≤ Q := by exact_mod_cast (NeZero.pos q).trans_le hq
  have hlcm : (Nat.lcm q₁ q : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast (Nat.lcm_le_mul (NeZero.pos q₁) (NeZero.pos q)).trans
      (show q₁ * q ≤ Q ^ 2 by simpa [pow_two] using Nat.mul_le_mul hq₁ hq)
  have hpos : 0 < (Nat.lcm q₁ q : ℝ) * (|rho.im| + 2) := by
    have : (0 : ℝ) < Nat.lcm q₁ q := by exact_mod_cast Nat.lcm_pos (NeZero.pos q₁) (NeZero.pos q)
    positivity
  calc
    Real.log ((Nat.lcm q₁ q : ℝ) * (|rho.im| + 2)) ≤
        Real.log (((Q : ℝ) * (T + 2)) ^ 2) := by
      apply Real.log_le_log hpos
      calc
        _ ≤ (Q : ℝ) ^ 2 * (T + 2) := mul_le_mul hlcm (by linarith) (by positivity) (by positivity)
        _ ≤ (Q : ℝ) ^ 2 * (T + 2) ^ 2 := by gcongr; nlinarith
        _ = _ := by ring
    _ = 2 * Real.log ((Q : ℝ) * (T + 2)) := by rw [Real.log_pow]; norm_num

/-- The quantitative repulsion bound for characters of different levels.
Distinctness is measured after their canonical lifts to a common level. -/
theorem exists_crossLevel_exceptional_zero_repulsion :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q₁ q Q : ℕ) [NeZero q₁] [NeZero q], 1 < q₁ → q₁ ≤ Q → q ≤ Q →
        ∀ (chi₁ : DirichletCharacter ℂ q₁) (chi : DirichletCharacter ℂ q),
          chi₁ ≠ 1 → chi₁ ^ 2 = 1 →
          ∀ beta : ℝ, 0 < beta → beta < 1 →
            DirichletCharacter.LFunction chi₁ (beta : ℂ) = 0 →
            ∀ (T : ℝ), 0 ≤ T → ∀ rho : ℂ, |rho.im| ≤ T →
              0 < rho.re → rho.re < 1 →
              DirichletCharacter.LFunction chi rho = 0 →
              (goldfeldCharactersDistinct chi₁ chi ∨ rho ≠ (beta : ℂ)) →
              Real.exp (-16384 * (A : ℝ) *
                Real.log ((Q : ℝ) * (T + 2)) * (1 - rho.re)) <
                262144 * (A : ℝ) * Real.log ((Q : ℝ) * (T + 2)) * (1 - beta) := by
  obtain ⟨A, hA, hrepulsion⟩ := exists_exceptional_zero_repulsion
  refine ⟨A, hA, ?_⟩
  intro q₁ q Q _ _ hq₁ hq₁Q hqQ chi₁ chi hchi₁ hsquare beta hbeta₀ hbeta₁ hzero₁
    T hT rho hheight hrho₀ hrho₁ hzero hne
  let d : ℕ := Nat.lcm q₁ q
  let : NeZero d := ⟨Nat.lcm_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  let psi₁ := chi₁.changeLevel (Nat.dvd_lcm_left q₁ q)
  let psi := chi.changeLevel (Nat.dvd_lcm_right q₁ q)
  have hd : 1 < d := hq₁.trans_le (Nat.le_of_dvd (NeZero.pos d) (Nat.dvd_lcm_left q₁ q))
  have hpsi₁ : psi₁ ≠ 1 :=
    (DirichletCharacter.changeLevel_eq_one_iff _).not.mpr hchi₁
  have hpsiSquare : psi₁ ^ 2 = 1 := by dsimp [psi₁]; rw [← map_pow, hsquare, map_one]
  have hzero₁' : DirichletCharacter.LFunction psi₁ (beta : ℂ) = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel _ chi₁ (.inl hchi₁), hzero₁, zero_mul]
  have hrho_ne : rho ≠ 1 := by intro h; subst rho; norm_num at hrho₁
  have hzero' : DirichletCharacter.LFunction psi rho = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel _ chi (.inr hrho_ne), hzero, zero_mul]
  have hne' : psi ≠ psi₁ ∨ rho ≠ (beta : ℂ) := by
    rcases hne with h | h
    · exact Or.inl (Ne.symm h)
    · exact Or.inr h
  have h := hrepulsion d hd psi₁ psi hpsi₁ hpsiSquare beta hbeta₀ hbeta₁ hzero₁'
    rho hrho₀ hrho₁ hzero' hne'
  have hlog := log_lcm_height_le_twice hq₁Q hqQ hT hheight
  have hA₀ : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hdelta : 0 ≤ 1 - rho.re := by linarith
  have hepsilon : 0 ≤ 1 - beta := by linarith
  have hproduct := mul_le_mul_of_nonneg_left hlog hA₀
  apply lt_of_le_of_lt (b := Real.exp (-8192 *
    ((A : ℝ) * Real.log ((d : ℝ) * (|rho.im| + 2))) * (1 - rho.re)))
  · apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hproduct hdelta
    dsimp [d]
    nlinarith
  · apply h.trans_le
    have := mul_le_mul_of_nonneg_right hproduct hepsilon
    dsimp [d]
    nlinarith

end Linnik
