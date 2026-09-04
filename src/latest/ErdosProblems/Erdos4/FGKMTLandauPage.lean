import BoundedGaps.BombieriVinogradov.Analytic.NonprincipalExceptionalZero
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldCrossLevelCharacters
import Mathlib.Tactic

/-!
# A common exceptional character across bounded moduli

Lift two primitive characters to the least common multiple of their
moduli. The proved same-modulus near-one uniqueness theorem then gives
uniqueness across all moduli at most `Q`, with a logarithmic zero-free scale.
-/

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

structure PrimitiveCharacter where
  modulus : ℕ
  modulus_gt_one : 1 < modulus
  character : DirichletCharacter ℂ modulus
  primitive : character.IsPrimitive
  nonprincipal : character ≠ 1

instance (χ : PrimitiveCharacter) : NeZero χ.modulus :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt χ.modulus_gt_one)⟩

theorem PrimitiveCharacter.eq_of_lifts_eq (χ ψ : PrimitiveCharacter)
    (heq : χ.character.changeLevel (Nat.dvd_lcm_left χ.modulus ψ.modulus) =
      ψ.character.changeLevel (Nat.dvd_lcm_right χ.modulus ψ.modulus)) : χ = ψ := by
  by_cases hm : χ.modulus = ψ.modulus
  · cases χ with
    | mk q hq chi hprimitive hnonprincipal =>
      cases ψ with
      | mk q' hq' psi hprimitive' hnonprincipal' =>
        dsimp at hm
        subst q'
        let : NeZero q := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hq)⟩
        let : NeZero (Nat.lcm q q) := ⟨Nat.lcm_ne_zero (NeZero.ne q) (NeZero.ne q)⟩
        have hc : chi = psi := DirichletCharacter.changeLevel_injective
          (R := ℂ) (Nat.dvd_lcm_left q q) heq
        subst psi
        rfl
  · exact False.elim ((goldfeldCharactersDistinct_of_modulus_ne χ.character ψ.character
      χ.primitive ψ.primitive hm) heq)

noncomputable def exceptionalWidth (M Q : ℕ) : ℝ :=
  1 / ((M : ℝ) ^ 2 * Real.log (2 * (Q : ℝ) ^ 2))

def HasExceptionalRealZero (M Q : ℕ) (χ : PrimitiveCharacter) : Prop :=
  χ.modulus ≤ Q ∧ ∃ β : ℝ, 0 < β ∧ β < 1 ∧
    DirichletCharacter.LFunction χ.character (β : ℂ) = 0 ∧ 1 - exceptionalWidth M Q ≤ β

theorem exceptionalWidth_le_local {M Q q : ℕ} (hM : 2 ≤ M) (hq0 : 0 < q) (hqQ : q ≤ Q ^ 2) :
    exceptionalWidth M Q ≤ 1 / ((M : ℝ) ^ 2 * Real.log ((q : ℝ) * 2)) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hlog : 0 < Real.log ((q : ℝ) * 2) := Real.log_pos (by linarith)
  have hbound : (q : ℝ) * 2 ≤ 2 * (Q : ℝ) ^ 2 := by
    have hh : (q : ℝ) ≤ (Q : ℝ) ^ 2 := by exact_mod_cast hqQ
    linarith
  apply one_div_le_one_div_of_le (mul_pos (sq_pos_of_pos hMr) hlog)
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith) hbound) (sq_nonneg _)

theorem exceptionalCharacter_unique_of_local_uniqueness (M : ℕ) (hM : 2 ≤ M)
    (hunique : ∀ (q : ℕ) [NeZero q] (chi psi : DirichletCharacter ℂ q) (ρ σ : ℂ),
      IsNonprincipalNontrivialLFunctionZero chi ρ →
      IsNonprincipalNontrivialLFunctionZero psi σ →
      1 - 1 / ((M : ℝ) ^ 2 * Real.log ((q : ℝ) * (|ρ.im| + 2))) ≤ ρ.re →
      1 - 1 / ((M : ℝ) ^ 2 * Real.log ((q : ℝ) * (|σ.im| + 2))) ≤ σ.re →
      chi = psi ∧ ρ = σ) (Q : ℕ) :
    Set.Subsingleton {χ : PrimitiveCharacter | HasExceptionalRealZero M Q χ} := by
  intro χ hχ ψ hψ
  obtain ⟨hqχ, β, hβ0, hβ1, hβzero, hβnear⟩ := hχ
  obtain ⟨hqψ, γ, hγ0, hγ1, hγzero, hγnear⟩ := hψ
  let q := Nat.lcm χ.modulus ψ.modulus
  let : NeZero q := ⟨Nat.lcm_ne_zero (NeZero.ne χ.modulus) (NeZero.ne ψ.modulus)⟩
  let chi := χ.character.changeLevel (Nat.dvd_lcm_left χ.modulus ψ.modulus)
  let psi := ψ.character.changeLevel (Nat.dvd_lcm_right χ.modulus ψ.modulus)
  have hqn : 0 < q := NeZero.pos q
  have hqQ : q ≤ Q ^ 2 := by
    have hprod := Nat.le_of_dvd (Nat.mul_pos (NeZero.pos χ.modulus) (NeZero.pos ψ.modulus))
      (Nat.lcm_dvd_mul χ.modulus ψ.modulus)
    exact hprod.trans (by simpa only [pow_two] using Nat.mul_le_mul hqχ hqψ)
  have hlocal := exceptionalWidth_le_local hM hqn hqQ
  have hchi : chi ≠ 1 := fun heq => χ.nonprincipal
    ((DirichletCharacter.changeLevel_eq_one_iff _).mp heq)
  have hpsi : psi ≠ 1 := fun heq => ψ.nonprincipal
    ((DirichletCharacter.changeLevel_eq_one_iff _).mp heq)
  have hchiZero : DirichletCharacter.LFunction chi (β : ℂ) = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel _ _ (.inl χ.nonprincipal), hβzero, zero_mul]
  have hpsiZero : DirichletCharacter.LFunction psi (γ : ℂ) = 0 := by
    rw [DirichletCharacter.LFunction_changeLevel _ _ (.inl ψ.nonprincipal), hγzero, zero_mul]
  have hchiNontrivial : IsNonprincipalNontrivialLFunctionZero chi (β : ℂ) :=
    (isNonprincipalNontrivialLFunctionZero_iff chi _).mpr ⟨hchi, hchiZero, hβ0, hβ1⟩
  have hpsiNontrivial : IsNonprincipalNontrivialLFunctionZero psi (γ : ℂ) :=
    (isNonprincipalNontrivialLFunctionZero_iff psi _).mpr ⟨hpsi, hpsiZero, hγ0, hγ1⟩
  have hnearβ : 1 - 1 / ((M : ℝ) ^ 2 * Real.log ((q : ℝ) * (|(β : ℂ).im| + 2))) ≤
      (β : ℂ).re := by
    simp only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re]
    linarith
  have hnearγ : 1 - 1 / ((M : ℝ) ^ 2 * Real.log ((q : ℝ) * (|(γ : ℂ).im| + 2))) ≤
      (γ : ℂ).re := by
    simp only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re]
    linarith
  exact PrimitiveCharacter.eq_of_lifts_eq χ ψ
    (hunique q chi psi (β : ℂ) (γ : ℂ) hchiNontrivial hpsiNontrivial hnearβ hnearγ).1

/-- One absolute constant works simultaneously for every modulus bound. -/
theorem exists_landauPage_unique :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ Q : ℕ,
      Set.Subsingleton {χ : PrimitiveCharacter | HasExceptionalRealZero M Q χ} := by
  obtain ⟨M, hM, huniq⟩ := exists_nat_nonprincipalNontrivialLFunctionZero_character_eq_and_zero_eq
  exact ⟨M, hM, exceptionalCharacter_unique_of_local_uniqueness M hM huniq⟩

end Erdos4.FGKMT
