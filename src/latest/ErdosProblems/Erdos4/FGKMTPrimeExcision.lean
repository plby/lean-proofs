import ErdosProblems.Erdos4.FGKMTLandauPage
import Mathlib.Data.Nat.Prime.Basic

/-! Removing one prime eliminates the common exceptional real character. -/

namespace Erdos4.FGKMT

theorem exists_prime_excision_of_unique {M Q : ℕ} (hQ : 2 ≤ Q)
    (hunique : Set.Subsingleton {χ : PrimitiveCharacter | HasExceptionalRealZero M Q χ}) :
    ∃ B : ℕ, B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
      ∀ χ : PrimitiveCharacter, χ.modulus.Coprime B → ¬HasExceptionalRealZero M Q χ := by
  classical
  by_cases hex : ∃ χ : PrimitiveCharacter, HasExceptionalRealZero M Q χ
  · obtain ⟨χ, hχ⟩ := hex
    have hBprime : χ.modulus.minFac.Prime := Nat.minFac_prime (ne_of_gt χ.modulus_gt_one)
    have hBdvd := Nat.minFac_dvd χ.modulus
    have hBmod : χ.modulus.minFac ≤ χ.modulus :=
      Nat.le_of_dvd (NeZero.pos χ.modulus) hBdvd
    refine ⟨χ.modulus.minFac, hBmod.trans hχ.1, Or.inr hBprime, ?_⟩
    intro ψ hcop hψ
    have heq : χ = ψ := hunique hχ hψ
    subst ψ
    exact Nat.not_coprime_of_dvd_of_dvd hBprime.one_lt hBdvd (dvd_refl _) hcop
  · refine ⟨1, by omega, Or.inl rfl, ?_⟩
    intro χ _hcop hχ
    exact hex ⟨χ, hχ⟩

theorem exists_uniform_prime_excision :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ Q : ℕ, 2 ≤ Q →
      ∃ B : ℕ, B ≤ Q ∧ (B = 1 ∨ B.Prime) ∧
        ∀ χ : PrimitiveCharacter, χ.modulus.Coprime B → ¬HasExceptionalRealZero M Q χ := by
  obtain ⟨M, hM, huniq⟩ := exists_landauPage_unique
  exact ⟨M, hM, fun Q hQ => exists_prime_excision_of_unique hQ (huniq Q)⟩

theorem real_zero_gap_of_prime_excision {M Q B : ℕ}
    (hexc : ∀ χ : PrimitiveCharacter, χ.modulus.Coprime B → ¬HasExceptionalRealZero M Q χ)
    (χ : PrimitiveCharacter) (hq : χ.modulus ≤ Q) (hcop : χ.modulus.Coprime B)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ.character (β : ℂ) = 0) :
    β < 1 - exceptionalWidth M Q := by
  by_contra hnear
  exact hexc χ hcop ⟨hq, β, hβ0, hβ1, hzero, le_of_not_gt hnear⟩

end Erdos4.FGKMT
