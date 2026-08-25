import ErdosProblems.Erdos964.SmallConductorPrimes

/-!
# The small-conductor part of a semiprime block

Cancellation in the larger prime factor suffices at logarithmic conductors.
The estimates below retain uniformity over product endpoints and sum over
the primitive characters with the reciprocal-totient weight.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem exists_smallConductor_semiprimeBlockMaximum_le_logSaving :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
        ∀ L U : ℕ, X₀ ≤ L → L ≤ U →
          ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
          ∀ K q : ℕ, 0 < q → (q : ℝ) ≤ Real.rpow (Real.log (L : ℝ)) B →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            primeProductBlockMaximum P ((Finset.Ioc L U).filter Nat.Prime) K q χ ≤
              C * (P.card : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A := by
  intro A B hA hB
  obtain ⟨C, hC, X₀, hX₀, hsave⟩ :=
    exists_smallConductor_primeIntervalMaximum_le_logSaving A B hA hB
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro L U hL hLU P hP hPL K q hq hqlog χ hχ
  have hQ : ∀ r ∈ (Finset.Ioc L U).filter Nat.Prime, r.Prime :=
    fun r hr => (Finset.mem_filter.mp hr).2
  have hsep : ∀ p ∈ P, ∀ r ∈ (Finset.Ioc L U).filter Nat.Prime, p < r := by
    intro p hp r hr
    exact (hPL p hp).trans_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
  have hQinterval : (Finset.Ioc L U).filter Nat.Prime ⊆ Finset.Ioc 0 U := by
    intro r hr
    have hrLU := Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le L).trans_lt hrLU.1, hrLU.2⟩
  calc
    _ ≤ (P.card : ℝ) * finiteCharacterCutoffMaximum ((Finset.Ioc L U).filter Nat.Prime) U q χ :=
      primeProductBlockMaximum_le_card_mul_linearMaximum P _ K U q χ hP hQ hsep hQinterval
    _ ≤ (P.card : ℝ) * (C * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A) :=
      mul_le_mul_of_nonneg_left (hsave L U hL hLU q hq hqlog χ hχ) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The full small-conductor reciprocal-totient mass has arbitrary
logarithmic savings, apart from the displayed conductor count. -/
theorem exists_smallConductor_semiprimeBlockMass_le_logSaving :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
        ∀ L U : ℕ, X₀ ≤ L → L ≤ U →
          ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
          ∀ K D : ℕ, (D : ℝ) ≤ Real.rpow (Real.log (L : ℝ)) B →
            (∑ d ∈ Finset.Ioc 1 D,
              (∑ ψ : primitiveCharacters d,
                primeProductBlockMaximum P ((Finset.Ioc L U).filter Nat.Prime) K d ψ.1) /
                  d.totient) ≤
              C * (D : ℝ) * (P.card : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A := by
  classical
  intro A B hA hB
  obtain ⟨C, hC, X₀, hX₀, hsave⟩ :=
    exists_smallConductor_semiprimeBlockMaximum_le_logSaving A B hA hB
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro L U hL hLU P hP hPL K D hD
  let E := C * (P.card : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A
  have hL4 : 4 ≤ L := hX₀.trans hL
  have hlog : 0 ≤ Real.log (L : ℝ) := Real.log_natCast_nonneg L
  have hE : 0 ≤ E := div_nonneg
    (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (Real.rpow_nonneg hlog A)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 1 D, E := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hd1, hdD⟩ := Finset.mem_Ioc.mp hd
      have hdpos : 0 < d := by omega
      have hphi : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hdpos
      have hdlog : (d : ℝ) ≤ Real.rpow (Real.log (L : ℝ)) B :=
        (by exact_mod_cast hdD : (d : ℝ) ≤ D).trans hD
      calc
        _ ≤ ((Fintype.card (primitiveCharacters d) : ℝ) * E) / d.totient := by
          apply div_le_div_of_nonneg_right _ hphi.le
          calc
            _ ≤ ∑ ψ : primitiveCharacters d, E := by
              apply Finset.sum_le_sum
              intro ψ hψ
              exact hsave L U hL hLU P hP hPL K d hdpos hdlog ψ.1
                (primitiveCharacter_ne_one_of_one_lt hd1 ψ)
            _ = _ := by simp
        _ ≤ ((d.totient : ℝ) * E) / d.totient := by
          apply div_le_div_of_nonneg_right _ hphi.le
          apply mul_le_mul_of_nonneg_right _ hE
          exact_mod_cast card_primitiveCharacters_le_totient hdpos
        _ = E := by field_simp
    _ ≤ (D : ℝ) * E := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast Nat.sub_le D 1
    _ = _ := by dsimp only [E]; ring

end Erdos964
