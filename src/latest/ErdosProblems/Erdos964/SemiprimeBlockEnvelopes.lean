import ErdosProblems.Erdos964.SemiprimeBlockDistribution

/-!
# Scalar bounds for the dyadic semiprime errors

For the smaller primes in `(M,2M]`, `φ(p) ≥ M` and there are at most `M`
terms. These facts turn the remaining imprimitive correction into a scalar
bound with no sum over prime factors.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

noncomputable def dyadicSemiprimeCorrectionEnvelope (M U T : ℕ) : ℝ :=
  (U : ℝ) + ((Nat.log 2 T + 1 : ℕ) : ℝ) *
    (3 * akbaryHambrookC3 * (Real.sqrt (U : ℝ) + 2 * ((T : ℝ) / M)) *
      Real.sqrt (U : ℝ) * Real.log (2 * (U : ℝ)))

theorem dyadicSemiprimeCorrectionEnvelope_nonneg (M U T : ℕ) (hU : 0 < U) :
    0 ≤ dyadicSemiprimeCorrectionEnvelope M U T := by
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 0 ≤ Real.log (2 * (U : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith
  unfold dyadicSemiprimeCorrectionEnvelope
  positivity

theorem dyadicSemiprimeCorrection_le_envelope (P Q : Finset ℕ) (M U T : ℕ)
    (hM : 0 < M) (hU : 0 < U)
    (hP : ∀ p ∈ P, p.Prime)
    (hPinterval : P ⊆ Finset.Ioc M (M + M)) (hQinterval : Q ⊆ Finset.Ioc 0 U) :
    (∑ p ∈ P, linearCharacterMeanEnvelope Q U (T / p) / p.totient) ≤
      dyadicSemiprimeCorrectionEnvelope M U T := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hPcard : P.card ≤ M := by
    calc
      _ ≤ (Finset.Ioc M (M + M)).card := Finset.card_le_card hPinterval
      _ = M := by simp
  have hQcard : Q.card ≤ U := by
    calc
      _ ≤ (Finset.Ioc 0 U).card := Finset.card_le_card hQinterval
      _ = U := by simp
  have hQcardReal : (Q.card : ℝ) ≤ U := by exact_mod_cast hQcard
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 0 ≤ Real.log (2 * (U : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith
  have hE := dyadicSemiprimeCorrectionEnvelope_nonneg M U T hU
  have hpoint (p : ℕ) (hp : p ∈ P) :
      linearCharacterMeanEnvelope Q U (T / p) ≤ dyadicSemiprimeCorrectionEnvelope M U T := by
    have hMp : M ≤ p := (Finset.mem_Ioc.mp (hPinterval hp)).1.le
    have hdiv : ((T / p : ℕ) : ℝ) ≤ (T : ℝ) / M := by
      apply (le_div_iff₀ hMreal).mpr
      have hnat : (T / p) * M ≤ T :=
        (Nat.mul_le_mul_left (T / p) hMp).trans (Nat.div_mul_le_self T p)
      exact_mod_cast hnat
    have hcount : ((Nat.log 2 (T / p) + 1 : ℕ) : ℝ) ≤ ((Nat.log 2 T + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self T p)) 1
    unfold linearCharacterMeanEnvelope dyadicSemiprimeCorrectionEnvelope
    gcongr
  calc
    _ ≤ ∑ p ∈ P, dyadicSemiprimeCorrectionEnvelope M U T / M := by
      apply Finset.sum_le_sum
      intro p hp
      have hphi : M ≤ p.totient := by
        rw [Nat.totient_prime (hP p hp)]
        have := (Finset.mem_Ioc.mp (hPinterval hp)).1
        omega
      have hphiReal : (M : ℝ) ≤ p.totient := by exact_mod_cast hphi
      calc
        _ ≤ dyadicSemiprimeCorrectionEnvelope M U T / p.totient :=
          div_le_div_of_nonneg_right (hpoint p hp) (Nat.cast_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left hE hMreal hphiReal
    _ = (P.card : ℝ) * (dyadicSemiprimeCorrectionEnvelope M U T / M) := by simp
    _ ≤ (M : ℝ) * (dyadicSemiprimeCorrectionEnvelope M U T / M) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hPcard) (div_nonneg hE hMreal.le)
    _ = _ := by field_simp

noncomputable def dyadicSemiprimeLargeEnvelope (M U D T : ℕ) : ℝ :=
  ((Nat.log 2 T + 1 : ℕ) : ℝ) * akbaryHambrookC3 *
    ((2 / (D : ℝ)) * (M : ℝ) * U +
      2 * (M : ℝ) * Real.sqrt (U : ℝ) + 2 * (U : ℝ) * Real.sqrt (M : ℝ) +
      4 * T * Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ)) *
    Real.log (2 * (((M + M) * U : ℕ) : ℝ))

theorem dyadicSemiprimeLarge_le_envelope (P Q : Finset ℕ) (M U D T : ℕ)
    (hM : 0 < M) (hU : 0 < U)
    (hPinterval : P ⊆ Finset.Ioc M (M + M)) (hQinterval : Q ⊆ Finset.Ioc 0 U) :
    semiprimeLargeConductorEnvelope P Q M M U D T ≤ dyadicSemiprimeLargeEnvelope M U D T := by
  have hPcard : (P.card : ℝ) ≤ M := by
    exact_mod_cast (Finset.card_le_card hPinterval).trans_eq (by simp)
  have hQcard : (Q.card : ℝ) ≤ U := by
    exact_mod_cast (Finset.card_le_card hQinterval).trans_eq (by simp)
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 0 ≤ Real.log (2 * (((M + M) * U : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hK : (1 : ℝ) ≤ (((M + M) * U : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega : 0 < M + M) hU
    linarith
  have halgebra :
      ((2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ) +
        2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (U : ℝ) + 4 * T) *
          Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ) =
      (2 / (D : ℝ)) * (M : ℝ) * U +
        2 * (M : ℝ) * Real.sqrt (U : ℝ) + 2 * (U : ℝ) * Real.sqrt (M : ℝ) +
        4 * T * Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ) := by
    ring_nf
    simp only [Real.sq_sqrt (Nat.cast_nonneg M), Real.sq_sqrt (Nat.cast_nonneg U)]
    ring
  unfold semiprimeLargeConductorEnvelope dyadicSemiprimeLargeEnvelope
  calc
    _ ≤ ((Nat.log 2 T + 1 : ℕ) : ℝ) * (akbaryHambrookC3 *
        ((2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ) +
          2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (U : ℝ) + 4 * T) *
        Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ) *
          Real.log (2 * (((M + M) * U : ℕ) : ℝ))) := by gcongr
    _ = _ := by
      calc
        _ = ((Nat.log 2 T + 1 : ℕ) : ℝ) * akbaryHambrookC3 *
            (((2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ) +
              2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (U : ℝ) + 4 * T) *
              Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ)) *
                Real.log (2 * (((M + M) * U : ℕ) : ℝ)) := by ring
        _ = _ := by rw [halgebra]

/-- The complete block-distribution estimate with all prime-support sums
replaced by explicit scalar errors. -/
theorem exists_dyadicSemiprimeBlock_sum_discrepancy_bound :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
        ∀ L U M D T : ℕ,
          X₀ ≤ L → L ≤ U → 0 < M → 0 < D → D ≤ T → T < L →
          (D : ℝ) ≤ Real.rpow (Real.log (L : ℝ)) B →
          ∀ X : ℕ → ℕ, (∀ q, 0 < q → q ≤ T → X q ∈ Finset.Icc 1 ((M + M) * U)) →
          ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
          P ⊆ Finset.Ioc M (M + M) →
          ∀ a : ℕ → ℕ, (∀ q, 0 < q → q ≤ T → (a q).Coprime q) →
          let Q := (Finset.Ioc L U).filter Nat.Prime
          (∑ q ∈ Finset.Ioc 0 T,
            |(finiteResidueCount (primeProductBlock P Q (X q)) q (a q) : ℝ) -
              ((primeProductBlock P Q (X q)).card : ℝ) / q.totient|) ≤
            (4 * (1 + Real.log (T : ℝ))) *
              (C * (D : ℝ) * (M : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A +
                dyadicSemiprimeLargeEnvelope M U D T +
                dyadicSemiprimeCorrectionEnvelope M U T) := by
  intro A B hA hB
  obtain ⟨C, hC, X₀, hX₀, hblock⟩ := exists_semiprimeBlock_sum_discrepancy_bound A B hA hB
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro L U M D T hL hLU hM hD hDT hTL hDlog X hX P hP hPL hPinterval a ha
  let Q := (Finset.Ioc L U).filter Nat.Prime
  have hU : 0 < U := by have := hX₀.trans hL; omega
  have hQinterval : Q ⊆ Finset.Ioc 0 U := by
    intro r hr
    have hrLU := Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le L).trans_lt hrLU.1, hrLU.2⟩
  have hPcard : (P.card : ℝ) ≤ M := by
    exact_mod_cast (Finset.card_le_card hPinterval).trans_eq (by simp)
  have hsmall :
      C * (D : ℝ) * (P.card : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A ≤
        C * (D : ℝ) * (M : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A := by
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Real.log_natCast_nonneg L) A)
    gcongr
  apply (hblock L U M M D T hL hLU hM hD hDT hTL hDlog X hX P hP hPL hPinterval a ha).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add
      (add_le_add hsmall (dyadicSemiprimeLarge_le_envelope P Q M U D T hM hU hPinterval hQinterval))
      (dyadicSemiprimeCorrection_le_envelope P Q M U T hM hU hP hPinterval hQinterval)
  · have := Real.log_natCast_nonneg T
    positivity

end Erdos964
