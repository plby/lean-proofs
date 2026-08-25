import ErdosProblems.Erdos964.SemiprimeEndpointReduction
import ErdosProblems.Erdos964.LinearCharacterSievePrefix
import ErdosProblems.Erdos964.SmallConductorSemiprimes
import ErdosProblems.Erdos964.LargeConductorSemiprimes

/-!
# Assembling the finite distribution bound for a semiprime block

The centered primitive mass splits at a conductor threshold, with its
conductor-one term exactly zero. The explicit envelopes below are proved
bounds, not additional analytic assumptions.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem centeredSemiprimeMass_le_split (P Q : Finset ℕ) (K D T X : ℕ)
    (hD : 0 < D) (hDT : D ≤ T) (hX : X ∈ Finset.Icc 1 K) :
    (∑ d ∈ Finset.Ioc 0 T,
      (∑ ψ : primitiveCharacters d,
        ‖finiteCenteredCharacterSum (primeProductBlock P Q X) d ψ.1‖) / d.totient) ≤
      (∑ d ∈ Finset.Ioc 1 D,
        (∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1) / d.totient) +
      ∑ d ∈ Finset.Ioc D T,
        (∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1) / d.totient := by
  classical
  let U (d : ℕ) :=
    (∑ ψ : primitiveCharacters d,
      ‖finiteCenteredCharacterSum (primeProductBlock P Q X) d ψ.1‖) / d.totient
  let V (d : ℕ) :=
    (∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1) / d.totient
  have hone : U 1 = 0 := by
    simp only [U, finiteCenteredCharacterSum_level_one, norm_zero, Finset.sum_const_zero, zero_div]
  have hpoint (d : ℕ) (hd : 1 < d) : U d ≤ V d := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro ψ hψ
    rw [finiteCenteredCharacterSum_primitive_of_one_lt _ hd ψ, finiteCharacterSum]
    exact norm_primeProductBlock_le_maximum P Q K d X ψ.1 hX
  change (∑ d ∈ Finset.Ioc 0 T, U d) ≤
    (∑ d ∈ Finset.Ioc 1 D, V d) + ∑ d ∈ Finset.Ioc D T, V d
  rw [← Finset.sum_Ioc_consecutive U (by norm_num : 0 ≤ 1) (hD.trans_le hDT),
    show Finset.Ioc 0 1 = {1} by decide, Finset.sum_singleton, hone, zero_add,
    ← Finset.sum_Ioc_consecutive U hD hDT]
  apply add_le_add
  · exact Finset.sum_le_sum (fun d hd => hpoint d (Finset.mem_Ioc.mp hd).1)
  · apply Finset.sum_le_sum
    intro d hd
    exact hpoint d (by have := (Finset.mem_Ioc.mp hd).1; omega)

noncomputable def linearCharacterMeanEnvelope (S : Finset ℕ) (N T : ℕ) : ℝ :=
  (S.card : ℝ) + ((Nat.log 2 T + 1 : ℕ) : ℝ) *
    (3 * akbaryHambrookC3 * (Real.sqrt (N : ℝ) + 2 * T) * Real.sqrt S.card *
      Real.log (2 * (N : ℝ)))

theorem linearCharacterMeanEnvelope_nonneg (S : Finset ℕ) (N T : ℕ) (hN : 0 < N) :
    0 ≤ linearCharacterMeanEnvelope S N T := by
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold linearCharacterMeanEnvelope
  positivity

theorem finiteCharacterCutoffMean_le_envelope (S : Finset ℕ) (N T : ℕ)
    (hN : 0 < N) (hS : S ⊆ Finset.Ioc 0 N) :
    (∑ d ∈ Finset.Ioc 0 T,
      (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum S N d ψ.1) / d.totient) ≤
      linearCharacterMeanEnvelope S N T := by
  by_cases hT : 0 < T
  · simpa only [zero_add, linearCharacterMeanEnvelope] using
      finiteCharacterCutoffMaximum_mean_le T 0 N hT hN S (by simpa only [zero_add] using hS)
  · have hz : T = 0 := Nat.eq_zero_of_not_pos hT
    subst T
    simpa only [Finset.Ioc_self, Finset.sum_empty] using
      linearCharacterMeanEnvelope_nonneg S N 0 hN

noncomputable def semiprimeLargeConductorEnvelope (P Q : Finset ℕ)
    (m₀ M N D T : ℕ) : ℝ :=
  ((Nat.log 2 T + 1 : ℕ) : ℝ) * (akbaryHambrookC3 *
    ((2 / (D : ℝ)) * Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ) +
      2 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (N : ℝ) + 4 * T) *
    Real.sqrt P.card * Real.sqrt Q.card *
      Real.log (2 * (((m₀ + M) * N : ℕ) : ℝ)))

/-- A complete finite distribution estimate for one smaller-prime block
and one full larger-prime interval. All analytic constants are obtained
unconditionally. The larger primes exceed every modulus, so their
imprimitive correction is exactly zero. -/
theorem exists_semiprimeBlock_sum_discrepancy_bound :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
        ∀ L U m₀ M D T : ℕ,
          X₀ ≤ L → L ≤ U → 0 < M → 0 < D → D ≤ T → T < L →
          (D : ℝ) ≤ Real.rpow (Real.log (L : ℝ)) B →
          ∀ X : ℕ → ℕ, (∀ q, 0 < q → q ≤ T → X q ∈ Finset.Icc 1 ((m₀ + M) * U)) →
          ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
          P ⊆ Finset.Ioc m₀ (m₀ + M) →
          ∀ a : ℕ → ℕ, (∀ q, 0 < q → q ≤ T → (a q).Coprime q) →
          let Q := (Finset.Ioc L U).filter Nat.Prime
          (∑ q ∈ Finset.Ioc 0 T,
            |(finiteResidueCount (primeProductBlock P Q (X q)) q (a q) : ℝ) -
              ((primeProductBlock P Q (X q)).card : ℝ) / q.totient|) ≤
            (4 * (1 + Real.log (T : ℝ))) *
              (C * (D : ℝ) * (P.card : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A +
                semiprimeLargeConductorEnvelope P Q m₀ M U D T +
                ∑ p ∈ P, linearCharacterMeanEnvelope Q U (T / p) / p.totient) := by
  classical
  intro A B hA hB
  obtain ⟨C, hC, X₀, hX₀, hsmall⟩ :=
    exists_smallConductor_semiprimeBlockMass_le_logSaving A B hA hB
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro L U m₀ M D T hL hLU hM hD hDT hTL hDlog X hX P hP hPL hPinterval a ha
  let Q := (Finset.Ioc L U).filter Nat.Prime
  let W := 4 * (1 + Real.log (T : ℝ))
  have hW : 0 ≤ W := by dsimp only [W]; have := Real.log_natCast_nonneg T; positivity
  have hU : 0 < U := by have := hX₀.trans hL; omega
  have hT : 0 < T := hD.trans_le hDT
  have hQ : ∀ r ∈ Q, r.Prime := fun r hr => (Finset.mem_filter.mp hr).2
  have hQinterval : Q ⊆ Finset.Ioc 0 U := by
    intro r hr
    have hrLU := Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1
    exact Finset.mem_Ioc.mpr ⟨(Nat.zero_le L).trans_lt hrLU.1, hrLU.2⟩
  have hPzero : P ⊆ Finset.Ioc 0 (m₀ + M) := by
    intro p hp
    exact Finset.mem_Ioc.mpr ⟨(hP p hp).pos, (Finset.mem_Ioc.mp (hPinterval hp)).2⟩
  have hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r := by
    intro p hp r hr
    exact (hPL p hp).trans_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
  have hsize : ∀ p ∈ P, ∀ r ∈ Q, T < p * r := by
    intro p hp r hr
    have hrT := hTL.trans (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
    have hpr : r ≤ p * r := by simpa only [one_mul] using Nat.mul_le_mul_right r (hP p hp).one_le
    exact hrT.trans_le hpr
  have hlarge :
      (∑ d ∈ Finset.Ioc D T,
        (∑ ψ : primitiveCharacters d,
          primeProductBlockMaximum P Q ((m₀ + M) * U) d ψ.1) / d.totient) ≤
        semiprimeLargeConductorEnvelope P Q m₀ M U D T := by
    simpa only [zero_add, semiprimeLargeConductorEnvelope] using
      semiprimeBlock_largeConductor_mean_le D T m₀ M 0 U hD hT hM hU
        P Q hPinterval (by simpa only [zero_add] using hQinterval) hP hQ hsep
  have hcenter :
      (∑ d ∈ Finset.Ioc 1 T,
        (∑ ψ : primitiveCharacters d,
          primeProductBlockMaximum P Q ((m₀ + M) * U) d ψ.1) / d.totient) ≤
        C * (D : ℝ) * (P.card : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A +
          semiprimeLargeConductorEnvelope P Q m₀ M U D T := by
    rw [← Finset.sum_Ioc_consecutive
      (fun d => (∑ ψ : primitiveCharacters d,
        primeProductBlockMaximum P Q ((m₀ + M) * U) d ψ.1) / (d.totient : ℝ)) hD hDT]
    exact add_le_add (hsmall L U hL hLU P hP hPL ((m₀ + M) * U) D hDlog) hlarge
  have hPcorrection :
      (∑ p ∈ P, ((p.totient : ℝ)⁻¹ * W) *
        ∑ d ∈ Finset.Ioc 0 (T / p),
          (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum Q U d ψ.1) / d.totient) ≤
        W * ∑ p ∈ P, linearCharacterMeanEnvelope Q U (T / p) / p.totient := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    calc
      _ ≤ ((p.totient : ℝ)⁻¹ * W) * linearCharacterMeanEnvelope Q U (T / p) :=
        mul_le_mul_of_nonneg_left (finiteCharacterCutoffMean_le_envelope Q U (T / p) hU hQinterval)
          (mul_nonneg (by positivity) hW)
      _ = _ := by ring
  have hQcorrection :
      (∑ r ∈ Q, ((r.totient : ℝ)⁻¹ * W) *
        ∑ d ∈ Finset.Ioc 0 (T / r),
          (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum P (m₀ + M) d ψ.1) /
            d.totient) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    have hrT := hTL.trans (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
    have hz : T / r = 0 := Nat.div_eq_of_lt hrT
    simp only [hz, Finset.Ioc_self, Finset.sum_empty, mul_zero]
  calc
    _ ≤ W *
        (∑ d ∈ Finset.Ioc 1 T,
          (∑ ψ : primitiveCharacters d,
            primeProductBlockMaximum P Q ((m₀ + M) * U) d ψ.1) / d.totient) +
        (∑ p ∈ P, ((p.totient : ℝ)⁻¹ * W) *
          ∑ d ∈ Finset.Ioc 0 (T / p),
            (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum Q U d ψ.1) / d.totient) +
        (∑ r ∈ Q, ((r.totient : ℝ)⁻¹ * W) *
          ∑ d ∈ Finset.Ioc 0 (T / r),
            (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum P (m₀ + M) d ψ.1) /
              d.totient) :=
      semiprimeBlock_family_sum_discrepancy_le P Q (m₀ + M) U ((m₀ + M) * U) T X hX
        hP hQ hPzero hQinterval hsep hsize a ha
    _ ≤ W *
        (C * (D : ℝ) * (P.card : ℝ) * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A +
          semiprimeLargeConductorEnvelope P Q m₀ M U D T) +
        W * (∑ p ∈ P, linearCharacterMeanEnvelope Q U (T / p) / p.totient) + 0 :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hcenter hW) hPcorrection) hQcorrection.le
    _ = _ := by dsimp only [W]; ring

end Erdos964
