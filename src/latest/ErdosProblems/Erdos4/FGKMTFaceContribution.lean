import ErdosProblems.Erdos4.FGKMTFaceLabels
import ErdosProblems.Erdos4.FGKMTIdealPairs

/-! Exact mixed divisor mass inside a positive ideal projection term. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k R : ℕ}

theorem faceLabel_profile (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (L b : ℝ)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (j : Fin k) (s : Fin 2) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T L a) :
    rationalProfileProduct b ell (faceLabel ell j s a) =
      logarithmicReciprocal b (a (Sum.inr s)) *
        ∏ i : SieveCore j, logarithmicReciprocal b (a (Sum.inl i)) := by
  unfold rationalProfileProduct
  simp_rw [faceLabel_coordinate ell hprime hinj L hcover j s a ha]
  exact prod_faceTuple (fun n => logarithmicReciprocal b n) j s a

theorem faceLabel_normalization_sq (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (L : ℝ) (hcop : ∀ p, (ell p).Coprime W)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (j : Fin k) (s : Fin 2) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T L a) :
    normalization ell (faceLabel ell j s a) ^ 2 =
      squarefreeHarmonicWeight W (a (Sum.inr s)) *
        ∏ i : SieveCore j, squarefreeHarmonicWeight W (a (Sum.inl i)) := by
  rw [normalization_sq_eq_harmonic_product ell hprime hinj hcop]
  simp_rw [faceLabel_coordinate ell hprime hinj L hcover j s a ha]
  exact prod_faceTuple (squarefreeHarmonicWeight W) j s a

theorem faceLabel_mixed_factor (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (L b : ℝ) (hcop : ∀ p, (ell p).Coprime W)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (j : Fin k) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T L a) :
    rationalProfileProduct b ell (faceLabel ell j 0 a) *
      rationalProfileProduct b ell (faceLabel ell j 1 a) *
      normalization ell (faceLabel ell j 0 a) ^ 2 *
      ((coordinateDivisor ell (faceLabel ell j 1 a) j).totient : ℝ)⁻¹ =
        mixedDivisorNumerator (SieveCore j) W b T a := by
  rw [faceLabel_profile ell hprime hinj L b hcover j 0 a ha,
    faceLabel_profile ell hprime hinj L b hcover j 1 a ha,
    faceLabel_normalization_sq ell hprime hinj L hcop hcover j 0 a ha,
    faceLabel_coordinate ell hprime hinj L hcover j 1 a ha j, faceTuple_anchor]
  have hphi : ((a (Sum.inr 1) : ℕ).totient : ℝ)⁻¹ = squarefreeHarmonicWeight W (a (Sum.inr 1)) := by
    rw [squarefreeHarmonicWeight, if_pos (ha.1 (Sum.inr 1)), one_div]
  rw [hphi]
  unfold mixedDivisorNumerator
  rw [Fin.prod_univ_two, if_pos (ha.2.1 0), if_pos (ha.2.1 1), Finset.prod_mul_distrib,
    Finset.prod_pow]
  ring

theorem faceLabel_contribution_lower {b : ℝ} (hb : 0 ≤ b) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R)
    (hcop : ∀ p, (ell p).Coprime W)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (j : Fin k) (a : (SieveCore j ⊕ Fin 2) → Fin (R + 1))
    (ha : MixedDivisorGood (SieveCore j) W T (Real.log (R : ℝ) / 2) a) :
    sieveWindowDensity ell * mixedDivisorNumerator (SieveCore j) W b T a ≤
      rationalIdealPair b R ell j (faceLabel ell j 0 a) (faceLabel ell j 1 a) := by
  have hh := rationalIdealPair_lower hb R ell hprime hinj j (faceLabel ell j 0 a) (faceLabel ell j 1 a)
    (faceLabel_compatible ell hprime hinj (Real.log (R : ℝ) / 2) hcover j a ha)
    (faceLabel_cutoff ell hprime hinj hR hT hTR hcover j 0 a ha)
    (faceLabel_cutoff ell hprime hinj hR hT hTR hcover j 1 a ha)
  rwa [faceLabel_mixed_factor ell hprime hinj (Real.log (R : ℝ) / 2) b hcop hcover j a ha] at hh

end Erdos4.FGKMT
