import ErdosProblems.Erdos964.ScalarCandidateSecondMain
import ErdosProblems.Erdos964.ScalarAffineS2PowerScale

/-!
# The concrete candidate's second-sum approximation

Both density records, the polynomial coefficients, the prime support, and
all scale conditions are instantiated. The remaining main term is the explicit
fixed-modulus sum, not an assumed asymptotic formula.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_normalizedScalarCandidateS2_logSaving (A B : Fin 3 → ℕ)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 < B i)
    (hne : ∀ i j, i ≠ j → A i * B j ≠ A j * B i)
    (hadm : ∀ p, p.Prime → ∃ n : ℕ, ∀ i, ¬ p ∣ A i * n + B i)
    (j : Fin 3) (v K : ℕ)
    (hv : ∀ i, (A i * v + B i).Coprime (affineNormalizationModulus A B))
    (hK : 1 ≤ K)
    (hKsize : 2 * (A j * affineNormalizationModulus A B) + (A j * v + B j) ≤ K ^ 2)
    (a : ℕ) (β η θβ θp : ℝ) (hβ : 0 < β) (hη : 0 < η)
    (hβθβ : 2 * β ≤ θβ) (hθβ1 : θβ < 1) (hβθp : β < θp) (hθphalf : θp < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ t₀ : ℕ, 4 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      let M := affineNormalizationModulus A B
      let R := modulusCutoff β t
      let L := K * t
      let P := scalarSmallPrimeSupport η K t
      let x := A j * M * t ^ 2 + (A j * v + B j) - 1
      let z := A j * M * (2 * t ^ 2) + (A j * v + B j) - 1
      let s := normalizedScalarTripleSieve A B hA hne hadm v (t ^ 2) R
      |scalarAffineSecondSum (fun i => A i * M) (fun i => A i * v + B i) j
          (t ^ 2) s.prodPrimes (scalarSelbergCoefficient s (scalarLinearY R))
          (semiprimeScaleInterval P L x z) -
        1 / (A j * M).totient *
          scalarCandidateSecondMain M R P ((Finset.Ioc L (L ^ 2)).filter Nat.Prime) x z| ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  have hm : 0 < A j * affineNormalizationModulus A B :=
    Nat.mul_pos (hA j) (affineNormalizationModulus_pos A B hA hne)
  have hc : 0 < A j * v + B j := Nat.add_pos_right _ (hB j)
  have hprim := (normalized_affine_form_coprime A B v hv j).symm
  obtain ⟨C, hC, t₀, ht₀, hbound⟩ := exists_normalized_scalarAffineS2_powerScale_logSaving
    A B j v K hm hc hprim hK hKsize a β η θβ θp hβ hη hβθβ hθβ1 hβθp hθphalf
  refine ⟨C, hC, t₀, ht₀, ?_⟩
  intro t ht
  dsimp only
  let M := affineNormalizationModulus A B
  let R := modulusCutoff β t
  let P := scalarSmallPrimeSupport η K t
  let s := normalizedScalarTripleSieve A B hA hne hadm v (t ^ 2) R
  have hsP : s.prodPrimes = scalarSievePrimeProduct M R := rfl
  have hgood (p : ℕ) (hp : p.Prime) (hpP : p ∣ s.prodPrimes) : 3 < p :=
    scalarSievePrimeProduct_good A B hA hne hadm R p hp hpP
  let tS := scalarSecondDensitySieve s hgood
  have hM : s.prodPrimes.Coprime M := scalarSievePrimeProduct_coprime M R
  have hs (p : ℕ) (hp : p.Prime) (_ : p ∣ s.prodPrimes) : s.nu p = (3 : ℝ) / p :=
    scalarTripleSieve_density _ _ _ _ _ _ p hp
  have htS (p : ℕ) (hp : p.Prime) (_ : p ∣ s.prodPrimes) :
      tS.nu p = (2 : ℝ) / ((p : ℝ) - 1) := scalarSecondDensitySieve_density s hgood p hp
  have h := hbound t ht s tS rfl hM hs htS (scalarLinearY R)
    (abs_scalarLinearY_le R) (scalarLinearY_eq_zero_of_radius R)
  have hprime (p : ℕ) (hp : p ∈ P) : p.Prime :=
    (scalarSmallPrimeSupport_spec η K t p hp).1
  have hmain := scalarCandidateSecondMain_eq_kernel_sum M R P
    ((Finset.Ioc (K * t) ((K * t) ^ 2)).filter Nat.Prime)
    (A j * M * t ^ 2 + (A j * v + B j) - 1)
    (A j * M * (2 * t ^ 2) + (A j * v + B j) - 1) hprime s tS hsP rfl hs htS
  rw [← hmain] at h
  exact h

end Erdos964
