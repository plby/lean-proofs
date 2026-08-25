import ErdosProblems.Erdos1197.BMCover

/-!
# Unconditional Buczolich–Mauldin approximation data

The supporting modules adapt the proof by Tom de Groot, Enrique Barschkis,
ChatGPT, and Aristotle from
https://github.com/Tomodovodoo/Erdos_1197/tree/158f83062ced47e2665780f2811c825f8b9fae0b.
The two upstream admitted PNT inputs are replaced by the proved local
`chebyshev_asymptotic` and `theta_pos_implies_prime_in_interval`.
-/

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

lemma bm_approx_data_of_positive_flat_data
    (hData :
      ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
        ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
          ∃ q : ℕ, 0 < q ∧
            ∃ p : PrimeIdx k → ℕ,
              (∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
                    (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν) ∧
              ∃ m : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
                (∀ j,
                  |(q : ℝ) * bmFlatAlpha p j - (m j : ℝ) - bmFlatBeta k ν j| <
                    1 / (4 * (2 : ℝ) ^ k))) :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k)) := by
  obtain ⟨K₀, hK₀⟩ := hData
  refine ⟨K₀, fun k hk => ?_⟩
  obtain ⟨N_k, hN_k⟩ := hK₀ k hk
  refine ⟨max N_k 3, fun ν hν => ?_⟩
  obtain ⟨q, hq, p, hp_window, m, hm⟩ := hN_k ν ((le_max_left N_k 3).trans hν)
  refine ⟨q, hq, ?_, ?_⟩
  · exact bm_prime_cover_of_positive_q hq p
      (fun i => m (Fin.castAdd (2 ^ (ν - 2) + 1) i))
      hp_window
      (fun i => by simpa using bm_prime_coordinate_of_common_q hm i)
  · exact bm_integer_cover_of_positive_q hq ((le_max_right N_k 3).trans hν) hm

/-- **Kronecker–PNT approximation data** for the BM construction. -/
lemma bm_approx_data :
    ∃ K₀ : ℕ, ∀ k, K₀ ≤ k →
      ∃ N_k : ℕ, ∀ ν, N_k ≤ ν →
        ∃ q : ℕ, 0 < q ∧
          (∀ y ∈ I_inf, ∃ m : ℕ, 0 < m ∧
            (m : ℝ) * y ∈ Ioo ((8 : ℝ) / 9 * 2 ^ ν) ((2 : ℝ) ^ ν) ∧
            ∃ n : ℤ, |Real.logb 2 ((m : ℝ) * y) - (n : ℝ) / (q : ℝ)| <
              1 / ((q : ℝ) * 2 ^ k)) ∧
          (∀ n : ℕ, (n : ℝ) ∈ Ioo ((7 : ℝ) / 8 * 2 ^ ν) ((9 : ℝ) / 8 * 2 ^ ν) →
            ∃ m : ℤ, |Real.logb 2 (n : ℝ) - (m : ℝ) / (q : ℝ)| <
              1 / (4 * (q : ℝ) * 2 ^ k)) := by
  refine ⟨1, ?_⟩
  intro k hk
  obtain ⟨Np, hNp⟩ := bm_many_primes k
  refine ⟨max Np 3, ?_⟩
  intro ν hν
  have hνp : Np ≤ ν := (le_max_left Np 3).trans hν
  have hν3 : 3 ≤ ν := (le_max_right Np 3).trans hν
  obtain ⟨p, hpPairwise, hpPrime, hpWindow⟩ := hNp ν hνp
  have hIntrel :
      ∀ r : Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℤ,
        (∃ z : ℤ, ∑ j, bmFlatAlpha p j * (r j : ℝ) = z) →
        ∃ z : ℤ, ∑ j, bmFlatBeta k ν j * (r j : ℝ) = z :=
    bm_flat_intrel_of_prime_window hν3 p hpPairwise hpPrime hpWindow
  obtain ⟨qInt, hqInt, m, hPrimeCoords, hIntCoords⟩ :=
    bm_kronecker_coordinate_data hk p hIntrel
  let q : ℕ := Int.natAbs qInt
  have hq : 0 < q := Int.natAbs_pos.mpr hqInt
  refine ⟨q, hq, ?_, ?_⟩
  · rcases lt_or_gt_of_ne hqInt with hqNeg | hqPos
    · have hqabs : (q : ℝ) = -(qInt : ℝ) := by
        have hqabs_int : ((Int.natAbs qInt : ℕ) : ℤ) = -qInt := by
          rw [Int.natCast_natAbs, abs_of_neg hqNeg]
        have hqabs_real : (((Int.natAbs qInt : ℕ) : ℤ) : ℝ) = ((-qInt : ℤ) : ℝ) := by
          exact_mod_cast hqabs_int
        dsimp [q]
        simpa using hqabs_real
      let aNeg : PrimeIdx k → ℤ := fun i => -m (Fin.castAdd (2 ^ (ν - 2) + 1) i)
      have happroxNeg :
          ∀ i,
            |(q : ℝ) * Real.logb 2 (p i : ℝ) - (aNeg i : ℝ) + (i : ℝ) / (2 : ℝ) ^ k| <
              1 / (4 * (2 : ℝ) ^ k) := by
        intro i
        have hi := hPrimeCoords i
        have hi_neg :
            |-( (qInt : ℝ) * Real.logb 2 (p i : ℝ) -
                (m (Fin.castAdd (2 ^ (ν - 2) + 1) i) : ℝ) -
                (i : ℝ) / (2 : ℝ) ^ k)| <
              1 / (4 * (2 : ℝ) ^ k) := by
          convert hi using 1
          rw [abs_neg]
        rw [hqabs]
        convert hi_neg using 1
        · simp [aNeg]
          ring_nf
      exact bm_prime_cover_of_negative_q hq p aNeg hpWindow happroxNeg
    · have hqabs : (q : ℝ) = (qInt : ℝ) := by
        have hqabs_int : ((Int.natAbs qInt : ℕ) : ℤ) = qInt := by
          rw [Int.natCast_natAbs, abs_of_nonneg hqPos.le]
        have hqabs_real : (((Int.natAbs qInt : ℕ) : ℤ) : ℝ) = (qInt : ℝ) := by
          exact_mod_cast hqabs_int
        dsimp [q]
        simpa using hqabs_real
      let aPos : PrimeIdx k → ℤ := fun i => m (Fin.castAdd (2 ^ (ν - 2) + 1) i)
      have happroxPos :
          ∀ i,
            |(q : ℝ) * Real.logb 2 (p i : ℝ) - (aPos i : ℝ) - (i : ℝ) / (2 : ℝ) ^ k| <
              1 / (4 * (2 : ℝ) ^ k) := by
        intro i
        rw [hqabs]
        simpa [aPos] using hPrimeCoords i
      exact bm_prime_cover_of_positive_q hq p aPos hpWindow happroxPos
  · have hIntApprox :
        ∀ j : IntIdx ν,
          |(qInt : ℝ) * Real.logb 2 (bmIntVal ν j : ℝ) -
              (m (Fin.natAdd (2 ^ k) j) : ℝ)| <
            1 / (4 * (2 : ℝ) ^ k) := by
        intro j
        simpa using hIntCoords j
    have hIntWindow :=
      bm_integer_cover_of_coordinate_data hqInt hν3
        (fun j => m (Fin.natAdd (2 ^ k) j)) hIntApprox
    intro n hn
    obtain ⟨z, hz⟩ := hIntWindow n hn
    exact ⟨z, by simpa [q] using hz⟩

end

end Erdos1197

/-- info: 'Erdos1197.bm_approx_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1197.bm_approx_data
