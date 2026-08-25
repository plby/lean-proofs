import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy

/-!
# Distribution errors after multiplying the moduli by a fixed integer

The squarefree divisor-pair modulus is used for the multiplicity estimate;
the actual prime progression has modulus `q` times that modulus.  Keeping
these separate retains the tau mean estimate even when `q` is not squarefree.
-/

namespace MaynardBFT

open BoundedGaps.Maynard
open scoped BigOperators ArithmeticFunction.omega

theorem sum_tauPow_mul_progressionDiscrepancy
    {theta A C : ℝ} {X₀ x d Q q : ℕ}
    (hw : PrimeLevelWitness theta A C X₀) (hx : X₀ ≤ x) (hq : 0 < q)
    (S : Finset ℕ) (hSQ : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ n ∈ S, Squarefree n)
    (hqx : ∀ n ∈ S, q * n ≤ x + 1)
    (hcut : ∀ n ∈ S, q * n ∈ Finset.Icc 1 (modulusCutoff theta x)) :
    (∑ n ∈ S, ((d ^ ω n : ℕ) : ℝ) * maxProgressionDiscrepancy x (q * n)) ≤
      Real.sqrt ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
        (1 + Real.log Q) ^ (2 * d ^ 2)) *
      Real.sqrt (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  classical
  let X : ℝ := 3 * ((x + 1 : ℕ) : ℝ)
  have hX : 0 ≤ X := by positivity
  have htriv (n : ℕ) (hn : n ∈ S) :
      maxProgressionDiscrepancy x (q * n) ≤ X / (n.totient : ℝ) := by
    have hnpos : 0 < n := (Finset.mem_Icc.mp (hSQ hn)).1
    have hqnpos : 0 < q * n := mul_pos hq hnpos
    have hphi : n.totient ≤ (q * n).totient :=
      Nat.le_of_dvd (Nat.totient_pos.mpr hqnpos)
        (Nat.totient_dvd_of_dvd (Nat.dvd_mul_left n q))
    exact (maxProgressionDiscrepancy_le_three_mul_div hqnpos (hqx n hn)).trans
      (div_le_div_of_nonneg_left hX
        (Nat.cast_pos.mpr (Nat.totient_pos.mpr hnpos)) (by exact_mod_cast hphi))
  have hweighted := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun n => ((d ^ ω n : ℕ) : ℝ))
    (fun n => maxProgressionDiscrepancy x (q * n))
    (fun n => (n.totient : ℝ)) X
    (fun n _ => maxProgressionDiscrepancy_nonneg x (q * n)) htriv
  have htau := sum_tauPow_sq_div_totient_le_one_add_log d Q S hSQ hsq
  have hlevel := hw.sum_maxProgressionDiscrepancy_subset hx (S.image (q * ·)) (by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    exact hcut m hm)
  have hsum : (∑ n ∈ S, maxProgressionDiscrepancy x (q * n)) =
      ∑ n ∈ S.image (q * ·), maxProgressionDiscrepancy x n := by
    symm
    apply Finset.sum_image
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hq hab
  rw [← hsum] at hlevel
  calc
    _ ≤ Real.sqrt (X * ∑ n ∈ S, (((d ^ ω n : ℕ) : ℝ) ^ 2) / n.totient) *
        Real.sqrt (∑ n ∈ S, maxProgressionDiscrepancy x (q * n)) := hweighted
    _ ≤ Real.sqrt (X * (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ n ∈ S, maxProgressionDiscrepancy x (q * n)) :=
      mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htau hX)) (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlevel) (Real.sqrt_nonneg _)

end MaynardBFT
