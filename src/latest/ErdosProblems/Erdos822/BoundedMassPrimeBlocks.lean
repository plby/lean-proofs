/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.BoundedMassProgressionSieve

/-! # Reciprocal progression estimates on arbitrary multiplicative blocks -/

namespace Erdos822

open scoped BigOperators Classical

theorem primeSet_subset_residue_blocks {P : Finset ℕ} {N L d a y : ℕ}
    (hL : 0 < L)
    (hP : ∀ q ∈ P, L < q ∧ q ≤ N * L ∧ q.Prime ∧ y < q ∧ q % d = a % d) :
    P ⊆ (Finset.Icc 1 N).biUnion (fun j ↦ primeResidueInterval d a (j * L) ((j + 1) * L) y) := by
  intro q hq
  have hdata := hP q hq
  let j := (q - 1) / L
  have hjpos : 0 < j := Nat.div_pos (by omega) hL
  have hjle : j ≤ N := by
    apply (Nat.div_le_iff_le_mul hL).mpr
    omega
  have hleft : j * L < q := by
    have hmul := Nat.div_mul_le_self (q - 1) L
    dsimp [j]
    omega
  have hright : q ≤ (j + 1) * L := by
    have hlt : (q - 1) / L < (q - 1) / L + 1 := by omega
    have hmul := (Nat.div_lt_iff_lt_mul hL).mp hlt
    dsimp [j]
    omega
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Icc.mpr ⟨hjpos, hjle⟩,
    mem_primeResidueInterval_iff.mpr ⟨hleft, hright, hdata.2.2⟩⟩

theorem sum_inv_primeSet_le_of_interval_sieve
    {P : Finset ℕ} {N L d a y S : ℕ} {D : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hdL : d ≤ L) (hy : 2 ≤ y) (hD : 0 ≤ D)
    (hP : ∀ q ∈ P, L < q ∧ q ≤ N * L ∧ q.Prime ∧ y < q ∧ q % d = a % d)
    (hcount : ∀ A B : ℕ, ((primeResidueInterval d a A B y).card : ℝ) ≤
      (((B - A) / d + 1 : ℕ) : ℝ) * (D / Real.log (y : ℝ)) + ((y ^ S : ℕ) : ℝ) ^ 2) :
    (∑ q ∈ P, (1 : ℝ) / q) ≤
      (2 * (D / Real.log (y : ℝ)) / d + ((y ^ S : ℕ) : ℝ) ^ 2 / L) * (harmonic N : ℝ) := by
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  calc
    _ ≤ ∑ q ∈ (Finset.Icc 1 N).biUnion
        (fun j ↦ primeResidueInterval d a (j * L) ((j + 1) * L) y), (1 : ℝ) / q :=
      Finset.sum_le_sum_of_subset_of_nonneg (primeSet_subset_residue_blocks hL hP)
        (fun q hq hnot ↦ by positivity)
    _ ≤ ∑ j ∈ Finset.Icc 1 N, ∑ q ∈ primeResidueInterval d a (j * L) ((j + 1) * L) y,
        (1 : ℝ) / q := by
      apply sum_biUnion_le_sum
      intro j hj q hq
      positivity
    _ ≤ ∑ j ∈ Finset.Icc 1 N,
        ((((L / d + 1 : ℕ) : ℝ) * (D / Real.log (y : ℝ)) + ((y ^ S : ℕ) : ℝ) ^ 2) /
          (j * L + 1 : ℕ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hwidth : (j + 1) * L - j * L = L := by
        rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]
      have hcard := hcount (j * L) ((j + 1) * L)
      rw [hwidth] at hcard
      refine (sum_inv_primeResidueInterval_le_card_div d a (j * L) ((j + 1) * L) y).trans ?_
      simpa only [Nat.cast_add, Nat.cast_one] using
        div_le_div_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ (j * L + 1 : ℕ))
    _ ≤ _ := sum_blockKernel_le_harmonic hL hd hdL (div_nonneg hD hlogy.le) (by positivity)

theorem exists_fixed_depth_boundedMass_primeSet_bound :
    ∃ S : ℕ, 101 ≤ S ∧ ∀ C : ℝ, ∃ D : ℝ, 0 < D ∧
      ∀ (P : Finset ℕ) (N L d a y : ℕ), 0 < L → 0 < d → d ≤ L →
        primeDivisorReciprocalMass d ≤ C → 2 ≤ y →
        (∀ q ∈ P, L < q ∧ q ≤ N * L ∧ q.Prime ∧ y < q ∧ q % d = a % d) →
        (∑ q ∈ P, (1 : ℝ) / q) ≤
          (2 * (D / Real.log (y : ℝ)) / d + ((y ^ S : ℕ) : ℝ) ^ 2 / L) * (harmonic N : ℝ) := by
  obtain ⟨S, hS, hbound⟩ := exists_fixed_depth_boundedMass_primeResidueInterval_bound
  refine ⟨S, hS, ?_⟩
  intro C
  obtain ⟨D, hD, hcount⟩ := hbound C
  refine ⟨D, hD, ?_⟩
  intro P N L d a y hL hd hdL hmass hy hP
  exact sum_inv_primeSet_le_of_interval_sieve hL hd hdL hy hD.le hP
    (fun A B ↦ hcount d a A B y hd hmass hy)

#print axioms exists_fixed_depth_boundedMass_primeSet_bound

end Erdos822
