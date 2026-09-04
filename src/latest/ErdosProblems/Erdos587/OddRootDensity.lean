import ErdosProblems.Erdos587.RootSmallPeriod
import ErdosProblems.Erdos587.EulerDensity

/-!
# Uniform odd-modulus root density

The analytic and periodic cases are combined with a single fixed
polylogarithmic loss. The threshold does not depend on the affine parameters.
-/

open scoped BigOperators

namespace Erdos587

lemma exists_nat_affine_shift_of_coprime {q D R : ℕ} (hq : 0 < q) (hR : R.Coprime q) :
    ∃ M : ℕ, D ≡ R * M [MOD q] := by
  let : NeZero q := ⟨hq.ne'⟩
  let u := ZMod.unitOfCoprime R hR
  let z : ZMod q := (u⁻¹ : (ZMod q)ˣ) * (D : ZMod q)
  have hRcast : (R : ZMod q) = (u : ZMod q) := (ZMod.coe_unitOfCoprime R hR).symm
  have hz : (R : ZMod q) * z = D := by
    dsimp only [z]
    rw [hRcast, ← mul_assoc, ← Units.val_mul]
    simp
  refine ⟨z.val, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  exact hz.symm

lemma half_density_lower_of_inverse_bound {rho A H : ℝ}
    (hrho : 0 < rho) (hA : 0 < A) (hH : 0 ≤ H) (hbound : rho⁻¹ ≤ A) :
    H / (2 * A) ≤ H * rho / 2 := by
  have h1 : 1 ≤ A * rho := by
    apply (div_le_iff₀ hrho).mp
    simpa only [one_div] using hbound
  have hAinv : 1 / A ≤ rho := (div_le_iff₀ hA).mpr (by linarith)
  calc
    H / (2 * A) = (H / 2) * (1 / A) := by ring
    _ ≤ (H / 2) * rho := mul_le_mul_of_nonneg_left hAinv (by positivity)
    _ = H * rho / 2 := by ring

theorem exists_uniform_unitSquareExpansion_density :
    ∃ K : ℕ, 3 ≤ K ∧ ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p ≠ 2) →
      ∀ (D R H : ℕ), R.Coprime (primeSetModulus s) → 2 * K ≤ H →
        (primeSetModulus s : ℝ) ≤ (H : ℝ) ^ 2 →
        (H : ℝ) / (C * (1 + Real.log (primeSetModulus s)) ^ O) ≤
          ∑ i ∈ Finset.range H, unitSquareExpansionValue (primeSetModulus s) (D + R * i) := by
  obtain ⟨Q₀, hQ₀⟩ := exists_unitSquareAffineDensityThreshold
  obtain ⟨A, hA, O, hO, hEuler⟩ := exists_primeSetUnitDensity_inv_polylog_bound
  let K := max 3 Q₀
  let C : ℝ := 2 * (K + A + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨K, by dsimp [K]; omega, C, hC, O, hO, ?_⟩
  intro s hs hodd D R H hR hH hroot
  let Q := primeSetModulus s
  let F : ℝ := (1 + Real.log Q) ^ O
  have hQpos : 0 < Q := Finset.prod_pos (fun p hp => (hs p hp).pos)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQpos)
  have hF : 1 ≤ F := one_le_pow₀ (by linarith)
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  have hHpos : 0 < H := by dsimp [K] at hH; omega
  change (H : ℝ) / (C * F) ≤ _
  by_cases hlarge : K ≤ Q
  · have hQthree : 3 ≤ Q := (le_max_left 3 Q₀).trans hlarge
    have hQthreshold : Q₀ ≤ Q := (le_max_right 3 Q₀).trans hlarge
    obtain ⟨M, hDM⟩ := exists_nat_affine_shift_of_coprime (D := D) hQpos hR
    have hmain := hQ₀ s hs hodd hQthreshold D R M H hR hDM hHpos hroot
    have hbound : (primeSetUnitDensity s)⁻¹ ≤ A * F := by
      apply (hEuler s hs hQthree).trans
      apply mul_le_mul_of_nonneg_left _ hA.le
      exact pow_le_pow_left₀ hlogQ (by linarith) O
    have hdenom : 2 * (A * F) ≤ C * F := by
      have hconst : 2 * A ≤ C := by
        dsimp [C]
        have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hconst hFpos.le]
    calc
      _ ≤ (H : ℝ) / (2 * (A * F)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity) hdenom
      _ ≤ (H : ℝ) * primeSetUnitDensity s / 2 :=
        half_density_lower_of_inverse_bound (primeSetUnitDensity_pos s hs)
          (mul_pos hA hFpos) (Nat.cast_nonneg H) hbound
      _ ≤ _ := hmain
  · have hQK : Q ≤ K := by omega
    have htwo : 2 * Q ≤ H := (Nat.mul_le_mul_left 2 hQK).trans hH
    have hdenom : 2 * (Q : ℝ) ≤ C * F := by
      have hconst : 2 * (Q : ℝ) ≤ C := by
        have hQKR : (Q : ℝ) ≤ K := by exact_mod_cast hQK
        dsimp [C]
        linarith
      exact hconst.trans (le_mul_of_one_le_right hC.le hF)
    calc
      _ ≤ (H : ℝ) / (2 * Q) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg H) (by positivity) hdenom
      _ ≤ _ := unitSquareExpansion_affine_sum_lower_of_two_periods (D := D) hQpos hR htwo

theorem exists_uniform_odd_root_density :
    ∃ K : ℕ, 3 ≤ K ∧ ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q D R H : ℕ), 0 < q → (∀ p ∈ q.primeFactors, p ≠ 2) →
        R.Coprime (primeSetModulus q.primeFactors) → 2 * K ≤ H →
        (primeSetModulus q.primeFactors : ℝ) ≤ (H : ℝ) ^ 2 →
        (H : ℝ) / (C * (1 + Real.log (primeSetModulus q.primeFactors)) ^ O) ≤
          ∑ i ∈ Finset.range H, (squareRootCount q (D + R * i) : ℝ) := by
  obtain ⟨K, hK, C, hC, O, hO, hmean⟩ := exists_uniform_unitSquareExpansion_density
  refine ⟨K, hK, C, hC, O, hO, ?_⟩
  intro q D R H hq hodd hR hH hroot
  let : NeZero q := ⟨hq.ne'⟩
  apply (hmean q.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    hodd D R H hR hH hroot).trans
  exact Finset.sum_le_sum (fun i hi => unitSquareExpansionValue_le_squareRootCount_odd hodd _)

end Erdos587
