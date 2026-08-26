import ErdosProblems.Erdos941.SphereLocalProduct
import ErdosProblems.Erdos941.SquareContent
import ErdosProblems.Erdos941.DivisorBounds

/-! # A uniform bound for integral sphere-pair orbits -/

namespace Erdos941

theorem bad_sphere_local_card_le_factor (n e : ℤ) (base : SpherePair ℤ n e)
    (hn : n ≠ 0) (hnd : e ^ 2 ≠ n ^ 2) (p : BadSpherePrime n e) :
    (Nat.card (BadLocalSphereOrbit n e p) : ℝ) ≤
      (16 * (((spherePairDiscriminant n e).natAbs.factorization p : ℝ) + 1) ^ 2) *
        (p : ℝ) ^ (pairSquareContent (-n) (-(2 * e))).factorization p := by
  letI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase p.2)⟩
  have h := card_padicSpherePairOrbits_le p.1 (Finset.ne_of_mem_erase p.2)
    (mapSpherePair (Int.castRingHom (PadicInt p.1)) base) hn hnd
  rw [← pairSquareContent_factorization] at h
  have hR : (Nat.card (BadLocalSphereOrbit n e p) : ℝ) ≤
      16 * (((spherePairDiscriminant n e).natAbs.factorization p : ℝ) + 1) *
        (p : ℝ) ^ (pairSquareContent (-n) (-(2 * e))).factorization p := by exact_mod_cast h
  have hfac : ((spherePairDiscriminant n e).natAbs.factorization p : ℝ) + 1 ≤
      (((spherePairDiscriminant n e).natAbs.factorization p : ℝ) + 1) ^ 2 := by
    have hnonneg : 0 ≤ ((spherePairDiscriminant n e).natAbs.factorization p : ℝ) := by positivity
    nlinarith
  exact hR.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hfac (by norm_num)) (by positivity))

theorem exists_sphere_pair_orbit_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n e : ℤ) (_base : SpherePair ℤ n e),
      n ≠ 0 → e ^ 2 ≠ n ^ 2 →
      (Nat.card (SpherePairOrbits ℤ n e) : ℝ) ≤
        C * pairSquareContent (-n) (-(2 * e)) *
          ((spherePairDiscriminant n e).natAbs : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hprod⟩ := Analytic.exists_local_factor_product_le (c := 16) (by norm_num) hε
  refine ⟨C, hC, ?_⟩
  intro n e base hn hnd
  let D := (spherePairDiscriminant n e).natAbs
  let f := pairSquareContent (-n) (-(2 * e))
  let F : ℕ → ℝ := fun p => (16 * ((D.factorization p : ℝ) + 1) ^ 2) *
    (p : ℝ) ^ f.factorization p
  have hD : D ≠ 0 := Int.natAbs_ne_zero.mpr (spherePairDiscriminant_ne_zero hnd)
  have hf : f ∣ D := pairSquareContent_dvd_binary_discriminant (-n) (-(2 * e))
  have hcard : (Nat.card (SpherePairOrbits ℤ n e) : ℝ) ≤
      ∏ p : BadSpherePrime n e, (Nat.card (BadLocalSphereOrbit n e p) : ℝ) := by
    exact_mod_cast card_integer_spherePairOrbits_le_local_product base hnd
  have hlocal : (∏ p : BadSpherePrime n e, (Nat.card (BadLocalSphereOrbit n e p) : ℝ)) ≤
      ∏ p ∈ D.primeFactors, F p := by
    calc
      _ ≤ ∏ p : BadSpherePrime n e, F p := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro p _
        exact bad_sphere_local_card_le_factor n e base hn hnd p
      _ = ∏ p ∈ D.primeFactors.erase 2, F p := by
        exact Finset.prod_coe_sort _ F
      _ ≤ ∏ p ∈ D.primeFactors, F p := by
        apply Finset.prod_le_prod_of_subset_of_one_le (Finset.erase_subset _ _)
        · intro p _
          dsimp [F]
          positivity
        intro p hp _
        have hp1 : (1 : ℝ) ≤ p := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
        have hpow : 1 ≤ (p : ℝ) ^ f.factorization p := one_le_pow₀ hp1
        have hfac : 1 ≤ 16 * ((D.factorization p : ℝ) + 1) ^ 2 := by
          have hnonneg : 0 ≤ (D.factorization p : ℝ) := by positivity
          nlinarith
        exact one_le_mul_of_one_le_of_one_le hfac hpow
  exact hcard.trans (hlocal.trans (hprod D f hD hf))

theorem exists_sphere_pair_orbit_bound_all {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n e : ℤ, n ≠ 0 → e ^ 2 ≠ n ^ 2 →
      (Nat.card (SpherePairOrbits ℤ n e) : ℝ) ≤
        C * pairSquareContent (-n) (-(2 * e)) *
          ((spherePairDiscriminant n e).natAbs : ℝ) ^ ε := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_sphere_pair_orbit_bound hε
  refine ⟨C, hC, ?_⟩
  intro n e hn hnd
  by_cases hp : Nonempty (SpherePair ℤ n e)
  · exact hbound n e (Classical.choice hp) hn hnd
  · letI : IsEmpty (SpherePair ℤ n e) := not_nonempty_iff.mp hp
    haveI : IsEmpty (SpherePairOrbits ℤ n e) := inferInstance
    simp only [Nat.card_of_isEmpty, Nat.cast_zero]
    positivity

end Erdos941
