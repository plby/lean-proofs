import ErdosProblems.Erdos394.PrimeSubset

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Three-state Euler algebra for non-rational pair-lattice boundaries
-/

open Nat Finset

namespace Erdos394

/-- Sum over an ordered three-way partition of a finite set. -/
noncomputable def threeStateSubsetSum [DecidableEq α] (P : Finset α)
    (x y z : α → ℝ) : ℝ :=
  ∑ A ∈ P.powerset,
    (∏ p ∈ A, x p) *
      ∑ B ∈ (P \ A).powerset,
        (∏ p ∈ B, y p) * ∏ p ∈ (P \ A) \ B, z p

/-- Exact factorization of the three-state subset sum. -/
theorem threeStateSubsetSum_eq_prod [DecidableEq α]
    (P : Finset α) (x y z : α → ℝ) :
    threeStateSubsetSum P x y z =
      ∏ p ∈ P, (x p + y p + z p) := by
  unfold threeStateSubsetSum
  have hinner : ∀ A ∈ P.powerset,
      (∑ B ∈ (P \ A).powerset,
        (∏ p ∈ B, y p) * ∏ p ∈ (P \ A) \ B, z p) =
      ∏ p ∈ P \ A, (y p + z p) := by
    intro A hA
    exact (Finset.prod_add y z (P \ A)).symm
  calc
    (∑ A ∈ P.powerset,
      (∏ p ∈ A, x p) *
        ∑ B ∈ (P \ A).powerset,
          (∏ p ∈ B, y p) * ∏ p ∈ (P \ A) \ B, z p) =
        ∑ A ∈ P.powerset,
          (∏ p ∈ A, x p) * ∏ p ∈ P \ A, (y p + z p) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [hinner A hA]
    _ = ∏ p ∈ P, (x p + (y p + z p)) := by
      rw [Finset.prod_add]
    _ = ∏ p ∈ P, (x p + y p + z p) := by
      apply Finset.prod_congr rfl
      intro p hp
      ring

/-- Euler product produced by the both-zero, Möbius-forced-zero, and remaining
states in the non-rational boundary sum. -/
noncomputable def nonRationalBoundaryEuler (P : Finset ℕ) (c z : ℕ) : ℝ :=
  ∏ p ∈ P,
    (1 / (p : ℝ) + (c : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) +
      (c : ℝ) / ((z : ℝ) * (p - 1 : ℕ)))

/-- The three-state sum is exactly the non-rational boundary Euler product. -/
theorem threeState_nonRationalBoundary_eq (P : Finset ℕ) (c z : ℕ) :
    threeStateSubsetSum P
      (fun p ↦ 1 / (p : ℝ))
      (fun p ↦ (c : ℝ) / ((p : ℝ) * (p - 1 : ℕ)))
      (fun p ↦ (c : ℝ) / ((z : ℝ) * (p - 1 : ℕ))) =
    nonRationalBoundaryEuler P c z := by
  rw [threeStateSubsetSum_eq_prod]
  rfl

/-- If `1≤z≤p` at every prime, the non-rational boundary product is at most
`1/q` times the uniform correction `(1+4c/z)^|P|`. -/
theorem nonRationalBoundaryEuler_le (P : Finset ℕ) (c z : ℕ)
    (hz : 1 ≤ z) (hprime : ∀ p ∈ P, p.Prime)
    (hzp : ∀ p ∈ P, z ≤ p) :
    nonRationalBoundaryEuler P c z ≤
      (1 / (primeProduct P : ℝ)) *
        ∏ _p ∈ P, (1 + 4 * (c : ℝ) / (z : ℝ)) := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hz)
  unfold nonRationalBoundaryEuler
  calc
    (∏ p ∈ P,
      (1 / (p : ℝ) + (c : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) +
        (c : ℝ) / ((z : ℝ) * (p - 1 : ℕ)))) ≤
        ∏ p ∈ P, ((1 / (p : ℝ)) *
          (1 + 4 * (c : ℝ) / (z : ℝ))) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hp2 : 2 ≤ p := (hprime p hp).two_le
        have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
        have hp1R : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast (by omega : 0 < p - 1)
        have hzpR : (z : ℝ) ≤ p := by exact_mod_cast hzp p hp
        rw [Nat.cast_sub (hprime p hp).one_le]
        norm_num only [Nat.cast_one]
        have hpminuspos : (0 : ℝ) < (p : ℝ) - 1 := by
          have hpone : (1 : ℝ) < p := by exact_mod_cast (hprime p hp).one_lt
          linarith
        have hsum : (z : ℝ) + (p : ℝ) ≤ 4 * ((p : ℝ) - 1) := by
          have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
          nlinarith
        have hfrac :
            ((z : ℝ) + (p : ℝ)) /
                ((z : ℝ) * ((p : ℝ) - 1)) ≤ 4 / (z : ℝ) := by
          apply (div_le_iff₀ (mul_pos hzR hpminuspos)).mpr
          calc
            (z : ℝ) + (p : ℝ) ≤ 4 * ((p : ℝ) - 1) := hsum
            _ = (4 / (z : ℝ)) * ((z : ℝ) * ((p : ℝ) - 1)) := by
              field_simp
        have hcR : (0 : ℝ) ≤ c := by positivity
        calc
          1 / (p : ℝ) + (c : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) +
              (c : ℝ) / ((z : ℝ) * ((p : ℝ) - 1)) =
            (1 / (p : ℝ)) *
              (1 + (c : ℝ) * (((z : ℝ) + (p : ℝ)) /
                ((z : ℝ) * ((p : ℝ) - 1)))) := by
                  field_simp
                  ring
          _ ≤ (1 / (p : ℝ)) * (1 + (c : ℝ) * (4 / (z : ℝ))) := by
            gcongr
          _ = (1 / (p : ℝ)) * (1 + 4 * (c : ℝ) / (z : ℝ)) := by ring
    _ = (1 / (primeProduct P : ℝ)) *
        ∏ _p ∈ P, (1 + 4 * (c : ℝ) / (z : ℝ)) := by
      rw [Finset.prod_mul_distrib]
      unfold primeProduct
      push_cast
      rw [Finset.prod_div_distrib]
      simp

end Erdos394
