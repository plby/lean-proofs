import ErdosProblems.Erdos394.RootBoxFirstMoment

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A generic positive two-state divisor moment

This packages the floor-expansion used to sum rational pair-lattice boundary
terms.  At each prime the local weight is `A_p` on multiples and `B_p`
otherwise, with `B_p ≤ A_p`.
-/

open Nat Finset

namespace Erdos394

/-- Product of arbitrary local two-state weights. -/
def twoStateLocalWeight (P : Finset ℕ) (A B : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∏ p ∈ P, if p ∣ j then A p else B p

/-- Sum of the two-state weights over positive times. -/
def twoStateMoment (P : Finset ℕ) (A B : ℕ → ℕ) (Y : ℕ) : ℕ :=
  ∑ j ∈ Icc 1 Y, twoStateLocalWeight P A B j

/-- Positive subset-expansion coefficient. -/
def twoStateSubsetCoeff (P : Finset ℕ) (A B : ℕ → ℕ)
    (T : Finset ℕ) : ℕ :=
  (∏ p ∈ T, (A p - B p)) * ∏ p ∈ P \ T, B p

/-- Pointwise positive subset expansion. -/
theorem twoStateLocalWeight_subset_expansion (P : Finset ℕ)
    (A B : ℕ → ℕ) (j : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hBA : ∀ p ∈ P, B p ≤ A p) :
    twoStateLocalWeight P A B j =
      ∑ T ∈ P.powerset, twoStateSubsetCoeff P A B T *
        (if primeProduct T ∣ j then 1 else 0) := by
  classical
  unfold twoStateLocalWeight
  calc
    (∏ p ∈ P, if p ∣ j then A p else B p) =
        ∏ p ∈ P, ((if p ∣ j then A p - B p else 0) + B p) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpBA : B p ≤ A p := hBA p hp
      by_cases hpj : p ∣ j
      · simp only [hpj, if_true]
        omega
      · simp [hpj]
    _ = ∑ T ∈ P.powerset,
          (∏ p ∈ T, if p ∣ j then A p - B p else 0) *
            ∏ p ∈ P \ T, B p := by
      exact Finset.prod_add (fun p ↦ if p ∣ j then A p - B p else 0) B P
    _ = ∑ T ∈ P.powerset, twoStateSubsetCoeff P A B T *
          (if primeProduct T ∣ j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro T hTP
      have hTsub : T ⊆ P := Finset.mem_powerset.mp hTP
      unfold twoStateSubsetCoeff
      have hTprime : ∀ p ∈ T, p.Prime :=
        fun p hp ↦ hprime p (hTsub hp)
      by_cases hdiv : primeProduct T ∣ j
      · have hall : ∀ p ∈ T, p ∣ j :=
          (primeProduct_dvd_iff_all_dvd T hTprime j).mp hdiv
        have hprod :
            (∏ p ∈ T, if p ∣ j then A p - B p else 0) =
              ∏ p ∈ T, (A p - B p) := by
          apply Finset.prod_congr rfl
          intro p hp
          simp [hall p hp]
        rw [hprod]
        simp [hdiv]
      · have hnotall : ¬ ∀ p ∈ T, p ∣ j := by
          intro hall
          exact hdiv ((primeProduct_dvd_iff_all_dvd T hTprime j).mpr hall)
        push Not at hnotall
        obtain ⟨p, hpT, hpnd⟩ := hnotall
        have hzero :
            (∏ p ∈ T, if p ∣ j then A p - B p else 0) = 0 := by
          apply Finset.prod_eq_zero hpT
          simp [hpnd]
        rw [hzero]
        simp [hdiv]

/-- Exact divisor/floor expansion of the generic moment. -/
theorem twoStateMoment_subset_expansion (P : Finset ℕ)
    (A B : ℕ → ℕ) (Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hBA : ∀ p ∈ P, B p ≤ A p) :
    twoStateMoment P A B Y =
      ∑ T ∈ P.powerset, twoStateSubsetCoeff P A B T *
        (Y / primeProduct T) := by
  classical
  unfold twoStateMoment
  calc
    (∑ j ∈ Icc 1 Y, twoStateLocalWeight P A B j) =
        ∑ j ∈ Icc 1 Y, ∑ T ∈ P.powerset,
          twoStateSubsetCoeff P A B T *
            (if primeProduct T ∣ j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact twoStateLocalWeight_subset_expansion P A B j hprime hBA
    _ = ∑ T ∈ P.powerset, ∑ j ∈ Icc 1 Y,
          twoStateSubsetCoeff P A B T *
            (if primeProduct T ∣ j then 1 else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ T ∈ P.powerset, twoStateSubsetCoeff P A B T *
          (Y / primeProduct T) := by
      apply Finset.sum_congr rfl
      intro T hTP
      have hTsub : T ⊆ P := Finset.mem_powerset.mp hTP
      have hdpos : 0 < primeProduct T := by
        unfold primeProduct
        apply Finset.prod_pos
        intro p hp
        exact (hprime p (hTsub hp)).pos
      rw [← Finset.mul_sum]
      congr 1
      exact sum_Icc_dvd_indicator hdpos

/-- A cast coefficient divided by its prime product factors coordinatewise. -/
theorem cast_twoStateSubsetCoeff_div (P : Finset ℕ)
    (A B : ℕ → ℕ) (T : Finset ℕ) :
    (twoStateSubsetCoeff P A B T : ℝ) / (primeProduct T : ℝ) =
      (∏ p ∈ T, ((A p - B p : ℕ) : ℝ) / (p : ℝ)) *
        ∏ p ∈ P \ T, (B p : ℝ) := by
  unfold twoStateSubsetCoeff primeProduct
  push_cast
  rw [Finset.prod_div_distrib]
  ring

/-- Positive floors give an Euler-product upper bound with exact leading
coefficient one. -/
theorem twoStateMoment_le_euler (P : Finset ℕ)
    (A B : ℕ → ℕ) (Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hBA : ∀ p ∈ P, B p ≤ A p) :
    (twoStateMoment P A B Y : ℝ) ≤
      (Y : ℝ) * ∏ p ∈ P,
        ((B p : ℝ) + ((A p - B p : ℕ) : ℝ) / (p : ℝ)) := by
  classical
  rw [twoStateMoment_subset_expansion P A B Y hprime hBA]
  push_cast
  calc
    (∑ T ∈ P.powerset,
      (twoStateSubsetCoeff P A B T : ℝ) * (Y / primeProduct T : ℕ)) ≤
        ∑ T ∈ P.powerset,
          (twoStateSubsetCoeff P A B T : ℝ) *
            ((Y : ℝ) / (primeProduct T : ℝ)) := by
      apply Finset.sum_le_sum
      intro T hTP
      gcongr
      exact Nat.cast_div_le
    _ = (Y : ℝ) * ∑ T ∈ P.powerset,
          (twoStateSubsetCoeff P A B T : ℝ) /
            (primeProduct T : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hTP
      ring
    _ = (Y : ℝ) * ∑ T ∈ P.powerset,
          (∏ p ∈ T, ((A p - B p : ℕ) : ℝ) / (p : ℝ)) *
            ∏ p ∈ P \ T, (B p : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro T hTP
      exact cast_twoStateSubsetCoeff_div P A B T
    _ = (Y : ℝ) * ∏ p ∈ P,
          (((A p - B p : ℕ) : ℝ) / (p : ℝ) + (B p : ℝ)) := by
      rw [Finset.prod_add]
    _ = (Y : ℝ) * ∏ p ∈ P,
          ((B p : ℝ) + ((A p - B p : ℕ) : ℝ) / (p : ℝ)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      ring

end Erdos394
