import ErdosProblems.Erdos964.ScalarPrimeSupport
import ErdosProblems.Erdos964.ScalarSieveCandidate

/-!
# The fixed-modulus inner sum in the transformed coefficient

After removing an outer squarefree divisor `r`, the inner summation is
over squarefree integers coprime to `M*r`, with the exact strict cutoff.
-/

namespace Erdos964

open scoped BigOperators

theorem squarefree_dvd_quotient_iff (P r m : ℕ) (hP : Squarefree P) (hr : r ∣ P) :
    m ∣ P / r ↔ m ∣ P ∧ m.Coprime r := by
  have hmul : r * (P / r) = P := Nat.mul_div_cancel' hr
  have hcop : r.Coprime (P / r) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  constructor
  · intro hm
    exact ⟨hm.trans (Nat.div_dvd_of_dvd hr), (hcop.coprime_dvd_right hm).symm⟩
  · rintro ⟨hm, hmr⟩
    exact (Nat.dvd_div_iff_mul_dvd hr).mpr (hmr.symm.mul_dvd_of_dvd_of_dvd hr hm)

theorem scalar_transform_inner_divisors (M R r : ℕ) (hR : 1 ≤ R)
    (hr : r ∣ scalarSievePrimeProduct M R) :
    (scalarSievePrimeProduct M R / r).divisors.filter (fun m => r * m < R) =
      (Finset.Icc 1 ((R - 1) / r)).filter (fun m => Squarefree m ∧ m.Coprime (M * r)) := by
  have hP := scalarSievePrimeProduct_squarefree M R
  have hr0 : 0 < r := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP.ne_zero hr)
  have hquot0 : scalarSievePrimeProduct M R / r ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP.ne_zero) hr) hr0).ne'
  ext m
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hmdiv, _⟩, hmcut⟩
    have hmdata := (squarefree_dvd_quotient_iff _ r m hP hr).mp hmdiv
    have hm0 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP.ne_zero hmdata.1)
    have hmR : m ≤ R := (Nat.le_mul_of_pos_left m hr0).trans hmcut.le
    have hmsq := (dvd_scalarSievePrimeProduct_iff M R m hmR).mp hmdata.1
    refine ⟨⟨hm0, ?_⟩, hmsq.1, hmsq.2.mul_right hmdata.2⟩
    rw [Nat.le_div_iff_mul_le hr0, Nat.mul_comm m r]
    omega
  · rintro ⟨⟨hm0, hmQ⟩, hmsq, hmcop⟩
    have hmcop' := Nat.coprime_mul_iff_right.mp hmcop
    have hmR : m ≤ R := hmQ.trans ((Nat.div_le_self (R - 1) r).trans (Nat.sub_le R 1))
    have hmP := (dvd_scalarSievePrimeProduct_iff M R m hmR).mpr ⟨hmsq, hmcop'.1⟩
    refine ⟨⟨(squarefree_dvd_quotient_iff _ r m hP hr).mpr ⟨hmP, hmcop'.2⟩, hquot0⟩, ?_⟩
    have hmul := (Nat.le_div_iff_mul_le hr0).mp hmQ
    rw [Nat.mul_comm m r] at hmul
    omega

theorem scalarSemiprimeTransform_eq_fixed_modulus_sum (M R r : ℕ) (hR : 1 ≤ R)
    (hr : r ∣ scalarSievePrimeProduct M R) :
    scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r =
      ((r : ℝ) / r.totient) *
        ∑ m ∈ (Finset.Icc 1 ((R - 1) / r)).filter
            (fun m => Squarefree m ∧ m.Coprime (M * r)),
          scalarLinearY R (r * m) / m.totient := by
  rw [scalarSemiprimeTransform_eq_sum _ _ r (scalarSievePrimeProduct_squarefree M R).ne_zero hr]
  rw [← scalar_transform_inner_divisors M R r hR hr, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : r * m < R
  · exact (if_pos hm).symm
  · rw [if_neg hm, scalarLinearY_eq_zero_of_radius R (r * m) (Nat.le_of_not_gt hm), zero_div]

end Erdos964
