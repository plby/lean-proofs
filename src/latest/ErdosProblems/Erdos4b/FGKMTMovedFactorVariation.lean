/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTupleVariation

/-!
# Reassigning a fixed product among divisor coordinates

After the moved factors are removed, both tuples share the same positive
integer base. The total logarithmic increment is exactly the logarithm
of the moved product, divided by the common logarithmic scale.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def sieveLogTuple {j : ℕ} (R : ℕ) (r : Fin j → ℕ) : Fin j → ℝ :=
  fun i => Real.log (r i) / Real.log R

theorem sieveLogTuple_nonneg {j : ℕ} (R : ℕ) (r : Fin j → ℕ) (i : Fin j) :
    0 ≤ sieveLogTuple R r i :=
  div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem sieveLogTuple_mul {j : ℕ} (R : ℕ) (r a : Fin j → ℕ)
    (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i) :
    sieveLogTuple R (fun i => r i * a i) =
      fun i => sieveLogTuple R r i + sieveLogTuple R a i := by
  funext i
  simp only [sieveLogTuple, Nat.cast_mul]
  rw [Real.log_mul (by exact_mod_cast (hr i).ne') (by exact_mod_cast (ha i).ne'), add_div]

theorem sieveLogTuple_le_mul {j : ℕ} (R : ℕ) (r a : Fin j → ℕ)
    (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i) (i : Fin j) :
    sieveLogTuple R r i ≤ sieveLogTuple R (fun q => r q * a q) i := by
  rw [sieveLogTuple_mul R r a hr ha]
  exact le_add_of_nonneg_right (sieveLogTuple_nonneg R a i)

theorem sum_sieveLogTuple {j : ℕ} (R : ℕ) (a : Fin j → ℕ)
    (ha : ∀ i, 0 < a i) :
    (∑ i, sieveLogTuple R a i) = Real.log (∏ i, a i : ℕ) / Real.log R := by
  simp only [sieveLogTuple]
  rw [← Finset.sum_div, Nat.cast_prod,
    Real.log_prod (fun i _hi => by exact_mod_cast (ha i).ne')]

theorem sieveLogTuple_mul_sub_sum {j : ℕ} (R : ℕ) (r a : Fin j → ℕ)
    (hr : ∀ i, 0 < r i) (ha : ∀ i, 0 < a i) :
    (∑ i, (sieveLogTuple R (fun q => r q * a q) i - sieveLogTuple R r i)) =
      Real.log (∏ i, a i : ℕ) / Real.log R := by
  simp only [sieveLogTuple_mul R r a hr ha, add_sub_cancel_left]
  exact sum_sieveLogTuple R a ha

theorem exists_sieveProfile_movedFactor_variation_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k : ℕ}, 0 < k → 10000 ≤ Real.log k →
      ∀ (j R : ℕ) (r a b : Fin j → ℕ),
        (∀ i, 0 < r i) → (∀ i, 0 < a i) → (∀ i, 0 < b i) →
        (∏ i, a i) = (∏ i, b i) →
        |sieveProfile k j (sieveLogTuple R (fun i => r i * a i)) -
          sieveProfile k j (sieveLogTuple R (fun i => r i * b i))| ≤
          (C * sieveProfileScale k * sieveProfileMajorant k j (sieveLogTuple R r)) *
            (Real.log (∏ i, a i : ℕ) / Real.log R) := by
  obtain ⟨C, hC, hbound⟩ := exists_sieveProfile_reassignment_variation_bound
  refine ⟨C, hC, ?_⟩
  intro k hk hlog j R r a b hr ha hb hprod
  apply hbound hk hlog j (sieveLogTuple R r)
    (sieveLogTuple R (fun i => r i * a i)) (sieveLogTuple R (fun i => r i * b i))
    (Real.log (∏ i, a i : ℕ) / Real.log R)
  · exact sieveLogTuple_nonneg R r
  · exact sieveLogTuple_le_mul R r a hr ha
  · exact sieveLogTuple_le_mul R r b hr hb
  · exact (sieveLogTuple_mul_sub_sum R r a hr ha).le
  · rw [sieveLogTuple_mul_sub_sum R r b hr hb, hprod]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveLogTuple_mul_sub_sum
#print axioms Erdos4b.FGKMT.exists_sieveProfile_movedFactor_variation_bound
