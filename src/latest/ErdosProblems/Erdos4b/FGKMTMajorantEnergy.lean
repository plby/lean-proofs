/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTOneLongTensor

/-!
# The full square energy of the error majorant

Finite Cauchy--Schwarz and the exact one-long-factor tensor integrals
give a quadratic, not exponential, loss in the dimension.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory
open scoped BigOperators

def sieveProfileMajorant (k j : ℕ) (t : Fin j → ℝ) : ℝ := ∑ i, oneLongTensor k j i t

theorem sieveProfileMajorant_continuous (k j : ℕ) : Continuous (sieveProfileMajorant k j) :=
  continuous_finsetSum _ (fun i _ => oneLongTensor_continuous k j i)

theorem sieveProfileMajorant_nonneg (k j : ℕ) (t : Fin j → ℝ) :
    0 ≤ sieveProfileMajorant k j t := Finset.sum_nonneg fun i _ => oneLongTensor_nonneg k j i t

theorem sieveProfileMajorant_sq_le (k j : ℕ) (t : Fin j → ℝ) :
    sieveProfileMajorant k j t ^ 2 ≤ (j : ℝ) * ∑ i, oneLongTensor k j i t ^ 2 := by
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sieveProfileMajorant] using
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin j => (1 : ℝ))
      (fun i => oneLongTensor k j i t)

theorem oneLongTensor_sq_sum_integrableOn {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    IntegrableOn (fun t : Fin j → ℝ => ∑ i, oneLongTensor k j i t ^ 2)
      (Set.univ.pi (fun _ : Fin j => Set.Ioi (0 : ℝ))) :=
  integrable_finsetSum Finset.univ
    (fun i _ => oneLongTensor_pow_integrableOn hk hlog (j := j) i 1)

theorem integral_oneLongTensor_sq_sum {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        ∑ i, oneLongTensor k j i t ^ 2) =
      (j : ℝ) * (dimensionLongMass k * dimensionProfileMass k ^ (j - 1)) := by
  rw [integral_finsetSum Finset.univ
    (fun i _ => oneLongTensor_pow_integrableOn hk hlog (j := j) i 1)]
  simp only [integral_oneLongTensor_sq hk hlog, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

theorem sieveProfileMajorant_sq_integrableOn {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    IntegrableOn (fun t => sieveProfileMajorant k j t ^ 2)
      (Set.univ.pi (fun _ : Fin j => Set.Ioi (0 : ℝ))) := by
  have hsum := oneLongTensor_sq_sum_integrableOn hk hlog (j := j)
  apply (hsum.const_mul (j : ℝ)).mono'
    ((sieveProfileMajorant_continuous k j).pow 2).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    change |sieveProfileMajorant k j t ^ 2| ≤ (j : ℝ) * ∑ i, oneLongTensor k j i t ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact sieveProfileMajorant_sq_le k j t

theorem integral_sieveProfileMajorant_sq_le {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        sieveProfileMajorant k j t ^ 2) ≤
      (j : ℝ) ^ 2 * dimensionLongMass k * dimensionProfileMass k ^ (j - 1) := by
  have hsum := oneLongTensor_sq_sum_integrableOn hk hlog (j := j)
  calc
    _ ≤ ∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        (j : ℝ) * ∑ i, oneLongTensor k j i t ^ 2 :=
      integral_mono (sieveProfileMajorant_sq_integrableOn hk hlog) (hsum.const_mul _)
        (fun t => sieveProfileMajorant_sq_le k j t)
    _ = (j : ℝ) * ((j : ℝ) * (dimensionLongMass k * dimensionProfileMass k ^ (j - 1))) := by
      rw [integral_const_mul, integral_oneLongTensor_sq_sum hk hlog]
    _ = _ := by ring

theorem integral_sieveProfileMajorant_sq_tensor_bound {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        sieveProfileMajorant k j t ^ 2) ≤ 2 * (j : ℝ) ^ 2 * dimensionProfileMass k ^ j := by
  have hmass := dimensionProfileMass_pos hk hlog
  refine (integral_sieveProfileMajorant_sq_le hk hlog).trans ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have hpow : dimensionProfileMass k ^ j =
        dimensionProfileMass k ^ (j - 1) * dimensionProfileMass k := by
      simpa only [Nat.sub_add_cancel (show 1 ≤ j by omega)] using
        pow_succ (dimensionProfileMass k) (j - 1)
    calc
      _ ≤ (j : ℝ) ^ 2 * (2 * dimensionProfileMass k) * dimensionProfileMass k ^ (j - 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (dimensionLongMass_le_twice hk hlog) (sq_nonneg _))
          (pow_nonneg hmass.le _)
      _ = _ := by rw [hpow]; ring

theorem integral_sieveProfileMajorant_sq_energy_bound {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    (∫ t : Fin j → ℝ in Set.univ.pi (fun _ => Set.Ioi (0 : ℝ)),
        sieveProfileMajorant k j t ^ 2) ≤ 6 * (j : ℝ) ^ 2 * dimensionProfileEnergy k j := by
  have hI := (dimensionProfileEnergy_bounds hk hlog hj).1
  have hmass : dimensionProfileMass k ^ j ≤ 3 * dimensionProfileEnergy k j := by linarith
  calc
    _ ≤ 2 * (j : ℝ) ^ 2 * dimensionProfileMass k ^ j :=
      integral_sieveProfileMajorant_sq_tensor_bound hk hlog
    _ ≤ 2 * (j : ℝ) ^ 2 * (3 * dimensionProfileEnergy k j) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveProfileMajorant_sq_integrableOn
#print axioms Erdos4b.FGKMT.integral_sieveProfileMajorant_sq_energy_bound
