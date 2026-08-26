import ErdosProblems.Erdos421.ShiftedPrimeCode
import ErdosProblems.Erdos421.PowerSumAffine

/-! # Why a common residue class forces compatible shifted power codes -/

namespace Erdos421

theorem vinogradov_shifted_append_eq {k s N : ℕ}
    (z w : Fin k → Fin N) (u v : Fin s → Fin N) (a : ℤ)
    (h : vinogradovSums k (Fin.append z u) = vinogradovSums k (Fin.append w v)) (j : Fin k) :
    (∑ i : Fin k, ((z i : ℤ) + 1 - a) ^ ((j : ℕ) + 1)) +
        (∑ i : Fin s, ((u i : ℤ) + 1 - a) ^ ((j : ℕ) + 1)) =
      (∑ i : Fin k, ((w i : ℤ) + 1 - a) ^ ((j : ℕ) + 1)) +
        ∑ i : Fin s, ((v i : ℤ) + 1 - a) ^ ((j : ℕ) + 1) := by
  have hshift := powerSumVector_add_const_eq (n := k)
    (fun i : Fin (k + s) ↦ ((Fin.append z u i).val : ℤ) + 1)
    (fun i : Fin (k + s) ↦ ((Fin.append w v i).val : ℤ) + 1) h (-a)
  have he := congrFun hshift j
  simpa only [powerSumVector, Fin.sum_univ_add, Fin.append_left, Fin.append_right,
    sub_eq_add_neg] using he

theorem integerResidueClass_dvd_shift {N p : ℕ} [NeZero p] (c : ZMod p)
    (y : Fin N) (hy : y ∈ integerResidueClass N p c) :
    (p : ℤ) ∣ (y : ℤ) + 1 - c.val := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simp only [Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast, ZMod.natCast_zmod_val]
  exact sub_eq_zero.mpr (Finset.mem_filter.mp hy).2

theorem integerResidueClass_pow_shift_zero {N p : ℕ} [NeZero p] (c : ZMod p)
    (y : Fin N) (hy : y ∈ integerResidueClass N p c) (e : ℕ) :
    ((y : ZMod (p ^ e)) + 1 - c.val) ^ e = 0 := by
  have hd := pow_dvd_pow_of_dvd (integerResidueClass_dvd_shift c y hy) e
  have hz : ((((y : ℤ) + 1 - c.val) ^ e : ℤ) : ZMod (p ^ e)) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    simpa only [Nat.cast_pow] using hd
  simpa only [Int.cast_pow, Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast] using hz

theorem shiftedPowerCode_compatible {k s N p : ℕ} [NeZero p] (c : ZMod p)
    (z w : Fin k → Fin N) (u v : Fin s → Fin N)
    (hu : ∀ i, u i ∈ integerResidueClass N p c)
    (hv : ∀ i, v i ∈ integerResidueClass N p c)
    (h : vinogradovSums k (Fin.append z u) = vinogradovSums k (Fin.append w v)) :
    shiftedPowerCode p k N c.val z = shiftedPowerCode p k N c.val w := by
  funext j
  have he := vinogradov_shifted_append_eq z w u v c.val h j
  have hm := congrArg (Int.castRingHom (ZMod (p ^ ((j : ℕ) + 1)))) he
  simp only [map_add, map_sum, map_pow, map_sub, map_one, map_natCast] at hm
  have hu0 : (∑ i : Fin s, ((u i : ZMod (p ^ ((j : ℕ) + 1))) + 1 - c.val) ^
      ((j : ℕ) + 1)) = 0 :=
    Finset.sum_eq_zero (fun i _ ↦ integerResidueClass_pow_shift_zero c (u i) (hu i) _)
  have hv0 : (∑ i : Fin s, ((v i : ZMod (p ^ ((j : ℕ) + 1))) + 1 - c.val) ^
      ((j : ℕ) + 1)) = 0 :=
    Finset.sum_eq_zero (fun i _ ↦ integerResidueClass_pow_shift_zero c (v i) (hv i) _)
  rw [hu0, hv0, add_zero, add_zero] at hm
  simpa only [shiftedPowerCode, Int.cast_natCast] using hm

end Erdos421
