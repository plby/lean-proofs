import ErdosProblems.Erdos633b.CosineCyclotomicTransfer

/-! Nonvanishing of rational-angle sines at coprime conjugates,
proved by integer divisibility after cancelling pi. -/

namespace Erdos633b

theorem sine_weight_coprime_ne_zero (N k m : ℕ) (hN : 0 < N)
    (hk : k.Coprime N) (hm : 0 < m) (hmN : m < N) :
    Real.sin ((m : ℝ) * (k * (Real.pi / N))) ≠ 0 := by
  intro hz
  obtain ⟨b, hb⟩ := Real.sin_eq_zero_iff.mp hz
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (b : ℝ) * N = (m : ℝ) * k := by
    have hh := congrArg (fun x : ℝ => x * ((N : ℝ) / Real.pi)) hb
    field_simp [hN', Real.pi_ne_zero] at hh
    exact hh
  have hei : b * (N : ℤ) = (m : ℤ) * k := by exact_mod_cast he
  have hd : (N : ℤ) ∣ (m : ℤ) * k := ⟨b, by rw [← hei]; ring⟩
  have hdm : (N : ℤ) ∣ (m : ℤ) := hk.isCoprime.symm.dvd_of_dvd_mul_right hd
  have hdn : N ∣ m := Int.natCast_dvd_natCast.mp hdm
  exact (Nat.not_dvd_of_pos_of_lt hm hmN) hdn

theorem sine_pi_div_ne_zero (N : ℕ) (hN : 1 < N) : Real.sin (Real.pi / N) ≠ 0 := by
  simpa using sine_weight_coprime_ne_zero N 1 1 (by omega) (by simp) (by decide) hN

theorem sine_coprime_pi_div_ne_zero (N k : ℕ) (hN : 1 < N) (hk : k.Coprime N) :
    Real.sin (k * (Real.pi / N)) ≠ 0 := by
  simpa using sine_weight_coprime_ne_zero N k 1 (by omega) hk (by decide) hN

end Erdos633b
