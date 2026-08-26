import Mathlib

/-! # Reduced rational frequencies of an integer lattice -/

namespace Erdos421

theorem lattice_frequency_den_dvd (h : ℤ) (m : ℕ) : ((h : ℚ) / m).den ∣ m := by
  have hb := Rat.den_dvd h (m : ℤ)
  simpa only [Rat.divInt_eq_div, Int.cast_natCast, Int.natCast_dvd_natCast] using hb

theorem lattice_frequency_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun h : ℤ ↦ (h : ℚ) / m) := by
  intro h k he
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact_mod_cast (div_left_inj' hmQ).mp he

theorem rational_lattice_frequency_iff {m : ℕ} (hm : 0 < m) (q : ℚ) :
    (∃ h : ℤ, (h : ℚ) / m = q) ↔ q.den ∣ m := by
  constructor
  · rintro ⟨h, rfl⟩
    exact lattice_frequency_den_dvd h m
  · intro hdiv
    refine ⟨q.num * (m / q.den : ℕ), ?_⟩
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have hdQ : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    have hmul : (q.den : ℚ) * (m / q.den : ℕ) = m := by
      exact_mod_cast Nat.mul_div_cancel' hdiv
    rw [Int.cast_mul, Int.cast_natCast]
    calc
      _ = (q.num : ℚ) / q.den := by
        apply (div_eq_div_iff hmQ hdQ).mpr
        calc
          _ = (q.num : ℚ) * ((q.den : ℚ) * (m / q.den : ℕ)) := by ring
          _ = _ := by rw [hmul]
      _ = q := Rat.num_div_den q

end Erdos421
