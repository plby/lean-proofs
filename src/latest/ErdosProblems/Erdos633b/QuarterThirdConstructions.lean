import ErdosProblems.Erdos633b.CoprimeMiddleInterval

/-! Explicit coprime residues strictly between one quarter and one third
of every sufficiently large modulus, by elementary congruence cases. -/

namespace Erdos633b

def QuarterThirdResidue (D r : ℕ) : Prop := r.Coprime D ∧ D < 4 * r ∧ 3 * r < D

theorem quarter_third_of_four_dvd (D : ℕ) (hD : 60 < D) (hd : 4 ∣ D) :
    ∃ r, QuarterThirdResidue D r := by
  obtain ⟨q, hq⟩ := hd
  have hqpos : 15 < q := by omega
  by_cases hqeven : Even q
  · let r := q + 1
    have hr : Odd r := by rw [Nat.odd_iff]; obtain ⟨t, ht⟩ := hqeven; dsimp [r]; omega
    have hr4 : r.Coprime 4 := by simpa using (Nat.coprime_two_right.mpr hr).pow_right 2
    have hrq : r.Coprime q := by dsimp [r]; rw [Nat.coprime_self_add_left]; simp
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [hq]; exact hr4.mul_right hrq
    · dsimp [r]; omega
    · dsimp [r]; omega
  · have hqodd : Odd q := Nat.not_even_iff_odd.mp hqeven
    let r := q + 2
    have hr : Odd r := by rw [Nat.odd_iff] at hqodd ⊢; dsimp [r]; omega
    have hr4 : r.Coprime 4 := by simpa using (Nat.coprime_two_right.mpr hr).pow_right 2
    have hrq : r.Coprime q := by
      dsimp [r]
      rw [Nat.coprime_self_add_left]
      exact (Nat.coprime_two_right.mpr hqodd).symm
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [hq]; exact hr4.mul_right hrq
    · dsimp [r]; omega
    · dsimp [r]; omega

theorem quarter_third_of_mod_three_one (D : ℕ) (hD : 60 < D) (hd : D % 3 = 1) :
    ∃ r, QuarterThirdResidue D r := by
  let r := (D - 1) / 3
  have he : D = 3 * r + 1 := by dsimp [r]; omega
  refine ⟨r, ?_, by omega, by omega⟩
  rw [he, Nat.coprime_mul_right_add_right]
  simp

theorem quarter_third_of_three_dvd (D : ℕ) (hD : 60 < D) (hd : 3 ∣ D) :
    ∃ r, QuarterThirdResidue D r := by
  obtain ⟨q, hq⟩ := hd
  have hqpos : 20 < q := by omega
  by_cases hq1 : q % 3 = 1
  · let r := q - 3
    have he : q = r + 3 := by dsimp [r]; omega
    have hr3 : r.Coprime 3 :=
      ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr (by dsimp [r]; omega)).symm
    have hrq : r.Coprime q := by rw [he, Nat.coprime_self_add_right]; exact hr3
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [hq]; exact hr3.mul_right hrq
    · dsimp [r]; omega
    · dsimp [r]; omega
  · let r := q - 1
    have he : q = r + 1 := by dsimp [r]; omega
    have hr3 : r.Coprime 3 :=
      ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr (by dsimp [r]; omega)).symm
    have hrq : r.Coprime q := by rw [he, Nat.coprime_self_add_right]; simp
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [hq]; exact hr3.mul_right hrq
    · dsimp [r]; omega
    · dsimp [r]; omega

theorem quarter_third_of_odd_mod_three_two (D : ℕ) (hD : 60 < D)
    (hd : D % 3 = 2) (hodd : Odd D) : ∃ r, QuarterThirdResidue D r := by
  let r := (D - 2) / 3
  have he : D = 3 * r + 2 := by dsimp [r]; omega
  have hr : Odd r := by rw [Nat.odd_iff] at hodd ⊢; dsimp [r]; omega
  refine ⟨r, ?_, by omega, by omega⟩
  rw [he, Nat.coprime_mul_right_add_right]
  exact Nat.coprime_two_right.mpr hr

theorem quarter_third_of_ten_dvd (D : ℕ) (hD : 60 < D)
    (hd : 10 ∣ D) (hmod : D % 4 = 2) : ∃ r, QuarterThirdResidue D r := by
  obtain ⟨L, hL⟩ := hd
  have hLp : 6 < L := by omega
  have hLo : Odd L := by rw [Nat.odd_iff]; omega
  let r := 3 * L - 2
  have hr2 : r.Coprime 2 := Nat.coprime_two_right.mpr (by
    rw [Nat.odd_iff] at hLo ⊢; dsimp [r]; omega)
  have hrL : r.Coprime L := by
    have he : 3 * L = r + 2 := by dsimp [r]; omega
    have hh : r.Coprime (3 * L) := by rw [he, Nat.coprime_self_add_right]; exact hr2
    exact Nat.Coprime.of_dvd_right (dvd_mul_left L 3) hh
  by_cases hr5 : 5 ∣ r
  · let s := 3 * L + 2
    have hs2 : s.Coprime 2 := Nat.coprime_two_right.mpr (by
      rw [Nat.odd_iff] at hLo ⊢; dsimp [s]; omega)
    have hs5 : s.Coprime 5 :=
      ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr (by
        dsimp [r] at hr5
        dsimp [s]
        omega)).symm
    have hsL : s.Coprime L := by
      dsimp [s]
      rw [Nat.coprime_mul_right_add_left]
      exact (Nat.coprime_two_right.mpr hLo).symm
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [hL]
      exact (hs2.mul_right hs5).mul_right hsL
    · dsimp [s]; omega
    · dsimp [s]; omega
  · have hr5' : r.Coprime 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hr5).symm
    refine ⟨r, ?_, ?_, ?_⟩
    · rw [hL]
      exact (hr2.mul_right hr5').mul_right hrL
    · dsimp [r]; omega
    · dsimp [r]; omega

theorem quarter_third_of_even_mod_three_two (D : ℕ) (hD : 60 < D)
    (hd : D % 3 = 2) (hmod : D % 4 = 2) : ∃ r, QuarterThirdResidue D r := by
  let r := (D - 5) / 3
  have he : D = 3 * r + 5 := by dsimp [r]; omega
  by_cases h5 : 5 ∣ r
  · apply quarter_third_of_ten_dvd D hD ?_ hmod
    dsimp [r] at h5
    omega
  · have hr5 : r.Coprime 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm
    refine ⟨r, ?_, by omega, by omega⟩
    rw [he, Nat.coprime_mul_right_add_right]
    exact hr5

theorem exists_quarter_third_residue_of_gt_sixty (D : ℕ) (hD : 60 < D) :
    ∃ r, QuarterThirdResidue D r := by
  by_cases h4 : 4 ∣ D
  · exact quarter_third_of_four_dvd D hD h4
  have h3 : D % 3 = 0 ∨ D % 3 = 1 ∨ D % 3 = 2 := by omega
  rcases h3 with h3 | h3 | h3
  · exact quarter_third_of_three_dvd D hD (Nat.dvd_of_mod_eq_zero h3)
  · exact quarter_third_of_mod_three_one D hD h3
  · by_cases hodd : Odd D
    · exact quarter_third_of_odd_mod_three_two D hD h3 hodd
    · have hmod : D % 4 = 2 := by rw [Nat.odd_iff] at hodd; omega
      exact quarter_third_of_even_mod_three_two D hD h3 hmod

end Erdos633b
