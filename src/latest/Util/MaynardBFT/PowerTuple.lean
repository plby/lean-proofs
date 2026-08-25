import BoundedGaps.Foundations.Admissible
import Mathlib.Tactic

/-! # Admissible scaled powers with a modulus-independent span factor -/

namespace MaynardBFT

def powerTuple (K q : ℕ) : Finset ℕ :=
  (Finset.range K).image fun j => q * 2 ^ (j + 1)

theorem mem_powerTuple {K q h : ℕ} :
    h ∈ powerTuple K q ↔ ∃ j < K, h = q * 2 ^ (j + 1) := by
  simp [powerTuple, eq_comm]

theorem powerTuple_card (K : ℕ) {q : ℕ} (hq : 0 < q) :
    (powerTuple K q).card = K := by
  rw [powerTuple, Finset.card_image_iff.mpr, Finset.card_range]
  intro a ha b hb hab
  have hp := Nat.eq_of_mul_eq_mul_left hq hab
  have hi := Nat.pow_right_injective (a := 2) (by omega) hp
  omega

theorem powerTuple_divisible {K q h : ℕ} (hh : h ∈ powerTuple K q) : q ∣ h := by
  obtain ⟨j, _, rfl⟩ := mem_powerTuple.mp hh
  exact dvd_mul_right _ _

theorem powerTuple_pos {K q h : ℕ} (hq : 0 < q) (hh : h ∈ powerTuple K q) : 0 < h := by
  obtain ⟨j, _, rfl⟩ := mem_powerTuple.mp hh
  exact mul_pos hq (pow_pos (by norm_num) _)

theorem powerTuple_le_span {K q h : ℕ} (hh : h ∈ powerTuple K q) : h ≤ q * 2 ^ K := by
  obtain ⟨j, hj, rfl⟩ := mem_powerTuple.mp hh
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem powerTuple_admissible (K q : ℕ) : BoundedGaps.IsAdmissible (powerTuple K q) := by
  rw [BoundedGaps.isAdmissible_iff_avoids_residue]
  intro p hp
  by_cases hpq : p ∣ q
  · refine ⟨1, hp.one_lt, ?_⟩
    intro h hh
    have hph := hpq.trans (powerTuple_divisible hh)
    simp only [Nat.mod_eq_zero_of_dvd hph]
    exact Nat.zero_ne_one
  · by_cases hpTwo : p = 2
    · subst p
      refine ⟨1, by norm_num, ?_⟩
      intro h hh
      obtain ⟨j, _, rfl⟩ := mem_powerTuple.mp hh
      simp [pow_succ, Nat.mul_mod]
    · refine ⟨0, hp.pos, ?_⟩
      intro h hh hmod
      obtain ⟨j, _, rfl⟩ := mem_powerTuple.mp hh
      have hpd := Nat.dvd_of_mod_eq_zero hmod
      rcases hp.dvd_mul.mp hpd with h | h
      · exact hpq h
      · have hp2 := hp.dvd_of_dvd_pow h
        exact hpTwo ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2)

end MaynardBFT
