import ErdosProblems.Erdos941.PrimitiveLifting
import ErdosProblems.Erdos941.ThreeSquares

/-! # Primitive three-square representations for all admissible radii -/

namespace Erdos941

theorem exists_primitive_odd_square_lift {s : ℕ} (hs : Odd s)
    {v : Triple} (hv : PrimitiveTriple v) :
    ∃ w : Triple, PrimitiveTriple w ∧ tripleNorm w = (s : ℤ) ^ 2 * tripleNorm v := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases hs1 : s = 1
    · subst s
      exact ⟨v, hv, by simp⟩
    · obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd hs1
      obtain ⟨k, hk⟩ := hps
      have hspos : 0 < s := hs.pos
      have hkpos : 0 < k := by
        by_contra h
        have hk0 : k = 0 := by omega
        simp only [hk0, mul_zero] at hk
        omega
      have hklt : k < s := by nlinarith [hp.two_le]
      have hpk : Odd p ∧ Odd k := by
        exact Nat.odd_mul.mp (hk ▸ hs)
      have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hpk
      obtain ⟨u, hpu, hun⟩ := ih k hklt hpk.2
      obtain ⟨w, hpw, hwn⟩ := exists_primitive_prime_square_lift hp hp2 hpu
      refine ⟨w, hpw, ?_⟩
      rw [hwn, hun, hk]
      push_cast
      ring

theorem primitive_three_squares_four_free {n : ℕ} (hn : 0 < n) (h4 : ¬4 ∣ n)
    (h8 : n % 8 ≠ 7) :
    ∃ v : Triple, PrimitiveTriple v ∧ tripleNorm v = n := by
  obtain ⟨m, s, heq, hsq⟩ := Nat.sq_mul_squarefree n
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    simp only [hm0, mul_zero] at heq
    omega
  have hs2 : ¬2 ∣ s := by
    intro hd
    apply h4
    rw [← heq]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hd 2) m
  have hso : Odd s := Nat.odd_iff.mpr (by omega)
  have hmod : n % 8 = m % 8 := by
    rw [← heq, Nat.mul_mod, odd_sq_mod_eight hso, one_mul, Nat.mod_mod]
  obtain ⟨X, Y, Z, hXYZ⟩ := three_squares_squarefree hm hsq (hmod ▸ h8)
  have hv : tripleNorm (X, Y, Z) = m := hXYZ
  obtain ⟨v, hpv, hvn⟩ := exists_primitive_odd_square_lift hso
    (primitiveTriple_of_squarefree_norm hv hsq)
  refine ⟨v, hpv, ?_⟩
  rw [hvn, hv]
  exact_mod_cast heq

theorem primitive_three_squares_of_two_three_six {n : ℕ}
    (h8 : n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 6) :
    ∃ v : Triple, PrimitiveTriple v ∧ v ∈ spherePoints n := by
  obtain ⟨v, hpv, hv⟩ := primitive_three_squares_four_free
    (by omega : 0 < n) (by omega : ¬4 ∣ n) (by omega : n % 8 ≠ 7)
  exact ⟨v, hpv, mem_spherePoints.mpr hv⟩

end Erdos941
