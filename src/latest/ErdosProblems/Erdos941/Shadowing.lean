import ErdosProblems.Erdos941.CrossShadowing

/-! # The dot-product congruence forced by a common centered trajectory -/

namespace Erdos941

theorem norm_smul_triple (d : ℤ) (v : Triple) :
    tripleNorm (d • v) = d ^ 2 * tripleNorm v := by
  dsimp [tripleNorm, norm3]
  ring

theorem TripleDivisible.square_dvd_norm {d : ℤ} {v : Triple} (h : TripleDivisible d v) :
    d ^ 2 ∣ tripleNorm v := by
  obtain ⟨u, rfl⟩ := h.exists_smul
  rw [norm_smul_triple]
  exact dvd_mul_right _ _

theorem three_pow_dvd_difference_of_squares {n e : ℤ} (hn : n % 3 = 2) (k : ℕ)
    (h : (3 : ℤ) ^ k ∣ n ^ 2 - e ^ 2) :
    (3 : ℤ) ^ k ∣ e - n ∨ (3 : ℤ) ^ k ∣ e + n := by
  have hp : Prime (3 : ℤ) := Nat.prime_iff_prime_int.mp (by decide : Nat.Prime 3)
  have hmul : (3 : ℤ) ^ k ∣ (e - n) * (e + n) := by
    have hh := dvd_neg.mpr h
    convert hh using 1 <;> try rfl
    ring
  by_cases hminus : (3 : ℤ) ∣ e - n
  · have hplus : ¬(3 : ℤ) ∣ e + n := by omega
    exact Or.inl (hp.pow_dvd_of_dvd_mul_right k hplus hmul)
  · exact Or.inr (hp.pow_dvd_of_dvd_mul_left k hminus hmul)

theorem cross_divisible_dot_congruence {n : ℕ} {v w : Triple}
    (hn : n % 3 = 2) (hv : tripleNorm v = n) (hw : tripleNorm w = n) (L : ℕ)
    (hcross : TripleDivisible ((3 : ℤ) ^ L) (cross3 v w)) :
    (3 : ℤ) ^ (2 * L) ∣ dot3 v w - n ∨
      (3 : ℤ) ^ (2 * L) ∣ dot3 v w + n := by
  have hh := hcross.square_dvd_norm
  rw [cross3_norm, hv, hw, ← pow_mul, mul_comm L 2, ← pow_two (n : ℤ)] at hh
  apply three_pow_dvd_difference_of_squares _ (2 * L) hh
  exact_mod_cast hn

theorem centered_trajectory_dot_congruence (L n : ℕ) (axes : ℕ → Axis) (v w : ℕ → Triple)
    (hn : n % 3 = 2)
    (hvnorm : ∀ i, i ≤ 2 * L → tripleNorm (v i) = n)
    (hwnorm : ∀ i, i ≤ 2 * L → tripleNorm (w i) = n)
    (hv : ∀ i, i < 2 * L → Admissible (axes i) (v i) ∧
      v (i + 1) = rotate (axes i) (v i))
    (hw : ∀ i, i < 2 * L → Admissible (axes i) (w i) ∧
      w (i + 1) = rotate (axes i) (w i))
    (hred : ∀ i, i + 1 < 2 * L → axes i ≠ axes (i + 1)) :
    (3 : ℤ) ^ (2 * L) ∣ dot3 (v L) (w L) - n ∨
      (3 : ℤ) ^ (2 * L) ∣ dot3 (v L) (w L) + n := by
  apply cross_divisible_dot_congruence hn (hvnorm L (by omega)) (hwnorm L (by omega)) L
  apply cross_divisible_interior (2 * L) axes v w _ hv hw hred L L le_rfl (by omega)
  intro i hi
  rw [hvnorm i hi]
  exact_mod_cast hn

end Erdos941
