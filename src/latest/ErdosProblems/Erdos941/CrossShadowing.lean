import ErdosProblems.Erdos941.RotationCross

/-!
# Iterating the local cross-product constraint

Each step inward from both ends of a common reduced trajectory adds one factor
of three to the cross product. No matrix normal-form theorem is needed.
-/

namespace Erdos941

theorem shadow_local_strengthen {a b : Axis} (hab : a ≠ b) {v c l r : Triple}
    (hn : tripleNorm v % 3 = 2) (ha : Admissible a v) (hb : Admissible b v)
    (hl : rotationNumerator a c = (3 : ℤ) • l)
    (hr : rotationNumerator b c = (3 : ℤ) • r) (hc : dot3 v c = 0)
    {d : ℤ} (hd : d ≠ 0) (hdl : TripleDivisible d l)
    (hdc : TripleDivisible d c) (hdr : TripleDivisible d r) :
    TripleDivisible (3 * d) c := by
  obtain ⟨u, hu⟩ := hdc.exists_smul
  obtain ⟨ul, hul⟩ := hdl.exists_smul
  obtain ⟨ur, hur⟩ := hdr.exists_smul
  have hnorm {a : Axis} {x y : Triple}
      (h : rotationNumerator a (d • x) = (3 : ℤ) • (d • y)) :
      rotationNumerator a x = (3 : ℤ) • y := by
    apply triple_smul_cancel hd
    simpa only [map_smul, smul_smul, mul_comm d 3] using h
  have hla : rotationNumerator a u = (3 : ℤ) • ul := hnorm (by rwa [hu, hul] at hl)
  have hra : rotationNumerator b u = (3 : ℤ) • ur := hnorm (by rwa [hu, hur] at hr)
  have hdiv (x : Triple) : TripleDivisible 3 ((3 : ℤ) • x) :=
    ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩
  have hca : Admissible a u := admissible_of_rotationNumerator_divisible (hla ▸ hdiv ul)
  have hcb : Admissible b u := admissible_of_rotationNumerator_divisible (hra ▸ hdiv ur)
  have hcu : dot3 v u = 0 := by
    rw [hu] at hc
    have hh : d * dot3 v u = 0 := by
      dsimp [dot3] at hc ⊢
      linear_combination hc
    exact (mul_eq_zero.mp hh).resolve_left hd
  have h3 := shadow_local_divisible hab hn ha hb hca hcb hcu
  obtain ⟨z, hz⟩ := h3.exists_smul
  rw [hu, hz, smul_smul, mul_comm d 3]
  exact ⟨dvd_mul_right _ _, dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem cross_divisible_interior (T : ℕ) (axes : ℕ → Axis) (v w : ℕ → Triple)
    (hn : ∀ i, i ≤ T → tripleNorm (v i) % 3 = 2)
    (hv : ∀ i, i < T → Admissible (axes i) (v i) ∧ v (i + 1) = rotate (axes i) (v i))
    (hw : ∀ i, i < T → Admissible (axes i) (w i) ∧ w (i + 1) = rotate (axes i) (w i))
    (hred : ∀ i, i + 1 < T → axes i ≠ axes (i + 1))
    (k i : ℕ) (hleft : k ≤ i) (hright : i + k ≤ T) :
    TripleDivisible ((3 : ℤ) ^ k) (cross3 (v i) (w i)) := by
  induction k generalizing i with
  | zero => simp [TripleDivisible]
  | succ k ih =>
    have hi0 : 0 < i := by omega
    have hiT : i < T := by omega
    have hiPrev : i - 1 < T := by omega
    have he : i - 1 + 1 = i := by omega
    obtain ⟨hva, hvnext⟩ := hv i hiT
    obtain ⟨hwa, hwnext⟩ := hw i hiT
    obtain ⟨hvprev, hvprevnext⟩ := hv (i - 1) hiPrev
    obtain ⟨hwprev, hwprevnext⟩ := hw (i - 1) hiPrev
    rw [he] at hvprevnext hwprevnext
    have ha : Admissible (axes (i - 1)) (v i) := by
      rw [hvprevnext]
      exact rotate_admissible hvprev
    have hab : axes (i - 1) ≠ axes i := by
      simpa only [he] using hred (i - 1) (by omega)
    have hcrossprev : rotationNumerator (axes (i - 1)) (cross3 (v i) (w i)) =
        (3 : ℤ) • cross3 (v (i - 1)) (w (i - 1)) := by
      apply rotationNumerator_reverse
      rw [hvprevnext, hwprevnext]
      exact cross3_rotate hvprev hwprev
    have hcrossnext : rotationNumerator (axes i) (cross3 (v i) (w i)) =
        (3 : ℤ) • cross3 (v (i + 1)) (w (i + 1)) := by
      rw [hvnext, hwnext]
      exact cross3_rotate hva hwa
    have h := shadow_local_strengthen hab (hn i (by omega)) ha hva hcrossprev hcrossnext
      (cross3_orthogonal_left (v i) (w i)) (pow_ne_zero k (by norm_num : (3 : ℤ) ≠ 0))
      (ih (i - 1) (by omega) (by omega)) (ih i (by omega) (by omega))
      (ih (i + 1) (by omega) (by omega))
    simpa only [pow_succ, mul_comm (3 : ℤ)] using h

end Erdos941
