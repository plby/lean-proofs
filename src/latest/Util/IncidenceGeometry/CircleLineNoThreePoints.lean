import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

lemma CircleLineNoThreePoints
    {c x y u v w : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hxy : x ≠ y)
    (hu : u ∈ line[ℝ, x, y])
    (hv : v ∈ line[ℝ, x, y])
    (hw : w ∈ line[ℝ, x, y])
    (hdu : dist u c = r)
    (hdv : dist v c = r)
    (hdw : dist w c = r)
    (huv : u ≠ v)
    (huw : u ≠ w)
    (hvw : v ≠ w) :
    False := by
  have circle_sq :
      ∀ {z : EuclideanSpace ℝ (Fin 2)},
        dist z c = r →
          (z 0 - c 0) ^ 2 + (z 1 - c 1) ^ 2 = r ^ 2 := by
    intro z hz
    have hsq : dist z c ^ 2 = r ^ 2 := by rw [hz]
    rw [dist_eq_norm] at hsq
    change ‖z - c‖ ^ 2 = r ^ 2 at hsq
    have hnorm := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (z - c)
    rw [hnorm] at hsq
    norm_num at hsq
    simpa [EuclideanSpace, Fin.sum_univ_two, sub_eq_add_neg, sq] using hsq
  have quadratic_no_three :
      ∀ {A B C t₁ t₂ t₃ : ℝ}, A ≠ 0 →
        A * t₁ ^ 2 + B * t₁ + C = 0 →
        A * t₂ ^ 2 + B * t₂ + C = 0 →
        A * t₃ ^ 2 + B * t₃ + C = 0 →
        t₁ ≠ t₂ → t₁ ≠ t₃ → t₂ ≠ t₃ → False := by
    intro A B C t₁ t₂ t₃ hA h₁ h₂ h₃ h₁₂ h₁₃ h₂₃
    have hf₁₂ : (t₁ - t₂) * (A * (t₁ + t₂) + B) = 0 := by
      nlinarith
    have hlin₁₂ : A * (t₁ + t₂) + B = 0 :=
      (mul_eq_zero.mp hf₁₂).resolve_left (sub_ne_zero.mpr h₁₂)
    have hf₁₃ : (t₁ - t₃) * (A * (t₁ + t₃) + B) = 0 := by
      nlinarith
    have hlin₁₃ : A * (t₁ + t₃) + B = 0 :=
      (mul_eq_zero.mp hf₁₃).resolve_left (sub_ne_zero.mpr h₁₃)
    have hzero : A * (t₂ - t₃) = 0 := by
      nlinarith
    exact h₂₃ (sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hA))
  let d0 : ℝ := y 0 - x 0
  let d1 : ℝ := y 1 - x 1
  let A : ℝ := d0 ^ 2 + d1 ^ 2
  let B : ℝ := 2 * ((x 0 - c 0) * d0 + (x 1 - c 1) * d1)
  let C : ℝ := (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 - r ^ 2
  have hA : A ≠ 0 := by
    have hd : d0 ≠ 0 ∨ d1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hxy
      apply PiLp.ext
      intro i
      fin_cases i
      · dsimp [d0] at h ⊢
        linarith
      · dsimp [d1] at h ⊢
        linarith
    rcases hd with hd | hd
    · have hpos : 0 < A := by
        dsimp [A]
        exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd) (sq_nonneg d1)
      exact ne_of_gt hpos
    · have hpos : 0 < A := by
        dsimp [A]
        exact add_pos_of_nonneg_of_pos (sq_nonneg d0) (sq_pos_of_ne_zero hd)
      exact ne_of_gt hpos
  have root_of_line :
      ∀ {z : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
        z = AffineMap.lineMap x y t →
          dist z c = r →
            A * t ^ 2 + B * t + C = 0 := by
    intro z t hzline hdist
    have hsq := circle_sq hdist
    subst z
    dsimp [A, B, C, d0, d1]
    simp [AffineMap.lineMap_apply_module] at hsq ⊢
    ring_nf at hsq ⊢
    nlinarith
  rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := u)
      (p₁ := x) (p₂ := y)).mp hu with ⟨tu, htu⟩
  rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := v)
      (p₁ := x) (p₂ := y)).mp hv with ⟨tv, htv⟩
  rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := w)
      (p₁ := x) (p₂ := y)).mp hw with ⟨tw, htw⟩
  have htu_root := root_of_line htu.symm hdu
  have htv_root := root_of_line htv.symm hdv
  have htw_root := root_of_line htw.symm hdw
  have htu_ne_tv : tu ≠ tv := by
    intro ht
    apply huv
    rw [← htu, ← htv, ht]
  have htu_ne_tw : tu ≠ tw := by
    intro ht
    apply huw
    rw [← htu, ← htw, ht]
  have htv_ne_tw : tv ≠ tw := by
    intro ht
    apply hvw
    rw [← htv, ← htw, ht]
  exact quadratic_no_three hA htu_root htv_root htw_root htu_ne_tv htu_ne_tw htv_ne_tw
