import ErdosProblems.Erdos941.ShadowResidues

/-! # Integral transport of cross products along the half-turn trajectories -/

namespace Erdos941

def cross3 (v w : Triple) : Triple :=
  (v.2.1 * w.2.2 - v.2.2 * w.2.1,
    v.2.2 * w.1 - v.1 * w.2.2,
    v.1 * w.2.1 - v.2.1 * w.1)

theorem cross3_orthogonal_left (v w : Triple) : dot3 v (cross3 v w) = 0 := by
  dsimp [dot3, cross3]
  ring

theorem cross3_smul (a b : ℤ) (v w : Triple) :
    cross3 (a • v) (b • w) = (a * b) • cross3 v w := by
  ext <;> dsimp [cross3] <;> ring

theorem cross3_norm (v w : Triple) :
    tripleNorm (cross3 v w) = tripleNorm v * tripleNorm w - dot3 v w ^ 2 := by
  dsimp [tripleNorm, norm3, cross3, dot3]
  ring

def rotationNumerator (a : Axis) : Triple →ₗ[ℤ] Triple where
  toFun v :=
    (2 * axisDot a v - 3 * v.1,
      2 * sign a.1 * axisDot a v - 3 * v.2.1,
      2 * sign a.2 * axisDot a v - 3 * v.2.2)
  map_add' v w := by ext <;> dsimp [axisDot] <;> ring
  map_smul' r v := by ext <;> dsimp [axisDot] <;> ring

theorem rotationNumerator_apply (a : Axis) (v : Triple) :
    rotationNumerator a v =
      (2 * axisDot a v - 3 * v.1,
        2 * sign a.1 * axisDot a v - 3 * v.2.1,
        2 * sign a.2 * axisDot a v - 3 * v.2.2) := rfl

theorem rotationNumerator_rotate {a : Axis} {v : Triple} (ha : Admissible a v) :
    rotationNumerator a v = (3 : ℤ) • rotate a v := by
  have hd := Int.mul_ediv_cancel' ha
  rw [rotationNumerator_apply]
  apply Prod.ext
  · dsimp [rotate]
    linear_combination -2 * hd
  · apply Prod.ext
    · dsimp [rotate]
      linear_combination -2 * sign a.1 * hd
    · dsimp [rotate]
      linear_combination -2 * sign a.2 * hd

theorem rotationNumerator_involutive (a : Axis) (v : Triple) :
    rotationNumerator a (rotationNumerator a v) = (9 : ℤ) • v := by
  rcases a with ⟨a, b⟩
  simp only [rotationNumerator_apply]
  cases a <;> cases b <;> ext <;> dsimp [axisDot, sign] <;> ring

theorem rotationNumerator_cross (a : Axis) (v w : Triple) :
    cross3 (rotationNumerator a v) (rotationNumerator a w) =
      (3 : ℤ) • rotationNumerator a (cross3 v w) := by
  rcases a with ⟨a, b⟩
  simp only [rotationNumerator_apply]
  cases a <;> cases b <;> ext <;> dsimp [cross3, axisDot, sign] <;> ring

theorem cross3_rotate {a : Axis} {v w : Triple}
    (hv : Admissible a v) (hw : Admissible a w) :
    rotationNumerator a (cross3 v w) = (3 : ℤ) • cross3 (rotate a v) (rotate a w) := by
  have h := rotationNumerator_cross a v w
  rw [rotationNumerator_rotate hv, rotationNumerator_rotate hw, cross3_smul] at h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    change (3 * 3) * (cross3 (rotate a v) (rotate a w)).1 =
      3 * (rotationNumerator a (cross3 v w)).1 at h1
    change (rotationNumerator a (cross3 v w)).1 = 3 * (cross3 (rotate a v) (rotate a w)).1
    omega
  · apply Prod.ext
    · have h1 := congrArg (fun x : Triple => x.2.1) h
      change (3 * 3) * (cross3 (rotate a v) (rotate a w)).2.1 =
        3 * (rotationNumerator a (cross3 v w)).2.1 at h1
      change (rotationNumerator a (cross3 v w)).2.1 = 3 * (cross3 (rotate a v) (rotate a w)).2.1
      omega
    · have h1 := congrArg (fun x : Triple => x.2.2) h
      change (3 * 3) * (cross3 (rotate a v) (rotate a w)).2.2 =
        3 * (rotationNumerator a (cross3 v w)).2.2 at h1
      change (rotationNumerator a (cross3 v w)).2.2 = 3 * (cross3 (rotate a v) (rotate a w)).2.2
      omega

theorem admissible_of_rotationNumerator_divisible {a : Axis} {v : Triple}
    (h : TripleDivisible 3 (rotationNumerator a v)) : Admissible a v := by
  have hh := h.1
  rw [rotationNumerator_apply] at hh
  change (3 : ℤ) ∣ 2 * axisDot a v - 3 * v.1 at hh
  change (3 : ℤ) ∣ axisDot a v
  omega

theorem TripleDivisible.exists_smul {d : ℤ} {v : Triple} (hv : TripleDivisible d v) :
    ∃ u : Triple, v = d • u := by
  obtain ⟨a, ha⟩ := hv.1
  obtain ⟨b, hb⟩ := hv.2.1
  obtain ⟨c, hc⟩ := hv.2.2
  exact ⟨(a, b, c), Prod.ext ha (Prod.ext hb hc)⟩

theorem triple_smul_cancel {d : ℤ} (hd : d ≠ 0) {v w : Triple} (h : d • v = d • w) : v = w := by
  apply Prod.ext
  · exact mul_left_cancel₀ hd (congrArg Prod.fst h)
  · apply Prod.ext
    · exact mul_left_cancel₀ hd (congrArg (fun x : Triple => x.2.1) h)
    · exact mul_left_cancel₀ hd (congrArg (fun x : Triple => x.2.2) h)

theorem rotationNumerator_reverse {a : Axis} {v w : Triple}
    (h : rotationNumerator a v = (3 : ℤ) • w) :
    rotationNumerator a w = (3 : ℤ) • v := by
  have hh := congrArg (rotationNumerator a) h
  rw [rotationNumerator_involutive, map_smul] at hh
  apply triple_smul_cancel (by norm_num : (3 : ℤ) ≠ 0)
  rw [← hh, smul_smul]
  rfl

end Erdos941
