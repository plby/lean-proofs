import ErdosProblems.Erdos941.Rotations

/-! # Finite integral spheres and their admissible words -/

namespace Erdos941

private theorem coordinate_bounds {x : ℤ} {n : ℕ} (h : x ^ 2 ≤ n) :
    -(n : ℤ) ≤ x ∧ x ≤ n := by
  have hn : (n : ℤ) ≤ (n : ℤ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have hn' : 1 ≤ (n : ℤ) := by exact_mod_cast hn
      nlinarith
  exact abs_le.mp (abs_le_of_sq_le_sq (h.trans hn) (Nat.cast_nonneg n))

noncomputable def spherePoints (n : ℕ) : Finset Triple :=
  ((Finset.Icc (-(n : ℤ)) n).product
    ((Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n))).filter
      fun v => tripleNorm v = n

@[simp] theorem mem_spherePoints {n : ℕ} {v : Triple} :
    v ∈ spherePoints n ↔ tripleNorm v = n := by
  refine ⟨fun h => (Finset.mem_filter.mp h).2, fun h => ?_⟩
  have hA : v.1 ^ 2 ≤ n := by
    dsimp [tripleNorm, norm3] at h
    nlinarith [sq_nonneg v.2.1, sq_nonneg v.2.2]
  have hB : v.2.1 ^ 2 ≤ n := by
    dsimp [tripleNorm, norm3] at h
    nlinarith [sq_nonneg v.1, sq_nonneg v.2.2]
  have hC : v.2.2 ^ 2 ≤ n := by
    dsimp [tripleNorm, norm3] at h
    nlinarith [sq_nonneg v.1, sq_nonneg v.2.1]
  apply Finset.mem_filter.mpr
  refine ⟨?_, h⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (coordinate_bounds hA),
    Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (coordinate_bounds hB),
      Finset.mem_Icc.mpr (coordinate_bounds hC)⟩⟩

noncomputable def sphereCount (n : ℕ) : ℕ := (spherePoints n).card

theorem rotate_mem_spherePoints {n : ℕ} {a : Axis} {v : Triple}
    (hv : v ∈ spherePoints n) (ha : Admissible a v) : rotate a v ∈ spherePoints n := by
  rw [mem_spherePoints, rotate_norm ha]
  exact mem_spherePoints.mp hv

def FollowsWord : List Axis → Triple → Prop
  | [], _ => True
  | a :: w, v => Admissible a v ∧ FollowsWord w (rotate a v)

def wordEndpoint : List Axis → Triple → Triple
  | [], v => v
  | a :: w, v => wordEndpoint w (rotate a v)

theorem wordEndpoint_norm {w : List Axis} {v : Triple} (h : FollowsWord w v) :
    tripleNorm (wordEndpoint w v) = tripleNorm v := by
  induction w generalizing v with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := h
    exact (ih hw).trans (rotate_norm ha)

/-- A reduced word with a prescribed incoming label. -/
def ReducedAfter : Axis → List Axis → Prop
  | _, [] => True
  | a, b :: w => b ≠ a ∧ ReducedAfter b w

theorem exists_reduced_word (k : ℕ) {v : Triple} (hv : tripleNorm v % 3 = 2)
    (a : Axis) : ∃ w : List Axis, w.length = k ∧ FollowsWord w v ∧ ReducedAfter a w := by
  induction k generalizing v a with
  | zero => exact ⟨[], rfl, trivial, trivial⟩
  | succ k ih =>
    obtain ⟨b, hb, hba⟩ := exists_other_admissible hv a
    have hnext : tripleNorm (rotate b v) % 3 = 2 := by rwa [rotate_norm hb]
    obtain ⟨w, hwlen, hw, hred⟩ := ih hnext b
    exact ⟨b :: w, by simp only [List.length_cons, hwlen], ⟨hb, hw⟩, ⟨hba, hred⟩⟩

theorem reduced_word_unique {k : ℕ} {v : Triple} (hv : tripleNorm v % 3 = 2)
    {a : Axis} (ha : Admissible a v) {w₁ w₂ : List Axis}
    (hl₁ : w₁.length = k) (hl₂ : w₂.length = k)
    (hf₁ : FollowsWord w₁ v) (hf₂ : FollowsWord w₂ v)
    (hr₁ : ReducedAfter a w₁) (hr₂ : ReducedAfter a w₂) : w₁ = w₂ := by
  induction k generalizing v a w₁ w₂ with
  | zero =>
    have h₁ := List.length_eq_zero_iff.mp hl₁
    have h₂ := List.length_eq_zero_iff.mp hl₂
    exact h₁.trans h₂.symm
  | succ k ih =>
    cases w₁ with
    | nil => simp at hl₁
    | cons b w₁ =>
      cases w₂ with
      | nil => simp at hl₂
      | cons c w₂ =>
        have hbc : b = c := (existsUnique_other_admissible hv ha).unique
          ⟨hf₁.1, hr₁.1⟩ ⟨hf₂.1, hr₂.1⟩
        subst c
        congr 1
        apply ih (by rwa [rotate_norm hf₁.1]) (rotate_admissible hf₁.1)
          (by simpa using hl₁) (by simpa using hl₂) hf₁.2 hf₂.2 hr₁.2 hr₂.2

end Erdos941
