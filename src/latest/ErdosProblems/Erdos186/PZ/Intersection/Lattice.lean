/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# The elementary lattice-overlap step in Pham--Zakharov Theorem 4

The last step of the intersection argument uses only a covering-radius
consequence of the assertion that two full-rank lattices have bounded
covolume.  This file records that consequence precisely and proves the
finite pigeonhole argument which produces a *nonzero* common lattice point
in a sufficiently large translated cube.

No lattice theorem is postulated here: `HasCommonCoveringRadius L₁ L₂ R` is
the explicit conclusion which the determinant/covolume estimates in Lemma
11 must supply.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

/-- The real vector associated with an integral lattice point. -/
def realPoint {d : ℕ} (x : LatticePoint d) : Fin d → ℝ :=
  fun i ↦ (x i : ℝ)

/-- A point lies in the closed coordinate cube of radius `radius` about
`center`. -/
def MemCube {d : ℕ} (center : Fin d → ℝ) (radius : ℝ)
    (x : LatticePoint d) : Prop :=
  ∀ i, |(x i : ℝ) - center i| ≤ radius

/-- The intersection of `L₁` and `L₂` has integral covering radius at
most `R` in the sup norm.  This is a convenient exact form of the bounded
covolume conclusion used after Lemma 11. -/
def HasCommonCoveringRadius {d : ℕ}
    (L₁ L₂ : Set (LatticePoint d)) (R : ℕ) : Prop :=
  ∀ x : LatticePoint d, ∃ y : LatticePoint d,
    y ∈ L₁ ∧ y ∈ L₂ ∧ ∀ i, |y i - x i| ≤ (R : ℤ)

/-- The coordinatewise floor of a real vector. -/
def floorPoint {d : ℕ} (x : Fin d → ℝ) : LatticePoint d :=
  fun i ↦ ⌊x i⌋

lemma floorPoint_error {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    |((floorPoint x i : ℤ) : ℝ) - x i| ≤ 1 := by
  change |((⌊x i⌋ : ℤ) : ℝ) - x i| ≤ 1
  have hle : ((⌊x i⌋ : ℤ) : ℝ) ≤ x i := Int.floor_le (x i)
  have hlt : x i < ((⌊x i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (x i)
  rw [abs_le]
  constructor <;> linarith

/-- The standard integral basis vector in coordinate `i`. -/
def intBasis {d : ℕ} (i : Fin d) : LatticePoint d :=
  fun j ↦ if j = i then 1 else 0

@[simp] theorem intBasis_same {d : ℕ} (i : Fin d) : intBasis i i = 1 := by
  simp [intBasis]

/-- A common covering-radius bound gives two distinct common lattice points
in a translated cube.  The second target is separated from the first by
`2R+1` in one coordinate, so their two radius-`R` approximants cannot
coincide. -/
theorem exists_two_common_points_memCube {d R : ℕ} (hd : 0 < d)
    {L₁ L₂ : Set (LatticePoint d)}
    (hcover : HasCommonCoveringRadius L₁ L₂ R)
    (center : Fin d → ℝ) :
    ∃ y₁ y₂ : LatticePoint d,
      y₁ ∈ L₁ ∧ y₁ ∈ L₂ ∧ y₂ ∈ L₁ ∧ y₂ ∈ L₂ ∧
      y₁ ≠ y₂ ∧ MemCube center (3 * R + 2) y₁ ∧
      MemCube center (3 * R + 2) y₂ := by
  let i₀ : Fin d := ⟨0, hd⟩
  let x₁ : LatticePoint d := floorPoint center
  let x₂ : LatticePoint d :=
    x₁ + (2 * R + 1 : ℕ) • intBasis i₀
  obtain ⟨y₁, hy₁L₁, hy₁L₂, hy₁⟩ := hcover x₁
  obtain ⟨y₂, hy₂L₁, hy₂L₂, hy₂⟩ := hcover x₂
  refine ⟨y₁, y₂, hy₁L₁, hy₁L₂, hy₂L₁, hy₂L₂, ?_, ?_, ?_⟩
  · intro heq
    have h₁ := hy₁ i₀
    have h₂ := hy₂ i₀
    rw [heq] at h₁
    have hx₂coord : x₂ i₀ = x₁ i₀ + (2 * R + 1 : ℕ) := by
      simp [x₂, i₀]
    rw [hx₂coord] at h₂
    have hR : (R : ℤ) ≥ 0 := by positivity
    rw [abs_le] at h₁ h₂
    omega
  · intro i
    have hy := hy₁ i
    have hfloor := floorPoint_error center i
    have hy' : |(y₁ i : ℝ) - (x₁ i : ℝ)| ≤ R := by
      exact_mod_cast hy
    have htri := abs_add_le ((y₁ i : ℝ) - (x₁ i : ℝ))
      ((x₁ i : ℝ) - center i)
    calc
      |(y₁ i : ℝ) - center i| =
          |((y₁ i : ℝ) - (x₁ i : ℝ)) +
            ((x₁ i : ℝ) - center i)| := by congr 1 <;> ring
      _ ≤ |(y₁ i : ℝ) - (x₁ i : ℝ)| +
          |(x₁ i : ℝ) - center i| := htri
      _ ≤ (R : ℝ) + 1 := add_le_add hy' (by simpa [x₁] using hfloor)
      _ ≤ 3 * R + 2 := by
        have hR : (0 : ℝ) ≤ R := by positivity
        push_cast
        linarith
  · intro i
    have hy := hy₂ i
    have hfloor := floorPoint_error center i
    have hy' : |(y₂ i : ℝ) - (x₂ i : ℝ)| ≤ R := by
      exact_mod_cast hy
    have hxshift :
        |(x₂ i : ℝ) - (x₁ i : ℝ)| ≤ (2 * R + 1 : ℕ) := by
      have hxshiftInt : |x₂ i - x₁ i| ≤ (2 * R + 1 : ℕ) := by
        simp only [x₂, Pi.add_apply, nsmul_eq_mul, add_sub_cancel_left]
        change |↑(2 * R + 1) * intBasis i₀ i| ≤ ↑(2 * R + 1)
        by_cases hi : i = i₀
        · subst i
          simp only [intBasis_same, mul_one]
          rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (2 * R + 1 : ℕ))]
        · rw [show intBasis i₀ i = 0 by simp [intBasis, hi]]
          simp only [mul_zero, abs_zero]
          positivity
      exact_mod_cast hxshiftInt
    calc
      |(y₂ i : ℝ) - center i| ≤
          |(y₂ i : ℝ) - (x₂ i : ℝ)| +
            |(x₂ i : ℝ) - (x₁ i : ℝ)| +
            |(x₁ i : ℝ) - center i| := by
          calc
            |(y₂ i : ℝ) - center i| =
                |((y₂ i : ℝ) - (x₂ i : ℝ)) +
                  ((x₂ i : ℝ) - (x₁ i : ℝ)) +
                  ((x₁ i : ℝ) - center i)| := by congr 1 <;> ring
            _ ≤ |(y₂ i : ℝ) - (x₂ i : ℝ)| +
                  |(x₂ i : ℝ) - (x₁ i : ℝ)| +
                  |(x₁ i : ℝ) - center i| := by
                    exact (abs_add_three _ _ _)
      _ ≤ (R : ℝ) + (2 * R + 1 : ℕ) + 1 :=
        add_le_add (add_le_add hy' hxshift) (by simpa [x₁] using hfloor)
      _ = 3 * R + 2 := by push_cast; ring

/-- Consequently a sufficiently large translated cube contains a nonzero
point of both lattices. -/
theorem exists_nonzero_common_point_memCube {d R : ℕ} (hd : 0 < d)
    {L₁ L₂ : Set (LatticePoint d)}
    (hcover : HasCommonCoveringRadius L₁ L₂ R)
    (center : Fin d → ℝ) :
    ∃ y : LatticePoint d,
      y ∈ L₁ ∧ y ∈ L₂ ∧ y ≠ 0 ∧ MemCube center (3 * R + 2) y := by
  obtain ⟨y₁, y₂, hy₁L₁, hy₁L₂, hy₂L₁, hy₂L₂,
    hne, hy₁cube, hy₂cube⟩ :=
    exists_two_common_points_memCube hd hcover center
  by_cases hy₁ : y₁ = 0
  · exact ⟨y₂, hy₂L₁, hy₂L₂, fun hy₂ ↦ hne (hy₁.trans hy₂.symm), hy₂cube⟩
  · exact ⟨y₁, hy₁L₁, hy₁L₂, hy₁, hy₁cube⟩

end

end Erdos186.PZ.Intersection
