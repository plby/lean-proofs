import ErdosProblems.Erdos633.AngleCounting
import Mathlib.Algebra.Ring.Parity

/-!
# Two direction signs for the exceptional triangle tilings

Directions are represented by integer coefficients of two independent angles.
The signs are unchanged by a full turn. Both handednesses of a tile have the
same boundary factor. This file also proves the finite cancellation and
integer-sum statements needed by a geometric boundary ledger.

It does not assert that a `CongruentTiling` has already been converted into
such a ledger; in particular no edge-to-edge hypothesis is silently imposed.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def directionSign (u v : ℤ) (z : ℤ × ℤ) : ℝ :=
  (-1) ^ (u * z.1 + v * z.2)

@[simp] theorem directionSign_zero (u v : ℤ) : directionSign u v 0 = 1 := by
  simp [directionSign]

theorem directionSign_add (u v : ℤ) (z w : ℤ × ℤ) :
    directionSign u v (z + w) = directionSign u v z * directionSign u v w := by
  change (-1 : ℝ) ^ (u * (z.1 + w.1) + v * (z.2 + w.2)) = _
  rw [show u * (z.1 + w.1) + v * (z.2 + w.2) =
    (u * z.1 + v * z.2) + (u * w.1 + v * w.2) by ring,
    zpow_add₀ (by norm_num)]
  rfl

theorem directionSign_cases (u v : ℤ) (z : ℤ × ℤ) :
    directionSign u v z = 1 ∨ directionSign u v z = -1 := by
  rw [directionSign, neg_one_zpow_eq_ite]
  split_ifs <;> simp

@[simp] theorem directionSign_neg (u v : ℤ) (z : ℤ × ℤ) :
    directionSign u v (-z) = directionSign u v z := by
  have h := directionSign_add u v z (-z)
  rw [add_neg_cancel, directionSign_zero] at h
  rcases directionSign_cases u v z with hz | hz <;> rw [hz] at h ⊢ <;> linarith

theorem directionSign_sub (u v : ℤ) (z w : ℤ × ℤ) :
    directionSign u v (z - w) = directionSign u v z * directionSign u v w := by
  rw [sub_eq_add_neg, directionSign_add, directionSign_neg]

@[simp] theorem directionSign_double (u v : ℤ) (z : ℤ × ℤ) :
    directionSign u v (z + z) = 1 := by
  rw [directionSign_add]
  rcases directionSign_cases u v z with hz | hz <;> rw [hz] <;> norm_num

theorem directionSign_add_double (u v : ℤ) (z w : ℤ × ℤ) :
    directionSign u v (z + (w + w)) = directionSign u v z := by
  rw [directionSign_add, directionSign_double, mul_one]

def angleFromCoordinates (α β : ℝ) (z : ℤ × ℤ) : ℝ := z.1 * α + z.2 * β

/-- A full-turn equality fixes both coordinate differences. -/
theorem angle_coordinates_full_turn {α β π₀ : ℝ}
    (hind : IntegerIndependentAngles α β) (p q k : ℤ)
    (hπ : π₀ = p * α + q * β) (z w : ℤ × ℤ)
    (h : angleFromCoordinates α β z = angleFromCoordinates α β w + 2 * k * π₀) :
    z = w + ((k * p, k * q) + (k * p, k * q)) := by
  have hzero : (((z.1 - w.1 - 2 * k * p : ℤ) : ℝ) * α +
      ((z.2 - w.2 - 2 * k * q : ℤ) : ℝ) * β) = 0 := by
    push_cast
    dsimp [angleFromCoordinates] at h
    rw [hπ] at h
    linear_combination h
  obtain ⟨hm, hn⟩ := hind _ _ hzero
  apply Prod.ext
  · change z.1 = w.1 + (k * p + k * p)
    linear_combination hm
  · change z.2 = w.2 + (k * q + k * q)
    linear_combination hn

/-- The sign is independent of the representative modulo a full turn. -/
theorem directionSign_full_turn {α β π₀ : ℝ}
    (hind : IntegerIndependentAngles α β) (p q k u v : ℤ)
    (hπ : π₀ = p * α + q * β) (z w : ℤ × ℤ)
    (h : angleFromCoordinates α β z = angleFromCoordinates α β w + 2 * k * π₀) :
    directionSign u v z = directionSign u v w := by
  rw [angle_coordinates_full_turn hind p q k hπ z w h, directionSign_add_double]

/-- The sign factor for a counterclockwise tile with its c-edge in direction z. -/
theorem directionSign_tile (u v : ℤ) (πc z : ℤ × ℤ)
    (hπ : directionSign u v πc = -1) (a b c : ℝ) :
    a * directionSign u v (z + πc - (0, 1)) +
      b * directionSign u v (z + πc + (1, 0)) + c * directionSign u v z =
    directionSign u v z *
      (c - directionSign u v (0, 1) * a - directionSign u v (1, 0) * b) := by
  simp only [directionSign_sub, directionSign_add, hπ]
  ring

/-- Reflection of the tile gives exactly the same factor. -/
theorem directionSign_tile_reflected (u v : ℤ) (πc z : ℤ × ℤ)
    (hπ : directionSign u v πc = -1) (a b c : ℝ) :
    b * directionSign u v (z + πc - (1, 0)) +
      a * directionSign u v (z + πc + (0, 1)) + c * directionSign u v z =
    directionSign u v z *
      (c - directionSign u v (0, 1) * a - directionSign u v (1, 0) * b) := by
  simp only [directionSign_sub, directionSign_add, hπ]
  ring

theorem directionSign_factor_ne_zero (u v : ℤ) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a < b + c) (hbc : b < a + c) (hca : c < a + b) :
    c - directionSign u v (0, 1) * a - directionSign u v (1, 0) * b ≠ 0 := by
  rcases directionSign_cases u v (0, 1) with h₁ | h₁ <;>
    rcases directionSign_cases u v (1, 0) with h₂ | h₂ <;>
    rw [h₁, h₂] <;> linarith

/-- Paired internal atomic segments cancel without requiring full-edge matching. -/
theorem signed_internal_sum_eq_zero {ι : Type*} [Fintype ι]
    (rev : ι ≃ ι) (f : ι → ℝ) (hopp : ∀ i, f (rev i) = -f i) : ∑ i, f i = 0 := by
  have heq : (∑ i, f (rev i)) = ∑ i, f i := Equiv.sum_comp rev f
  simp_rw [hopp, Finset.sum_neg_distrib] at heq
  linarith only [heq]

theorem directionSign_sum_integer {ι : Type*} [Fintype ι]
    (u v : ℤ) (z : ι → ℤ × ℤ) : ∃ m : ℤ, (m : ℝ) = ∑ i, directionSign u v (z i) := by
  have hi (i : ι) : ∃ m : ℤ, (m : ℝ) = directionSign u v (z i) := by
    rcases directionSign_cases u v (z i) with h | h
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨-1, by simpa using h.symm⟩
  choose m hm using hi
  refine ⟨∑ i, m i, ?_⟩
  push_cast
  exact Finset.sum_congr rfl fun i _ => hm i

/-- A common tile factor yields an integer boundary coefficient. -/
theorem directionSign_boundary_integer {ι : Type*} [Fintype ι]
    (u v : ℤ) (z : ι → ℤ × ℤ) (B D : ℝ)
    (hboundary : B = ∑ i, directionSign u v (z i) * D) :
    ∃ m : ℤ, B = m * D := by
  obtain ⟨m, hm⟩ := directionSign_sum_integer u v z
  refine ⟨m, ?_⟩
  rw [hboundary, ← Finset.sum_mul, ← hm]

end Erdos633
