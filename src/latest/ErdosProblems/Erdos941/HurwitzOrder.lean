import Mathlib.Algebra.Quaternion
import Mathlib.Tactic

/-!
# The Hurwitz quaternion order

Coordinates are taken in the integral basis `1, i, j, (1+i+j+k)/2`.
-/

namespace Erdos941

open scoped Quaternion

def hurwitzCoordinates (a b c d : ℤ) : ℍ[ℚ] :=
  ⟨a + (d : ℚ) / 2, b + (d : ℚ) / 2, c + (d : ℚ) / 2, (d : ℚ) / 2⟩

theorem hurwitzCoordinates_add (a b c d e f g h : ℤ) :
    hurwitzCoordinates a b c d + hurwitzCoordinates e f g h =
      hurwitzCoordinates (a + e) (b + f) (c + g) (d + h) := by
  apply Quaternion.ext
  · rw [Quaternion.re_add]
    dsimp [hurwitzCoordinates]
    push_cast
    ring
  · rw [Quaternion.imI_add]
    dsimp [hurwitzCoordinates]
    push_cast
    ring
  · rw [Quaternion.imJ_add]
    dsimp [hurwitzCoordinates]
    push_cast
    ring
  · rw [Quaternion.imK_add]
    dsimp [hurwitzCoordinates]
    push_cast
    ring

theorem hurwitzCoordinates_neg (a b c d : ℤ) :
    -hurwitzCoordinates a b c d = hurwitzCoordinates (-a) (-b) (-c) (-d) := by
  apply Quaternion.ext
  · rw [Quaternion.re_neg]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imI_neg]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imJ_neg]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imK_neg]; dsimp [hurwitzCoordinates]; push_cast; ring

theorem hurwitzCoordinates_star (a b c d : ℤ) :
    star (hurwitzCoordinates a b c d) = hurwitzCoordinates (a + d) (-b) (-c) (-d) := by
  apply Quaternion.ext
  · rw [Quaternion.re_star]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imI_star]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imJ_star]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imK_star]; dsimp [hurwitzCoordinates]; push_cast; ring

theorem hurwitzCoordinates_mul (a b c d e f g h : ℤ) :
    hurwitzCoordinates a b c d * hurwitzCoordinates e f g h =
      hurwitzCoordinates
        (a * e - b * f - c * g - b * h - d * g - d * h - b * g + c * f)
        (a * f + b * e - b * g + c * f + c * h + d * f - d * g)
        (a * g + c * e - b * g + c * f - b * h + c * h + d * f)
        (a * h + d * e + 2 * b * g - 2 * c * f + b * h - c * h - d * f + d * g + d * h) := by
  apply Quaternion.ext
  · rw [Quaternion.re_mul]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imI_mul]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imJ_mul]; dsimp [hurwitzCoordinates]; push_cast; ring
  · rw [Quaternion.imK_mul]; dsimp [hurwitzCoordinates]; push_cast; ring

def hurwitzOrder : Subring ℍ[ℚ] where
  carrier := {q | ∃ a b c d : ℤ, q = hurwitzCoordinates a b c d}
  zero_mem' := ⟨0, 0, 0, 0, by ext <;> simp [hurwitzCoordinates]⟩
  one_mem' := ⟨1, 0, 0, 0, by ext <;> simp [hurwitzCoordinates]⟩
  add_mem' := by
    rintro q r ⟨a, b, c, d, rfl⟩ ⟨e, f, g, h, rfl⟩
    exact ⟨a + e, b + f, c + g, d + h, hurwitzCoordinates_add a b c d e f g h⟩
  neg_mem' := by
    rintro q ⟨a, b, c, d, rfl⟩
    exact ⟨-a, -b, -c, -d, hurwitzCoordinates_neg a b c d⟩
  mul_mem' := by
    rintro q r ⟨a, b, c, d, rfl⟩ ⟨e, f, g, h, rfl⟩
    exact ⟨_, _, _, _, hurwitzCoordinates_mul a b c d e f g h⟩

theorem hurwitz_star_mem {q : ℍ[ℚ]} (h : q ∈ hurwitzOrder) :
    star q ∈ hurwitzOrder := by
  obtain ⟨a, b, c, d, rfl⟩ := h
  exact ⟨a + d, -b, -c, -d, hurwitzCoordinates_star a b c d⟩

theorem hurwitzCoordinates_norm (a b c d : ℤ) :
    Quaternion.normSq (hurwitzCoordinates a b c d) =
      ((a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) * d + d ^ 2 : ℤ) : ℚ) := by
  rw [Quaternion.normSq_def']
  dsimp [hurwitzCoordinates]
  push_cast
  ring

theorem hurwitz_norm_integral {q : ℍ[ℚ]} (h : q ∈ hurwitzOrder) :
    ∃ n : ℕ, Quaternion.normSq q = n := by
  obtain ⟨a, b, c, d, rfl⟩ := h
  let k : ℤ := a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) * d + d ^ 2
  have hk : Quaternion.normSq (hurwitzCoordinates a b c d) = (k : ℚ) :=
    hurwitzCoordinates_norm a b c d
  have hkpos : 0 ≤ k := by
    have hh := Quaternion.normSq_nonneg (a := hurwitzCoordinates a b c d)
    rw [hk] at hh
    exact_mod_cast hh
  lift k to ℕ using hkpos with n hn
  exact ⟨n, by simpa using hk⟩

theorem integralQuaternion_mem (a b c d : ℤ) :
    (⟨(a : ℚ), (b : ℚ), (c : ℚ), (d : ℚ)⟩ : ℍ[ℚ]) ∈ hurwitzOrder := by
  refine ⟨a - d, b - d, c - d, 2 * d, ?_⟩
  ext <;> simp [hurwitzCoordinates] <;> ring

noncomputable def hurwitzNorm (q : hurwitzOrder) : ℕ :=
  (hurwitz_norm_integral q.property).choose

theorem hurwitzNorm_cast (q : hurwitzOrder) :
    (hurwitzNorm q : ℚ) = Quaternion.normSq (q : ℍ[ℚ]) :=
  (hurwitz_norm_integral q.property).choose_spec.symm

theorem hurwitzNorm_mul (q r : hurwitzOrder) :
    hurwitzNorm (q * r) = hurwitzNorm q * hurwitzNorm r := by
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_mul, hurwitzNorm_cast, hurwitzNorm_cast, hurwitzNorm_cast]
  exact Quaternion.normSq.map_mul _ _

theorem hurwitzNorm_eq_zero (q : hurwitzOrder) : hurwitzNorm q = 0 ↔ q = 0 := by
  rw [← Nat.cast_eq_zero (R := ℚ), hurwitzNorm_cast, Quaternion.normSq_eq_zero]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

end Erdos941
