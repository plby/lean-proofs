import Mathlib

open scoped EuclideanGeometry

namespace Erdos633

structure Triangle where
  a : ℂ
  b : ℂ
  c : ℂ
  nondegenerate : (b - a).re * (c - a).im - (b - a).im * (c - a).re ≠ 0

def Triangle.carrier (T : Triangle) : Set ℂ := convexHull ℝ {T.a, T.b, T.c}

structure TriangleDissection (P : Triangle) (N : ℕ) where
  tile : Fin N → Triangle
  covers : (⋃ i, (tile i).carrier) = P.carrier
  disjoint : Pairwise fun i j =>
    Disjoint (interior (tile i).carrier) (interior (tile j).carrier)

structure CongruentTiling (P R : Triangle) (N : ℕ) extends TriangleDissection P N where
  congruent : ∀ i, ∃ f : ℂ ≃ᵢ ℂ, f '' R.carrier = (tile i).carrier

noncomputable def Triangle.angleA (P : Triangle) : ℝ := ∠ P.b P.a P.c

noncomputable def Triangle.angleB (P : Triangle) : ℝ := ∠ P.a P.b P.c

noncomputable def Triangle.angleC (P : Triangle) : ℝ := ∠ P.a P.c P.b

def ListedNonsquareAngles (P : Triangle) : Prop :=
  P.angleA = P.angleB ∨
  (P.angleC = Real.pi / 2 ∧ ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
    dist P.b P.c / dist P.a P.c = (m : ℝ) / n ∧ ¬ IsSquare (m ^ 2 + n ^ 2)) ∨
  (P.angleA = Real.pi / 6 ∧ P.angleB = Real.pi / 2 ∧ P.angleC = Real.pi / 3) ∨
  (P.angleC = Real.pi / 3 ∧
    ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) ∨
  (P.angleB = 2 * P.angleA ∧
    ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2)) ∨
  (P.angleB = 2 * P.angleA ∧
    ∃ q : ℚ, (q : ℝ) = Real.sin (P.angleA / 2)) ∨
  (P.angleC = P.angleA / 2 + P.angleB ∧ ∃ m n : ℕ, 0 < n ∧
    2 * Real.sin (P.angleA / 4) = (m : ℝ) / n ∧ ¬ IsSquare (2 * n ^ 2 - m ^ 2)) ∨
  (P.angleC = 2 * P.angleA + P.angleB / 2 ∧
    ∃ q : ℚ, (q : ℝ) = Real.sqrt 3 * Real.tan (P.angleA / 2))

theorem erdos_633 (P : Triangle) :
    (∀ (N : ℕ) (R : Triangle), Nonempty (CongruentTiling P R N) → IsSquare N) ↔
      ¬ ∃ Q : Triangle, Q.carrier = P.carrier ∧ ListedNonsquareAngles Q := by
  sorry

end Erdos633
