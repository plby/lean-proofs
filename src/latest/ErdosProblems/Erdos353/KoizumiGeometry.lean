/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0 and strengthened to require convexity. -/
/-
Erdős Problem 353.
Informal authors: Junnosuke Koizumi.
Formal authors: Aristotle, JoshuaB.
Original Lean/Mathlib version: 4.28.0.
Source: https://www.erdosproblems.com/forum/thread/353#post-7085
Exact editor URL: data/urls.yaml, JoshuaB_353_koizumi.
-/
import Mathlib

open RealInnerProductSpace

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos353.Koizumi

/-- (Twice-halved) signed-area magnitude of the triangle `A B C`, i.e. its area, computed via the
cross product of the edge vectors. -/
noncomputable def area2 (A B C : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |(B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)| / 2
/-- The area of the quadrilateral `A B C D` (vertices in order), via the shoelace formula. -/
noncomputable def quadArea (A B C D : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |(A 0 * B 1 - B 0 * A 1) + (B 0 * C 1 - C 0 * B 1)
    + (C 0 * D 1 - D 0 * C 1) + (D 0 * A 1 - A 0 * D 1)| / 2
/-- `A B C` are the vertices of an isosceles triangle of area `1`: the area is `1` and (at least)
two of the three sides have equal length. -/
def IsoscelesTriangleArea1 (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  area2 A B C = 1 ∧ (dist A B = dist A C ∨ dist B A = dist B C ∨ dist C A = dist C B)
/-- `A B C` are the vertices of a right-angled triangle of area `1`: the area is `1` and the angle
at one of the three vertices is a right angle. -/
def RightTriangleArea1 (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  area2 A B C = 1 ∧ (⟪B - A, C - A⟫ = 0 ∨ ⟪A - B, C - B⟫ = 0 ∨ ⟪A - C, B - C⟫ = 0)
/-- The source's algebraic trapezoid conditions. These also allow crossed quadrilaterals;
the public predicate `IsoTrapArea1` below additionally requires convexity. -/
def RawIsoTrapArea1 (A B C D : EuclideanSpace ℝ (Fin 2)) : Prop :=
  quadArea A B C D = 1 ∧
  ((B 0 - A 0) * (C 1 - D 1) = (B 1 - A 1) * (C 0 - D 0)) ∧
  dist A D = dist B C ∧ dist A C = dist B D ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D
noncomputable def orient (A B C : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0)

/-- Vertices form a strictly convex quadrilateral in either cyclic orientation. -/
def ConvexQuad (A B C D : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (0 < orient A B C ∧ 0 < orient B C D ∧ 0 < orient C D A ∧ 0 < orient D A B) ∨
  (orient A B C < 0 ∧ orient B C D < 0 ∧ orient C D A < 0 ∧ orient D A B < 0)

/-- A strictly convex isosceles trapezoid of area one, with `AB` and `DC` as bases. -/
def IsoTrapArea1 (A B C D : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (quadArea A B C D = 1 ∧
  ((B 0 - A 0) * (C 1 - D 1) = (B 1 - A 1) * (C 0 - D 0)) ∧
  dist A D = dist B C ∧ dist A C = dist B D ∧
  A ≠ B ∧ B ≠ C ∧ C ≠ D ∧ D ≠ A ∧ A ≠ C ∧ B ≠ D) ∧ ConvexQuad A B C D

/-- Contraction toward `O` by factor `R⁻¹`. -/
noncomputable def conAt (O : EuclideanSpace ℝ (Fin 2)) (R : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) := O + R⁻¹ • (p - O)

/-- A nonzero-area quadrilateral between two rays and their common contraction is convex. -/
lemma contraction_quad_convex {R : ℝ} (hR : 2 ≤ R)
    (O p q : EuclideanSpace ℝ (Fin 2))
    (harea : quadArea p q (conAt O R q) (conAt O R p) = 1) :
    ConvexQuad p q (conAt O R q) (conAt O R p) := by
  classical
  let c := (p 0 - O 0) * (q 1 - O 1) - (p 1 - O 1) * (q 0 - O 0)
  have ht : 0 < R⁻¹ := inv_pos.mpr (by linarith)
  have ht' : 0 < 1 - R⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  have harea' : quadArea p q (conAt O R q) (conAt O R p) =
      |(1 - (R⁻¹)^2) * c| / 2 := by
    unfold quadArea conAt
    congr 2
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    dsimp [c]
    ring
  have hc : c ≠ 0 := by
    intro h
    rw [harea', h] at harea
    norm_num at harea
  have h₁ : orient p q (conAt O R q) = (1 - R⁻¹) * c := by
    simp only [orient, conAt, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    dsimp [c]
    ring
  have h₂ : orient q (conAt O R q) (conAt O R p) = R⁻¹ * (1 - R⁻¹) * c := by
    simp only [orient, conAt, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    dsimp [c]
    ring
  have h₃ : orient (conAt O R q) (conAt O R p) p = R⁻¹ * (1 - R⁻¹) * c := by
    simp only [orient, conAt, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    dsimp [c]
    ring
  have h₄ : orient (conAt O R p) p q = (1 - R⁻¹) * c := by
    simp only [orient, conAt, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    dsimp [c]
    ring
  unfold ConvexQuad
  rw [h₁, h₂, h₃, h₄]
  rcases lt_or_gt_of_ne hc with hc | hc
  · exact Or.inr ⟨mul_neg_of_pos_of_neg ht' hc,
      mul_neg_of_pos_of_neg (mul_pos ht ht') hc,
      mul_neg_of_pos_of_neg (mul_pos ht ht') hc, mul_neg_of_pos_of_neg ht' hc⟩
  · exact Or.inl ⟨mul_pos ht' hc, mul_pos (mul_pos ht ht') hc,
      mul_pos (mul_pos ht ht') hc, mul_pos ht' hc⟩

end Erdos353.Koizumi
