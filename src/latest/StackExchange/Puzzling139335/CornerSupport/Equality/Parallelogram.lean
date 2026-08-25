import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Convex hulls of parallelograms and orthogonal rectangles

These lemmas only use the four vertices and a containing coordinate box.
They are independent of the support-corner geometry used to produce that box.
-/

open Set

namespace Puzzling139335.CornerSupport.Equality

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Two successive segment interpolations stay in the hull of the four vertices. -/
theorem mem_convexHull_parallelogram (a u v : E) {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    a + t • u + s • v ∈ convexHull ℝ ({a, a + u, a + u + v, a + v} : Set E) := by
  let V : Set E := {a, a + u, a + u + v, a + v}
  have ha : a ∈ convexHull ℝ V := subset_convexHull ℝ V (by simp [V])
  have hau : a + u ∈ convexHull ℝ V := subset_convexHull ℝ V (by simp [V])
  have hauv : a + u + v ∈ convexHull ℝ V := subset_convexHull ℝ V (by simp [V])
  have hav : a + v ∈ convexHull ℝ V := subset_convexHull ℝ V (by simp [V])
  have hconv := convex_convexHull ℝ V
  have hbottom : a + t • u ∈ convexHull ℝ V := hconv.add_smul_mem ha hau ht
  have htop : a + t • u + v ∈ convexHull ℝ V := by
    rw [add_right_comm a (t • u) v]
    apply hconv.add_smul_mem hav _ ht
    rw [add_right_comm a v u]
    exact hauv
  exact hconv.add_smul_mem hbottom htop hs

/-- A set containing the vertices and contained in their parametrized
parallelogram has the same convex hull as the vertices. -/
theorem convexHull_eq_parallelogram_of_parametrization (P : Set E) (a u v : E)
    (ha : a ∈ P) (hau : a + u ∈ P) (hauv : a + u + v ∈ P) (hav : a + v ∈ P)
    (hP : ∀ x ∈ P, ∃ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
      x = a + t • u + s • v) :
    convexHull ℝ P = convexHull ℝ ({a, a + u, a + u + v, a + v} : Set E) := by
  apply Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    obtain ⟨t, ht, s, hs, rfl⟩ := hP x hx
    exact mem_convexHull_parallelogram a u v ht hs
  · apply convexHull_mono
    intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hau
    · exact hauv
    · exact hav

end Module

/-- The convex hull of a set containing the four corners of a positive
orthogonal rectangle and satisfying its coordinate bounds is that rectangle. -/
theorem convexHull_eq_rectangle_of_orthonormal_bounds (P : Set Plane) (a : Plane)
    (B : OrthonormalBasis (Fin 2) ℝ Plane) (W H : ℝ) (hW : 0 < W) (hH : 0 < H)
    (ha : a ∈ P) (haW : a + W • B 0 ∈ P)
    (haWH : a + W • B 0 + H • B 1 ∈ P) (haH : a + H • B 1 ∈ P)
    (hP : ∀ x ∈ P, inner ℝ (B 0) (x - a) ∈ Icc (0 : ℝ) W ∧
      inner ℝ (B 1) (x - a) ∈ Icc (0 : ℝ) H) :
    convexHull ℝ P =
      convexHull ℝ ({a, a + W • B 0, a + W • B 0 + H • B 1,
        a + H • B 1} : Set Plane) := by
  apply convexHull_eq_parallelogram_of_parametrization P a (W • B 0) (H • B 1)
    ha haW haWH haH
  intro x hx
  obtain ⟨h0, h1⟩ := hP x hx
  refine ⟨inner ℝ (B 0) (x - a) / W, ?_, inner ℝ (B 1) (x - a) / H, ?_, ?_⟩
  · exact ⟨div_nonneg h0.1 hW.le, (div_le_one hW).mpr h0.2⟩
  · exact ⟨div_nonneg h1.1 hH.le, (div_le_one hH).mpr h1.2⟩
  · rw [smul_smul, smul_smul, div_mul_cancel₀ _ hW.ne', div_mul_cancel₀ _ hH.ne']
    have hrepr := B.sum_repr' (x - a)
    simp only [Fin.sum_univ_two] at hrepr
    calc
      x = a + (x - a) := by abel
      _ = a + (inner ℝ (B 0) (x - a) • B 0 +
        inner ℝ (B 1) (x - a) • B 1) := by rw [hrepr]
      _ = _ := by rw [add_assoc]

end Puzzling139335.CornerSupport.Equality
