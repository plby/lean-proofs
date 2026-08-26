import ErdosProblems.Erdos633b.TrapezoidPartition
import ErdosProblems.Erdos633b.CoordinateHalfplanes
import ErdosProblems.Erdos633b.Patch

/-! Closed geometric trapezoids and their exact three-region partition. -/

namespace Erdos633b.TrapezoidPartition

noncomputable def trapezoidSet (T : Triangle) (x y : ℝ) : Set Plane :=
  {v | trapezoid x y (T.coord 1 v) (T.coord 2 v)}

noncomputable def region (T : Triangle) (p q y : ℝ) : Piece → Set Plane
  | .left => {v | 0 ≤ T.coordForm 1 0 v} ∩
      ({v | T.coordForm 0 1 v ≤ y} ∩ {v | T.coordForm y (-p) v ≤ 0})
  | .right => {v | T.coordForm 0 1 v ≤ y} ∩
      ({v | T.coordForm 1 1 v ≤ p + q + y} ∩
        {v | y * (p + q + y) ≤ T.coordForm y (q + y) v})
  | .middle => {v | 0 ≤ T.coordForm 0 1 v} ∩
      ({v | 0 ≤ T.coordForm y (-p) v} ∩
        {v | T.coordForm y (q + y) v ≤ y * (p + q + y)})

theorem mem_region (T : Triangle) (p q y : ℝ) (k : Piece) (v : Plane) :
    v ∈ region T p q y k ↔ closed p q y (T.coord 1 v) (T.coord 2 v) k := by
  cases k <;> simp [region, closed, Triangle.coordForm_apply, neg_mul, ← sub_eq_add_neg]

theorem mem_interior_region (T : Triangle) (p q y : ℝ) (hy : 0 < y) (k : Piece) (v : Plane) :
    v ∈ interior (region T p q y k) ↔ inside p q y (T.coord 1 v) (T.coord 2 v) k := by
  have hxg := T.interior_coordForm_ge 1 0 0 (Or.inl one_ne_zero)
  have hyl := T.interior_coordForm_le 0 1 y (Or.inr one_ne_zero)
  have hyg := T.interior_coordForm_ge 0 1 0 (Or.inr one_ne_zero)
  have hsum := T.interior_coordForm_le 1 1 (p + q + y) (Or.inl one_ne_zero)
  have hll := T.interior_coordForm_le y (-p) 0 (Or.inl hy.ne')
  have hlg := T.interior_coordForm_ge y (-p) 0 (Or.inl hy.ne')
  have hrl := T.interior_coordForm_le y (q + y) (y * (p + q + y)) (Or.inl hy.ne')
  have hrg := T.interior_coordForm_ge y (q + y) (y * (p + q + y)) (Or.inl hy.ne')
  cases k <;> simp only [region, interior_inter, hxg, hyl, hyg, hsum, hll, hlg, hrl, hrg] <;>
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, inside, Triangle.coordForm_apply,
      one_mul, zero_mul, add_zero, zero_add, neg_mul, ← sub_eq_add_neg, sub_neg, sub_pos]

theorem regions_cover (T : Triangle) (p q y : ℝ) (hp : 0 < p) (hq : 0 < q) (hy : 0 < y) :
    (⋃ k : Piece, region T p q y k) = trapezoidSet T (p + q) y := by
  ext v
  simp only [Set.mem_iUnion, mem_region, trapezoidSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk⟩
    exact closed_subset p q y hp hq hy _ _ k hk
  · exact exists_closed p q y _ _

theorem regions_disjoint_interiors (T : Triangle) (p q y : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hy : 0 < y) :
    Pairwise fun k l => Disjoint (interior (region T p q y k)) (interior (region T p q y l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro v hk hl
  exact hkl (inside_unique p q y hp hq hy _ _ k l
    ((mem_interior_region T p q y hy k v).mp hk)
    ((mem_interior_region T p q y hy l v).mp hl))

noncomputable def assemble (T R : Triangle) (p q y : ℝ) (hp : 0 < p) (hq : 0 < q) (hy : 0 < y)
    (n : Piece → ℕ) (d : ∀ k, Patch R (region T p q y k) (n k)) :
    Patch R (trapezoidSet T (p + q) y) (∑ k, n k) := by
  have result := Patch.glue R (region T p q y) n d (regions_disjoint_interiors T p q y hp hq hy)
  rwa [regions_cover T p q y hp hq hy] at result

end Erdos633b.TrapezoidPartition
