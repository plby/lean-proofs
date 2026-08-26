import ErdosProblems.Erdos633b.CoordinateHalfplanes
import ErdosProblems.Erdos633b.TriquadraticPartition
import ErdosProblems.Erdos633b.Patch

/-! A genuine closed-set partition of a Euclidean triangle into the four coarse regions. -/

namespace Erdos633b.TriquadraticPartition

noncomputable def region (T : Triangle) (t : ℝ) : Piece → Set Plane
  | .first => {p | 0 ≤ T.coordForm 1 0 p} ∩
      ({p | T.coordForm 1 (-t) p ≤ 0} ∩ {p | T.coordForm 1 (t ^ 2) p ≤ t ^ 2})
  | .second => {p | 0 ≤ T.coordForm 0 1 p} ∩
      ({p | 0 ≤ T.coordForm 1 (-t) p} ∩ {p | T.coordForm 1 1 p ≤ t})
  | .third => {p | t ≤ T.coordForm 0 (1 + t) p} ∩
      ({p | t ^ 2 ≤ T.coordForm 1 (t ^ 2) p} ∩ {p | T.coordForm 1 1 p ≤ 1})
  | .parallelogram => {p | 0 ≤ T.coordForm 0 1 p} ∩
      ({p | T.coordForm 0 (1 + t) p ≤ t} ∩
        ({p | t ≤ T.coordForm 1 1 p} ∩ {p | T.coordForm 1 1 p ≤ 1}))

theorem mem_region (T : Triangle) (t : ℝ) (k : Piece) (p : Plane) :
    p ∈ region T t k ↔ Closed t k (T.coord 1 p) (T.coord 2 p) := by
  cases k <;> simp [region, Closed, Triangle.coordForm_apply, neg_mul, ← sub_eq_add_neg]

theorem mem_interior_region (T : Triangle) (t : ℝ) (ht : 0 < t) (k : Piece) (p : Plane) :
    p ∈ interior (region T t k) ↔ Inside t k (T.coord 1 p) (T.coord 2 p) := by
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  have ht' : 1 + t ≠ 0 := by linarith
  have hl (b c : ℝ) := T.interior_coordForm_le 1 b c (Or.inl h1)
  have hg (b c : ℝ) := T.interior_coordForm_ge 1 b c (Or.inl h1)
  have hyl := T.interior_coordForm_le 0 (1 + t) t (Or.inr ht')
  have hyg := T.interior_coordForm_ge 0 (1 + t) t (Or.inr ht')
  have hy := T.interior_coordForm_ge 0 1 0 (Or.inr h1)
  cases k <;> simp only [region, interior_inter, hl, hg, hyl, hyg, hy] <;>
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Inside, Triangle.coordForm_apply,
      one_mul, zero_mul, add_zero, zero_add, neg_mul, ← sub_eq_add_neg, sub_neg, sub_pos]

theorem regions_cover (T : Triangle) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (⋃ k : Piece, region T t k) = T.support := by
  ext p
  simp only [Set.mem_iUnion, mem_region, Triangle.mem_support_iff_coords]
  constructor
  · rintro ⟨k, hk⟩
    exact closed_subset t ht ht1 k hk
  · rintro ⟨hx, hy, hxy⟩
    exact exists_closed t ht ht1 (T.coord 1 p) (T.coord 2 p) hx hy hxy

theorem regions_disjoint_interiors (T : Triangle) (t : ℝ) (ht : 0 < t) :
    Pairwise fun k l => Disjoint (interior (region T t k)) (interior (region T t l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro p hk hl
  exact hkl (inside_unique t k l ((mem_interior_region T t ht k p).mp hk)
    ((mem_interior_region T t ht l p).mp hl))

/-- Vertex coordinates identify the support of the first enlarged triangle. -/
theorem first_support_of_vertices (T S : Triangle) (t q : ℝ) (ht : 0 < t) (hq : 0 < q)
    (he : (1 + t) * q = t)
    (hx : ∀ i, T.coord 1 (S.points i) = ![0, 0, t * q] i)
    (hy : ∀ i, T.coord 2 (S.points i) = ![0, 1, q] i) :
    S.support = region T t .first := by
  have hpx (p : Plane) : T.coord 1 p = t * q * S.coord 2 p := by
    simpa [hx] using S.affine_scalar_interpolation (T.coord 1) p
  have hpy (p : Plane) : T.coord 2 p = S.coord 1 p + q * S.coord 2 p := by
    simpa [hy] using S.affine_scalar_interpolation (T.coord 2) p
  ext p
  rw [Triangle.mem_support_iff_coords, mem_region, hpx, hpy, first_coordinates t q ht hq he]

/-- Vertex coordinates identify the support of the reflected enlarged triangle. -/
theorem second_support_of_vertices (T S : Triangle) (t q : ℝ) (ht : 0 < t) (hq : 0 < q)
    (he : (1 + t) * q = t)
    (hx : ∀ i, T.coord 1 (S.points i) = ![0, t, t * q] i)
    (hy : ∀ i, T.coord 2 (S.points i) = ![0, 0, q] i) :
    S.support = region T t .second := by
  have hpx (p : Plane) : T.coord 1 p = t * S.coord 1 p + t * q * S.coord 2 p := by
    simpa [hx] using S.affine_scalar_interpolation (T.coord 1) p
  have hpy (p : Plane) : T.coord 2 p = q * S.coord 2 p := by
    simpa [hy] using S.affine_scalar_interpolation (T.coord 2) p
  ext p
  rw [Triangle.mem_support_iff_coords, mem_region, hpx, hpy, second_coordinates t q ht hq he]

/-- Vertex coordinates identify the support of the third enlarged triangle. -/
theorem third_support_of_vertices (T S : Triangle) (t q : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hq : 0 < q) (he : (1 + t) * q = t)
    (hx : ∀ i, T.coord 1 (S.points i) = ![0, 1 - q, t * q] i)
    (hy : ∀ i, T.coord 2 (S.points i) = ![1, q, q] i) :
    S.support = region T t .third := by
  have hpx (p : Plane) : T.coord 1 p = (1 - q) * S.coord 1 p + t * q * S.coord 2 p := by
    simpa [hx] using S.affine_scalar_interpolation (T.coord 1) p
  have hpy (p : Plane) : T.coord 2 p = 1 - (1 - q) * (S.coord 1 p + S.coord 2 p) := by
    have h : T.coord 2 p = S.coord 0 p + q * S.coord 1 p + q * S.coord 2 p := by
      simpa [hy] using S.affine_scalar_interpolation (T.coord 2) p
    nlinarith [S.coord_sum p]
  ext p
  rw [Triangle.mem_support_iff_coords, mem_region, hpx, hpy, third_coordinates t q ht ht1 hq he]

/-- Any congruent subdivisions of these four regions assemble to a triangle tiling. -/
noncomputable def assemblePatch (T R : Triangle) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (n : Piece → ℕ) (d : ∀ k, Patch R (region T t k) (n k)) : Patch R T.support (∑ k, n k) := by
  have result := Patch.glue R (region T t) n d (regions_disjoint_interiors T t ht)
  rw [regions_cover T t ht ht1] at result
  exact result

noncomputable def assemble (T R : Triangle) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (n : Piece → ℕ) (d : ∀ k, Patch R (region T t k) (n k)) : Tiling T (∑ k, n k) :=
  (assemblePatch T R t ht ht1 n d).toTiling

end Erdos633b.TriquadraticPartition
