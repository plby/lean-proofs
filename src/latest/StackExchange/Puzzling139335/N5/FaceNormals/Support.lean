import StackExchange.Puzzling139335.N5.FaceNormals.Defs
import StackExchange.Puzzling139335.PlaneIsometries

/-!
# Open normal cones have only one support point

These arguments use only pointwise half-plane bounds.  In particular, no
convexity, normal fan, tangent, or regularity assumption is made on the set.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

private theorem nonpos_pair_eq_zero {u v : ℝ}
    (hu : u ≤ 0) (hv : v ≤ 0) (hsum : 0 ≤ u + v) : u = 0 ∧ v = 0 := by
  constructor <;> linarith

private theorem eq_origin_of_open_normal_cone {p : Plane} {nx ny : ℝ}
    (hy : 0 ≤ p 1) (hdiag : p 1 ≤ p 0)
    (hnx : nx < 0) (hsum : nx + ny < 0)
    (hmax : 0 ≤ nx * p 0 + ny * p 1) : p = corner 0 := by
  have hu : nx * (p 0 - p 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hnx.le (sub_nonneg.mpr hdiag)
  have hv : (nx + ny) * p 1 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hsum.le hy
  have huv : 0 ≤ nx * (p 0 - p 1) + (nx + ny) * p 1 := by
    nlinarith only [hmax]
  obtain ⟨hu₀, hv₀⟩ := nonpos_pair_eq_zero hu hv huv
  have hdiff : p 0 - p 1 = 0 :=
    (mul_eq_zero.mp hu₀).resolve_left (ne_of_lt hnx)
  have hy₀ : p 1 = 0 := (mul_eq_zero.mp hv₀).resolve_left (ne_of_lt hsum)
  have hx₀ : p 0 = 0 := by linarith
  apply plane_ext <;> norm_num [corner, Fin.ext_iff, hx₀, hy₀]

private theorem eq_bottom_right_of_open_normal_cone {p : Plane} {nx ny : ℝ}
    (hx : p 0 ≤ 1) (hy : 0 ≤ p 1)
    (hnx : 0 < nx) (hny : ny < 0)
    (hmax : nx ≤ nx * p 0 + ny * p 1) : p = corner 1 := by
  have hu : (-nx) * (1 - p 0) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hx)
  have hv : ny * p 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hny.le hy
  have huv : 0 ≤ (-nx) * (1 - p 0) + ny * p 1 := by
    nlinarith only [hmax]
  obtain ⟨hu₀, hv₀⟩ := nonpos_pair_eq_zero hu hv huv
  have hdiff : 1 - p 0 = 0 :=
    (mul_eq_zero.mp hu₀).resolve_left (by linarith)
  have hy₀ : p 1 = 0 := (mul_eq_zero.mp hv₀).resolve_left (ne_of_lt hny)
  have hx₁ : p 0 = 1 := by linarith
  apply plane_ext <;> norm_num [corner, Fin.ext_iff, hx₁, hy₀]

private theorem eq_corner_point_of_open_normal_cone {p C : Plane} {c s nx ny : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hu : c * (p 0 - C 0) + s * (p 1 - C 1) ≤ 0)
    (hv : (-s) * (p 0 - C 0) + c * (p 1 - C 1) ≤ 0)
    (ha : 0 < c * nx + s * ny) (hb : 0 < (-s) * nx + c * ny)
    (hmax : nx * C 0 + ny * C 1 ≤ nx * p 0 + ny * p 1) : p = C := by
  let u := c * (p 0 - C 0) + s * (p 1 - C 1)
  let v := (-s) * (p 0 - C 0) + c * (p 1 - C 1)
  let a := c * nx + s * ny
  let b := (-s) * nx + c * ny
  have hau : a * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hu
  have hbv : b * v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le hv
  have hid : a * u + b * v = nx * (p 0 - C 0) + ny * (p 1 - C 1) := by
    dsimp [a, b, u, v]
    calc
      _ = (c ^ 2 + s ^ 2) * (nx * (p 0 - C 0) + ny * (p 1 - C 1)) := by ring
      _ = _ := by rw [hcs, one_mul]
  have hsum : 0 ≤ a * u + b * v := by
    rw [hid]
    nlinarith only [hmax]
  obtain ⟨hau₀, hbv₀⟩ := nonpos_pair_eq_zero hau hbv hsum
  have hu₀ : u = 0 := (mul_eq_zero.mp hau₀).resolve_left (ne_of_gt ha)
  have hv₀ : v = 0 := (mul_eq_zero.mp hbv₀).resolve_left (ne_of_gt hb)
  have hx : p 0 - C 0 = 0 := by
    calc
      p 0 - C 0 = (c ^ 2 + s ^ 2) * (p 0 - C 0) := by rw [hcs, one_mul]
      _ = c * u - s * v := by dsimp [u, v]; ring
      _ = 0 := by rw [hu₀, hv₀]; ring
  have hy : p 1 - C 1 = 0 := by
    calc
      p 1 - C 1 = (c ^ 2 + s ^ 2) * (p 1 - C 1) := by rw [hcs, one_mul]
      _ = s * u + c * v := by dsimp [u, v]; ring
      _ = 0 := by rw [hu₀, hv₀]; ring
  exact plane_ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hy)

/-- A normal in the open lower-diagonal cone has the origin as its unique
support point, so it cannot attain a support level at two distinct points. -/
theorem support_normal_not_in_origin_cone {P : Set Plane} {nx ny : ℝ}
    (hP : P ⊆ unitSquare) (hbelow : P ⊆ {p | p 1 ≤ p 0})
    (hA : corner 0 ∈ P) (hface : HasTwoPointSupport P nx ny) :
    ¬ (nx < 0 ∧ nx + ny < 0) := by
  rintro ⟨hnx, hsum⟩
  obtain ⟨m, X, Y, hX, hY, hXY, hbound, hXm, hYm⟩ := hface
  have hm : 0 ≤ m := by
    have h := hbound (corner 0) hA
    norm_num [corner, Fin.ext_iff] at h
    exact h
  have hXA : X = corner 0 := eq_origin_of_open_normal_cone
    (hP hX).2.1 (hbelow hX) hnx hsum (by rw [hXm]; exact hm)
  have hYA : Y = corner 0 := eq_origin_of_open_normal_cone
    (hP hY).2.1 (hbelow hY) hnx hsum (by rw [hYm]; exact hm)
  exact hXY (hXA.trans hYA.symm)

/-- A normal pointing strictly right and down has the bottom-right corner
as its unique support point. -/
theorem support_normal_not_in_bottom_right_cone {P : Set Plane} {nx ny : ℝ}
    (hP : P ⊆ unitSquare) (hB : corner 1 ∈ P)
    (hface : HasTwoPointSupport P nx ny) : ¬ (0 < nx ∧ ny < 0) := by
  rintro ⟨hnx, hny⟩
  obtain ⟨m, X, Y, hX, hY, hXY, hbound, hXm, hYm⟩ := hface
  have hm : nx ≤ m := by
    have h := hbound (corner 1) hB
    norm_num [corner, Fin.ext_iff] at h
    exact h
  have hXB : X = corner 1 := eq_bottom_right_of_open_normal_cone
    (hP hX).1.2 (hP hX).2.1 hnx hny (by rw [hXm]; exact hm)
  have hYB : Y = corner 1 := eq_bottom_right_of_open_normal_cone
    (hP hY).1.2 (hP hY).2.1 hnx hny (by rw [hYm]; exact hm)
  exact hXY (hXB.trans hYB.symm)

/-- Positive combinations of both actual supporting normals at `C` make
`C` the unique support point. -/
theorem support_normal_not_in_corner_cone {P : Set Plane} {C : Plane}
    {c s nx ny : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hC : C ∈ P)
    (hcorner : ∀ p ∈ P,
      c * (p 0 - C 0) + s * (p 1 - C 1) ≤ 0 ∧
      (-s) * (p 0 - C 0) + c * (p 1 - C 1) ≤ 0)
    (hface : HasTwoPointSupport P nx ny) :
    ¬ (0 < c * nx + s * ny ∧ 0 < (-s) * nx + c * ny) := by
  rintro ⟨ha, hb⟩
  obtain ⟨m, X, Y, hX, hY, hXY, hbound, hXm, hYm⟩ := hface
  have hm : nx * C 0 + ny * C 1 ≤ m := hbound C hC
  have hXC : X = C := eq_corner_point_of_open_normal_cone hcs
    (hcorner X hX).1 (hcorner X hX).2 ha hb (by rw [hXm]; exact hm)
  have hYC : Y = C := eq_corner_point_of_open_normal_cone hcs
    (hcorner Y hY).1 (hcorner Y hY).2 ha hb (by rw [hYm]; exact hm)
  exact hXY (hXC.trans hYC.symm)

end Puzzling139335.N5
