import ErdosProblems.Erdos633b.CoordinateTriangle
import ErdosProblems.Erdos633b.Barycentric

/-! A genuine Euclidean coordinate frame with axes at sixty degrees. -/

namespace Erdos633b.Sixty

noncomputable def point (d s t : ℝ) : Plane := !₂[s + t / 2, d * t / 2]

theorem point_zero (d : ℝ) : point d 0 0 = 0 := by
  ext i
  fin_cases i <;> simp [point]

theorem point_linear (d s t : ℝ) :
    point d s t = s • point d 1 0 + t • point d 0 1 := by
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem point_add (d s t u v : ℝ) :
    point d (s + u) (t + v) = point d s t + point d u v := by
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem point_smul (d r s t : ℝ) : point d (r * s) (r * t) = r • point d s t := by
  ext i
  fin_cases i <;> simp [point] <;> ring

theorem point_norm_sq (d : ℝ) (he : d ^ 2 = 3) (s t : ℝ) :
    ‖point d s t‖ ^ 2 = s ^ 2 + s * t + t ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [point, Fin.sum_univ_two]
  change (s + t / 2) ^ 2 + (d * t / 2) ^ 2 = _
  linear_combination (t ^ 2 / 4) * he

theorem point_dist_sq (d : ℝ) (he : d ^ 2 = 3) (s t u v : ℝ) :
    dist (point d s t) (point d u v) ^ 2 =
      (s - u) ^ 2 + (s - u) * (t - v) + (t - v) ^ 2 := by
  have hsub : point d s t - point d u v = point d (s - u) (t - v) := by
    ext i
    fin_cases i <;> simp [point] <;> ring
  rw [dist_eq_norm, hsub, point_norm_sq d he]

theorem point_determinant (d s₀ t₀ s₁ t₁ s₂ t₂ : ℝ) :
    ((s₁ + t₁ / 2) - (s₀ + t₀ / 2)) * (d * t₂ / 2 - d * t₀ / 2) -
      ((s₂ + t₂ / 2) - (s₀ + t₀ / 2)) * (d * t₁ / 2 - d * t₀ / 2) =
      (d / 2) * ((s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀)) := by ring

noncomputable def triangle (d : ℝ) (hd : 0 < d) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hdet : (s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀) ≠ 0) : Triangle :=
  coordinateTriangle (s₀ + t₀ / 2) (d * t₀ / 2) (s₁ + t₁ / 2) (d * t₁ / 2)
    (s₂ + t₂ / 2) (d * t₂ / 2) (by
      rw [point_determinant]
      exact mul_ne_zero (div_pos hd (by norm_num)).ne' hdet)

theorem triangle_points (d : ℝ) (hd : 0 < d) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hdet : (s₁ - s₀) * (t₂ - t₀) - (s₂ - s₀) * (t₁ - t₀) ≠ 0) :
    (triangle d hd s₀ t₀ s₁ t₁ s₂ t₂ hdet).points =
      ![point d s₀ t₀, point d s₁ t₁, point d s₂ t₂] := rfl

noncomputable def frame (d : ℝ) (hd : 0 < d) : Triangle :=
  triangle d hd 0 0 1 0 0 1 (by norm_num)

theorem frame_coords (d : ℝ) (hd : 0 < d) (s t : ℝ) :
    (frame d hd).coord 1 (point d s t) = s ∧ (frame d hd).coord 2 (point d s t) = t := by
  have h0 : (frame d hd).points 0 = 0 := point_zero d
  have hP : point d s t = s • (frame d hd).points 1 + t • (frame d hd).points 2 :=
    point_linear d s t
  rw [hP]
  exact (frame d hd).coord_origin_combination h0 s t

theorem coords_of_points (d : ℝ) (hd : 0 < d) (T : Triangle) (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hp : T.points = ![point d s₀ t₀, point d s₁ t₁, point d s₂ t₂]) (p : Plane) :
    (frame d hd).coord 1 p = s₀ * T.coord 0 p + s₁ * T.coord 1 p + s₂ * T.coord 2 p ∧
      (frame d hd).coord 2 p = t₀ * T.coord 0 p + t₁ * T.coord 1 p + t₂ * T.coord 2 p := by
  have hx := T.affine_scalar_interpolation ((frame d hd).coord 1) p
  have hy := T.affine_scalar_interpolation ((frame d hd).coord 2) p
  rw [hp] at hx hy
  change (frame d hd).coord 1 p =
    (frame d hd).coord 1 (point d s₀ t₀) * T.coord 0 p +
    (frame d hd).coord 1 (point d s₁ t₁) * T.coord 1 p +
    (frame d hd).coord 1 (point d s₂ t₂) * T.coord 2 p at hx
  change (frame d hd).coord 2 p =
    (frame d hd).coord 2 (point d s₀ t₀) * T.coord 0 p +
    (frame d hd).coord 2 (point d s₁ t₁) * T.coord 1 p +
    (frame d hd).coord 2 (point d s₂ t₂) * T.coord 2 p at hy
  rw [(frame_coords d hd s₀ t₀).1, (frame_coords d hd s₁ t₁).1,
    (frame_coords d hd s₂ t₂).1] at hx
  rw [(frame_coords d hd s₀ t₀).2, (frame_coords d hd s₁ t₁).2,
    (frame_coords d hd s₂ t₂).2] at hy
  exact ⟨hx, hy⟩

theorem side_sq_of_points (d : ℝ) (he : d ^ 2 = 3) (T : Triangle)
    (s₀ t₀ s₁ t₁ s₂ t₂ : ℝ)
    (hp : T.points = ![point d s₀ t₀, point d s₁ t₁, point d s₂ t₂]) (i : Fin 3) :
    T.side i ^ 2 =
      (![s₀, s₁, s₂] (i + 1) - ![s₀, s₁, s₂] (i + 2)) ^ 2 +
      (![s₀, s₁, s₂] (i + 1) - ![s₀, s₁, s₂] (i + 2)) *
        (![t₀, t₁, t₂] (i + 1) - ![t₀, t₁, t₂] (i + 2)) +
      (![t₀, t₁, t₂] (i + 1) - ![t₀, t₁, t₂] (i + 2)) ^ 2 := by
  have hv (j : Fin 3) : T.points j = point d (![s₀, s₁, s₂] j) (![t₀, t₁, t₂] j) := by
    rw [hp]
    fin_cases j <;> rfl
  change dist (T.points (i + 1)) (T.points (i + 2)) ^ 2 = _
  rw [hv, hv, point_dist_sq d he]

end Erdos633b.Sixty
