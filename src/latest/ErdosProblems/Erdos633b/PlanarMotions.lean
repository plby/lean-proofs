import ErdosProblems.Erdos633b.TriquadraticCoordinates

/-! Explicit orthogonal linear maps and the rigid motions in the triquadratic construction. -/

namespace Erdos633b

noncomputable def rotationMap (u v : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := !₂[u * p 0 - v * p 1, v * p 0 + u * p 1]
  map_add' p q := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r p := by ext i; fin_cases i <;> simp <;> ring

noncomputable def reflectionMap (u v : ℝ) : Plane →ₗ[ℝ] Plane where
  toFun p := !₂[u * p 0 + v * p 1, v * p 0 - u * p 1]
  map_add' p q := by ext i; fin_cases i <;> simp <;> ring
  map_smul' r p := by ext i; fin_cases i <;> simp <;> ring

theorem rotationMap_inverse (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (p : Plane) :
    rotationMap u (-v) (rotationMap u v p) = p := by
  ext i
  fin_cases i
  · simp [rotationMap]
    linear_combination p 0 * h
  · simp [rotationMap]
    linear_combination p 1 * h

theorem reflectionMap_involutive (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (p : Plane) :
    reflectionMap u v (reflectionMap u v p) = p := by
  ext i
  fin_cases i
  · simp [reflectionMap]
    linear_combination p 0 * h
  · simp [reflectionMap]
    linear_combination p 1 * h

theorem rotationMap_norm (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (p : Plane) :
    ‖rotationMap u v p‖ = ‖p‖ := by
  have hs : ‖rotationMap u v p‖ ^ 2 = ‖p‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, rotationMap]
    linear_combination (p 0 ^ 2 + p 1 ^ 2) * h
  nlinarith [norm_nonneg (rotationMap u v p), norm_nonneg p]

theorem reflectionMap_norm (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) (p : Plane) :
    ‖reflectionMap u v p‖ = ‖p‖ := by
  have hs : ‖reflectionMap u v p‖ ^ 2 = ‖p‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, reflectionMap]
    linear_combination (p 0 ^ 2 + p 1 ^ 2) * h
  nlinarith [norm_nonneg (reflectionMap u v p), norm_nonneg p]

noncomputable def rotation (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv :=
    { toLinearMap := rotationMap u v
      invFun := rotationMap u (-v)
      left_inv := rotationMap_inverse u v h
      right_inv := fun p => by
        have h' : u ^ 2 + (-v) ^ 2 = 1 := by nlinarith
        simpa using rotationMap_inverse u (-v) h' p }
  norm_map' := rotationMap_norm u v h

noncomputable def reflection (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) : Plane ≃ₗᵢ[ℝ] Plane where
  toLinearEquiv :=
    { toLinearMap := reflectionMap u v
      invFun := reflectionMap u v
      left_inv := reflectionMap_involutive u v h
      right_inv := reflectionMap_involutive u v h }
  norm_map' := reflectionMap_norm u v h

namespace TriquadraticCoordinates

theorem w_components (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) :
    (w s d 0) ^ 2 + (w s d 1) ^ 2 = 1 := by
  simpa [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using unit_w s d hd

noncomputable def mirror (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) : Plane ≃ₗᵢ[ℝ] Plane :=
  reflection (w s d 0) (w s d 1) (w_components s d hd)

noncomputable def turn (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) : Plane ≃ₗᵢ[ℝ] Plane :=
  rotation (-s / 2) (d / 2) (by nlinarith)

theorem mirror_e (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) :
    mirror s d hd !₂[1, 0] = w s d := by
  ext i
  fin_cases i <;> simp [mirror, reflection, reflectionMap]

theorem mirror_z (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) :
    mirror s d hd (z s d) = z s d := by
  ext i
  fin_cases i
  · simp [mirror, reflection, reflectionMap, w, z]
    linear_combination (s ^ 2 * (2 - s ^ 2) / 4) * hd
  · simp [mirror, reflection, reflectionMap, w, z]
    ring

theorem turn_e (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) :
    turn s d hd !₂[1, 0] = !₂[-s / 2, d / 2] := by
  ext i
  fin_cases i <;> simp [turn, rotation, rotationMap]

theorem turn_third_vertex (c s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) :
    bigC c s + turn s d hd ((c ^ 2 * s * (1 - s ^ 2)) • z s d) = centerQ c s d := by
  ext i
  fin_cases i
  · simp [bigC, centerQ, turn, rotation, rotationMap, z]
    linear_combination (c ^ 2 * s ^ 2 * (s ^ 2 - 1) / 4) * hd
  · simp [bigC, centerQ, turn, rotation, rotationMap, z]
    ring

end TriquadraticCoordinates

end Erdos633b
