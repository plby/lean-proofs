import Wikipedia.HopfProblem.CuspHoneycombTiling
import Wikipedia.HopfProblem.CuspHoneycombHexagonPolygon

/-!
# The linear identification of the standard and dual hexagons

The matrix with rows `(2,1)` and `(-1,1)` sends the literal dual cell to
the standard hexagon used by the six actual component charts.  Its inverse
identifies each standard vertex with the barycenter of the corresponding
actual integral triangle.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

open ToricFan ToricComponent

/-- The determinant-three linear change from the dual cell to the
standard hexagon. -/
def dualStandardLinearEquiv : Plane ≃ₗ[ℝ] Plane where
  toFun x := ![2 * x 0 + x 1, x 1 - x 0]
  invFun y := ![(y 0 - y 1) / 3, (y 0 + 2 * y 1) / 3]
  left_inv x := by
    funext i
    fin_cases i
    · change ((2 * x 0 + x 1) - (x 1 - x 0)) / 3 = x 0
      ring
    · change ((2 * x 0 + x 1) + 2 * (x 1 - x 0)) / 3 = x 1
      ring
  right_inv y := by
    funext i
    fin_cases i
    · change 2 * ((y 0 - y 1) / 3) + (y 0 + 2 * y 1) / 3 = y 0
      ring
    · change (y 0 + 2 * y 1) / 3 - (y 0 - y 1) / 3 = y 1
      ring
  map_add' x y := by
    funext i
    fin_cases i
    · change 2 * (x 0 + y 0) + (x 1 + y 1) = (2 * x 0 + x 1) + (2 * y 0 + y 1)
      ring
    · change (x 1 + y 1) - (x 0 + y 0) = (x 1 - x 0) + (y 1 - y 0)
      ring
  map_smul' a x := by
    funext i
    fin_cases i
    · change 2 * (a * x 0) + a * x 1 = a * (2 * x 0 + x 1)
      ring
    · change a * x 1 - a * x 0 = a * (x 1 - x 0)
      ring

@[simp] theorem dualStandardLinearEquiv_apply (x : Plane) :
    dualStandardLinearEquiv x = ![2 * x 0 + x 1, x 1 - x 0] := rfl

@[simp] theorem dualStandardLinearEquiv_symm_apply (y : Plane) :
    dualStandardLinearEquiv.symm y = ![(y 0 - y 1) / 3, (y 0 + 2 * y 1) / 3] := rfl

/-- The same full-plane linear change, with the ordinary real-plane topology. -/
def dualStandardPlaneHomeomorph : Plane ≃ₜ Plane where
  toEquiv := dualStandardLinearEquiv.toEquiv
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact (continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)
    · exact (continuous_apply 1).sub (continuous_apply 0)
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((continuous_apply 0).sub (continuous_apply 1)).div_const 3
    · exact ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).div_const 3

@[simp] theorem dualStandardPlaneHomeomorph_apply (x : Plane) :
    dualStandardPlaneHomeomorph x = ![2 * x 0 + x 1, x 1 - x 0] := rfl

@[simp] theorem dualStandardPlaneHomeomorph_symm_apply (y : Plane) :
    dualStandardPlaneHomeomorph.symm y =
      ![(y 0 - y 1) / 3, (y 0 + 2 * y 1) / 3] := rfl

theorem dualStandardPlaneHomeomorph_mem_hexagon (x : Plane) :
    dualStandardPlaneHomeomorph x ∈ CuspHoneycombHexagon.Hexagon ↔ x ∈ baseCell := by
  change (|2 * x 0 + x 1| ≤ 1 ∧ |x 1 - x 0| ≤ 1 ∧
    |2 * x 0 + x 1 + (x 1 - x 0)| ≤ 1) ↔ _
  have he : 2 * x 0 + x 1 + (x 1 - x 0) = x 0 + 2 * x 1 := by ring
  rw [he, abs_sub_comm (x 1) (x 0)]
  rfl

theorem dualStandardPlaneHomeomorph_symm_mem_baseCell (y : Plane) :
    dualStandardPlaneHomeomorph.symm y ∈ baseCell ↔ y ∈ CuspHoneycombHexagon.Hexagon := by
  simpa only [Homeomorph.apply_symm_apply] using
    (dualStandardPlaneHomeomorph_mem_hexagon (dualStandardPlaneHomeomorph.symm y)).symm

/-- The standard closed hexagon is homeomorphic to the literal dual cell,
by the displayed inverse linear map. -/
def standardHexagonDualHomeomorph : CuspHoneycombHexagon.Hexagon ≃ₜ baseCell where
  toFun y := ⟨dualStandardPlaneHomeomorph.symm y,
    (dualStandardPlaneHomeomorph_symm_mem_baseCell y).mpr y.2⟩
  invFun x := ⟨dualStandardPlaneHomeomorph x,
    (dualStandardPlaneHomeomorph_mem_hexagon x).mpr x.2⟩
  left_inv y := Subtype.ext (dualStandardPlaneHomeomorph.apply_symm_apply y)
  right_inv x := Subtype.ext (dualStandardPlaneHomeomorph.symm_apply_apply x)
  continuous_toFun :=
    (dualStandardPlaneHomeomorph.symm.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (dualStandardPlaneHomeomorph.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem standardHexagonDualHomeomorph_coe (y : CuspHoneycombHexagon.Hexagon) :
    (standardHexagonDualHomeomorph y : Plane) = dualStandardPlaneHomeomorph.symm y := rfl

@[simp] theorem standardHexagonDualHomeomorph_symm_coe (x : baseCell) :
    (standardHexagonDualHomeomorph.symm x : Plane) = dualStandardPlaneHomeomorph x := rfl

/-- The ordinary arithmetic mean of the three integral vertices of an
actual toric triangle, viewed in the real plane. -/
def triangleBarycenter (s : Triangle) : Plane := fun i =>
  ((s.vertex 0 i : ℝ) + (s.vertex 1 i : ℝ) + (s.vertex 2 i : ℝ)) / 3

theorem triangleBarycenter_zeroTriangle (i : Fin 6) :
    triangleBarycenter (zeroTriangle i) = fun j =>
      ((hexagonRay i j : ℝ) + (hexagonRay (i + 1) j : ℝ)) / 3 := by
  have hs : (zeroTriangle i).vertex 0 + (zeroTriangle i).vertex 1 +
      (zeroTriangle i).vertex 2 = hexagonRay i + hexagonRay (i + 1) := by
    fin_cases i <;> decide
  funext j
  have hj : (zeroTriangle i).vertex 0 j + (zeroTriangle i).vertex 1 j +
      (zeroTriangle i).vertex 2 j = hexagonRay i j + hexagonRay (i + 1) j :=
    congrFun hs j
  have hreal : ((zeroTriangle i).vertex 0 j : ℝ) + ((zeroTriangle i).vertex 1 j : ℝ) +
      ((zeroTriangle i).vertex 2 j : ℝ) =
        (hexagonRay i j : ℝ) + (hexagonRay (i + 1) j : ℝ) := by
    exact_mod_cast hj
  exact congrArg (fun r : ℝ => r / 3) hreal

/-- The standard hexagon's vertex labels agree exactly with the actual
zero-component chart triangles, without a cyclic relabeling. -/
theorem dual_standard_vertex (i : Fin 6) :
    dualStandardPlaneHomeomorph.symm (CuspHoneycombHexagon.vertex i) =
      triangleBarycenter (zeroTriangle i) := by
  have hr : ∀ i : Fin 6,
      hexagonRay (i + 1) 0 = -hexagonRay i 1 ∧
        hexagonRay (i + 1) 1 = hexagonRay i 0 + hexagonRay i 1 := by decide
  rw [triangleBarycenter_zeroTriangle]
  funext j
  fin_cases j
  · change ((hexagonRay i 0 : ℝ) - (hexagonRay i 1 : ℝ)) / 3 =
      ((hexagonRay i 0 : ℝ) + (hexagonRay (i + 1) 0 : ℝ)) / 3
    rw [(hr i).1, Int.cast_neg]
    ring
  · change ((hexagonRay i 0 : ℝ) + 2 * (hexagonRay i 1 : ℝ)) / 3 =
      ((hexagonRay i 1 : ℝ) + (hexagonRay (i + 1) 1 : ℝ)) / 3
    rw [(hr i).2, Int.cast_add]
    ring

end Wikipedia.HopfProblem.CuspHoneycombTiling
