import Wikipedia.HopfProblem.StandardSixSphereCircleModelBoundary

/-!
# The standard compact exterior as a three-ball times a three-sphere

The complement chart reverses radial inequalities: outside the normal
radius-`r` tube is the closed three-ball of radius `sqrt (1-r²)/r` times `S³`.
The exterior here is a subset of the original standard six-sphere.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel

theorem sqrt_boundaryProductRadius {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Real.sqrt (1 + boundaryProductRadius r ^ 2) = r⁻¹ := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (inv_pos.mpr hr).le).mp
  rw [Real.sq_sqrt (by nlinarith [sq_nonneg (boundaryProductRadius r)]),
    boundaryProductRadius, div_pow, boundaryBaseRadius_sq hr.le hr1.le]
  field_simp
  ring

/-- The larger-normal-radius side is precisely the bounded side of the product chart. -/
theorem le_normalRadius_iff_norm_forward_le {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : Complement) :
    r ≤ normalRadius p ↔ ‖(forward p).1‖ ≤ boundaryProductRadius r := by
  have ha : 0 < 1 + ‖(forward p).1‖ ^ 2 := by nlinarith [sq_nonneg ‖(forward p).1‖]
  have hb : 0 < 1 + boundaryProductRadius r ^ 2 := by
    nlinarith [sq_nonneg (boundaryProductRadius r)]
  calc
    r ≤ normalRadius p ↔
        (Real.sqrt (1 + boundaryProductRadius r ^ 2))⁻¹ ≤
          (Real.sqrt (1 + ‖(forward p).1‖ ^ 2))⁻¹ := by
      rw [sqrt_boundaryProductRadius hr hr1, inv_inv]
      change r ≤ normalRadius p ↔ r ≤ inverseScale (forward p).1
      rw [inverseScale_forward]
    _ ↔ Real.sqrt (1 + ‖(forward p).1‖ ^ 2) ≤
        Real.sqrt (1 + boundaryProductRadius r ^ 2) :=
      inv_le_inv₀ (Real.sqrt_pos.mpr hb) (Real.sqrt_pos.mpr ha)
    _ ↔ ‖(forward p).1‖ ≤ boundaryProductRadius r := by
      rw [Real.sqrt_le_sqrt_iff hb.le, add_le_add_iff_left,
        sq_le_sq₀ (norm_nonneg _) (boundaryProductRadius_pos hr hr1).le]

theorem lt_normalRadius_iff_norm_forward_lt {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : Complement) :
    r < normalRadius p ↔ ‖(forward p).1‖ < boundaryProductRadius r := by
  rw [lt_iff_le_and_ne, le_normalRadius_iff_norm_forward_le hr hr1,
    lt_iff_le_and_ne]
  have he := normalRadius_eq_iff_norm_forward hr hr1 p
  constructor
  · rintro ⟨hle, hne⟩
    exact ⟨hle, fun h => hne (he.mpr h).symm⟩
  · rintro ⟨hle, hne⟩
    exact ⟨hle, fun h => hne (he.mp h.symm)⟩

/-- This closed region is defined on the original sphere, not a replacement space. -/
def closedExterior (r : ℝ) : Set Sphere := {p | r ≤ ‖normal p.val‖}

def exteriorInComplement (r : ℝ) : Set Complement := {p | r ≤ normalRadius p}

def exteriorAsComplement (r : ℝ) (hr : 0 < r) :
    ↥(closedExterior r) ≃ₜ ↥(exteriorInComplement r) where
  toFun p := ⟨⟨p.val, norm_pos_iff.mp (hr.trans_le p.property)⟩, p.property⟩
  invFun p := ⟨p.val.val, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.subtype_mk _).subtype_mk _)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Splitting the literal first-coordinate radius predicate off the product. -/
def productClosedBallHomeomorph (R : ℝ) :
    {q : Base × NormalSphere // ‖q.1‖ ≤ R} ≃ₜ
      ↥(Metric.closedBall (0 : Base) R) × NormalSphere where
  toFun q := (⟨q.val.1, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using q.property⟩, q.val.2)
  invFun q := ⟨(q.1.val, q.2), by
    simpa only [Metric.mem_closedBall, dist_zero_right] using q.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk
    continuous_subtype_val.snd
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk
    continuous_snd).subtype_mk _

/-- The actual standard-sphere exterior is a closed three-ball times the unit `S³`. -/
def closedExteriorHomeomorph (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    ↥(closedExterior r) ≃ₜ
      ↥(Metric.closedBall (0 : Base) (boundaryProductRadius r)) × NormalSphere :=
  (exteriorAsComplement r hr).trans
    ((homeomorph.subtype (le_normalRadius_iff_norm_forward_le hr hr1)).trans
      (productClosedBallHomeomorph (boundaryProductRadius r)))

@[simp] theorem closedExteriorHomeomorph_fst_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ↥(closedExterior r)) :
    (closedExteriorHomeomorph r hr hr1 p).1.val =
      ‖normal p.val.val‖⁻¹ • base p.val.val := rfl

@[simp] theorem closedExteriorHomeomorph_snd_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ↥(closedExterior r)) :
    (closedExteriorHomeomorph r hr hr1 p).2.val =
      ‖normal p.val.val‖⁻¹ • normal p.val.val := rfl

@[simp] theorem closedExteriorHomeomorph_symm_val_val (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1)
    (q : ↥(Metric.closedBall (0 : Base) (boundaryProductRadius r)) × NormalSphere) :
    ((closedExteriorHomeomorph r hr hr1).symm q).val.val =
      inverseScale q.1.val • join q.1.val q.2.val := rfl

end Wikipedia.HopfProblem.StandardSixSphereCircleModel
