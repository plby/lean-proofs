import Wikipedia.HopfProblem.DegreeCollapseDiskHomotopyExtension

/-!
# The full disk cylinder and its literal sphere boundary

The affine change of its time coordinate identifies I × D(V) with the
unit ball in the max-norm product ℝ × V. Its full boundary corresponds
exactly to the unit sphere, including zero-dimensional V.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.CylinderBall

open DiskCylinder

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def boundary : Set (I × Disk (E := V)) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ ‖(p.2 : V)‖ = 1}

theorem time_norm_le (t : I) : ‖(2 * t.val - 1 : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [t.property.1, t.property.2]

def forward : C(I × Disk (E := V), Disk (E := ℝ × V)) where
  toFun p := ⟨(2 * p.1.val - 1, p.2.val), mem_closedBall_zero_iff.mpr
    (max_le (time_norm_le p.1) (mem_closedBall_zero_iff.mp p.2.property))⟩
  continuous_toFun :=
    (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
      continuous_const).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def inverseTime (z : Disk (E := ℝ × V)) : I :=
  ⟨(z.val.1 + 1) / 2, by
    have hn : |z.val.1| ≤ 1 := (max_le_iff.mp
      (mem_closedBall_zero_iff.mp z.property)).1
    rcases abs_le.mp hn with ⟨hl, hu⟩
    constructor <;> linarith⟩

def inverseSpace (z : Disk (E := ℝ × V)) : Disk (E := V) :=
  ⟨z.val.2, mem_closedBall_zero_iff.mpr
    ((max_le_iff.mp (mem_closedBall_zero_iff.mp z.property)).2)⟩

def inverse : C(Disk (E := ℝ × V), I × Disk (E := V)) where
  toFun z := (inverseTime z, inverseSpace z)
  continuous_toFun := by
    have ht : Continuous (fun z : Disk (E := ℝ × V) => (z.val.1 + 1) / 2) := by fun_prop
    exact (ht.subtype_mk _).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def homeomorph : (I × Disk (E := V)) ≃ₜ Disk (E := ℝ × V) where
  toFun := forward
  invFun := inverse
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((2 * p.1.val - 1) + 1) / 2 = p.1.val
      ring
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change 2 * ((z.val.1 + 1) / 2) - 1 = z.val.1
      ring
    · rfl
  continuous_toFun := forward.continuous
  continuous_invFun := inverse.continuous

omit [NormedSpace ℝ V] in
theorem norm_eq_one_iff (p : I × Disk (E := V)) :
    ‖((homeomorph (V := V) p).val)‖ = 1 ↔ p ∈ boundary := by
  change max ‖(2 * p.1.val - 1 : ℝ)‖ ‖p.2.val‖ = 1 ↔ _
  constructor
  · intro he
    rcases le_total ‖(2 * p.1.val - 1 : ℝ)‖ ‖p.2.val‖ with h | h
    · exact Or.inr (Or.inr (by rwa [max_eq_right h] at he))
    · rw [max_eq_left h, Real.norm_eq_abs] at he
      have he' : |2 * p.1.val - 1| = |(1 : ℝ)| := by simpa using he
      rcases abs_eq_abs.mp he' with h | h
      · exact Or.inr (Or.inl (Subtype.ext (show p.1.val = (1 : ℝ) by linarith)))
      · exact Or.inl (Subtype.ext (show p.1.val = (0 : ℝ) by linarith))
  · rintro (h | h | h)
    · have ht : p.1.val = 0 := congrArg Subtype.val h
      rw [ht]
      norm_num
      exact mem_closedBall_zero_iff.mp p.2.property
    · have ht : p.1.val = 1 := congrArg Subtype.val h
      rw [ht]
      norm_num
      exact mem_closedBall_zero_iff.mp p.2.property
    · rw [h, max_eq_right (time_norm_le p.1)]

def diskSphereHomeomorph :
    {z : Disk (E := V) // ‖(z : V)‖ = 1} ≃ₜ Sphere (E := V) where
  toFun z := ⟨z.val.val, mem_sphere_zero_iff_norm.mpr z.property⟩
  invFun s := ⟨boundaryToDisk s, mem_sphere_zero_iff_norm.mp s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := boundaryToDisk.continuous.subtype_mk _

/-- The entire boundary of the original cylinder is the literal max-norm sphere. -/
def boundaryHomeomorph : boundary (V := V) ≃ₜ Sphere (E := ℝ × V) :=
  ((homeomorph (V := V)).subtype (fun p => (norm_eq_one_iff p).symm)).trans diskSphereHomeomorph

omit [NormedSpace ℝ V] in
theorem boundaryHomeomorph_coe (p : boundary (V := V)) :
    (boundaryHomeomorph p).val = (homeomorph p.val).val := rfl

omit [NormedSpace ℝ V] in
theorem boundaryHomeomorph_symm_apply (s : Sphere (E := ℝ × V)) :
    (boundaryHomeomorph.symm s).val = homeomorph.symm (boundaryToDisk s) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.CylinderBall
