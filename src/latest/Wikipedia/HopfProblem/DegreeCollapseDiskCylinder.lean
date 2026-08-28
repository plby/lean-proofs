import Wikipedia.HopfProblem.DegreeCollapseHandleRetraction

/-!
# A native closed-disk cylinder retracts to its bottom and side

The explicit handle retraction preserves the nonnegative half of its
one-dimensional positive disk. Its restriction gives the relative geometry
needed for disk-boundary homotopy extension, in every dimension.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Disk := closedBall (0 : E) 1
abbrev Sphere := sphere (0 : E) 1

def toHandle : C(I × Disk (E := E), Handle.Space (N := E) (P := ℝ)) where
  toFun p := (p.2, ⟨p.1.val, mem_closedBall_zero_iff.mpr (by
    rw [Real.norm_of_nonneg p.1.property.1]
    exact p.1.property.2)⟩)
  continuous_toFun := continuous_snd.prodMk
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _)

def retractedTime (p : I × Disk (E := E)) : I :=
  ⟨Handle.positiveMultiplier (toHandle p) * p.1.val,
    mul_nonneg (Handle.positiveMultiplier_nonneg _) p.1.property.1,
    (by
      have h := mul_le_mul_of_nonneg_right
        (Handle.positiveMultiplier_le_one (toHandle p)) p.1.property.1
      exact (h.trans_eq (one_mul p.1.val)).trans p.1.property.2)⟩

omit [NormedSpace ℝ E] in
theorem retractedTime_coe (p : I × Disk (E := E)) :
    (retractedTime p : ℝ) = Handle.positive (toHandle p) := rfl

omit [NormedSpace ℝ E] in
theorem continuous_retractedTime : Continuous (retractedTime (E := E)) :=
  (Handle.continuous_positive.comp toHandle.continuous).subtype_mk _

def retractedDisk (p : I × Disk (E := E)) : Disk (E := E) :=
  (Handle.retraction (toHandle p)).1

theorem continuous_retractedDisk : Continuous (retractedDisk (E := E)) :=
  continuous_fst.comp (Handle.retraction.continuous.comp toHandle.continuous)

def bottomOrSide : Set (I × Disk (E := E)) := {p | p.1 = 0 ∨ ‖(p.2 : E)‖ = 1}

theorem retracted_mem_bottomOrSide (p : I × Disk (E := E)) :
    (retractedTime p, retractedDisk p) ∈ bottomOrSide := by
  rcases Handle.retraction_mem_faceCore (toHandle p) with hp | hp
  · exact Or.inr hp
  · apply Or.inl
    apply Subtype.ext
    exact hp

def retraction : C(I × Disk (E := E), bottomOrSide (E := E)) :=
  ⟨fun p => ⟨(retractedTime p, retractedDisk p), retracted_mem_bottomOrSide p⟩,
    (continuous_retractedTime.prodMk continuous_retractedDisk).subtype_mk _⟩

theorem retraction_fixed (p : I × Disk (E := E)) (hp : p ∈ bottomOrSide) :
    (retraction p).val = p := by
  have hh : toHandle p ∈ Handle.faceCore := by
    rcases hp with ht | hx
    · exact Or.inr (congrArg Subtype.val ht)
    · exact Or.inl hx
  have hr := Handle.retraction_eq_self (toHandle p) hh
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : Handle.Space (N := E) (P := ℝ) => (z.2 : ℝ)) hr
  · exact congrArg Prod.fst hr

end Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder
