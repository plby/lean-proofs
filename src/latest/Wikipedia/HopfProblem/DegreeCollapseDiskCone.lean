import Wikipedia.HopfProblem.DegreeCollapseDiskHomotopyExtension
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# A sphere nullhomotopy extends over the literal closed disk

Radial multiplication maps the sphere cylinder onto the closed disk, with
exactly the entire zero-time slice identified. Compactness makes this a
genuine quotient, so a nullhomotopy descends continuously even at the center.
-/

noncomputable section

open Set Metric Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskCone

open DiskCylinder NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radial : C(I × Sphere (E := E), Disk (E := E)) where
  toFun p := ⟨p.1.val • p.2.val, mem_closedBall_zero_iff.mpr (by
    rw [norm_smul, Real.norm_of_nonneg p.1.property.1,
      mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
    exact p.1.property.2)⟩
  continuous_toFun := ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem radial_norm (p : I × Sphere (E := E)) : ‖(radial p : E)‖ = p.1.val := by
  change ‖p.1.val • p.2.val‖ = p.1.val
  rw [norm_smul, Real.norm_of_nonneg p.1.property.1,
    mem_sphere_zero_iff_norm.mp p.2.property, mul_one]

@[simp] theorem radial_one (s : Sphere (E := E)) : radial (1, s) = boundaryToDisk s :=
  Subtype.ext (one_smul ℝ s.val)

@[simp] theorem radial_zero (s : Sphere (E := E)) :
    radial (0, s) = (⟨0, by simp⟩ : Disk (E := E)) := Subtype.ext (zero_smul ℝ s.val)

theorem radial_surjective (s0 : Sphere (E := E)) : Function.Surjective (radial (E := E)) := by
  intro z
  by_cases hz : z.val = 0
  · exact ⟨(0, s0), (radial_zero s0).trans (Subtype.ext hz.symm)⟩
  · let t : I := ⟨‖z.val‖, norm_nonneg _, mem_closedBall_zero_iff.mp z.property⟩
    let s : Sphere (E := E) := ⟨normalize z.val, mem_sphere_zero_iff_norm.mpr (norm_normalize hz)⟩
    exact ⟨(t, s), Subtype.ext (norm_smul_normalize z.val)⟩

theorem radial_eq_iff (p q : I × Sphere (E := E)) :
    radial p = radial q ↔ p = q ∨ p.1 = 0 ∧ q.1 = 0 := by
  constructor
  · intro h
    have ht : p.1 = q.1 := Subtype.ext
      ((radial_norm p).symm.trans ((congrArg (fun z : Disk (E := E) => ‖(z : E)‖) h).trans
        (radial_norm q)))
    by_cases hp : p.1 = 0
    · exact Or.inr ⟨hp, ht.symm.trans hp⟩
    · left
      apply Prod.ext ht
      apply Subtype.ext
      have hn : p.1.val ≠ 0 := fun he => hp (Subtype.ext he)
      have hv : p.1.val • p.2.val = q.1.val • q.2.val := congrArg Subtype.val h
      rw [← ht] at hv
      exact (smul_right_inj hn).mp hv
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · change radial (p.1, p.2) = radial (q.1, q.2)
      rw [hp, hq, radial_zero, radial_zero]

variable [FiniteDimensional ℝ E]

theorem radial_isQuotientMap (s0 : Sphere (E := E)) : IsQuotientMap (radial (E := E)) :=
  .of_surjective_continuous (radial_surjective s0) radial.continuous

variable {X : Type*} [TopologicalSpace X] (s0 : Sphere (E := E))
  (G : C(I × Sphere (E := E), X)) (x : X) (hG : ∀ s, G (0, s) = x)

include hG in
omit [FiniteDimensional ℝ E] in
theorem constant_on_radial_fibres (p q : I × Sphere (E := E)) (h : radial p = radial q) :
    G p = G q := by
  rcases (radial_eq_iff p q).mp h with rfl | ⟨hp, hq⟩
  · rfl
  · change G (p.1, p.2) = G (q.1, q.2)
    rw [hp, hq, hG, hG]

/-- The descended nullhomotopy is continuous at the center as well as on the boundary. -/
def extension : C(Disk (E := E), X) :=
  (radial_isQuotientMap s0).lift G (constant_on_radial_fibres G x hG)

theorem extension_radial (t : I) (s : Sphere (E := E)) :
    extension s0 G x hG (radial (t, s)) = G (t, s) :=
  ContinuousMap.congr_fun ((radial_isQuotientMap s0).lift_comp G
    (constant_on_radial_fibres G x hG)) (t, s)

theorem extension_boundary (s : Sphere (E := E)) :
    extension s0 G x hG (boundaryToDisk s) = G (1, s) := by
  rw [← radial_one, extension_radial]

theorem extension_center : extension s0 G x hG ⟨0, by simp⟩ = x := by
  rw [← radial_zero s0, extension_radial, hG]

end Wikipedia.HopfProblem.DegreeCollapse.DiskCone
