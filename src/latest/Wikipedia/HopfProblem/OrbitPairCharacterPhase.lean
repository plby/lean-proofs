import Wikipedia.HopfProblem.OrbitPairUnitCircleAction
import Wikipedia.HopfProblem.OrbitPairPhaseTrivialization
import Wikipedia.HopfProblem.StandardSixSphereCircleModelSmoothFunctions

/-!
# Smooth phase and product splitting on the actual character neighborhood

Every free point admits one of these characters. Its nonzero set is an
invariant open subset of the original manifold contained in the free
locus. The phase uses the native smooth structure on the unit circle.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace unitCircleMulAction
  unitCircleAction_continuous Threefold.space_isSmoothRealManifold

local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

/-- A smooth character of weight one for the original action. -/
structure SmoothOrbitCharacter where
  toFun : Threefold.Space → ℂ
  smooth : ContMDiff IX 𝓘(ℝ, ℂ) ∞ toFun
  equivariant : ∀ (u : Circle) x, toFun (u • x) = (u : ℂ) * toFun x

namespace SmoothOrbitCharacter

instance : CoeFun SmoothOrbitCharacter (fun _ => Threefold.Space → ℂ) := ⟨toFun⟩

variable (F : SmoothOrbitCharacter)

def nonzeroSet : TopologicalSpace.Opens Threefold.Space :=
  ⟨{x | F x ≠ 0}, isOpen_ne.preimage F.smooth.continuous⟩

theorem nonzeroSet_smul (u : Circle) (x : Threefold.Space) (hx : x ∈ F.nonzeroSet) :
    u • x ∈ F.nonzeroSet := by
  change F (u • x) ≠ 0
  rw [F.equivariant]
  exact mul_ne_zero u.coe_ne_zero hx

theorem nonzeroSet_subset_freeLocus : (F.nonzeroSet : Set Threefold.Space) ⊆ freeLocus := by
  intro x hx hfixed
  have h := F.equivariant (-1) x
  rw [unitCircle_fixed_of_mem_D₀ (-1) x hfixed, Circle.coe_neg, Circle.coe_one,
    neg_one_mul] at h
  exact hx (neg_eq_self.mp h.symm)

/-- Restriction to an invariant open set, retaining the original action. -/
instance nonzeroSet_mulAction : MulAction Circle F.nonzeroSet where
  smul u x := ⟨u • x.val, F.nonzeroSet_smul u x.val x.property⟩
  one_smul x := Subtype.ext (one_smul Circle x.val)
  mul_smul u v x := Subtype.ext (mul_smul u v x.val)

instance nonzeroSet_continuousSMul : ContinuousSMul Circle F.nonzeroSet :=
  ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

/-- The phase of the actual complex-valued character. -/
def phase (x : F.nonzeroSet) : Circle :=
  ⟨‖F x.val‖⁻¹ • F x.val, mem_sphere_zero_iff_norm.mpr (by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr x.property)])⟩

@[simp] theorem phase_coe (x : F.nonzeroSet) :
    (F.phase x : ℂ) = ‖F x.val‖⁻¹ • F x.val := rfl

theorem phase_smooth : ContMDiff IX (𝓡 1) ∞ F.phase := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  apply ContMDiff.codRestrict_sphere
  exact StandardSixSphereCircleModel.contMDiff_normalize_of_ne_zero
    (F.smooth.comp contMDiff_subtype_val) (fun x => x.property)

theorem phase_equivariant (u : Circle) (x : F.nonzeroSet) :
    F.phase (u • x) = u * F.phase x := by
  apply Circle.ext
  change ‖F (u • x.val)‖⁻¹ • F (u • x.val) = (u : ℂ) * (‖F x.val‖⁻¹ • F x.val)
  rw [F.equivariant, norm_mul, Circle.norm_coe, one_mul, mul_smul_comm]

/-- The actual identity-phase slice, with its subspace topology. -/
abbrev Slice := PhaseSlice F.phase

/-- Explicit phase splitting of the original invariant open neighborhood. -/
def productHomeomorph : F.nonzeroSet ≃ₜ Circle × F.Slice :=
  phaseTrivialization F.phase F.phase_smooth.continuous F.phase_equivariant

@[simp] theorem productHomeomorph_fst (x : F.nonzeroSet) :
    (F.productHomeomorph x).1 = F.phase x := rfl

@[simp] theorem productHomeomorph_symm (u : Circle) (x : F.Slice) :
    (F.productHomeomorph.symm (u, x) : Threefold.Space) = u • x.val.val := rfl

end SmoothOrbitCharacter

/-- Characters of weight one cover the actual free locus. -/
theorem exists_smoothOrbitCharacter (x : freeLocus) :
    ∃ F : SmoothOrbitCharacter, x.val ∈ F.nonzeroSet := by
  obtain ⟨F, hF, he, hx⟩ := exists_unitCircle_equivariant_smooth_function_at_free_point
    x.val x.property
  exact ⟨⟨F, hF, he⟩, hx⟩

end Wikipedia.HopfProblem.OrbitPair
