import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDisjoint
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The genuine biholomorphism of a chosen coordinate disc

A holomorphic partial coordinate chart restricts to a biholomorphism from
the actual inverse-image coordinate disc to the literal complex ball.
Both maps are the original chart maps, and both holomorphy statements use
the inherited open-submanifold structures.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The literal complex coordinate ball as an open complex submanifold. -/
def coordinateBall (r : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 r, Metric.isOpen_ball⟩

@[simp] theorem mem_coordinateBall (r : ℝ) (z : ℂ) :
    z ∈ coordinateBall r ↔ z ∈ Metric.ball 0 r := Iff.rfl

variable (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ)

/-- The actual chart restricted to its chosen coordinate disc. -/
def coordinateDiscForward : coordinateDisc e.toOpenPartialHomeomorph r → coordinateBall r :=
  fun x => ⟨e x, x.property.2⟩

/-- The actual inverse chart restricted to the full coordinate ball. -/
def coordinateDiscInverse (hball : Metric.ball 0 r ⊆ e.target) :
    coordinateBall r → coordinateDisc e.toOpenPartialHomeomorph r :=
  fun z => ⟨e.symm z, e.map_target (hball z.property), by
    change e (e.symm (z : ℂ)) ∈ Metric.ball 0 r
    have he : e (e.symm (z : ℂ)) = (z : ℂ) := e.right_inv (hball z.property)
    exact he.symm ▸ z.property⟩

theorem coordinateDiscForward_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscForward e r) := by
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun x : coordinateDisc e.toOpenPartialHomeomorph r => e (x : X)) :=
    e.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun x => x.property.1)
  intro x
  have h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y => (coordinateDiscForward e r y : ℂ)) x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscForward e r) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hf x)

theorem coordinateDiscInverse_holomorphic (hball : Metric.ball 0 r ⊆ e.target) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscInverse e r hball) := by
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : coordinateBall r => e.symm (z : ℂ)) :=
    e.symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => hball z.property)
  intro z
  have h : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun w => (coordinateDiscInverse e r hball w : X)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscInverse e r hball) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hf z)

/-- The original holomorphic chart gives an actual biholomorphism from
the chosen open patch to the entire complex coordinate ball. -/
def coordinateDiscBiholomorph (hball : Metric.ball 0 r ⊆ e.target) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (coordinateDisc e.toOpenPartialHomeomorph r)
      (coordinateBall r) ω where
  toFun := coordinateDiscForward e r
  invFun := coordinateDiscInverse e r hball
  left_inv x := Subtype.ext (e.left_inv x.property.1)
  right_inv z := Subtype.ext (e.right_inv (hball z.property))
  contMDiff_toFun := coordinateDiscForward_holomorphic e r
  contMDiff_invFun := coordinateDiscInverse_holomorphic e r hball

@[simp] theorem coordinateDiscBiholomorph_apply_coe
    (hball : Metric.ball 0 r ⊆ e.target) (x : coordinateDisc e.toOpenPartialHomeomorph r) :
    (coordinateDiscBiholomorph e r hball x : ℂ) = e (x : X) := rfl

@[simp] theorem coordinateDiscBiholomorph_symm_apply_coe
    (hball : Metric.ball 0 r ⊆ e.target) (z : coordinateBall r) :
    ((coordinateDiscBiholomorph e r hball).symm z : X) = e.symm (z : ℂ) := rfl

/-- The restricted chart has the full prescribed coordinate ball as
its image, not a smaller or merely locally equivalent target. -/
theorem coordinateDisc_image (hball : Metric.ball 0 r ⊆ e.target) :
    e '' (coordinateDisc e.toOpenPartialHomeomorph r : Set X) = Metric.ball 0 r := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.2
  · intro hz
    obtain ⟨x, hx⟩ := (coordinateDiscBiholomorph e r hball).surjective
      (⟨z, hz⟩ : coordinateBall r)
    exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- The inverse coordinate parametrization has exactly the chosen open
patch as its range in the original manifold. -/
theorem coordinateDiscInverse_range (hball : Metric.ball 0 r ⊆ e.target) :
    range (fun z : coordinateBall r => e.symm (z : ℂ)) =
      (coordinateDisc e.toOpenPartialHomeomorph r : Set X) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact (coordinateDiscInverse e r hball z).property
  · intro hx
    refine ⟨coordinateDiscBiholomorph e r hball ⟨x, hx⟩, ?_⟩
    exact e.left_inv hx.1

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
