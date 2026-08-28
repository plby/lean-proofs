import Wikipedia.NoExoticSixSphere.OnePointFiberGermHomotopy
import Wikipedia.NoExoticSixSphere.Definitions
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Actual sphere maps with the same distinguished-fiber germ are homotopic

Stereographic coordinates with pole at the distinguished value transport
the explicit finite-coordinate interpolation back to the original sphere.
Agreement is required on a neighborhood of the common fiber, not merely
on the fiber itself. The homotopy fixes every point where the endpoints
agree, so a shared basepoint value is preserved as well.
-/

noncomputable section

open Set Filter Topology Submodule
open scoped unitInterval OnePoint

namespace NoExoticSixSphere.SphereFiberGerm

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

def poleHomeomorph (b : Sphere n) : OnePoint (ℝ ∙ b.val)ᗮ ≃ₜ Sphere n :=
  onePointHyperplaneHomeoUnitSphere (by simp)

theorem poleHomeomorph_infty (b : Sphere n) : poleHomeomorph b ∞ = b := rfl

theorem poleHomeomorph_symm_eq_infty (b y : Sphere n) :
    (poleHomeomorph b).symm y = ∞ ↔ y = b := by
  rw [Homeomorph.symm_apply_eq, poleHomeomorph_infty]

def homotopy (f g : C(X, Sphere n)) (b : Sphere n)
    (hK : ∀ x, f x = b ↔ g x = b) (U : Set X) (hU : IsOpen U)
    (hKU : f ⁻¹' {b} ⊆ U) (hfg : EqOn f g U) : f.Homotopy g := by
  let c := poleHomeomorph b
  let F : C(X, OnePoint (ℝ ∙ b.val)ᗮ) :=
    ⟨fun x ↦ c.symm (f x), c.symm.continuous.comp f.continuous⟩
  let G : C(X, OnePoint (ℝ ∙ b.val)ᗮ) :=
    ⟨fun x ↦ c.symm (g x), c.symm.continuous.comp g.continuous⟩
  have hFG : ∀ x, F x = ∞ ↔ G x = ∞ := by
    intro x
    change c.symm (f x) = ∞ ↔ c.symm (g x) = ∞
    rw [poleHomeomorph_symm_eq_infty, poleHomeomorph_symm_eq_infty]
    exact hK x
  have hFU : F ⁻¹' {∞} ⊆ U := by
    intro x hx
    apply hKU
    exact (poleHomeomorph_symm_eq_infty b (f x)).mp hx
  have heq : EqOn F G U := fun x hx ↦ congrArg c.symm (hfg hx)
  let H := OnePointFiberGerm.homotopy F G hFG U hU hFU heq
  exact {
    toFun := fun z ↦ c (H z)
    continuous_toFun := c.continuous.comp H.continuous
    map_zero_left := fun x ↦ (congrArg c (H.apply_zero x)).trans (c.apply_symm_apply (f x))
    map_one_left := fun x ↦ (congrArg c (H.apply_one x)).trans (c.apply_symm_apply (g x)) }

theorem homotopy_fixed (f g : C(X, Sphere n)) (b : Sphere n)
    (hK : ∀ x, f x = b ↔ g x = b) (U : Set X) (hU : IsOpen U)
    (hKU : f ⁻¹' {b} ⊆ U) (hfg : EqOn f g U) (t : I) (x : X) (hx : f x = g x) :
    homotopy f g b hK U hU hKU hfg (t, x) = f x := by
  change poleHomeomorph b (OnePointFiberGerm.interpolate
    (fun y ↦ (poleHomeomorph b).symm (f y))
    (fun y ↦ (poleHomeomorph b).symm (g y)) t x) = f x
  rw [OnePointFiberGerm.interpolate_fixed _ _ t x (congrArg (poleHomeomorph b).symm hx)]
  exact (poleHomeomorph b).apply_symm_apply (f x)

/-- Pointwise neighborhood agreement along the actual common fiber suffices. -/
theorem exists_homotopy_of_fiber_germs (f g : C(X, Sphere n)) (b : Sphere n)
    (hK : ∀ x, f x = b ↔ g x = b)
    (hgerm : ∀ x, f x = b → (f : X → Sphere n) =ᶠ[𝓝 x] g) :
    ∃ H : f.Homotopy g, ∀ (t : I) (x : X), f x = g x → H (t, x) = f x := by
  let U := interior {x | f x = g x}
  have hKU : f ⁻¹' {b} ⊆ U := fun x hx ↦ mem_interior_iff_mem_nhds.mpr (hgerm x hx)
  have heq : EqOn f g U := fun _ hx ↦ (interior_subset (s := {y | f y = g y})) hx
  exact ⟨homotopy f g b hK U isOpen_interior hKU heq,
    homotopy_fixed f g b hK U isOpen_interior hKU heq⟩

end NoExoticSixSphere.SphereFiberGerm
