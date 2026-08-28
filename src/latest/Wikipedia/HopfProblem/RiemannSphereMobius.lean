import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Affine maps and inversion on the analytic Riemann sphere

These are automorphisms of the existing `RiemannSphere` atlas, not new
manifold structures transported through a set-theoretic equivalence.
Holomorphicity at infinity is checked in the reciprocal affine chart.
-/

noncomputable section

open Set Filter Topology OnePoint
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannSphere

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A biholomorphism for the fixed two-chart analytic sphere. -/
abbrev Biholomorph := Diffeomorph I₁ I₁ RiemannSphere RiemannSphere ω

/-- Complex inversion, with zero and infinity exchanged. -/
def reciprocal (p : RiemannSphere) : RiemannSphere :=
  p.elim ((0 : ℂ) : RiemannSphere) infinityParametrization

@[simp] theorem reciprocal_infty : reciprocal ∞ = ((0 : ℂ) : RiemannSphere) := rfl

@[simp] theorem reciprocal_coe (z : ℂ) :
    reciprocal (z : RiemannSphere) = infinityParametrization z := rfl

@[simp] theorem reciprocal_infinityParametrization (z : ℂ) :
    reciprocal (infinityParametrization z) = (z : RiemannSphere) := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [infinityParametrization_of_ne hz, reciprocal_coe,
      infinityParametrization_of_ne (inv_ne_zero hz), inv_inv]

theorem reciprocal_involutive : Function.Involutive reciprocal := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp
  | coe z => simp

theorem reciprocal_holomorphic : ContMDiff I₁ I₁ ω reciprocal := by
  apply standardCharts.contMDiff_of_comp_affineMaps I₁
  intro b
  have he : reciprocal ∘ standardCharts.affineMap b = standardCharts.affineMap (!b) := by
    funext z
    cases b
    · rfl
    · exact reciprocal_infinityParametrization z
  rw [he]
  exact standardCharts.affineMap_holomorphic (!b)

/-- Inversion as an actual biholomorphic self-map. -/
def reciprocalBiholomorph : Biholomorph where
  toEquiv := reciprocal_involutive.toPerm reciprocal
  contMDiff_toFun := reciprocal_holomorphic
  contMDiff_invFun := reciprocal_holomorphic

@[simp] theorem reciprocalBiholomorph_apply (p : RiemannSphere) :
    reciprocalBiholomorph p = reciprocal p := rfl

/-- The affine homeomorphism of the complex line. -/
def affineComplexHomeomorph (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)

@[simp] theorem affineComplexHomeomorph_apply (a b z : ℂ) (ha : a ≠ 0) :
    affineComplexHomeomorph a b ha z = a * z + b := rfl

@[simp] theorem affineComplexHomeomorph_symm_apply (a b z : ℂ) (ha : a ≠ 0) :
    (affineComplexHomeomorph a b ha).symm z = a⁻¹ * (z - b) := rfl

/-- Extension of an invertible affine map by fixing infinity. -/
def affineHomeomorph (a b : ℂ) (ha : a ≠ 0) : RiemannSphere ≃ₜ RiemannSphere :=
  (affineComplexHomeomorph a b ha).onePointCongr

@[simp] theorem affineHomeomorph_coe (a b z : ℂ) (ha : a ≠ 0) :
    affineHomeomorph a b ha (z : RiemannSphere) = ((a * z + b : ℂ) : RiemannSphere) := rfl

@[simp] theorem affineHomeomorph_infty (a b : ℂ) (ha : a ≠ 0) :
    affineHomeomorph a b ha (∞ : RiemannSphere) = (∞ : RiemannSphere) := rfl

theorem affineHomeomorph_infinityParametrization (a b z : ℂ) (ha : a ≠ 0)
    (hz : a + b * z ≠ 0) :
    affineHomeomorph a b ha (infinityParametrization z) =
      infinityParametrization (z / (a + b * z)) := by
  by_cases hz0 : z = 0
  · subst z
    simp
  · rw [infinityParametrization_of_ne hz0, affineHomeomorph_coe,
      infinityParametrization_of_ne (div_ne_zero hz0 hz)]
    congr 1
    field_simp

theorem affineHomeomorph_holomorphic (a b : ℂ) (ha : a ≠ 0) :
    ContMDiff I₁ I₁ ω (affineHomeomorph a b ha) := by
  apply standardCharts.contMDiff_of_comp_affineMaps I₁
  intro chart
  cases chart
  · have hc : ContDiff ℂ ω (fun z : ℂ => a * z + b) :=
      (contDiff_const.mul contDiff_id).add contDiff_const
    exact (standardCharts.affineMap_holomorphic false).comp hc.contMDiff
  · intro z
    by_cases hz : z = 0
    · subst z
      have hd : ContDiffAt ℂ ω (fun w : ℂ => w / (a + b * w)) 0 :=
        contDiffAt_id.div (contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id))
          (by simpa using ha)
      have hc : ContMDiffAt I₁ I₁ ω
          (fun w : ℂ => infinityParametrization (w / (a + b * w))) 0 :=
        (standardCharts.affineMap_holomorphic true).contMDiffAt.comp 0 hd.contMDiffAt
      apply hc.congr_of_eventuallyEq
      have hn : ∀ᶠ w : ℂ in 𝓝 0, a + b * w ≠ 0 :=
        (isOpen_ne_fun (continuous_const.add (continuous_const.mul continuous_id))
          continuous_const).mem_nhds (by simpa using ha)
      filter_upwards [hn] with w hw
      exact affineHomeomorph_infinityParametrization a b w ha hw
    · have hd : ContDiffAt ℂ ω (fun w : ℂ => a * w⁻¹ + b) z :=
        (contDiffAt_const.mul (contDiffAt_inv ℂ hz)).add contDiffAt_const
      have hc : ContMDiffAt I₁ I₁ ω
          (fun w : ℂ => ((a * w⁻¹ + b : ℂ) : RiemannSphere)) z :=
        (standardCharts.affineMap_holomorphic false).contMDiffAt.comp z hd.contMDiffAt
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with w hw
      change w ≠ 0 at hw
      change affineHomeomorph a b ha (infinityParametrization w) = _
      rw [infinityParametrization_of_ne hw, affineHomeomorph_coe]

theorem affineHomeomorph_symm_eq (a b : ℂ) (ha : a ≠ 0) :
    ⇑(affineHomeomorph a b ha).symm =
      affineHomeomorph a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha) := by
  funext p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change ((a⁻¹ * (z - b) : ℂ) : RiemannSphere) =
      ((a⁻¹ * z + -a⁻¹ * b : ℂ) : RiemannSphere)
    congr 1
    ring

/-- An extended affine map and its inverse are holomorphic for the fixed atlas. -/
def affineBiholomorph (a b : ℂ) (ha : a ≠ 0) : Biholomorph where
  toEquiv := (affineHomeomorph a b ha).toEquiv
  contMDiff_toFun := affineHomeomorph_holomorphic a b ha
  contMDiff_invFun := by
    change ContMDiff I₁ I₁ ω (affineHomeomorph a b ha).symm
    rw [affineHomeomorph_symm_eq]
    exact affineHomeomorph_holomorphic a⁻¹ (-a⁻¹ * b) (inv_ne_zero ha)

@[simp] theorem affineBiholomorph_coe (a b z : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha (z : RiemannSphere) = ((a * z + b : ℂ) : RiemannSphere) := rfl

@[simp] theorem affineBiholomorph_infty (a b : ℂ) (ha : a ≠ 0) :
    affineBiholomorph a b ha (∞ : RiemannSphere) = (∞ : RiemannSphere) := rfl

end Wikipedia.HopfProblem.RiemannSphere
