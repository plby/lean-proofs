import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# A sphere from two affine complex charts

Two continuous injective complex-line parametrizations covering a Hausdorff
space and glued by inversion identify it with the one-point compactification
of the complex line. Continuity at infinity is proved using the limit of
inversion, rather than imposed as an additional hypothesis.
-/

noncomputable section

open Set Filter Topology Bornology OnePoint

namespace Wikipedia.HopfProblem

structure TwoAffineCharts (Y : Type*) [TopologicalSpace Y] where
  left : ℂ → Y
  right : ℂ → Y
  continuous_left : Continuous left
  continuous_right : Continuous right
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  inversion : ∀ z : ℂ, z ≠ 0 → left z = right z⁻¹
  endpoints_ne : left 0 ≠ right 0
  covered : ∀ y : Y, (∃ z, left z = y) ∨ ∃ z, right z = y

namespace TwoAffineCharts

variable {Y : Type*} [TopologicalSpace Y] (A : TwoAffineCharts Y)

theorem left_ne_right_zero (z : ℂ) : A.left z ≠ A.right 0 := by
  by_cases hz : z = 0
  · subst z
    exact A.endpoints_ne
  · intro h
    have h' := A.right_injective ((A.inversion z hz).symm.trans h)
    exact inv_ne_zero hz h'

theorem cross_eq_iff (z w : ℂ) : A.left z = A.right w ↔ z ≠ 0 ∧ w = z⁻¹ := by
  constructor
  · intro h
    have hw : w ≠ 0 := by
      rintro rfl
      exact A.left_ne_right_zero z h
    have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw)
    have hz : z = w⁻¹ := A.left_injective (h.trans hi.symm)
    refine ⟨by rw [hz]; exact inv_ne_zero hw, ?_⟩
    rw [hz, inv_inv]
  · rintro ⟨hz, rfl⟩
    exact A.inversion z hz

def symm : TwoAffineCharts Y where
  left := A.right
  right := A.left
  continuous_left := A.continuous_right
  continuous_right := A.continuous_left
  left_injective := A.right_injective
  right_injective := A.left_injective
  inversion z hz := by simpa using (A.inversion z⁻¹ (inv_ne_zero hz)).symm
  endpoints_ne := A.endpoints_ne.symm
  covered y := (A.covered y).symm

def extension (p : OnePoint ℂ) : Y := p.elim (A.right 0) A.left

@[simp] theorem extension_coe (z : ℂ) : A.extension (z : OnePoint ℂ) = A.left z := rfl

@[simp] theorem extension_infty : A.extension (∞ : OnePoint ℂ) = A.right 0 := rfl

theorem extension_injective : Function.Injective A.extension := by
  intro p q h
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => rfl
    | coe w => exact False.elim (A.left_ne_right_zero w h.symm)
  | coe z =>
    induction q using OnePoint.rec with
    | infty => exact False.elim (A.left_ne_right_zero z h)
    | coe w => exact congrArg ((↑) : ℂ → OnePoint ℂ) (A.left_injective h)

theorem extension_surjective : Function.Surjective A.extension := by
  intro y
  obtain ⟨z, hz⟩ | ⟨w, hw⟩ := A.covered y
  · exact ⟨(z : OnePoint ℂ), hz⟩
  · by_cases hw0 : w = 0
    · subst w
      exact ⟨∞, hw⟩
    · refine ⟨(w⁻¹ : ℂ), ?_⟩
      change A.left w⁻¹ = y
      have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw0)
      exact hi.trans hw

theorem extension_continuous : Continuous A.extension := by
  rw [OnePoint.continuous_iff]
  constructor
  · change Tendsto A.left (coclosedCompact ℂ) (𝓝 (A.right 0))
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    have h : Tendsto (fun z : ℂ => A.right z⁻¹) (cobounded ℂ) (𝓝 (A.right 0)) :=
      A.continuous_right.continuousAt.tendsto.comp tendsto_inv₀_cobounded
    apply h.congr'
    filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
    exact (A.inversion z hz).symm
  · exact A.continuous_left

def homeomorph [T2Space Y] : OnePoint ℂ ≃ₜ Y :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective A.extension ⟨A.extension_injective, A.extension_surjective⟩)
    A.extension_continuous

@[simp] theorem homeomorph_coe [T2Space Y] (z : ℂ) :
    A.homeomorph (z : OnePoint ℂ) = A.left z := rfl

@[simp] theorem homeomorph_infty [T2Space Y] :
    A.homeomorph (∞ : OnePoint ℂ) = A.right 0 := rfl

theorem left_isOpenEmbedding [T2Space Y] : IsOpenEmbedding A.left := by
  have h := A.homeomorph.isOpenEmbedding.comp (OnePoint.isOpenEmbedding_coe (X := ℂ))
  exact h

theorem right_isOpenEmbedding [T2Space Y] : IsOpenEmbedding A.right :=
  A.symm.left_isOpenEmbedding

theorem range_left : range A.left = {A.right 0}ᶜ := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact A.left_ne_right_zero z
  · intro hy
    change y ≠ A.right 0 at hy
    obtain ⟨z, hz⟩ | ⟨w, hw⟩ := A.covered y
    · exact ⟨z, hz⟩
    · have hw0 : w ≠ 0 := fun h => hy (by rw [← hw, h])
      refine ⟨w⁻¹, ?_⟩
      have hi : A.left w⁻¹ = A.right w := by simpa using A.inversion w⁻¹ (inv_ne_zero hw0)
      exact hi.trans hw

theorem range_right : range A.right = {A.left 0}ᶜ := A.symm.range_left

end TwoAffineCharts

end Wikipedia.HopfProblem
