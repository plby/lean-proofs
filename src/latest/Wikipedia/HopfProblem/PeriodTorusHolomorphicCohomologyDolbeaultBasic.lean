import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic

/-!
# Actual functions in the native period-torus Dolbeault sequence

Both section types use the unchanged discrete-quotient charts on the
original torus. Holomorphic sections have complex analytic order; smooth
sections have real infinite differentiability. Extension by zero only
names ambient representatives and makes no regularity claim outside the
original open domain.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open HolomorphicSheafCohomology

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

/-- Actual holomorphic functions on an original torus open. -/
abbrev HolomorphicSection (p : PeriodDomain) (U : Opens p.Torus) :=
  HolomorphicFunctionSheaf.Section I₂ p.Torus U

/-- Actual smooth functions in the same original quotient charts. -/
abbrev SmoothSection (p : PeriodDomain) (U : Opens p.Torus) :=
  SmoothFunctions.Section IR₂ p.Torus U

/-- The genuine smooth complex-valued function sheaf on the native torus. -/
abbrev smoothSheaf (p : PeriodDomain) := SmoothFunctions.additiveSheaf IR₂ p.Torus

/-- Literal restriction of smooth functions to an actual smaller torus open. -/
abbrev restriction (p : PeriodDomain) {U V : Opens p.Torus} (h : U ≤ V) :
    SmoothSection p V →+* SmoothSection p U :=
  ContMDiffMap.restrictRingHom IR₂ IR₁ ℂ h

/-- An ambient representative; no smoothness is asserted outside its domain. -/
def smoothExtend (p : PeriodDomain) (U : Opens p.Torus) (s : SmoothSection p U)
    (x : p.Torus) : ℂ := by
  classical
  exact if hx : x ∈ U then s ⟨x, hx⟩ else 0

@[simp] theorem smoothExtend_apply (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) (x : p.Torus) (hx : x ∈ U) :
    smoothExtend p U s x = s ⟨x, hx⟩ := by
  classical
  simp only [smoothExtend, dif_pos hx]

theorem smoothExtend_comp_val (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) :
    (fun x : U => smoothExtend p U s x) = (s : U → ℂ) :=
  funext fun x => smoothExtend_apply p U s x x.property

/-- The actual representative is smooth at every point of its original domain. -/
theorem smoothExtend_contMDiffAt (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) (x : p.Torus) (hx : x ∈ U) :
    ContMDiffAt IR₂ IR₁ ∞ (smoothExtend p U s) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
  rw [smoothExtend_comp_val]
  exact s.contMDiff _

theorem smoothExtend_contMDiffOn (p : PeriodDomain) (U : Opens p.Torus)
    (s : SmoothSection p U) : ContMDiffOn IR₂ IR₁ ∞ (smoothExtend p U s) U :=
  fun x hx => (smoothExtend_contMDiffAt p U s x hx).contMDiffWithinAt

theorem smoothExtend_add (p : PeriodDomain) (U : Opens p.Torus)
    (s t : SmoothSection p U) :
    smoothExtend p U (s + t) = fun x => smoothExtend p U s x + smoothExtend p U t x := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [smoothExtend, dif_pos hx]
    rfl
  · simp only [smoothExtend, dif_neg hx, add_zero]

theorem smoothExtend_smul (p : PeriodDomain) (U : Opens p.Torus)
    (c : ℂ) (s : SmoothSection p U) :
    smoothExtend p U (c • s) = fun x => c * smoothExtend p U s x := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [smoothExtend, dif_pos hx]
    rfl
  · simp only [smoothExtend, dif_neg hx, mul_zero]

theorem smoothExtend_restrict_germ (p : PeriodDomain) {U V : Opens p.Torus}
    (h : U ≤ V) (s : SmoothSection p V) (x : p.Torus) (hx : x ∈ U) :
    smoothExtend p U (restriction p h s) =ᶠ[𝓝 x] smoothExtend p V s := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  rw [smoothExtend_apply _ _ _ y hy, smoothExtend_apply _ _ _ y (h hy)]
  rfl

/-- An actual smooth function near each point of `U` defines its native section. -/
def sectionOfSmooth (p : PeriodDomain) (U : Opens p.Torus) (f : p.Torus → ℂ)
    (hf : ∀ x ∈ U, ContMDiffAt IR₂ IR₁ ∞ f x) : SmoothSection p U :=
  ⟨fun x => f x, fun x => contMDiffAt_subtype_iff.mpr (hf x x.property)⟩

@[simp] theorem sectionOfSmooth_apply (p : PeriodDomain) (U : Opens p.Torus)
    (f : p.Torus → ℂ) (hf : ∀ x ∈ U, ContMDiffAt IR₂ IR₁ ∞ f x) (x : U) :
    sectionOfSmooth p U f hf x = f x := rfl

theorem smoothExtend_sectionOfSmooth_germ (p : PeriodDomain) (U : Opens p.Torus)
    (f : p.Torus → ℂ) (hf : ∀ x ∈ U, ContMDiffAt IR₂ IR₁ ∞ f x)
    (x : p.Torus) (hx : x ∈ U) :
    smoothExtend p U (sectionOfSmooth p U f hf) =ᶠ[𝓝 x] f := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact smoothExtend_apply p U (sectionOfSmooth p U f hf) y hy

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
