import Wikipedia.HopfProblem.PeriodTorusAppellHumbertCoreIdentification
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertSectionsAnalytic
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreSections

/-!
# The actual vector bundle's holomorphic sections and theta functions

The analytic fibre-linear identification with the quotient sends Mathlib's
actual `ContMDiffSection` objects to right-inverse quotient sections.
Conversely, the analytic scalar pullback of a quotient section gives
compatible holomorphic coefficients in every original bundle chart.
These constructions are inverse, giving the genuine line bundle's
holomorphic-section/entire-theta correspondence.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ComplexPlane₂ × ℂ)

/-- Mathlib's actual holomorphic sections of the constructed vector bundle. -/
abbrev HolomorphicSection := ContMDiffSection IC ℂ ω (data F).core.Fiber

/-- The proved bundle/quotient identification sends a bundle section to a genuine right inverse. -/
def quotientSection (s : HolomorphicSection F) : Section F where
  toFun b := toAssociated F ⟨b, s b⟩
  projection_toFun b := projection_toAssociated F ⟨b, s b⟩

theorem quotientSection_holomorphic (s : HolomorphicSection F) :
    (quotientSection F s).IsHolomorphic F := by
  let := associatedChartedSpace F
  exact (toAssociated_holomorphic F).comp s.contMDiff

theorem quotientSection_injective : Function.Injective (quotientSection F) := by
  intro s t h
  apply ContMDiffSection.ext
  intro b
  exact associatedMap_fibre_injective F (lift p b b)
    (congrArg (fun q : Section F => q b) h)

@[simp] theorem quotientSection_zero :
    quotientSection F (0 : HolomorphicSection F) = zeroSection F := by
  apply Section.ext
  intro b
  calc
    quotientSection F 0 b = associatedMap F (lift p b b, 0) := rfl
    _ = zeroSection F (p.lattice.mkQ (lift p b b)) := (zeroSection_apply_project F _).symm
    _ = zeroSection F b := congrArg (zeroSection F) (lift_project p b (mem_baseSet p b))

/-- Coefficients obtained by evaluating the actual scalar pullback at each local covering lift. -/
def quotientLocalCoefficient (s : Section F) (i b : p.Torus) : ℂ :=
  s.pullback F (lift p i b)

theorem quotientLocalCoefficient_compatible (s : Section F) :
    (data F).IsCompatible (quotientLocalCoefficient F s) := by
  intro i j b hb
  change (F.factor (deck p i j b) (lift p i b) : ℂ) * s.pullback F (lift p i b) =
    s.pullback F (lift p j b)
  exact (s.pullback_automorphic F (deck p i j b) (lift p i b)).symm.trans
    (congrArg (s.pullback F) (deck_spec p i j hb))

theorem quotientLocalCoefficient_holomorphic (s : Section F) (hs : s.IsHolomorphic F)
    (i : p.Torus) :
    ContMDiffOn IC I₁ ω (quotientLocalCoefficient F s i) ((data F).baseSet i) :=
  (s.pullback_contMDiff F hs).comp_contMDiffOn (lift_holomorphic p i)

/-- Genuine gluing in the original holomorphic vector-bundle charts. -/
def sectionOfQuotient (s : Section F) (hs : s.IsHolomorphic F) : HolomorphicSection F :=
  (data F).holomorphicSectionFromLocal IC (quotientLocalCoefficient F s)
    (quotientLocalCoefficient_compatible F s) (quotientLocalCoefficient_holomorphic F s hs)

@[simp] theorem sectionOfQuotient_apply (s : Section F) (hs : s.IsHolomorphic F)
    (b : p.Torus) :
    sectionOfQuotient F s hs b = s.pullback F (lift p b b) := rfl

@[simp] theorem quotientSection_sectionOfQuotient (s : Section F)
    (hs : s.IsHolomorphic F) : quotientSection F (sectionOfQuotient F s hs) = s := by
  apply Section.ext
  intro b
  change associatedMap F (lift p b b, s.pullback F (lift p b b)) = s b
  rw [Section.associatedMap_pullback, lift_project p b (mem_baseSet p b)]

/-- The independently defined notions of actual holomorphic section coincide. -/
def sectionEquivQuotient :
    HolomorphicSection F ≃ {s : Section F // s.IsHolomorphic F} where
  toFun s := ⟨quotientSection F s, quotientSection_holomorphic F s⟩
  invFun s := sectionOfQuotient F s.val s.property
  left_inv s := quotientSection_injective F
    (quotientSection_sectionOfQuotient F (quotientSection F s)
      (quotientSection_holomorphic F s))
  right_inv s := Subtype.ext (quotientSection_sectionOfQuotient F s.val s.property)

/-- Genuine holomorphic sections of the actual line bundle correspond to entire theta functions. -/
def sectionEquivTheta : HolomorphicSection F ≃ EntireThetaFunction F :=
  (sectionEquivQuotient F).trans (PeriodTorusAppellHumbert.holomorphicSectionEquivTheta F)

end Wikipedia.HopfProblem.PeriodTorusAppellHumbert.Core
