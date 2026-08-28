import Wikipedia.NoExoticSixSphere.TimeCollarCoreHomologyNaturality
import Wikipedia.NoExoticSixSphere.TimeCollarInteriorCapDuality

/-!
# An actual relative fundamental class for a collared seven-dimensional half

The genuine supported fundamental class on a positive compact core is
transported through the original relative homology maps. Support
restriction and naturality prove independence of the core. Identification
of its connecting image with the native zero-boundary class is separate.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]
  {t : M → ℝ} (C : TimeCollar t B) (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)

local instance : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) := ⟨by simp⟩

def coreFundamentalClass :
    RelativeCoefficients.ModHomology 2 (compactCore C δ hδ : Set C.positiveInterior)ᶜ 7 :=
  CompactSupportedFundamentalClass.fundamentalClass (E := Vector 7) 4
    (compactCore C δ hδ : Set C.positiveInterior) (compactCore C δ hδ).isCompact

def relativeFundamentalClassOnCore : RelativeCoefficients.ModHomology 2 (boundary t) 7 :=
  coreToBoundaryModEquiv C δ hδ hδw 2 (by decide) 7 (coreFundamentalClass C δ hδ)

theorem relativeFundamentalClassOnCore_collar :
    boundaryToCollarModEquiv C δ hδ hδw 2 (by decide) 7
        (relativeFundamentalClassOnCore C δ hδ hδw) =
      coreModHomologyEquiv C δ hδ 2 (by decide) 7 (coreFundamentalClass C δ hδ) :=
  coreToBoundaryModEquiv_collar C δ hδ hδw 2 (by decide) 7 _

variable (ε : ℝ) (hε : 0 < ε) (hεw : ε ≤ C.width)

theorem coreFundamentalClass_restrict (hεδ : ε ≤ δ) :
    SupportedRelativeHomology.restrict (ModuleCat.of ℤ (ZMod 2))
      (compactCore_mono C δ ε hδ hε hεδ) 7 (coreFundamentalClass C ε hε) =
        coreFundamentalClass C δ hδ :=
  CompactSupportedFundamentalClass.restrict_fundamentalClass (E := Vector 7) 4
    (compactCore_mono C δ ε hδ hε hεδ) (compactCore C δ hδ).isCompact (compactCore C ε hε).isCompact

theorem relativeFundamentalClassOnCore_mono (hεδ : ε ≤ δ) :
    relativeFundamentalClassOnCore C ε hε hεw = relativeFundamentalClassOnCore C δ hδ hδw := by
  unfold relativeFundamentalClassOnCore
  rw [coreToBoundaryModEquiv_natural C δ hδ hδw ε hε hεw hεδ 2 (by decide) 7]
  rw [coreFundamentalClass_restrict C δ hδ ε hε hεδ]

theorem relativeFundamentalClassOnCore_independent :
    relativeFundamentalClassOnCore C δ hδ hδw = relativeFundamentalClassOnCore C ε hε hεw := by
  let η := min δ ε
  have hη : 0 < η := lt_min hδ hε
  have hηw : η ≤ C.width := (min_le_left _ _).trans hδw
  exact (relativeFundamentalClassOnCore_mono C δ hδ hδw η hη hηw (min_le_left _ _)).symm.trans
    (relativeFundamentalClassOnCore_mono C ε hε hεw η hη hηw (min_le_right _ _))

def relativeFundamentalClass : RelativeCoefficients.ModHomology 2 (boundary t) 7 :=
  relativeFundamentalClassOnCore C (C.width / 2) (half_pos C.width_pos)
    (half_lt_self C.width_pos).le

theorem relativeFundamentalClass_eq_onCore :
    relativeFundamentalClass C = relativeFundamentalClassOnCore C δ hδ hδw := by
  unfold relativeFundamentalClass
  exact relativeFundamentalClassOnCore_independent C (C.width / 2) (half_pos C.width_pos)
    (half_lt_self C.width_pos).le δ hδ hδw

theorem relativeFundamentalClass_core :
    (coreToBoundaryModEquiv C δ hδ hδw 2 (by decide) 7).symm (relativeFundamentalClass C) =
      coreFundamentalClass C δ hδ := by
  rw [relativeFundamentalClass_eq_onCore C δ hδ hδw]
  exact LinearEquiv.symm_apply_apply _ _

end NoExoticSixSphere.TimeCollarDuality
