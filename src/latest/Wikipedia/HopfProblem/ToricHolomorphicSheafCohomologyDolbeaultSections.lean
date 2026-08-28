import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultLocal
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultChain

/-!
# The actual antiholomorphic derivative on smooth sections

A section is extended by zero only to name an ambient representative;
all differentiability assertions are confined to its original open set.
The actual Fréchet derivative gives a smooth section there, independently
of the extension. Its complex linearity and compatibility with actual
restriction are proved pointwise from the derivative rules.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal

open HolomorphicCousin

section Extend

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- The actual smooth section, extended by zero outside its open domain. -/
def smoothExtend (U : Opens M) (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) M U)
    (p : M) : ℂ := by
  classical
  exact if hp : p ∈ U then s ⟨p, hp⟩ else 0

@[simp] theorem smoothExtend_apply (U : Opens M)
    (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) M U) (p : M) (hp : p ∈ U) :
    smoothExtend U s p = s ⟨p, hp⟩ := by
  classical
  simp only [smoothExtend, dif_pos hp]

theorem smoothExtend_comp_val (U : Opens M)
    (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) M U) :
    (fun p : U => smoothExtend U s p) = (s : U → ℂ) :=
  funext fun p => smoothExtend_apply U s p p.property

/-- The named ambient representative is genuinely smooth at every
point of the original open domain. -/
theorem smoothExtend_contMDiffAt (U : Opens M)
    (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) M U) (p : M) (hp : p ∈ U) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (smoothExtend U s) p := by
  apply (contMDiffAt_subtype_iff (x := (⟨p, hp⟩ : U))).mp
  rw [smoothExtend_comp_val U s]
  exact s.contMDiff _

theorem smoothExtend_add (U : Opens M)
    (s t : SmoothFunctions.Section 𝓘(ℝ, ℂ) M U) :
    smoothExtend U (s + t) = fun p => smoothExtend U s p + smoothExtend U t p := by
  classical
  funext p
  by_cases hp : p ∈ U
  · simp only [smoothExtend, dif_pos hp]
    rfl
  · simp only [smoothExtend, dif_neg hp, add_zero]

theorem smoothExtend_smul (U : Opens M) (c : ℂ)
    (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) M U) :
    smoothExtend U (c • s) = fun p => c * smoothExtend U s p := by
  classical
  funext p
  by_cases hp : p ∈ U
  · simp only [smoothExtend, dif_pos hp]
    rfl
  · simp only [smoothExtend, dif_neg hp, mul_zero]

/-- Restriction does not change the actual germ of an ambient
representative at any point of the smaller open set. -/
theorem smoothExtend_restrict_germ {U V : Opens M} (h : U ≤ V)
    (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) M V) (p : M) (hp : p ∈ U) :
    smoothExtend U (ContMDiffMap.restrictRingHom 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ h s) =ᶠ[𝓝 p]
      smoothExtend V s := by
  filter_upwards [U.isOpen.mem_nhds hp] with q hq
  rw [smoothExtend_apply _ _ q hq, smoothExtend_apply _ _ q (h hq)]
  rfl

end Extend

/-- The actual complex-linear antiholomorphic derivative on plane
sections. Its values are ordinary smooth functions in the coordinate. -/
def dbarSection (U : Opens ℂ) :
    SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ U →ₗ[ℂ]
      SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ U where
  toFun s :=
    ⟨fun z => dbar (smoothExtend U s) z,
      fun z => contMDiffAt_subtype_iff.mpr
        (contDiffAt_dbar (smoothExtend_contMDiffAt U s z z.property).contDiffAt).contMDiffAt⟩
  map_add' s t := by
    apply ContMDiffMap.ext
    intro z
    change dbar (smoothExtend U (s + t)) z =
      dbar (smoothExtend U s) z + dbar (smoothExtend U t) z
    rw [smoothExtend_add]
    exact dbar_add
      ((smoothExtend_contMDiffAt U s z z.property).contDiffAt.differentiableAt (by simp))
      ((smoothExtend_contMDiffAt U t z z.property).contDiffAt.differentiableAt (by simp))
  map_smul' c s := by
    apply ContMDiffMap.ext
    intro z
    change dbar (smoothExtend U (c • s)) z = c * dbar (smoothExtend U s) z
    rw [smoothExtend_smul]
    exact dbar_const_mul
      ((smoothExtend_contMDiffAt U s z z.property).contDiffAt.differentiableAt (by simp)) c

@[simp] theorem dbarSection_apply (U : Opens ℂ)
    (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ U) (z : U) :
    dbarSection U s z = dbar (smoothExtend U s) z := rfl

/-- The actual differential commutes with literal restriction of sections. -/
theorem dbarSection_restrict {U V : Opens ℂ} (h : U ≤ V)
    (s : SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ V) :
    dbarSection U (ContMDiffMap.restrictRingHom 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ h s) =
      ContMDiffMap.restrictRingHom 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ h (dbarSection V s) := by
  apply ContMDiffMap.ext
  intro z
  exact dbar_congr_of_eventuallyEq (smoothExtend_restrict_germ h s z z.property)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal
