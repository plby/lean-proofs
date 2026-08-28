import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeGeometrySmooth
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic

/-!
# Native smooth and holomorphic functions on original open sets

Extension by zero is used only to name ambient representatives.  All
regularity and derivative statements are local to the original open set.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Functions

open HolomorphicSheafCohomology

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

local notation "IR" => modelWithCornersSelf ℝ E
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

abbrev SmoothSection (U : Opens M) := SmoothFunctions.Section IR M U
abbrev smoothSheaf := SmoothFunctions.additiveSheaf IR M

abbrev restriction {U V : Opens M} (h : U ≤ V) :
    SmoothSection E M V →+* SmoothSection E M U :=
  ContMDiffMap.restrictRingHom IR IR₁ ℂ h

def extend (U : Opens M) (s : SmoothSection E M U) (x : M) : ℂ := by
  classical
  exact if hx : x ∈ U then s ⟨x, hx⟩ else 0

@[simp] theorem extend_apply (U : Opens M) (s : SmoothSection E M U)
    (x : M) (hx : x ∈ U) : extend E M U s x = s ⟨x, hx⟩ := by
  classical
  simp only [extend, dif_pos hx]

theorem extend_comp_val (U : Opens M) (s : SmoothSection E M U) :
    (fun x : U => extend E M U s x) = (s : U → ℂ) :=
  funext fun x => extend_apply E M U s x x.property

theorem extend_contMDiffAt (U : Opens M) (s : SmoothSection E M U)
    (x : M) (hx : x ∈ U) : ContMDiffAt IR IR₁ ∞ (extend E M U s) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
  rw [extend_comp_val]
  exact s.contMDiff _

theorem extend_contMDiffOn (U : Opens M) (s : SmoothSection E M U) :
    ContMDiffOn IR IR₁ ∞ (extend E M U s) U :=
  fun x hx => (extend_contMDiffAt E M U s x hx).contMDiffWithinAt

theorem extend_add (U : Opens M) (s t : SmoothSection E M U) :
    extend E M U (s + t) = fun x => extend E M U s x + extend E M U t x := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [extend, dif_pos hx]
    rfl
  · simp only [extend, dif_neg hx, add_zero]

theorem extend_smul (U : Opens M) (c : ℂ) (s : SmoothSection E M U) :
    extend E M U (c • s) = fun x => c * extend E M U s x := by
  classical
  funext x
  by_cases hx : x ∈ U
  · simp only [extend, dif_pos hx]
    rfl
  · simp only [extend, dif_neg hx, mul_zero]

theorem extend_restrict_germ {U V : Opens M} (h : U ≤ V)
    (s : SmoothSection E M V) (x : M) (hx : x ∈ U) :
    extend E M U (restriction E M h s) =ᶠ[𝓝 x] extend E M V s := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  rw [extend_apply _ _ _ _ y hy, extend_apply _ _ _ _ y (h hy)]
  rfl

def sectionOfSmooth (U : Opens M) (f : M → ℂ)
    (hf : ∀ x ∈ U, ContMDiffAt IR IR₁ ∞ f x) : SmoothSection E M U :=
  ⟨fun x => f x, fun x => contMDiffAt_subtype_iff.mpr (hf x x.property)⟩

@[simp] theorem sectionOfSmooth_apply (U : Opens M) (f : M → ℂ)
    (hf : ∀ x ∈ U, ContMDiffAt IR IR₁ ∞ f x) (x : U) :
    sectionOfSmooth E M U f hf x = f x := rfl

theorem extend_sectionOfSmooth_germ (U : Opens M) (f : M → ℂ)
    (hf : ∀ x ∈ U, ContMDiffAt IR IR₁ ∞ f x) (x : M) (hx : x ∈ U) :
    extend E M U (sectionOfSmooth E M U f hf) =ᶠ[𝓝 x] f := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact extend_apply E M U (sectionOfSmooth E M U f hf) y hy

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

local notation "IC" => modelWithCornersSelf ℂ E

abbrev HolomorphicSection (U : Opens M) := HolomorphicFunctionSheaf.Section IC M U
abbrev holomorphicSheaf := HolomorphicFunctionSheaf.additiveSheaf IC M

/-- The actual holomorphic section, regarded as a smooth section in the same atlas. -/
def inclusionSection (U : Opens M) (s : HolomorphicSection E M U) :
    SmoothSection E M U :=
  ⟨s, Geometry.contMDiff_real_of_complex U (s.contMDiff.of_le (by simp))⟩

@[simp] theorem inclusionSection_apply (U : Opens M) (s : HolomorphicSection E M U)
    (x : U) : inclusionSection E M U s x = s x := rfl

theorem extend_inclusion_contMDiffAt (U : Opens M) (s : HolomorphicSection E M U)
    (x : M) (hx : x ∈ U) :
    ContMDiffAt IC 𝓘(ℂ) ω (extend E M U (inclusionSection E M U s)) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
  rw [extend_comp_val]
  exact s.contMDiff _

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Functions
