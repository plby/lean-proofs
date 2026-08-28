import Wikipedia.NoExoticSixSphere.RegularPointNeighborhood
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of the critical-value set

For a smooth map on an open finite-dimensional domain, regular points form
an open subset of that domain. The complementary critical locus is
sigma-compact, and its continuous image is sigma-compact and Borel. This
supplies the measurability needed in the Fubini part of Sard's theorem.
-/

open scoped ContDiff Manifold
open Set Module TopologicalSpace

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem isOpen_regularPointsOn {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    IsOpen {x | x ∈ U ∧ Function.Surjective (fderiv ℝ f x)} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hreg : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) := by
    have he : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x : E →L[ℝ] F) = fderiv ℝ f x :=
      mfderiv_eq_fderiv
    intro w
    obtain ⟨v, hv⟩ := hx.2 w
    exact ⟨v, (congrArg (fun L : E →L[ℝ] F ↦ L v) he).trans hv⟩
  obtain ⟨V, hV, hxV, hVU, hr⟩ :=
    exists_regularPointNeighborhood_vector hU hx.1 hf.contMDiffOn hreg
  refine ⟨V, fun y hy ↦ ⟨hVU hy, ?_⟩, hV, hxV⟩
  have he : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f y : E →L[ℝ] F) = fderiv ℝ f y :=
    mfderiv_eq_fderiv
  intro w
  obtain ⟨v, hv⟩ := hr y hy w
  exact ⟨v, (congrArg (fun L : E →L[ℝ] F ↦ L v) he).symm.trans hv⟩

theorem isSigmaCompact_criticalPoints {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    IsSigmaCompact {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)} := by
  let O : Opens E := ⟨U, hU⟩
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  let C : Set O := {x | ¬ Function.Surjective (fderiv ℝ f x.val)}
  have hR : IsOpen {x : O | Function.Surjective (fderiv ℝ f x.val)} := by
    have heq : {x : O | Function.Surjective (fderiv ℝ f x.val)} =
        Subtype.val ⁻¹' {x | x ∈ U ∧ Function.Surjective (fderiv ℝ f x)} := by
      ext x
      exact ⟨fun h ↦ ⟨x.property, h⟩, fun h ↦ h.2⟩
    rw [heq]
    exact (isOpen_regularPointsOn hU hf).preimage continuous_subtype_val
  have hC : IsSigmaCompact C :=
    isSigmaCompact_univ.of_isClosed_subset hR.isClosed_compl (subset_univ _)
  have heq : (Subtype.val : O → E) '' C =
      {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hn⟩
      exact ⟨⟨x, hx⟩, hn, rfl⟩
  rw [← heq]
  exact hC.image continuous_subtype_val

theorem isSigmaCompact_criticalValues {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    IsSigmaCompact (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) :=
  (isSigmaCompact_criticalPoints hU hf).image_of_continuousOn
    (hf.continuousOn.mono (fun _ hx ↦ hx.1))

theorem measurableSet_criticalValues [MeasurableSpace F] [BorelSpace F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    MeasurableSet (f '' {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ f x)}) := by
  obtain ⟨K, hK, hcover⟩ := isSigmaCompact_criticalValues hU hf
  rw [← hcover]
  exact MeasurableSet.iUnion (fun i ↦ (hK i).isClosed.measurableSet)

end NoExoticSixSphere.Sard
