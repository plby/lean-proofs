import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationSource
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySourceSequence

/-!
# Reduction to the original regular fibre after source surjectivity

Exactness of the actual regular-family sequence leaves only an actual
fibre class after subtracting native cap-kernel relations.  This file
records that reduction and its consequences for the original star map.
All maps retain their original homology representatives and signs.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination

open SingularMayerVietoris PeriodTorusHigherHomology TrianglePeriodFamily
open TrianglePeriodFamily.Homology

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- Surjectivity onto the actual source kernel gives a fibre-plus-cap-kernel decomposition. -/
theorem exists_fibre_capKernel_decomposition (n : ℕ)
    (hs : Function.Surjective (nativeCapKernelSourceMap n))
    (r : SingularHomology SpecialRegularFamily (n + 1)) :
    ∃ b : SingularHomology RealTorus₄ (n + 1),
      ∃ a : ∀ i : Puncture, NativeCapKernel i (n + 1),
        singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) (n + 1) b +
          nativeCapKernelRegularMap (n + 1) a = r := by
  obtain ⟨a, ha⟩ := hs (sourceKernelProjection Dsp n r)
  have hr : r - nativeCapKernelRegularMap (n + 1) a ∈
      LinearMap.ker (sourceKernelProjection Dsp n) := by
    change sourceKernelProjection Dsp n (r - nativeCapKernelRegularMap (n + 1) a) = 0
    rw [map_sub, ← nativeCapKernelSourceMap_apply, ha, sub_self]
  rw [sourceKernelProjection_kernel] at hr
  obtain ⟨b, hb⟩ := hr
  exact ⟨b, a, hb ▸ sub_add_cancel r (nativeCapKernelRegularMap (n + 1) a)⟩

/-- Actual source surjectivity and the actual fibre image determine the whole regular image. -/
theorem nativeCapKernelRegularMap_surjective_of_fibre_range (n : ℕ)
    (hs : Function.Surjective (nativeCapKernelSourceMap n))
    (hf : LinearMap.range (singularHomologyMap
      (familyFibreInclusion Dsp normalizedSlitBaseLift) (n + 1)) ≤
        LinearMap.range (nativeCapKernelRegularMap (n + 1))) :
    Function.Surjective (nativeCapKernelRegularMap (n + 1)) := by
  intro r
  obtain ⟨b, a, hr⟩ := exists_fibre_capKernel_decomposition n hs r
  obtain ⟨c, hc⟩ := hf ⟨b, rfl⟩
  refine ⟨c + a, ?_⟩
  rw [map_add, hc]
  exact hr

/-- The actual normalized regular fibre included in the original global threefold. -/
def regularFibreIntoSpace : C(RealTorus₄, Space) :=
  originalRegularInclusion.comp (familyFibreInclusion Dsp normalizedSlitBaseLift)

/-- This is exactly composition of the original fibre and regular inclusion maps. -/
theorem regularFibreIntoSpace_homology (n : ℕ) :
    singularHomologyMap regularFibreIntoSpace n =
      (singularHomologyMap originalRegularInclusion n).comp
        (singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) n) :=
  singularHomologyMap_comp _ _ _

/-- Once the regular piece is onto and its source kernel is filled, the original fibre is onto. -/
theorem regularFibreIntoSpace_homology_surjective (n : ℕ)
    (hs : Function.Surjective (nativeCapKernelSourceMap n))
    (hr : Function.Surjective (singularHomologyMap originalRegularInclusion (n + 1))) :
    Function.Surjective (singularHomologyMap regularFibreIntoSpace (n + 1)) := by
  intro x
  obtain ⟨r, hr⟩ := hr x
  obtain ⟨b, a, hb⟩ := exists_fibre_capKernel_decomposition n hs r
  have hz : singularHomologyMap originalRegularInclusion (n + 1)
      (nativeCapKernelRegularMap (n + 1) a) = 0 :=
    (regularInclusion_eq_zero_iff_native (n + 1) _).mpr ⟨a, rfl⟩
  refine ⟨b, ?_⟩
  rw [regularFibreIntoSpace_homology, LinearMap.comp_apply]
  have h := congrArg (singularHomologyMap originalRegularInclusion (n + 1)) hb
  rw [map_add, hz, add_zero, hr] at h
  exact h

/-- Surjectivity of the native regular relation map gives surjectivity of the full original
signed star map, since the original filling maps are already onto. -/
theorem starLeft_surjective_of_nativeCapKernel (n : ℕ)
    (h : Function.Surjective (nativeCapKernelRegularMap n)) :
    Function.Surjective (starLeftHomologyMap n) := by
  intro p
  obtain ⟨b, hb⟩ := starOverlapToFillingsHomologyMap_surjective n (-p.2)
  have hrel : p.1 - starOverlapToRegularHomologyMap n b ∈
      LinearMap.range (nativeCapKernelRegularMap n) :=
    h (p.1 - starOverlapToRegularHomologyMap n b)
  rw [nativeCapKernelRegularMap_range] at hrel
  obtain ⟨c, hc⟩ := hrel
  have hc' : starOverlapToRegularHomologyMap n c.val =
      p.1 - starOverlapToRegularHomologyMap n b := hc
  refine ⟨c.val + b, ?_⟩
  rw [starLeft_regular_fillings]
  apply Prod.ext
  · change starOverlapToRegularHomologyMap n (c.val + b) = p.1
    rw [map_add, hc', sub_add_cancel]
  · change -starOverlapToFillingsHomologyMap n (c.val + b) = p.2
    rw [map_add, c.property, zero_add, hb, neg_neg]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.CapElimination
