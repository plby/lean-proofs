import Wikipedia.NoExoticSixSphere.CorankOneCoordinateCover
import Wikipedia.NoExoticSixSphere.CorankOneSubmersiveFamily
import Wikipedia.NoExoticSixSphere.CorankOneIsolated

/-!
# Local corank-one regularity in arbitrary leading-block dimensions

An invertible derivative of the actual residual isolates a singular point.
The argument applies on an arbitrary specified region and does not require
global smoothness of the original operator family. Parametric residual
regularity likewise works in any actual corank-one coordinate system.
-/

noncomputable section

open Set Function Filter Module TopologicalSpace
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff Topology

namespace NoExoticSixSphere.CorankOneCoordinates

open CorankOne

variable {X V W E F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem isDiscrete_singular_on (D : X → V →L[ℝ] W) (U : Set X)
    (hD : ∀ x ∈ U, ContDiffAt ℝ ∞ D x)
    (hres : ∀ x ∈ U, ¬ Injective (D x) → ∃ c : Coordinates V W E F,
      D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
        Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)) :
    IsDiscrete (U ∩ {x | ¬ Injective (D x)}) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro x hx
  obtain ⟨c, hxc, hz, hb⟩ := hres x hx.1 hx.2
  let R : X → F := fun y ↦ residual (operatorEquiv c (D y))
  have hR : ContDiffAt ℝ ∞ R x :=
    (contDiffAt_residual _ (leading_invertible hxc)).comp
      (f := fun y ↦ operatorEquiv c (D y)) x
      ((operatorEquiv c).contDiff.contDiffAt.comp x (hD x hx.1))
  let L : X ≃L[ℝ] F :=
    (LinearEquiv.ofBijective (fderiv ℝ R x).toLinearMap hb).toContinuousLinearEquiv
  have hL : HasFDerivAt R L.toContinuousLinearMap x :=
    (hR.differentiableAt (by simp)).hasFDerivAt
  let e := hR.toOpenPartialHomeomorph R hL (by simp)
  have hex : x ∈ e.source := hR.mem_toOpenPartialHomeomorph_source hL (by simp)
  have hn : D ⁻¹' (domain c : Set (V →L[ℝ] W)) ∈ 𝓝 x :=
    (hD x hx.1).continuousAt.preimage_mem_nhds ((domain c).isOpen.mem_nhds hxc)
  obtain ⟨N, hNc, hN, hxN⟩ := mem_nhds_iff.mp hn
  refine ⟨e.source ∩ N, e.open_source.inter hN, ?_⟩
  ext y
  constructor
  · rintro ⟨⟨hy, hyc⟩, hyU, hys⟩
    apply mem_singleton_iff.mpr
    apply e.injOn hy hex
    exact ((singular_iff_residual_zero (hNc hyc)).mp
      ((injective_operatorEquiv_iff c (D y)).not.mpr hys)).trans hz.symm
  · rintro rfl
    exact ⟨⟨hex, hxN⟩, hx⟩

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasurableSpace P] [BorelSpace P]

theorem ae_regular_submersive_coordinates (μ : Measure P) [IsAddHaarMeasure μ]
    (D : P × X → V →L[ℝ] W) (U : Opens (P × X)) (hD : ContDiffOn ℝ ∞ D U)
    (hs : ∀ q ∈ U, Surjective (fderiv ℝ D q)) (c : Coordinates V W E F) :
    ∀ᵐ a ∂μ, ∀ x, (a, x) ∈ U → D (a, x) ∈ domain c →
      residual (operatorEquiv c (D (a, x))) = 0 →
        Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D (a, y)))) x) := by
  let Q := operatorEquiv c
  have hQD : ContDiffOn ℝ ∞ (fun q ↦ Q (D q)) U := Q.contDiff.comp_contDiffOn hD
  have hsQD : ∀ q ∈ U, Surjective (fderiv ℝ (fun q ↦ Q (D q)) q) := by
    intro q hq
    have hd := (hD.contDiffAt (U.isOpen.mem_nhds hq)).differentiableAt (by simp)
    have he := (Q.hasFDerivAt.comp q hd.hasFDerivAt).fderiv
    change Surjective (fderiv ℝ (Q ∘ D) q)
    rw [he]
    exact Q.surjective.comp (hs q hq)
  exact CorankOneSubmersion.ae_regular_family μ (fun q ↦ Q (D q)) U hQD hsQD

end NoExoticSixSphere.CorankOneCoordinates
