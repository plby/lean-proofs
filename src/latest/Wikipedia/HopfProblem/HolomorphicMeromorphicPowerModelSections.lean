import Wikipedia.HopfProblem.HolomorphicMeromorphicPowerModelExtension
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackPowerProduct

/-!
# Scalar extension through an actual native meromorphic power model

An arbitrary native meromorphic section supplies genuine local
numerator and denominator sections near the central product point.
Shrinking to a product of balls preserves their actual nonzero
denominator germs. Agreement with the native power-projection pullback
then gives the scalar cozero fraction identity, including when the
denominator vanishes along the central fibre. The proved product-fraction
power extension theorem therefore applies without any fraction data
being assumed for the original section.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicPowerModelSections

open HolomorphicMeromorphic HolomorphicMeromorphicPowerModelExtension

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IP" => modelWithCornersSelf ℂ (ℂ × E)

/-- Genuine meromorphic germ agreement near a central product point,
off the zero first-coordinate divisor, forces scalar meromorphic
extension of the base section through the origin. -/
theorem meromorphicAt_scalarValue_of_section_power_model
    {W : Opens (ℂ × E)} (s : Section IP (ℂ × E) W) (w₀ : E)
    (hcenter : ((0 : ℂ), w₀) ∈ W)
    {U : Opens ℂ} (t : Section I₁ ℂ U) {n : ℕ} (hn : 0 < n)
    (hnear : ∀ᶠ u : ℂ × E in 𝓝 ((0 : ℂ), w₀),
      ∃ hW : u ∈ W, u.1 ≠ 0 → ∃ hU : u.1 ^ n ∈ U,
        s ⟨u, hW⟩ = germPullback IP I₁ (powerFstMap n) (powerFstMap_isOpenMap n hn) u
          (t ⟨u.1 ^ n, hU⟩)) :
    MeromorphicAt (scalarValue t) 0 := by
  obtain ⟨V, hVW, hcenterV, p, q, hq, hs⟩ :=
    local_representation IP (ℂ × E) s ⟨((0 : ℂ), w₀), hcenter⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (V.isOpen.mem_nhds hcenterV) hnear)
  let A : Opens ℂ := ⟨Metric.ball (0 : ℂ) r, Metric.isOpen_ball⟩
  let B : Opens E := ⟨Metric.ball w₀ r, Metric.isOpen_ball⟩
  let _ : PreconnectedSpace A :=
    isPreconnected_iff_preconnectedSpace.mp Metric.isPreconnected_ball
  let _ : Nonempty B := ⟨⟨w₀, Metric.mem_ball_self hr⟩⟩
  have hboxball (u : ProductDescent.box A B) : u.val ∈ Metric.ball ((0 : ℂ), w₀) r := by
    rw [← ball_prod_same]
    exact u.property
  have hboxV : ProductDescent.box A B ≤ V := fun u hu => (hball (hboxball ⟨u, hu⟩)).1
  let pB := HolomorphicFunctionSheaf.restrictionAlgHom IP (ℂ × E) hboxV p
  let qB := HolomorphicFunctionSheaf.restrictionAlgHom IP (ℂ × E) hboxV q
  have hqB : ∀ u : ProductDescent.box A B,
      holomorphicGerm IP (ℂ × E) (ProductDescent.box A B) u qB ≠ 0 := by
    intro u hu
    exact hq (Set.inclusion hboxV u)
      ((holomorphicGerm_restrict IP (ℂ × E) hboxV u q).symm.trans hu)
  apply meromorphicAt_of_native_product_fraction_power_model A B
    (Metric.mem_ball_self hr) pB qB hqB hn
  intro z w hz hqw
  let u : ProductDescent.box A B := ProductDescent.boxPoint A B z w
  obtain ⟨huW, hagree⟩ := (hball (hboxball u)).2
  obtain ⟨huU, he⟩ := hagree hz
  let tP := pullbackSection IP I₁ (powerFstMap n) (powerFstMap_isOpenMap n hn) U t
  have he' : s ⟨u.val, huW⟩ = tP ⟨u.val, huU⟩ := he
  have hfrac : s ⟨u.val, huW⟩ = fraction IP (ℂ × E) (ProductDescent.box A B) pB qB u :=
    (hs (Set.inclusion hboxV u)).trans (fraction_restrict IP (ℂ × E) hboxV p q u).symm
  have hv := value_eq_of_germ_eq IP s tP u.val huW huU he'
  have hvp := value_powerFst_pullback n hn t ⟨u.val, huU⟩ hz
  have hvf := value_eq_local_fraction IP (ℂ × E) s pB qB u.val huW u.property hfrac hqw
  exact (hv.trans hvp).symm.trans hvf

end Wikipedia.HopfProblem.HolomorphicMeromorphicPowerModelSections
