import Wikipedia.HopfProblem.HolomorphicMeromorphicPowerDescent
import Wikipedia.HopfProblem.HolomorphicMeromorphicProductFractions
import Wikipedia.HopfProblem.HolomorphicMeromorphicProductDescent
import Wikipedia.HopfProblem.HolomorphicMeromorphicScalar

/-!
# Extending a base function through a genuine local power model

An actual nonzero product denominator has a fixed-fibre slice which is
not identically zero on the connected base domain. Its isolated zeros
leave a punctured neighborhood where the base function composed with a
positive power is an ordinary quotient of analytic functions. Scalar
power descent then proves meromorphy of the base function at the origin.
No preferred transverse slice or nonvanishing denominator value at the
central point is assumed.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicPowerModelExtension

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A genuine analytic product fraction along a positive power model
forces meromorphic extension of the original scalar base function. -/
theorem meromorphicAt_of_product_fraction_power_model
    {U : Set ℂ} {V : Set E} {p q : ℂ × E → ℂ} {f : ℂ → ℂ} {n : ℕ}
    (hUopen : IsOpen U) (hU : IsPreconnected U) (hzero : (0 : ℂ) ∈ U)
    (hp : AnalyticOnNhd ℂ p (U ×ˢ V)) (hq : AnalyticOnNhd ℂ q (U ×ˢ V))
    (hne : ∃ a ∈ U, ∃ w ∈ V, q (a, w) ≠ 0) (hn : 0 < n)
    (hagree : ∀ z ∈ U, z ≠ 0 → ∀ w ∈ V, q (z, w) ≠ 0 →
      f (z ^ n) = p (z, w) / q (z, w)) : MeromorphicAt f 0 := by
  obtain ⟨a, ha, w, hw, hqw⟩ := hne
  have hqs : AnalyticOnNhd ℂ (fun z => q (z, w)) U :=
    fun z hz => (hq (z, w) ⟨hz, hw⟩).curry_left
  have hqgerm : ¬ (fun z => q (z, w)) =ᶠ[𝓝 (0 : ℂ)] 0 :=
    HolomorphicMeromorphicProductFractions.nonzero_germ_on_preconnected hU hqs
      ⟨a, ha, hqw⟩ hzero
  have hqnear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), q (z, w) ≠ 0 :=
    (hqs 0 hzero).eventually_eq_zero_or_eventually_ne_zero.resolve_left hqgerm
  have he : (fun z => f (z ^ n)) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z => p (z, w) / q (z, w) := by
    filter_upwards [nhdsWithin_le_nhds (hUopen.mem_nhds hzero), hqnear,
      self_mem_nhdsWithin] with z hz hzq hz0
    exact hagree z hz hz0 w hw hzq
  exact HolomorphicMeromorphicPowerDescent.meromorphicAt_of_comp_pow hn
    ((((hp (0, w) ⟨hzero, hw⟩).curry_left.meromorphicAt).div
      (hqs 0 hzero).meromorphicAt).congr he.symm)

/-- The same extension statement for native local holomorphic
numerators and denominators on the literal product open set. -/
theorem meromorphicAt_of_native_product_fraction_power_model
    (U : Opens ℂ) (V : Opens E) [PreconnectedSpace U] [Nonempty V]
    (hzero : (0 : ℂ) ∈ U)
    (p q : HolomorphicFunctionSheaf.Section 𝓘(ℂ, ℂ × E) (ℂ × E)
      (HolomorphicMeromorphic.ProductDescent.box U V))
    (hq : ∀ x : HolomorphicMeromorphic.ProductDescent.box U V,
      HolomorphicMeromorphic.holomorphicGerm 𝓘(ℂ, ℂ × E) (ℂ × E)
        (HolomorphicMeromorphic.ProductDescent.box U V) x q ≠ 0)
    {f : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (hagree : ∀ (z : U) (w : V), z.val ≠ 0 →
      q (HolomorphicMeromorphic.ProductDescent.boxPoint U V z w) ≠ 0 →
      f (z.val ^ n) = p (HolomorphicMeromorphic.ProductDescent.boxPoint U V z w) /
        q (HolomorphicMeromorphic.ProductDescent.boxPoint U V z w)) :
    MeromorphicAt f 0 := by
  let : Nonempty U := ⟨⟨0, hzero⟩⟩
  obtain ⟨w, hw⟩ := HolomorphicMeromorphic.ProductDescent.exists_slice_nonzero_germs U V q hq
  let p₀ := HolomorphicMeromorphic.ProductDescent.sliceHolomorphic U V w p
  let q₀ := HolomorphicMeromorphic.ProductDescent.sliceHolomorphic U V w q
  let P := HolomorphicFunctionSheaf.extendSection U p₀
  let Q := HolomorphicFunctionSheaf.extendSection U q₀
  have hP : AnalyticAt ℂ P 0 := HolomorphicFunctionSheaf.extendSection_analyticAt U p₀ 0 hzero
  have hQ : AnalyticAt ℂ Q 0 := HolomorphicFunctionSheaf.extendSection_analyticAt U q₀ 0 hzero
  have hqnear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q z ≠ 0 :=
    HolomorphicMeromorphic.extendSection_eventually_ne_zero_of_holomorphicGerm_ne_zero
      U q₀ 0 hzero (hw ⟨0, hzero⟩)
  have he : (fun z => f (z ^ n)) =ᶠ[𝓝[≠] (0 : ℂ)] fun z => P z / Q z := by
    filter_upwards [nhdsWithin_le_nhds (U.isOpen.mem_nhds hzero), hqnear,
      self_mem_nhdsWithin] with z hz hzq hz0
    have hQz : Q z = q₀ ⟨z, hz⟩ := HolomorphicFunctionSheaf.extendSection_apply U q₀ z hz
    have hPz : P z = p₀ ⟨z, hz⟩ := HolomorphicFunctionSheaf.extendSection_apply U p₀ z hz
    rw [hPz, hQz]
    exact hagree ⟨z, hz⟩ w hz0 (fun h => hzq (hQz.trans h))
  exact HolomorphicMeromorphicPowerDescent.meromorphicAt_of_comp_pow hn
    ((hP.meromorphicAt.div hQ.meromorphicAt).congr he.symm)

end Wikipedia.HopfProblem.HolomorphicMeromorphicPowerModelExtension
