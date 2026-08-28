import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-!
# A fixed-fibre representative for a meromorphic product fraction

An analytic denominator which is not identically zero has a fixed-fibre
slice whose analytic germ is nonzero at every point of the connected
base.  When numerator and denominator satisfy the fibrewise
cross-multiplication identity, this slice represents the same fraction
at every product point as an identity of neighborhood germs.

A nonzero denominator germ may have zero value.  Accordingly, equality
of scalar quotient values is asserted only where both denominator
values are nonzero; the cross-product germ identity holds everywhere.
-/

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicProductFractions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A nonzero analytic function on a preconnected set has a nonzero
neighborhood germ at every point of that set. -/
theorem nonzero_germ_on_preconnected {W : Set E} {f : E → ℂ}
    (hW : IsPreconnected W) (hf : AnalyticOnNhd ℂ f W)
    (hne : ∃ a ∈ W, f a ≠ 0) {x : E} (hx : x ∈ W) :
    ¬ f =ᶠ[𝓝 x] 0 := by
  obtain ⟨a, ha, hfa⟩ := hne
  intro hzero
  exact hfa (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hW hx hzero ha)

omit [NormedSpace ℂ E] in
/-- Pullback along the actual product projection preserves a nonzero
neighborhood germ.  The fixed-fibre inclusion detects vanishing. -/
theorem fst_nonzero_germ {b : ℂ → ℂ} {z : ℂ} (v : E)
    (hb : ¬ b =ᶠ[𝓝 z] 0) :
    ¬ (fun t : ℂ × E => b t.1) =ᶠ[𝓝 (z, v)] 0 := by
  intro hzero
  apply hb
  exact Filter.EventuallyEq.comp_tendsto hzero
    (continuousAt_id.prodMk continuousAt_const)

omit [NormedSpace ℂ E] in
/-- A cross-product identity on an open product holds as an actual
neighborhood-germ identity at each product point. -/
theorem cross_mul_eventuallyEq {U : Set ℂ} {V : Set E} {p q : ℂ × E → ℂ}
    (hU : IsOpen U) (hV : IsOpen V)
    (hcross : ∀ z ∈ U, ∀ v ∈ V, ∀ w ∈ V,
      p (z, v) * q (z, w) = p (z, w) * q (z, v))
    {w : E} (hw : w ∈ V) {z : ℂ} (hz : z ∈ U) {v : E} (hv : v ∈ V) :
    (fun t : ℂ × E => p t * q (t.1, w)) =ᶠ[𝓝 (z, v)]
      (fun t => p (t.1, w) * q t) := by
  filter_upwards [(hU.prod hV).mem_nhds ⟨hz, hv⟩] with t ht
  exact hcross t.1 ht.1 t.2 ht.2 w hw

/-- A fibrewise-constant analytic fraction has a representative obtained
by restricting both numerator and denominator to one fixed fibre point.
Its denominator germ is nonzero everywhere on the base, both product
denominator germs are nonzero everywhere, and cross-multiplication holds
as an actual neighborhood-germ identity even at denominator zeros. -/
theorem exists_fixed_slice_fraction {U : Set ℂ} {V : Set E}
    {p q : ℂ × E → ℂ} (hUopen : IsOpen U) (hU : IsPreconnected U)
    (hVopen : IsOpen V) (hV : IsPreconnected V)
    (hp : AnalyticOnNhd ℂ p (U ×ˢ V)) (hq : AnalyticOnNhd ℂ q (U ×ˢ V))
    (hne : ¬ EqOn q 0 (U ×ˢ V))
    (hcross : ∀ z ∈ U, ∀ v ∈ V, ∀ w ∈ V,
      p (z, v) * q (z, w) = p (z, w) * q (z, v)) :
    ∃ w ∈ V,
      AnalyticOnNhd ℂ (fun z => p (z, w)) U ∧
      AnalyticOnNhd ℂ (fun z => q (z, w)) U ∧
      (∀ z ∈ U, ¬ (fun a => q (a, w)) =ᶠ[𝓝 z] 0) ∧
      (∀ z ∈ U, ∀ v ∈ V, ¬ q =ᶠ[𝓝 (z, v)] 0) ∧
      (∀ z ∈ U, ∀ v ∈ V, ¬ (fun t : ℂ × E => q (t.1, w)) =ᶠ[𝓝 (z, v)] 0) ∧
      (∀ z ∈ U, ∀ v ∈ V,
        (fun t : ℂ × E => p t * q (t.1, w)) =ᶠ[𝓝 (z, v)]
          (fun t => p (t.1, w) * q t)) ∧
      (∀ z ∈ U, ∀ v ∈ V, q (z, v) ≠ 0 → q (z, w) ≠ 0 →
        p (z, v) / q (z, v) = p (z, w) / q (z, w)) := by
  have hwitness : ∃ a ∈ U, ∃ w ∈ V, q (a, w) ≠ 0 := by
    by_contra hnone
    apply hne
    rintro ⟨a, w⟩ ⟨ha, hw⟩
    by_contra hn
    exact hnone ⟨a, ha, w, hw, hn⟩
  obtain ⟨a, ha, w, hw, hqaw⟩ := hwitness
  have hpw : AnalyticOnNhd ℂ (fun z => p (z, w)) U :=
    fun z hz => (hp (z, w) ⟨hz, hw⟩).curry_left
  have hqw : AnalyticOnNhd ℂ (fun z => q (z, w)) U :=
    fun z hz => (hq (z, w) ⟨hz, hw⟩).curry_left
  have hbase : ∀ z ∈ U, ¬ (fun a => q (a, w)) =ᶠ[𝓝 z] 0 :=
    fun _ hz => nonzero_germ_on_preconnected hU hqw ⟨a, ha, hqaw⟩ hz
  refine ⟨w, hw, hpw, hqw, hbase, ?_, ?_, ?_, ?_⟩
  · intro z hz v hv
    exact nonzero_germ_on_preconnected (hU.prod hV) hq
      ⟨(a, w), ⟨ha, hw⟩, hqaw⟩ ⟨hz, hv⟩
  · intro z hz v _
    exact fst_nonzero_germ v (hbase z hz)
  · intro z hz v hv
    exact cross_mul_eventuallyEq hUopen hVopen hcross hw hz hv
  · intro z hz v hv hqv hqz
    exact (div_eq_div_iff hqv hqz).mpr (hcross z hz v hv w hw)

end Wikipedia.HopfProblem.HolomorphicMeromorphicProductFractions
