import Wikipedia.SmoothSixDPoincare.CornerStripData

/-!
# Restricting clean strips while preserving their actual maps

Restriction changes only the neighborhood and its positive width. All contact,
smoothness, injectivity, and complete endpoint-germ properties are retained.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.CleanStripPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {S T : Set M} {a : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M}

/-- Restrict the domain and width, without changing any value of the strip map. -/
def restrict (k : CleanStripPatch (E := E) S T a k₀ k₁)
    {ε : ℝ} (hε : 0 < ε) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hrect : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ U) (hUk : U ⊆ k.domain) :
    CleanStripPatch (E := E) S T a k₀ k₁ := by
  refine {
    width := ε
    width_pos := hε
    domain := U
    open_domain := hU
    contains_strip := hrect
    map := k.map
    smooth := k.smooth.mono hUk
    injective := k.injective.mono hUk
    closed_embedding := ?_
    derivative_injective := fun p hp => k.derivative_injective p (hUk hp)
    first_sheet := fun p hp => k.first_sheet p (hUk hp)
    second_sheet := fun p hp => k.second_sheet p (hUk hp)
    center := k.center
    left_germ := k.left_germ
    right_germ := k.right_germ }
  let R := Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε
  let : CompactSpace R := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have hc : Continuous (fun p : R => k.map p) :=
    continuousOn_iff_continuous_domRestrict.mp
      (k.smooth.continuousOn.mono (hrect.trans hUk))
  apply hc.isClosedEmbedding
  intro p q hpq
  exact Subtype.ext (k.injective (hUk (hrect p.property)) (hUk (hrect q.property)) hpq)

theorem restrict_map (k : CleanStripPatch (E := E) S T a k₀ k₁)
    {ε : ℝ} (hε : 0 < ε) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hrect : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ U) (hUk : U ⊆ k.domain) :
    (k.restrict hε hU hrect hUk).map = k.map := rfl

end Wikipedia.SmoothSixDPoincare.CleanStripPatch
