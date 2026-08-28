import Wikipedia.NoExoticSixSphere.InvolutionQuotientTopology
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Original local charts descend near free orbits

A chart on the original space restricts to an open neighborhood disjoint from
its swapped copy. The open embedding of that neighborhood into the actual
quotient transports the chart, with its value at the marked point unchanged.
The entire transported source avoids the image of the fixed-point set.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.InvolutionQuotient

variable {X H : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace H]

theorem exists_free_chart_with_lifts (σ : X → X) (hσ : Involutive σ) (hc : Continuous σ)
    (x : X) (hx : σ x ≠ x) (e : OpenPartialHomeomorph X H) (he : x ∈ e.source) :
    ∃ d : OpenPartialHomeomorph (Orbit σ hσ) H,
      proj σ hσ x ∈ d.source ∧ d (proj σ hσ x) = e x ∧
      Disjoint d.source (proj σ hσ '' {y | σ y = y}) ∧
      ∀ q ∈ d.source, ∃ y ∈ e.source, proj σ hσ y = q ∧ d q = e y := by
  let : Nonempty H := ⟨e x⟩
  obtain ⟨U, hU, hxU, hdis⟩ := exists_free_neighborhood σ hc x hx
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  let i := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → X)
  let c : OpenPartialHomeomorph U H := i.trans e
  have hq := isOpenEmbedding_restrict_proj σ hσ hc hU hdis
  let d := c.lift_openEmbedding hq
  have hxc : (⟨x, hxU⟩ : U) ∈ c.source := ⟨mem_univ _, he⟩
  refine ⟨d, ⟨⟨x, hxU⟩, hxc, rfl⟩, ?_, ?_, ?_⟩
  · change (c.lift_openEmbedding hq) (proj σ hσ (⟨x, hxU⟩ : U).val) = e x
    rw [c.lift_openEmbedding_apply hq]
    rfl
  · apply disjoint_left.mpr
    rintro y ⟨u, hu, rfl⟩ hy
    have hfix := (mem_fixed_orbits_iff σ hσ u.val).mp hy
    have hsu : σ u.val ∈ U := hfix.symm ▸ u.property
    exact (disjoint_left.mp hdis) u.property hsu
  · rintro q ⟨u, hu, rfl⟩
    refine ⟨u.val, hu.2, rfl, ?_⟩
    change (c.lift_openEmbedding hq) (proj σ hσ u.val) = e u.val
    rw [c.lift_openEmbedding_apply hq]
    rfl

theorem exists_free_chart (σ : X → X) (hσ : Involutive σ) (hc : Continuous σ)
    (x : X) (hx : σ x ≠ x) (e : OpenPartialHomeomorph X H) (he : x ∈ e.source) :
    ∃ d : OpenPartialHomeomorph (Orbit σ hσ) H,
      proj σ hσ x ∈ d.source ∧ d (proj σ hσ x) = e x ∧
      Disjoint d.source (proj σ hσ '' {y | σ y = y}) := by
  obtain ⟨d, hd, hvalue, hdis, _⟩ := exists_free_chart_with_lifts σ hσ hc x hx e he
  exact ⟨d, hd, hvalue, hdis⟩

end NoExoticSixSphere.InvolutionQuotient
