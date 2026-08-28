import Wikipedia.HopfProblem.CuspPositiveRetractionOrthant
import Wikipedia.HopfProblem.CuspPositiveRetractionSupported
import Wikipedia.HopfProblem.CuspPositiveRetractionPatching

/-!
# Local collapse in a genuine positive toric chart

The explicit orthant deformation extends through any open chart in which
the defining function is the coordinate product.  No local or global
deformation retraction is an input: the deformation is subtraction of the
smallest coordinate, multiplied by the compactly supported distance cutoff.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- A product chart around a zero of a nonnegative function produces an
actual supported collapse of an open neighborhood of that point. -/
theorem exists_localCollapse_of_orthant_chart (f : C(X, ℝ))
    (e : OpenPartialHomeomorph Orthant X) {r₀ : Orthant}
    (hr₀ : r₀ ∈ e.source) (hzero : height r₀ = 0)
    (hheight : ∀ r ∈ e.source, f (e r) = height r) :
    ∃ A : CuspRetraction.Patching.LocalCollapse f, e r₀ ∈ A.collapseSet := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp e.open_source r₀ hr₀
  let U := Metric.ball r₀ R
  let : Nonempty U := ⟨⟨r₀, Metric.mem_ball_self hR⟩⟩
  let ep : U → X := fun r => e r.1
  have hep : IsOpenEmbedding ep := by
    exact e.isOpenEmbedding_restrict.comp
      (IsOpenEmbedding.inclusion hball
        (Metric.isOpen_ball.preimage continuous_subtype_val))
  let H : C(unitInterval × U, U) :=
    ⟨fun p => ⟨localShrink r₀ R p.1 p.2.1,
      localShrink_map_ball hzero hR p.1 p.2.2⟩,
      ((localShrink_continuous r₀ R).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩
  let K : Set U := Subtype.val ⁻¹' Metric.closedBall r₀ (R / 3)
  have hK : IsCompact K := by
    apply IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (isCompact_closedBall r₀ (R / 3))
    intro r hr
    have hrU : r ∈ U := by
      change dist r r₀ < R
      have hd : dist r r₀ ≤ R / 3 := hr
      linarith
    exact ⟨⟨r, hrU⟩, rfl⟩
  have hfix : ∀ (s : unitInterval) (r : U), r ∉ K → H (s, r) = r := by
    intro s r hr
    exact Subtype.ext (localShrink_eq_self_of_not_mem_closedBall r₀ hR s hr)
  have hH0 : ∀ r : U, H (0, r) = r := by
    intro r
    exact Subtype.ext (localShrink_zero r₀ R r.1)
  have hHfix : ∀ (s : unitInterval) (r : U), f (ep r) = 0 → H (s, r) = r := by
    intro s r hr
    have hz : height r.1 = 0 := (hheight r.1 (hball r.2)).symm.trans hr
    exact Subtype.ext (localShrink_fixed r₀ R s hz)
  have hHle : ∀ (s : unitInterval) (r : U), f (ep (H (s, r))) ≤ f (ep r) := by
    intro s r
    change f (e (H (s, r)).1) ≤ f (e r.1)
    rw [hheight (H (s, r)).1 (hball (H (s, r)).2), hheight r.1 (hball r.2)]
    exact localShrink_height_le r₀ R s r.1
  let L : Set U := Subtype.val ⁻¹' Metric.ball r₀ (R / 4)
  have hL : IsOpen L := Metric.isOpen_ball.preimage continuous_subtype_val
  let A : CuspRetraction.Patching.LocalCollapse f :=
    { homotopy := Supported.embeddingMap ep hep H K hK hfix
      map_zero := Supported.embeddingExtend_id ep hep H 0 hH0
      fixes_zero := fun s x hx =>
        Supported.embeddingExtend_fixed ep hep H {y | f y = 0} hHfix s x hx
      nonincreasing := Supported.embeddingExtend_height_nonincrease ep hep H f hHle
      collapseSet := ep '' L
      isOpen_collapseSet := hep.isOpenMap L hL
      map_one_zero := by
        rintro x ⟨r, hr, rfl⟩
        change f (Supported.embeddingExtend ep hep H (1, ep r)) = 0
        rw [Supported.embeddingExtend_chart]
        change f (e (H (1, r)).1) = 0
        rw [hheight (H (1, r)).1 (hball (H (1, r)).2)]
        exact localShrink_one_height_of_mem_ball r₀ hR hr }
  refine ⟨A, ⟨⟨r₀, Metric.mem_ball_self hR⟩, ?_, rfl⟩⟩
  exact Metric.mem_ball_self (by linarith)

/-- With such actual charts at every zero, compactness produces a genuine
strong deformation retraction on all sufficiently small closed sublevels. -/
theorem exists_small_sublevel_collapse_of_orthant_charts (f : C(X, ℝ))
    (hf : ∀ x, 0 ≤ f x) {r : ℝ} (hr : 0 < r)
    (hcompact : IsCompact {x : X | f x ≤ r})
    (hcharts : ∀ x : X, f x = 0 →
      ∃ (e : OpenPartialHomeomorph Orthant X) (r₀ : Orthant),
        r₀ ∈ e.source ∧ e r₀ = x ∧
        ∀ r ∈ e.source, f (e r) = height r) :
    ∃ η : ℝ, 0 < η ∧ η ≤ r ∧
      ∃ A : CuspRetraction.Patching.LocalCollapse f,
        {x : X | f x ≤ η} ⊆ A.collapseSet := by
  apply CuspRetraction.Patching.exists_small_sublevel_localCollapse f hf hr hcompact
  intro x hx
  obtain ⟨e, r₀, hr₀, he, hh⟩ := hcharts x hx
  have hzero : height r₀ = 0 := (hh r₀ hr₀).symm.trans (he ▸ hx)
  obtain ⟨A, hA⟩ := exists_localCollapse_of_orthant_chart f e hr₀ hzero hh
  exact ⟨A, he ▸ hA⟩

end Wikipedia.HopfProblem.CuspPositiveRetraction
