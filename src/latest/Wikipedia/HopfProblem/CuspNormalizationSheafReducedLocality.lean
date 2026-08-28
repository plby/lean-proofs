import Wikipedia.HopfProblem.CuspNormalizationSheafReducedPredicate
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Locality of actual ambient holomorphic extension

A relative open set comes from an ambient open set. Intersecting this
ambient open with a neighbourhood carrying a holomorphic representative
proves the actual local extension condition is a local predicate.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

/-- Every open subset of a subspace is the inverse image of an actual
ambient open subset. -/
theorem exists_ambient_open {M : Type*} [TopologicalSpace M]
    (S : Set M) (W : Opens S) :
    ∃ V : Opens M, Subtype.val ⁻¹' (V : Set M) = (W : Set S) := by
  obtain ⟨V, hV, hpre⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp W.isOpen
  exact ⟨⟨V, hV⟩, hpre⟩

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- Local ambient extension is genuinely local on relative open sets. -/
theorem IsLocallyAmbient.locality {U : Opens S} (f : U → ℂ)
    (h : ∀ x : U, ∃ (W : Opens S) (_ : x.val ∈ W) (i : W ⟶ U),
      IsLocallyAmbient I S W (fun y => f (Set.inclusion i.le y))) :
    IsLocallyAmbient I S U f := by
  intro x
  obtain ⟨W, hxW, i, hW⟩ := h x
  obtain ⟨V, hxV, g, hg⟩ := hW ⟨x.val, hxW⟩
  obtain ⟨T, hT⟩ := exists_ambient_open S W
  have hxT : x.val.val ∈ T := by
    change x.val ∈ Subtype.val ⁻¹' (T : Set M)
    rw [hT]
    exact hxW
  refine ⟨V ⊓ T, ⟨hxV, hxT⟩,
    ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ inf_le_left g, ?_⟩
  intro y hy
  have hyW : y.val ∈ W := by
    change y.val ∈ (W : Set S)
    rw [← hT]
    exact hy.2
  have hi : Set.inclusion i.le ⟨y.val, hyW⟩ = y := Subtype.ext rfl
  change f y = g ⟨y.val.val, hy.1⟩
  simpa only [hi] using hg ⟨y.val, hyW⟩ hy.1

/-- The local predicate defining actual reduced holomorphic functions on
the subspace, independent of any normalization map. -/
def localPredicate : TopCat.LocalPredicate (fun _ : TopCat.of S => ℂ) where
  pred {U} f := IsLocallyAmbient I S U f
  res i _ hf := IsLocallyAmbient.restrict I S i.le hf
  locality f h := IsLocallyAmbient.locality I S f h

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
