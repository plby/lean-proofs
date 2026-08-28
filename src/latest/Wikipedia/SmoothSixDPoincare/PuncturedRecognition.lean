import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Recognition from a punctured Euclidean chart

This is a terminal topological step, not Smale's theorem: the punctured-space
homeomorphism is an explicit hypothesis. The geometric part of Smale's theorem
must construct such data from the smooth homotopy-sphere hypotheses.
-/

noncomputable section

open Set

namespace Wikipedia.SmoothSixDPoincare

variable {M E : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A compact Hausdorff space with one point removed homeomorphic to `E`
is the one-point compactification of `E`. -/
def homeomorphOnePointOfPunctured (p : M) (e : ({p}ᶜ : Set M) ≃ₜ E) :
    M ≃ₜ OnePoint E := by
  let f : E → M := Subtype.val ∘ e.symm
  have hf : Topology.IsEmbedding f :=
    Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
  have hr : range f = {p}ᶜ := by
    rw [show f = Subtype.val ∘ e.symm from rfl, range_comp,
      e.symm.surjective.range_eq, image_univ, Subtype.range_coe]
  exact (OnePoint.equivOfIsEmbeddingOfRangeEq p f hf hr).symm

/-- Punctured Euclidean recognition, with the standard Euclidean sphere as target. -/
def homeomorphSphereOfPunctured {n : ℕ} (p : M) (e : ({p}ᶜ : Set M) ≃ₜ E)
    (hdim : Module.finrank ℝ E = n) :
    M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  (homeomorphOnePointOfPunctured p e).trans
    (onePointEquivSphereOfFinrankEq (by simp [hdim]))

end Wikipedia.SmoothSixDPoincare
