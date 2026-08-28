import Wikipedia.NoExoticSixSphere.EmptyCompactSupportDuality
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Actual cap duality on bounded convex open Euclidean sets

Gauge rescaling gives an actual homeomorphism of each nonempty bounded
convex open set with the unit ball, hence with the full model. The
proved homeomorphism cap square transfers the Euclidean calculation.
The empty case uses vanishing of the original chains and cochains.
-/

noncomputable section

open Metric Bornology

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (U : Set E) [ChartedSpace E U]

/-- An unconditional Euclidean basis case for the original compact-support cap maps. -/
theorem bounded_convex_open_duality (hU : IsOpen U) (hc : Convex ℝ U) (hb : IsBounded U) :
    Duality (E := E) n U := by
  by_cases hne : U.Nonempty
  · obtain ⟨e, he, _, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hc (by simpa only [hU.interior_eq] using hne) hb
    rw [hU.interior_eq] at he
    let e' : U ≃ₜ ball (0 : E) 1 :=
      (e.isEmbedding.homeomorphImage U).trans (Homeomorph.setCongr he)
    exact duality_of_euclidean_homeomorph (E := E) n (Homeomorph.unitBall.trans e'.symm)
  · have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst U
    exact duality_of_isEmpty (∅ : Set E) (E := E) n

end NoExoticSixSphere.CompactSupportCapMap
