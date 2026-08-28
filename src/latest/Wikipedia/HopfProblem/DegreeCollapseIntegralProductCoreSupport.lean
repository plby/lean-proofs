import Wikipedia.HopfProblem.DegreeCollapseIntegralRadialSupport
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCore
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Original core-supported cohomology computes the whole open product

For a compact base and a proper normed vector fiber, compact radial tubes
are cofinal among all actual compact supports. Their original extensions
from the zero section are already proved bijective. Thus the original
map from core-supported cohomology into compact-support cohomology is
bijective in every degree, with the original forward map retained.
-/

noncomputable section

open Function Set Metric TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRadialSupport

variable (B E : Type) [TopologicalSpace B] [CompactSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedSpace ℝ E] in
theorem support_isCompact (r : ℝ) : IsCompact (support B E r) := by
  have he : support B E r = (univ : Set B) ×ˢ closedBall (0 : E) r := by
    ext p
    simp only [support, mem_ofPred_eq, mem_prod, mem_univ, true_and,
      mem_closedBall, dist_zero_right]
  rw [he]
  exact isCompact_univ.prod (isCompact_closedBall (0 : E) r)

def compactSupport (r : ℝ) : Compacts (B × E) := ⟨support B E r, support_isCompact B E r⟩

omit [NormedSpace ℝ E] in
theorem compactSupport_cofinal (L : Compacts (B × E)) :
    ∃ r : ℝ, 0 ≤ r ∧ L ≤ compactSupport B E r := by
  obtain ⟨a, ha⟩ := (L.isCompact.image (continuous_norm.comp continuous_snd)).bddAbove
  refine ⟨max a 0, le_max_right a 0, ?_⟩
  intro p hp
  exact (ha ⟨p, hp, rfl⟩).trans (le_max_left a 0)

theorem of_core_bijective (p : ℕ) :
    Bijective (IntegralCompactSupportCohomology.of (B × E) p (compactSupport B E 0)) := by
  apply IntegralCompactSupportCohomology.of_bijective_of_cofinal_extensions
  intro L
  obtain ⟨r, hr, hL⟩ := compactSupport_cofinal B E L
  exact ⟨compactSupport B E r, support_mono B E hr, hL, extend_bijective B E r hr p⟩

def coreToCompactEquiv (p : ℕ) : IntegralSupportedCohomology.Cohomology (support B E 0) p ≃ₗ[ℤ]
    IntegralCompactSupportCohomology.Cohomology (B × E) p :=
  LinearEquiv.ofBijective
    (IntegralCompactSupportCohomology.of (B × E) p (compactSupport B E 0)) (of_core_bijective B E p)

theorem coreToCompactEquiv_toLinearMap (p : ℕ) :
    (coreToCompactEquiv B E p).toLinearMap =
      IntegralCompactSupportCohomology.of (B × E) p (compactSupport B E 0) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRadialSupport
