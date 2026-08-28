import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization
import Wikipedia.HopfProblem.DegreeCollapseWholeLevelConnectionRealization

/-!
# Unique complete orbits for the two realized minimum branches

The one-dimensional attaching sphere has exactly two points. If those points
converge to distinct minima, each minimum meets the backward basin of the
one-handle in exactly one point on the original attaching level. Every
complete connecting orbit crosses that level, proving uniqueness up to time
translation. The argument uses the original function and remains valid after
flow-preserving changes of critical values.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem unique_connection_of_distinct_minimum_branches
    (S : SurgeryWindows E f) (hf : Continuous f) (G : Flow ℝ M)
    (p r q : criticalPoints E f) (hone : nativeMorseIndex E f q = 1)
    (hpr : p ≠ r) (hp : f p < S.lower q)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hback : ∀ x : (S.data q).LowerLevel,
      Tendsto (fun t => G t x) atBot (𝓝 q.val) ↔
        x ∈ range (S.data q).surgery.attachingSphere)
    (hu : Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val)
      atTop (𝓝 p.val))
    (hv : Tendsto (fun t => G t ((S.data q).surgery.attachingSphere v).val)
      atTop (𝓝 r.val)) :
    Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val)
      atBot (𝓝 q.val) ∧
      ∀ x, Tendsto (fun t => G t x) atBot (𝓝 q.val) →
        Tendsto (fun t => G t x) atTop (𝓝 p.val) →
        ∃ t, G t ((S.data q).surgery.attachingSphere u).val = x := by
  have hdim : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hone
  have huv : u ≠ v := by
    intro h
    apply hpr
    apply Subtype.ext
    exact tendsto_nhds_unique (h ▸ hu) hv
  have hbu : Tendsto (fun t => G t ((S.data q).surgery.attachingSphere u).val)
      atBot (𝓝 q.val) := (hback _).mpr (mem_range_self u)
  have hsingle (x : (S.data q).LowerLevel)
      (hb : Tendsto (fun t => G t x) atBot (𝓝 q.val))
      (hp' : Tendsto (fun t => G t x) atTop (𝓝 p.val)) :
      x = (S.data q).surgery.attachingSphere u := by
    obtain ⟨w, hw⟩ := (hback x).mp hb
    rcases unitSphere_eq_two_points_of_finrank_one hdim u v huv w with h | h
    · exact (congrArg (S.data q).surgery.attachingSphere h).symm.trans hw |>.symm
    · have hx : (S.data q).surgery.attachingSphere v = x := h ▸ hw
      have hrv : Tendsto (fun t => G t x) atTop (𝓝 r.val) := hx ▸ hv
      exact False.elim (hpr (Subtype.ext (tendsto_nhds_unique hp' hrv)))
  have h := FlowSuspension.unique_connection_of_level_basin_intersection G G hf
    (S.lower_lt_value q) hp id (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    ((S.data q).surgery.attachingSphere u) hbu hu hsingle
  exact ⟨h.1, h.2.2⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
