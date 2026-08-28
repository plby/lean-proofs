import Wikipedia.HopfProblem.DegreeCollapseIntegralDualityBasicUnion
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Actual integral cap duality on every Euclidean open subset

Gauge rescaling identifies each nonempty bounded convex open set with
the full Euclidean model. The empty case and closure of bounded convex
opens under intersections give an actual basic family. Its genuine
union is every Euclidean open set, so the proved cover assembly applies.
-/

noncomputable section

open TopologicalSpace Metric Bornology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

theorem bounded_convex_open_duality (U : Set E) (hU : IsOpen U)
    (hc : Convex ℝ U) (hb : IsBounded U) : HomeomorphicDuality (n + 3) U := by
  by_cases hne : U.Nonempty
  · obtain ⟨e, he, _, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hc (by simpa only [hU.interior_eq] using hne) hb
    rw [hU.interior_eq] at he
    let e' : U ≃ₜ ball (0 : E) 1 :=
      (e.isEmbedding.homeomorphImage U).trans (Homeomorph.setCongr he)
    exact homeomorphicDuality_of_euclidean_homeomorph (E := E) n
      (e'.trans Homeomorph.unitBall.symm)
  · have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst U
    exact homeomorphicDuality_of_isEmpty (∅ : Set E) (n + 3)

/-- Every actual Euclidean open subset satisfies duality for every primitive integral family. -/
theorem euclidean_open_duality (U : Opens E) : HomeomorphicDuality (n + 3) U := by
  let B (V : Opens E) : Prop := Convex ℝ (V : Set E) ∧ IsBounded (V : Set E)
  have hB (V : Opens E) (hV : B V) : HomeomorphicDuality (n + 3) V :=
    bounded_convex_open_duality n (V : Set E) V.isOpen hV.1 hV.2
  have hBI (V W : Opens E) (hV : B V) (hW : B W) : B (V ⊓ W) :=
    ⟨hV.1.inter hW.1, hV.2.subset Set.inter_subset_left⟩
  let I := {V : Opens E // V ≤ U ∧ B V}
  let F : I → Opens E := fun V => V.val
  have he : (⨆ i, F i) = U := by
    apply le_antisymm
    · exact iSup_le fun i => i.property.1
    · intro x hx
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
      let V : Opens E := ⟨ball x r, isOpen_ball⟩
      let i : I := ⟨V, hball, convex_ball x r, isBounded_ball⟩
      exact Opens.mem_iSup.mpr ⟨i, mem_ball_self hr⟩
  exact (congrArg (fun V : Opens E => HomeomorphicDuality (n + 3) V) he).mp
    (duality_iSup_of_basic_family (n + 3) B hB hBI F (fun i => i.property.2))

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality
