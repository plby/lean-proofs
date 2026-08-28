import Wikipedia.HopfProblem.DegreeCollapseIntegralDualityOpens
import Wikipedia.NoExoticSixSphere.OpenCoverPropertyInduction
import Mathlib.Order.CompleteLattice.Finset

/-!
# Integral duality assembled from an intersection-stable family of actual opens

Finite-union induction proves duality on finite subunions, including
their required overlap cases. Those subunions form a directed family
with the same supremum as the original family. The checked actual cap
directed-union theorem therefore proves duality on the full union.
-/

noncomputable section

open TopologicalSpace NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

variable {M : Type} [TopologicalSpace M] (d : ℕ)

/-- An intersection-stable collection of genuine duality opens permits arbitrary unions. -/
theorem duality_iSup_of_basic_family (B : Opens M → Prop)
    (hB : ∀ U, B U → HomeomorphicDuality d U)
    (hBI : ∀ U V, B U → B V → B (U ⊓ V))
    {ι : Type*} (U : ι → Opens M) (hU : ∀ i, B (U i)) :
    HomeomorphicDuality d (⨆ i, U i : Opens M) := by
  classical
  have hfinite (s : Finset ι) : HomeomorphicDuality d (s.sup U : Opens M) :=
    OpenCoverProperty.finite_sup (fun W : Opens M => HomeomorphicDuality d W) B
      (duality_opens_bot d) hB hBI (duality_opens_sup d)
      s U (fun i _ => hU i)
  have hd : Directed (· ≤ ·) (fun s : Finset ι => s.sup U) := by
    intro s t
    exact ⟨s ∪ t, Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have he : (⨆ s : Finset ι, s.sup U) = ⨆ i, U i := by
    simpa only [Finset.sup_eq_iSup] using (iSup_eq_iSup_finset U).symm
  exact (congrArg (fun W : Opens M => HomeomorphicDuality d W) he).mp
    (duality_opens_iSup d (fun s : Finset ι => s.sup U) hd hfinite)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality
