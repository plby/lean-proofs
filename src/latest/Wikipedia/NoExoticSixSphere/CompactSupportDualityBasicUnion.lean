import Wikipedia.NoExoticSixSphere.CompactSupportDualityOpens
import Wikipedia.NoExoticSixSphere.OpenCoverPropertyInduction
import Mathlib.Order.CompleteLattice.Finset

/-!
# Arbitrary unions from an intersection-stable family of duality opens

Finite-union induction proves duality on finite subunions, including
their required overlap cases. Those subunions form a directed family
with the same supremum as the original family. The checked actual cap
directed-union theorem therefore proves duality on the full union.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- An intersection-stable collection of genuine duality opens permits arbitrary unions. -/
theorem duality_iSup_of_basic_family (B : Opens M → Prop)
    (hB : ∀ U, B U → Duality (E := E) n U)
    (hBI : ∀ U V, B U → B V → B (U ⊓ V))
    {ι : Type*} (U : ι → Opens M) (hU : ∀ i, B (U i)) :
    Duality (E := E) n (⨆ i, U i : Opens M) := by
  classical
  have hfinite (s : Finset ι) : Duality (E := E) n (s.sup U : Opens M) :=
    OpenCoverProperty.finite_sup (fun W : Opens M => Duality (E := E) n W) B
      (duality_opens_bot (E := E) n) hB hBI (duality_opens_sup (E := E) n)
      s U (fun i _ => hU i)
  have hd : Directed (· ≤ ·) (fun s : Finset ι => s.sup U) := by
    intro s t
    exact ⟨s ∪ t, Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have he : (⨆ s : Finset ι, s.sup U) = ⨆ i, U i := by
    simpa only [Finset.sup_eq_iSup] using (iSup_eq_iSup_finset U).symm
  exact (congrArg (fun W : Opens M => Duality (E := E) n W) he).mp
    (duality_opens_iSup (E := E) n (fun s : Finset ι => s.sup U) hd hfinite)

end NoExoticSixSphere.CompactSupportCapMap
