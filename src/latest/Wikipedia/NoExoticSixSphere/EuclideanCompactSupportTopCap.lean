import Wikipedia.NoExoticSixSphere.ClosedBallTopCap
import Wikipedia.NoExoticSixSphere.CompactSupportCapMap

/-!
# Actual top compact-support duality on the Euclidean model

Every compact support lies in a closed ball. Equality of capped classes
can therefore be tested after extending both representatives to one ball,
where injectivity of the original cap map is proved. Surjectivity uses
the genuine class on a unit-ball support. Thus the actual direct-limit
cap map is bijective in top cohomological degree.
-/

noncomputable section

open Metric TopologicalSpace
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.CompactSupportCapMap

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Original compact-support caps are detected after enlarging both supports to a ball. -/
theorem euclidean_top_injective :
    Function.Injective (dualityMap (E := E) n E (n + 3) 0 (Nat.add_zero (n + 3))) := by
  intro a b hab
  obtain ⟨K, a, rfl⟩ := CompactSupportCohomology.exists_representative E (n + 3) a
  obtain ⟨L, b, rfl⟩ := CompactSupportCohomology.exists_representative E (n + 3) b
  rw [dualityMap_of, dualityMap_of] at hab
  obtain ⟨R, hR, hKL⟩ :=
    (K.isCompact.union L.isCompact).isBounded.subset_closedBall_lt 0 (0 : E)
  let B : Compacts E := ⟨closedBall (0 : E) R, isCompact_closedBall (0 : E) R⟩
  have hK : K ≤ B := fun _ hx => hKL (Or.inl hx)
  have hL : L ≤ B := fun _ hx => hKL (Or.inr hx)
  have he : CompactSupportCohomology.transition E (n + 3) K B hK a =
      CompactSupportCohomology.transition E (n + 3) L B hL b := by
    apply (ClosedBallLocalHomology.topCap_bijective E n R hR.le).1
    exact (CompactSupportedCapMap.dualityMap_extend (E := E) n hK K.isCompact B.isCompact
      (n + 3) 0 (Nat.add_zero (n + 3)) a).trans
      (hab.trans (CompactSupportedCapMap.dualityMap_extend (E := E) n hL
        L.isCompact B.isCompact (n + 3) 0 (Nat.add_zero (n + 3)) b).symm)
  exact (CompactSupportCohomology.of_transition E (n + 3) hK a).symm.trans
    ((congrArg (CompactSupportCohomology.of E (n + 3) B) he).trans
      (CompactSupportCohomology.of_transition E (n + 3) hL b))

/-- Every ambient zero-dimensional class is an actual cap of a unit-ball representative. -/
theorem euclidean_top_surjective :
    Function.Surjective (dualityMap (E := E) n E (n + 3) 0 (Nat.add_zero (n + 3))) := by
  intro b
  let B : Compacts E := ⟨closedBall (0 : E) 1, isCompact_closedBall (0 : E) 1⟩
  let F := ClosedBallLocalHomology.topCapEquiv E n 1 zero_le_one
  refine ⟨CompactSupportCohomology.of E (n + 3) B (F.symm b), ?_⟩
  exact F.apply_symm_apply b

/-- Top-degree compact-support duality for the genuine Euclidean cap map. -/
theorem euclidean_top_bijective :
    Function.Bijective (dualityMap (E := E) n E (n + 3) 0 (Nat.add_zero (n + 3))) :=
  ⟨euclidean_top_injective E n, euclidean_top_surjective E n⟩

/-- This equivalence retains the original direct-limit cap as its forward map. -/
def euclideanTopEquiv : CompactSupportCohomology.Cohomology E (n + 3) ≃ₗ[ℤ]
    ModHomology 2 E 0 :=
  LinearEquiv.ofBijective (dualityMap (E := E) n E (n + 3) 0 (Nat.add_zero (n + 3)))
    (euclidean_top_bijective E n)

theorem euclideanTopEquiv_toLinearMap :
    (euclideanTopEquiv E n).toLinearMap =
      dualityMap (E := E) n E (n + 3) 0 (Nat.add_zero (n + 3)) := rfl

end NoExoticSixSphere.CompactSupportCapMap
