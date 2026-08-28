import Wikipedia.NoExoticSixSphere.EuclideanCompactSupportTopCap
import Wikipedia.NoExoticSixSphere.ClosedBallModTwoVanishing
import Wikipedia.NoExoticSixSphere.FiniteCoefficientContractibleHomology

/-!
# Bijectivity of actual compact-support cap duality on Euclidean space

Closed balls compute every degree: the original top cap is bijective,
and all other complementary-degree source and target groups vanish.
Every compact support is contained in a ball, so the actual directed
limit also vanishes off the dimension. Together with the checked top
cap this proves Euclidean compact-support duality in every complementary
degree. No manifold local-to-global duality is asserted here.
-/

noncomputable section

open Metric TopologicalSpace
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- The genuine closed-ball cap is bijective in every pair of complementary degrees. -/
theorem ClosedBallLocalHomology.cap_bijective (R : ℝ) (hR : 0 ≤ R)
    (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (CompactSupportedCapMap.dualityMap (E := E) n
      (closedBall (0 : E) R) (isCompact_closedBall (0 : E) R) p q h) := by
  by_cases hq : q = 0
  · subst q
    have hp : p = n + 3 := by omega
    subst p
    exact ClosedBallLocalHomology.topCap_bijective E n R hR
  · let := ClosedBallLocalHomology.cohomology_subsingleton E n R hR p (by omega)
    let := contractible_modHomology_subsingleton E 2 (by decide) q hq
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-- An off-dimension compact-support class becomes zero after extension to an actual ball. -/
theorem CompactSupportCohomology.euclidean_eq_zero (p : ℕ) (hp : p ≠ n + 3)
    (a : CompactSupportCohomology.Cohomology E p) : a = 0 := by
  obtain ⟨K, a, rfl⟩ := CompactSupportCohomology.exists_representative E p a
  obtain ⟨R, hR, hK⟩ := K.isCompact.isBounded.subset_closedBall_lt 0 (0 : E)
  let B : Compacts E := ⟨closedBall (0 : E) R, isCompact_closedBall (0 : E) R⟩
  let := ClosedBallLocalHomology.cohomology_subsingleton E n R hR.le p hp
  have he : CompactSupportCohomology.transition E p K B hK a = 0 := Subsingleton.elim _ _
  exact (CompactSupportCohomology.of_transition E p hK a).symm.trans
    ((congrArg (CompactSupportCohomology.of E p B) he).trans
      (CompactSupportCohomology.of E p B).map_zero)

/-- Actual compact-support cohomology of the Euclidean model vanishes off its dimension. -/
theorem CompactSupportCohomology.euclidean_subsingleton (p : ℕ) (hp : p ≠ n + 3) :
    Subsingleton (CompactSupportCohomology.Cohomology E p) :=
  ⟨fun a b => (CompactSupportCohomology.euclidean_eq_zero E n p hp a).trans
    (CompactSupportCohomology.euclidean_eq_zero E n p hp b).symm⟩

/-- Euclidean duality is bijectivity of the original direct-limit cap map in every degree. -/
theorem CompactSupportCapMap.euclidean_bijective (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (CompactSupportCapMap.dualityMap (E := E) n E p q h) := by
  by_cases hq : q = 0
  · subst q
    have hp : p = n + 3 := by omega
    subst p
    exact CompactSupportCapMap.euclidean_top_bijective E n
  · let := CompactSupportCohomology.euclidean_subsingleton E n p (by omega)
    let := contractible_modHomology_subsingleton E 2 (by decide) q hq
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

/-- The Euclidean duality equivalence retains the original cap as its forward map. -/
def CompactSupportCapMap.euclideanEquiv (p q : ℕ) (h : p + q = n + 3) :
    CompactSupportCohomology.Cohomology E p ≃ₗ[ℤ] ModHomology 2 E q :=
  LinearEquiv.ofBijective (CompactSupportCapMap.dualityMap (E := E) n E p q h)
    (CompactSupportCapMap.euclidean_bijective E n p q h)

theorem CompactSupportCapMap.euclideanEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (CompactSupportCapMap.euclideanEquiv E n p q h).toLinearMap =
      CompactSupportCapMap.dualityMap (E := E) n E p q h := rfl

end NoExoticSixSphere
