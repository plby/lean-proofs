import Wikipedia.HopfProblem.DegreeCollapseIntegralBallFundamentalClass

/-!
# Coherent oriented integral classes on bounded Euclidean supports

Restrict the constructed class from an enclosing ball. The nested-ball
formula proves independence of that choice and exact compatibility with
every support restriction. In particular every compact Euclidean support
has an actual integral class with the prescribed signed local values.
This does not yet assert detection for arbitrary compact supports or
compatibility of different manifold charts.
-/

noncomputable section

open Metric

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralEuclideanOrientation

open NoExoticSixSphere SupportedRelativeHomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 1) + 1)]

/-- Restrict the original oriented ball class through the original identity map of pairs. -/
def fromBall (K : Set E) (R : ℝ) (hR : 0 ≤ R) (hKR : K ⊆ closedBall (0 : E) R) :
    Homology (ModuleCat.of ℤ ℤ) K (n + 2) :=
  restrict (ModuleCat.of ℤ ℤ) hKR (n + 2)
    (IntegralBallOrientation.fundamentalClass E n R hR)

theorem fromBall_evaluate (K : Set E) (R : ℝ) (hR : 0 ≤ R)
    (hKR : K ⊆ closedBall (0 : E) R) (x : E) (hx : x ∈ K) :
    evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) (fromBall E n K R hR hKR) =
      IntegralBallOrientation.pointClass E n x :=
  (LinearMap.congr_fun (evaluate_restrict (ModuleCat.of ℤ ℤ) hKR x hx (n + 2))
    (IntegralBallOrientation.fundamentalClass E n R hR)).trans
      (IntegralBallOrientation.fundamentalClass_evaluate E n R hR x (hKR hx))

theorem fromBall_enlarge (K : Set E) (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hRS : R ≤ S) (hKR : K ⊆ closedBall (0 : E) R) (hKS : K ⊆ closedBall (0 : E) S) :
    fromBall E n K R hR hKR = fromBall E n K S hS hKS := by
  unfold fromBall
  rw [← IntegralBallOrientation.restrict_fundamentalClass E n R S hR hS hRS]
  exact (LinearMap.congr_fun (restrict_trans (ModuleCat.of ℤ ℤ) hKR
    (closedBall_subset_closedBall hRS) (n + 2))
      (IntegralBallOrientation.fundamentalClass E n S hS)).symm

/-- No enclosing-ball choice changes the actual integral class. -/
theorem fromBall_independent (K : Set E) (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hKR : K ⊆ closedBall (0 : E) R) (hKS : K ⊆ closedBall (0 : E) S) :
    fromBall E n K R hR hKR = fromBall E n K S hS hKS := by
  have hT : 0 ≤ max R S := hR.trans (le_max_left R S)
  have hKT : K ⊆ closedBall (0 : E) (max R S) :=
    hKR.trans (closedBall_subset_closedBall (le_max_left R S))
  exact (fromBall_enlarge E n K R (max R S) hR hT (le_max_left R S) hKR hKT).trans
    (fromBall_enlarge E n K S (max R S) hS hT (le_max_right R S) hKS hKT).symm

/-- The actual integral relative class on a bounded support. -/
def fundamentalClass (K : Set E) (hK : Bornology.IsBounded K) :
    Homology (ModuleCat.of ℤ ℤ) K (n + 2) :=
  fromBall E n K (Classical.choose (hK.subset_closedBall_lt 0 (0 : E)))
    (Classical.choose_spec (hK.subset_closedBall_lt 0 (0 : E))).1.le
    (Classical.choose_spec (hK.subset_closedBall_lt 0 (0 : E))).2

theorem fundamentalClass_eq_fromBall (K : Set E) (hK : Bornology.IsBounded K)
    (R : ℝ) (hR : 0 ≤ R) (hKR : K ⊆ closedBall (0 : E) R) :
    fundamentalClass E n K hK = fromBall E n K R hR hKR := by
  unfold fundamentalClass
  exact fromBall_independent E n K _ R _ hR _ hKR

theorem fundamentalClass_evaluate (K : Set E) (hK : Bornology.IsBounded K)
    (x : E) (hx : x ∈ K) :
    evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) (fundamentalClass E n K hK) =
      IntegralBallOrientation.pointClass E n x := by
  unfold fundamentalClass
  exact fromBall_evaluate E n K _ _ _ x hx

/-- Exact compatibility with all actual restrictions between bounded supports. -/
theorem restrict_fundamentalClass {K L : Set E} (hKL : K ⊆ L)
    (hK : Bornology.IsBounded K) (hL : Bornology.IsBounded L) :
    restrict (ModuleCat.of ℤ ℤ) hKL (n + 2) (fundamentalClass E n L hL) =
      fundamentalClass E n K hK := by
  obtain ⟨R, hR, hLR⟩ := hL.subset_closedBall_lt 0 (0 : E)
  rw [fundamentalClass_eq_fromBall E n L hL R hR.le hLR,
    fundamentalClass_eq_fromBall E n K hK R hR.le (hKL.trans hLR)]
  exact (LinearMap.congr_fun (restrict_trans (ModuleCat.of ℤ ℤ) hKL hLR (n + 2))
    (IntegralBallOrientation.fundamentalClass E n R hR.le)).symm

/-- Compactness supplies the required class; no fundamental class is an input. -/
theorem compact_exists_fundamentalClass (K : Set E) (hK : IsCompact K) :
    ∃ a : Homology (ModuleCat.of ℤ ℤ) K (n + 2),
      ∀ (x : E) (hx : x ∈ K), evaluate (ModuleCat.of ℤ ℤ) K x hx (n + 2) a =
        IntegralBallOrientation.pointClass E n x :=
  ⟨fundamentalClass E n K hK.isBounded, fundamentalClass_evaluate E n K hK.isBounded⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralEuclideanOrientation
