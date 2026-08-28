import Wikipedia.NoExoticSixSphere.FiniteSupportComponents
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedCohomology
import Wikipedia.NoExoticSixSphere.SingularModTwoEvaluation

/-!
# Original evaluation is the sum of actual finite-support contributions

Forget support through the original relative-to-absolute map and evaluate
on the supplied original integral homology class. Support extension
commutes with this map. The proved unique singleton decomposition thus
expresses evaluation as a sum of its actual point contributions. If
each contribution is one, the result is the cardinality modulo two.
-/

noncomputable section

open scoped BigOperators
open Wikipedia.HopfProblem.SingularMayerVietoris

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X]

/-- Actual relative-to-absolute cohomology followed by original integral-class evaluation. -/
def value (K : Set X) (p : ℕ) (b : SingularHomology X p) : Cohomology K p →ₗ[ℤ] ZMod 2 :=
  ((SingularModTwoEvaluation.evaluation X p).flip b).comp
    (RelativeModTwoCochains.toAbsoluteCohomology Kᶜ p)

/-- Changing the support does not change the value on the original homology class. -/
theorem value_extend {K L : Set X} (h : K ⊆ L) (p : ℕ) (b : SingularHomology X p)
    (a : Cohomology K p) : value L p b (extend h p a) = value K p b a :=
  congrArg (fun c => SingularModTwoEvaluation.evaluation X p c b) (toAbsolute_extend h p a)

theorem value_pointTo (K : Set X) (p : ℕ) (b : SingularHomology X p) (x : X) (hx : x ∈ K)
    (a : Cohomology ({x} : Set X) p) : value K p b (pointTo K p x a) = value {x} p b a := by
  rw [pointTo_of_mem K p x hx]
  exact value_extend (Set.singleton_subset_iff.mpr hx) p b a

/-- Evaluating an original finite extension sum sums its original singleton evaluations. -/
theorem value_pointSum (s : Finset X) (p : ℕ) (b : SingularHomology X p)
    (a : ∀ x : X, Cohomology ({x} : Set X) p) :
    value (s : Set X) p b (pointSum s p a) = ∑ x ∈ s, value {x} p b (a x) := by
  rw [pointSum, map_sum]
  exact Finset.sum_congr rfl (fun x hx => value_pointTo (s : Set X) p b x hx (a x))

variable [T1Space X]

/-- Every actual finite-supported class evaluates to the sum of its unique point contributions. -/
theorem value_eq_sum_pointPieces (s : Finset X) (p : ℕ) (b : SingularHomology X p)
    (c : Cohomology (s : Set X) p) :
    value (s : Set X) p b c = ∑ x ∈ s, value {x} p b (pointPieces s p c x) :=
  (congrArg (value (s : Set X) p b) (pointSum_pointPieces s p c)).symm.trans
    (value_pointSum s p b (pointPieces s p c))

/-- Unit point contributions give the actual finite-support cardinality modulo two. -/
theorem value_eq_card_of_point_values_one (s : Finset X) (p : ℕ) (b : SingularHomology X p)
    (c : Cohomology (s : Set X) p)
    (hc : ∀ x ∈ s, value {x} p b (pointPieces s p c x) = 1) :
    value (s : Set X) p b c = (s.card : ZMod 2) := by
  rw [value_eq_sum_pointPieces]
  exact (Finset.sum_congr rfl hc).trans (by simp)

end NoExoticSixSphere.SupportedModTwoCohomology
