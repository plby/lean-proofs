import Wikipedia.HopfProblem.EllipticBundleNormal
import Wikipedia.HopfProblem.EllipticBundleCoreCriterion
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCoreTensor

/-!
# Exact order of the actual central normal line

The companion construction identifies `NormalBundle.data` with the normal
tangent quotient of the actual central immersion, and computes its
transition cocycle as the rotation character. These power cocycles therefore
have the tensor interpretation, including the original geometric bundle at
power one. Their analytic triviality has exact period three or four.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.NormalBundle

open HolomorphicCharacterBundle

local notation "IS" => modelWithCornersSelf ℂ ComplexPlane₂

def powerData (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ) :
    TransitionData (Surface j (centralPeriod j) v hv) (Surface j (centralPeriod j) v hv) := by
  letI := affineAction j (centralPeriod j) v hv.1
  exact AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv) (normalCharacter j ^ n)

instance powerData_isHolomorphic (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (n : ℕ) :
    (powerData j v hv n).IsHolomorphic IS := by
  let := affineAction j (centralPeriod j) v hv.1
  change (AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (normalCharacter j ^ n)).IsHolomorphic IS
  infer_instance

@[simp] theorem powerData_one (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    powerData j v hv 1 = data j v hv := by
  let := affineAction j (centralPeriod j) v hv.1
  change AssociatedCore.data
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (normalCharacter j ^ 1) = data j v hv
  rw [pow_one]
  exact (data_eq_associated j v hv).symm

@[simp] theorem powerData_transition (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (n : ℕ) (i k x : Surface j (centralPeriod j) v hv) :
    (powerData j v hv n).transition i k x = ((data j v hv).transition i k x) ^ n := by
  let := affineAction j (centralPeriod j) v hv.1
  rw [data_eq_associated j v hv]
  exact AssociatedCore.data_pow_transition
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (normalCharacter j) n i k x

/-- Triviality means a genuine fibrewise-linear analytic diffeomorphism of
the tensor-power bundle with the product, not a definition by the character. -/
theorem power_analyticTrivialization_iff (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (n : ℕ) :
    Nonempty ((powerData j v hv n).AnalyticTrivialization IS) ↔ j.order ∣ n := by
  let := affineAction j (centralPeriod j) v hv.1
  have h := BundleCore.characterCore_power_analyticTrivialization_iff
    (surfaceProjection_isQuotientCoveringMap j (centralPeriod j) v hv)
      (normalCharacter j) (affineAction_holomorphic j (centralPeriod j) v hv.1) n
  exact h.trans (by rw [normalCharacter_orderOf])

theorem order_isLeast (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    IsLeast {n : ℕ | 0 < n ∧
      Nonempty ((powerData j v hv n).AnalyticTrivialization IS)} j.order := by
  refine ⟨⟨j.order_pos, (power_analyticTrivialization_iff j v hv j.order).mpr (dvd_refl _)⟩, ?_⟩
  intro n hn
  exact Nat.le_of_dvd hn.1 ((power_analyticTrivialization_iff j v hv n).mp hn.2)

theorem order_power_trivial (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    Nonempty ((powerData j v hv j.order).AnalyticTrivialization IS) :=
  (power_analyticTrivialization_iff j v hv j.order).mpr (dvd_refl _)

theorem not_analytically_trivial (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    ¬ Nonempty ((data j v hv).AnalyticTrivialization IS) := by
  intro h
  have h1 : Nonempty ((powerData j v hv 1).AnalyticTrivialization IS) := by
    simpa only [powerData_one] using h
  have hd := (power_analyticTrivialization_iff j v hv 1).mp h1
  cases j <;> norm_num [Kind.order] at hd

end Wikipedia.HopfProblem.Elliptic.NormalBundle
