/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos88.RademacherLinearLower
import ErdosProblems.Erdos88.StructuredClaim121Lower
import ErdosProblems.Erdos88.StructuredClaims

/-!
# The outer count-vector local lower bound

This module applies the Rademacher Berry--Esseen estimate to the exact
independent-sign representation of the first count-vector shift.
-/

open scoped BigOperators Matrix.Norms.Frobenius

namespace Erdos88
namespace GaussianQuadratic

open BooleanSlices BoundedWindowAnalytic

attribute [local instance] Classical.propDecidable

/-- A count-vector window has the Gaussian-order lower mass supplied by the
first (linear) outer shift. -/
theorem countVectorMass_linearShift_interval_lower
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) {eps M R x : ℝ}
    (heps : 0 < eps)
    (hV : 0 < vectorSqNorm (countVectorLinearCoefficient P hbucket y))
    (hepssigma : eps ≤
      Real.sqrt (vectorSqNorm (countVectorLinearCoefficient P hbucket y)))
    (hM : 0 ≤ M)
    (hx : |x| ≤ M *
      Real.sqrt (vectorSqNorm (countVectorLinearCoefficient P hbucket y)))
    (hscale : ∀ i,
      2 * |countVectorLinearCoefficient P hbucket y i| ≤ eps)
    (hR : 4 ≤ R)
    (hratioScale :
      2 * (R * eps) * (|x| + R * eps) ≤
        vectorSqNorm (countVectorLinearCoefficient P hbucket y)) :
    (eps / Real.sqrt
        (vectorSqNorm (countVectorLinearCoefficient P hbucket y))) *
        (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant *
            (2 / R +
              (3 / 2 : ℝ) *
                RademacherLinearLower.thirdAbsMass
                  (countVectorLinearCoefficient P hbucket y) *
                (Real.pi ^ 4 /
                  vectorSqNorm
                    (countVectorLinearCoefficient P hbucket y) ^ 2) *
                Real.sqrt
                  (vectorSqNorm
                    (countVectorLinearCoefficient P hbucket y)))) ≤
      countVectorMass P (fun ell ↦
        |countVectorLinearShift P hbucket y ell - x| ≤ 30000 * eps) := by
  let a := countVectorLinearCoefficient P hbucket y
  let V := vectorSqNorm a
  have hVpos : 0 < V := by simpa only [V, a] using hV
  have hVsum : (∑ i, a i ^ 2) = V := by rfl
  have hVraw : 0 < ∑ i, a i ^ 2 := by rw [hVsum]; exact hVpos
  have hsigma : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
  have hratio := densityRatioOn_centeredGaussian_three
    (x := x) hsigma heps.le (by linarith : 0 ≤ R) (by
      rw [Real.sq_sqrt hVpos.le]
      simpa only [V, a] using hratioScale)
  have hlower :=
    RademacherLinearLower.smallBall_rademacherLinearLaw_lower
      a heps hVraw
      (by rw [hVsum]; simpa only [V, a] using hepssigma) hM
      (by rw [hVsum]; simpa only [V, a] using hx)
      (by simpa only [a] using hscale) hR hratio
  rw [countVectorMass_linearShift_interval_eq_finProbability]
  change (eps / Real.sqrt V) *
      (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
        Esseen.relativeEsseenConstant *
          (2 / R + (3 / 2 : ℝ) *
            RademacherLinearLower.thirdAbsMass a *
              (Real.pi ^ 4 / V ^ 2) * Real.sqrt V)) ≤
    Fourier.finProbability (Fin n → Bool) (fun xi ↦
      |∑ i, a i * Fourier.rademacherSign (xi i) - x| ≤ 30000 * eps)
  rw [hVsum] at hlower
  exact hlower.trans_eq
    (RademacherLinearLower.smallBall_rademacherLinearLaw_eq_finProbability
      a (30000 * eps) x)

/-- Convenient form with the normalized Berry--Esseen contribution replaced
by any explicit upper bound. -/
theorem countVectorMass_linearShift_interval_lower_of_error
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (y : Fin n → ℝ) {eps M R eta x : ℝ}
    (heps : 0 < eps)
    (hV : 0 < vectorSqNorm (countVectorLinearCoefficient P hbucket y))
    (hepssigma : eps ≤
      Real.sqrt (vectorSqNorm (countVectorLinearCoefficient P hbucket y)))
    (hM : 0 ≤ M)
    (hx : |x| ≤ M *
      Real.sqrt (vectorSqNorm (countVectorLinearCoefficient P hbucket y)))
    (hscale : ∀ i,
      2 * |countVectorLinearCoefficient P hbucket y i| ≤ eps)
    (hR : 4 ≤ R)
    (hratioScale :
      2 * (R * eps) * (|x| + R * eps) ≤
        vectorSqNorm (countVectorLinearCoefficient P hbucket y))
    (herror :
      (3 / 2 : ℝ) *
          RademacherLinearLower.thirdAbsMass
            (countVectorLinearCoefficient P hbucket y) *
          (Real.pi ^ 4 /
            vectorSqNorm (countVectorLinearCoefficient P hbucket y) ^ 2) *
          Real.sqrt
            (vectorSqNorm (countVectorLinearCoefficient P hbucket y)) ≤ eta) :
    (eps / Real.sqrt
        (vectorSqNorm (countVectorLinearCoefficient P hbucket y))) *
        (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant * (2 / R + eta)) ≤
      countVectorMass P (fun ell ↦
        |countVectorLinearShift P hbucket y ell - x| ≤ 30000 * eps) := by
  have hbase := countVectorMass_linearShift_interval_lower
    P hbucket y heps hV hepssigma hM hx hscale hR hratioScale
  have hsigma : 0 < Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient P hbucket y)) :=
    Real.sqrt_pos.2 hV
  have hfactor : 0 ≤ eps / Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient P hbucket y)) := by
    positivity
  apply (mul_le_mul_of_nonneg_left ?_ hfactor).trans hbase
  have hC := Esseen.relativeEsseenConstant_nonneg
  nlinarith

/-- For graph-effective coefficients the normalized Berry--Esseen error is
`O(n⁻¹/²)`, uniformly over the bucket partition. -/
theorem countVectorLinearCoefficient_graph_normalizedThirdError_le
    {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H A : ℝ) (hH : 0 ≤ H) (hA : 0 < A)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)) :
    let a := countVectorLinearCoefficient P hbucket
      (GraphQuadratic.graphEffectiveLinear G c)
    let V := vectorSqNorm a
    (3 / 2 : ℝ) * RademacherLinearLower.thirdAbsMass a *
        (Real.pi ^ 4 / V ^ 2) * Real.sqrt V ≤
      ((3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A) *
        (1 / Real.sqrt (n : ℝ)) := by
  dsimp only
  let a := countVectorLinearCoefficient P hbucket
    (GraphQuadratic.graphEffectiveLinear G c)
  let V := vectorSqNorm a
  let B := ((H + 1) * (n : ℝ)) / 2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hmax : ∀ i, |a i| ≤ B := by
    intro i
    exact countVectorLinearCoefficient_graph_abs_le
      P hbucket G c H hH hc0 hcH i
  have hVlower := countVectorLinearCoefficient_graph_sqNorm_lower
    hn P hbucket G c hA.le hc0 hedge
  have hbasePos : 0 < (A / 2) * (n : ℝ) * Real.sqrt (n : ℝ) := by
    positivity
  have hVpos : 0 < V := by
    have hlowerPos : 0 < (1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3) := by
      positivity
    exact hlowerPos.trans_le (by simpa only [V, a] using hVlower)
  have hbase : (A / 2) * (n : ℝ) * Real.sqrt (n : ℝ) ≤
      Real.sqrt V := by
    apply (sq_le_sq₀ hbasePos.le (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hVpos.le]
    have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt hnR.le
    calc
      ((A / 2) * (n : ℝ) * Real.sqrt (n : ℝ)) ^ 2 =
          (1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3) := by
            rw [mul_pow, mul_pow, hsqrtSq]
            ring
      _ ≤ V := by simpa only [V, a] using hVlower
  have hraw :=
    RademacherLinearLower.normalizedThirdError_le_max_div_sqrtVariance
      a hB hVpos (by rfl) hmax
  calc
    (3 / 2 : ℝ) * RademacherLinearLower.thirdAbsMass a *
        (Real.pi ^ 4 / V ^ 2) * Real.sqrt V ≤
      (3 / 2 : ℝ) * B * Real.pi ^ 4 / Real.sqrt V := hraw
    _ ≤ (3 / 2 : ℝ) * B * Real.pi ^ 4 /
        ((A / 2) * (n : ℝ) * Real.sqrt (n : ℝ)) := by
      exact div_le_div_of_nonneg_left (by positivity) hbasePos hbase
    _ = ((3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A) *
        (1 / Real.sqrt (n : ℝ)) := by
      dsimp only [B]
      field_simp [hA.ne', hnR.ne', (Real.sqrt_pos.2 hnR).ne']

/-- Pointwise graph coefficient control also gives the matching cubic-scale
upper bound for the outer Rademacher variance. -/
lemma countVectorLinearCoefficient_graph_sqNorm_le
    {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H : ℝ) (hH : 0 ≤ H)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ)) :
    vectorSqNorm (countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c)) ≤
      (n : ℝ) * (((H + 1) * (n : ℝ)) / 2) ^ 2 := by
  apply vectorSqNorm_le _ _ (by positivity)
  intro i
  exact countVectorLinearCoefficient_graph_abs_le
    P hbucket G c H hH hc0 hcH i

/-- Square-root form of `countVectorLinearCoefficient_graph_sqNorm_le`. -/
lemma sqrt_countVectorLinearCoefficient_graph_sqNorm_le
    {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H : ℝ) (hH : 0 ≤ H)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ)) :
    Real.sqrt (vectorSqNorm (countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c))) ≤
      ((H + 1) / 2) * (n : ℝ) * Real.sqrt (n : ℝ) := by
  have hraw := countVectorLinearCoefficient_graph_sqNorm_le
    P hbucket G c H hH hc0 hcH
  have hn : (0 : ℝ) ≤ n := by positivity
  have hV : 0 ≤ vectorSqNorm (countVectorLinearCoefficient P hbucket
      (GraphQuadratic.graphEffectiveLinear G c)) := by
    unfold vectorSqNorm
    positivity
  have hright : 0 ≤ ((H + 1) / 2) * (n : ℝ) *
      Real.sqrt (n : ℝ) := by positivity
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hright).mp
  rw [Real.sq_sqrt hV]
  calc
    vectorSqNorm (countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c)) ≤
      (n : ℝ) * (((H + 1) * (n : ℝ)) / 2) ^ 2 := hraw
    _ = (((H + 1) / 2) * (n : ℝ) *
        Real.sqrt (n : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hn]
      ring

/-- The graph-effective Berry--Esseen error can be absorbed into any fixed
positive tolerance once the ambient graph is large enough. -/
lemma eventually_countVectorLinearCoefficient_graph_error_le
    (H A eta : ℝ) (hH : 0 ≤ H) (hA : 0 < A) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A) *
          (1 / Real.sqrt (n : ℝ)) ≤ eta := by
  let K : ℝ := (3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A
  let B : ℝ := K / eta
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hB : 0 ≤ B := div_nonneg hK heta.le
  have hrate :=
    Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      B (-1 / 2) 0 hB (by norm_num)
  filter_upwards [hrate, Filter.eventually_ge_atTop 1] with n hnrate hn
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hinvSqrt : (n : ℝ) ^ (-1 / 2 : ℝ) =
      1 / Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow,
      show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hnR.le]
    simp only [one_div]
  have hnrate' : B * (n : ℝ) ^ (-1 / 2 : ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using hnrate
  calc
    ((3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A) *
          (1 / Real.sqrt (n : ℝ)) =
        eta * (B * (n : ℝ) ^ (-1 / 2 : ℝ)) := by
      rw [hinvSqrt]
      dsimp only [B, K]
      field_simp [heta.ne']
    _ ≤ eta * 1 := mul_le_mul_of_nonneg_left hnrate' heta.le
    _ = eta := mul_one eta

/-- Graph-effective specialization of the outer local lower bound.  The
remaining hypotheses are precisely the scale and target-window inequalities
that are verified in the eventual structured averaging argument. -/
theorem countVectorMass_graphLinearShift_interval_lower_of_error
    {n m : ℕ} (hn : 0 < n)
    (P : BucketPartition (Fin n) (Fin m))
    (hbucket : RobustRank.HasEqualBuckets P.bucket)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (H A : ℝ) (hH : 0 ≤ H) (hA : 0 < A)
    (hc0 : ∀ i, 0 ≤ c i) (hcH : ∀ i, c i ≤ H * (n : ℝ))
    (hedge : A * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    {eps M R eta x : ℝ}
    (heps : 0 < eps)
    (hepssigma : eps ≤ Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c))))
    (hM : 0 ≤ M)
    (hx : |x| ≤ M * Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient P hbucket
        (GraphQuadratic.graphEffectiveLinear G c))))
    (hcoeffScale : (H + 1) * (n : ℝ) ≤ eps)
    (hR : 4 ≤ R)
    (hratioScale :
      2 * (R * eps) * (|x| + R * eps) ≤
        vectorSqNorm (countVectorLinearCoefficient P hbucket
          (GraphQuadratic.graphEffectiveLinear G c)))
    (herror :
      ((3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A) *
        (1 / Real.sqrt (n : ℝ)) ≤ eta) :
    (eps / Real.sqrt
        (vectorSqNorm (countVectorLinearCoefficient P hbucket
          (GraphQuadratic.graphEffectiveLinear G c)))) *
        (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
          Esseen.relativeEsseenConstant * (2 / R + eta)) ≤
      countVectorMass P (fun ell ↦
        |countVectorLinearShift P hbucket
            (GraphQuadratic.graphEffectiveLinear G c) ell - x| ≤
          30000 * eps) := by
  let y := GraphQuadratic.graphEffectiveLinear G c
  let a := countVectorLinearCoefficient P hbucket y
  let V := vectorSqNorm a
  have hVlower := countVectorLinearCoefficient_graph_sqNorm_lower
    hn P hbucket G c hA.le hc0 hedge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : 0 < V := by
    have hlower : 0 < (1 / 4 : ℝ) * (A ^ 2 * (n : ℝ) ^ 3) := by
      positivity
    exact hlower.trans_le (by simpa only [V, a, y] using hVlower)
  have hscale : ∀ i, 2 * |a i| ≤ eps := by
    intro i
    have hi := countVectorLinearCoefficient_graph_abs_le
      P hbucket G c H hH hc0 hcH i
    have htwo : 2 * |a i| ≤ (H + 1) * (n : ℝ) := by
      dsimp only [a, y]
      linarith
    exact htwo.trans hcoeffScale
  have hthird :=
    countVectorLinearCoefficient_graph_normalizedThirdError_le
      hn P hbucket G c H A hH hA hc0 hcH hedge
  apply countVectorMass_linearShift_interval_lower_of_error
      P hbucket y heps (by simpa only [V, a] using hV)
      (by simpa only [V, a, y] using hepssigma) hM
      (by simpa only [V, a, y] using hx)
      (by simpa only [a] using hscale) hR
      (by simpa only [V, a, y] using hratioScale)
  exact hthird.trans herror

/-- Removing an exceptional predicate costs at most its total mass.  This
is the finite-law subtraction used in the lower averaging argument. -/
lemma countVectorMass_sub_le_and_not
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (E Bad : BucketCountVector P → Prop) :
    countVectorMass P E - countVectorMass P Bad ≤
      countVectorMass P (fun ell ↦ E ell ∧ ¬ Bad ell) := by
  unfold countVectorMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ell hell
  let w : ℝ :=
    (Fintype.card
        (ProductSlicePoint P (fun k ↦ (ell k).val)) : ℝ) /
      Fintype.card (Finset α)
  have hw : 0 ≤ w := by
    dsimp only [w]
    positivity
  by_cases hE : E ell <;> by_cases hBad : Bad ell <;>
    simp only [hE, hBad, false_and, true_and, not_true_eq_false,
      not_false_eq_true, if_true, if_false, sub_self, zero_sub, sub_zero] <;>
    linarith

/-- Quantitative form of `countVectorMass_sub_le_and_not`. -/
lemma countVectorMass_lower_sub_bad
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (E Bad : BucketCountVector P → Prop) {main bad : ℝ}
    (hmain : main ≤ countVectorMass P E)
    (hbad : countVectorMass P Bad ≤ bad) :
    main - bad ≤ countVectorMass P (fun ell ↦ E ell ∧ ¬ Bad ell) :=
  (sub_le_sub hmain hbad).trans (countVectorMass_sub_le_and_not P E Bad)

/-- Interval lower mass minus the Claim 12.2 exceptional mass leaves an
interval of count vectors with controlled quadratic/variance shift. -/
lemma countVectorMass_interval_shiftMoment_lt_lower
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (L W : BucketCountVector P → ℝ)
    {a b T main bad : ℝ}
    (hmain : main ≤ countVectorMass P (fun ell ↦
      a ≤ L ell ∧ L ell ≤ b))
    (hbad : countVectorMass P (fun ell ↦
      a ≤ L ell ∧ L ell ≤ b ∧ T ≤ W ell) ≤ bad) :
    main - bad ≤ countVectorMass P (fun ell ↦
      a ≤ L ell ∧ L ell ≤ b ∧ W ell < T) := by
  have hsub := countVectorMass_sub_le_and_not P
    (fun ell ↦ a ≤ L ell ∧ L ell ≤ b)
    (fun ell ↦ a ≤ L ell ∧ L ell ≤ b ∧ T ≤ W ell)
  apply (sub_le_sub hmain hbad).trans
  apply hsub.trans_eq
  apply congrArg (countVectorMass P)
  funext ell
  apply propext
  constructor
  · rintro ⟨hE, hnot⟩
    refine ⟨hE.1, hE.2, ?_⟩
    by_contra hW
    exact hnot ⟨hE.1, hE.2, le_of_not_gt hW⟩
  · rintro ⟨ha, hb, hW⟩
    exact ⟨⟨ha, hb⟩, fun hlarge ↦ (not_le_of_gt hW) hlarge.2.2⟩

/-- Source-facing outer selection estimate: the Berry--Esseen interval
mass survives after the large Claim 12.2 shift-moment vectors are removed.
The constants have deliberately not been asymptotically simplified. -/
theorem countVectorMass_graphLinearShift_smallMoment_lower
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {K H A eps M R eta x T : ℝ}
    (hclaim : ConditionedClaim122Bound D G c O hbucket K)
    (hq : 0 < Fintype.card D.Covered)
    (hH : 0 ≤ H) (hA : 0 < A)
    (hc0 : ∀ i, 0 ≤ D.conditionedCoveredCoefficient G c O i)
    (hcH : ∀ i, D.conditionedCoveredCoefficient G c O i ≤
      H * (Fintype.card D.Covered : ℝ))
    (hedge : A * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      ((D.finCoveredGraph G).edgeFinset.card : ℝ))
    (heps : 0 < eps)
    (hepssigma : eps ≤ Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient
        D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O)))))
    (hM : 0 ≤ M)
    (hx : |x| ≤ M * Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient
        D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O)))))
    (hcoeffScale : (H + 1) * (Fintype.card D.Covered : ℝ) ≤ eps)
    (hR : 4 ≤ R)
    (hratioScale :
      2 * (R * eps) * (|x| + R * eps) ≤
        vectorSqNorm (countVectorLinearCoefficient
          D.finCoveredPartition hbucket
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O))))
    (herror :
      ((3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A) *
        (1 / Real.sqrt (Fintype.card D.Covered : ℝ)) ≤ eta)
    (hT : 0 < T)
    (hFnorm : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ 60000 * eps) :
    let P := D.finCoveredPartition
    let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G c O)
    let L : BucketCountVector P → ℝ := fun ell ↦
      countVectorLinearShift P hbucket y ell
    let W : BucketCountVector P → ℝ := fun ell ↦
      countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
    let V := vectorSqNorm (countVectorLinearCoefficient P hbucket y)
    (eps / Real.sqrt V) *
          (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
            Esseen.relativeEsseenConstant * (2 / R + eta)) -
        (K * Real.sqrt (Fintype.card D.Covered) * (60000 * eps)) / T ≤
      countVectorMass P (fun ell ↦
        |L ell - x| ≤ 30000 * eps ∧ W ell < T) := by
  dsimp only
  let P := D.finCoveredPartition
  let Gc := D.finCoveredGraph G
  let cc := D.conditionedCoveredCoefficient G c O
  let y := GraphQuadratic.graphEffectiveLinear Gc cc
  let L : BucketCountVector P → ℝ := fun ell ↦
    countVectorLinearShift P hbucket y ell
  let W : BucketCountVector P → ℝ := fun ell ↦
    countVectorShiftMoment P hbucket Gc ell
  let V := vectorSqNorm (countVectorLinearCoefficient P hbucket y)
  let radius : ℝ := 30000 * eps
  let main : ℝ := (eps / Real.sqrt V) *
    (Real.exp (-((M + 1) ^ 2) / 2) / 12 -
      Esseen.relativeEsseenConstant * (2 / R + eta))
  let bad : ℝ :=
    (K * Real.sqrt (Fintype.card D.Covered) * (60000 * eps)) / T
  have hmainAbs : main ≤ countVectorMass P (fun ell ↦
      |L ell - x| ≤ radius) := by
    simpa only [main, V, P, L, y, Gc, cc, radius] using
      countVectorMass_graphLinearShift_interval_lower_of_error
        hq D.finCoveredPartition hbucket (D.finCoveredGraph G)
        (D.conditionedCoveredCoefficient G c O) H A hH hA hc0 hcH
        hedge heps hepssigma hM hx hcoeffScale hR hratioScale herror
  have hmain : main ≤ countVectorMass P (fun ell ↦
      x - radius ≤ L ell ∧ L ell ≤ x + radius) := by
    apply hmainAbs.trans_eq
    apply congrArg (countVectorMass P)
    funext ell
    apply propext
    rw [abs_le]
    constructor <;> rintro ⟨hleft, hright⟩ <;>
      constructor <;> linarith
  have hwidth : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤
      (x + radius) - (x - radius) := by
    dsimp only [radius]
    nlinarith
  have hbadRaw := countVectorMass_largeShiftMoment_interval_le
    D G c O hbucket hclaim (x - radius) (x + radius) T hT hwidth
  have hbadEq :
      (K * Real.sqrt (Fintype.card D.Covered) *
          ((x + radius) - (x - radius))) / T = bad := by
    dsimp only [bad, radius]
    ring
  have hbad : countVectorMass P (fun ell ↦
      x - radius ≤ L ell ∧ L ell ≤ x + radius ∧ T ≤ W ell) ≤
      bad := by
    simpa only [P, L, W, y, Gc, cc] using hbadRaw.trans_eq hbadEq
  have hgood := countVectorMass_interval_shiftMoment_lt_lower
    P L W hmain hbad
  have hmassEq : countVectorMass P (fun ell ↦
      x - radius ≤ L ell ∧ L ell ≤ x + radius ∧ W ell < T) =
      countVectorMass P (fun ell ↦
        |L ell - x| ≤ radius ∧ W ell < T) := by
    apply congrArg (countVectorMass P)
    funext ell
    apply propext
    rw [abs_le]
    constructor
    · rintro ⟨ha, hb, hW⟩
      exact ⟨⟨by linarith, by linarith⟩, hW⟩
    · rintro ⟨⟨ha, hb⟩, hW⟩
      exact ⟨by linarith, by linarith, hW⟩
  simpa only [main, bad, V, P, L, W, y, Gc, cc, radius] using
    hgood.trans_eq hmassEq

/-- The elementary signed-center geometry behind the lower half of Claim
12.1.  It is stated independently of the graph objects so the subsequent
averaging proof can use it without exposing the long conditional center. -/
lemma signed_target_offset_mem_interval
    {s base L qshift U radius shiftBound : ℝ}
    (hs : s = 1 ∨ s = -1)
    (hL : |L - (base - s * U)| ≤ radius)
    (hq : |qshift| ≤ shiftBound) :
    U - radius - shiftBound ≤ s * (base - L - qshift) ∧
      s * (base - L - qshift) ≤ U + radius + shiftBound := by
  rcases hs with rfl | rfl
  · rw [one_mul]
    rw [abs_le] at hL hq
    constructor <;> linarith
  · simp only [neg_mul, one_mul]
    rw [abs_le] at hL hq
    constructor <;> linarith

/-- A signed outer interval and a small Claim 12.2 shift moment imply the
one-sided translated-target hypotheses used by the uniform fixed-slice
Claim 12.1 lower theorem. -/
lemma conditionedCountVectorTargetOffset_signed_bounds
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (target s U radius shiftBound : ℝ)
    (hs : s = 1 ∨ s = -1)
    (ell : BucketCountVector D.finCoveredPartition)
    (hlinear :
      |countVectorLinearShift D.finCoveredPartition hbucket
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O)) ell -
        (conditionedCountVectorBaseCenter D G e0 c O hbucket target -
          s * U)| ≤ radius)
    (hmoment : countVectorShiftMoment D.finCoveredPartition hbucket
      (D.finCoveredGraph G) ell ≤ shiftBound ^ 2)
    (hshiftBound : 0 ≤ shiftBound) :
    U - radius - shiftBound ≤
        s * conditionedCountVectorTargetOffset
          D G e0 c O hbucket target ell ∧
      s * conditionedCountVectorTargetOffset
          D G e0 c O hbucket target ell ≤
        U + radius + shiftBound := by
  have hq := abs_countVectorQuadraticShift_le_of_shiftMoment_le_sq
    D.finCoveredPartition hbucket (D.finCoveredGraph G) ell
      hshiftBound hmoment
  simpa only [conditionedCountVectorTargetOffset] using
    signed_target_offset_mem_interval hs hlinear hq

/-- If the Claim 12.2 shift is at most half of the zero-count scale, the
actual conditional Claim 12.1 scale remains at least half of that base
scale. -/
lemma zeroCountClaim121Scale_div_two_le_of_shiftMoment_lt
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ)
    (O : Finset (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (ell : BucketCountVector D.finCoveredPartition) {t : ℝ}
    (ht : 0 ≤ t)
    (htBase : 2 * t ≤ zeroCountClaim121Scale D G c O hbucket)
    (hmoment : countVectorShiftMoment D.finCoveredPartition hbucket
      (D.finCoveredGraph G) ell < t ^ 2) :
    zeroCountClaim121Scale D G c O hbucket / 2 ≤
      countVectorClaim121Scale D G c O hbucket ell := by
  let P := D.finCoveredPartition
  let Gc := D.finCoveredGraph G
  let y := GraphQuadratic.graphEffectiveLinear Gc
    (D.conditionedCoveredCoefficient G c O)
  let F := bucketCenteredAdjacency P.bucket hbucket.choose Gc
  let f0 := Structured.wStar
    (bucketProjectionMatrix P.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix Gc) y 0
  let f := Structured.wStar
    (bucketProjectionMatrix P.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix Gc) y
    (productSliceDelta P hbucket.choose (fun j ↦ (ell j).val))
  let sigma0 := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f0)
  let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
  let W := countVectorShiftMoment P hbucket Gc ell
  have hback := baseScaleSq_le_claim121Scale_add_shiftMoment
    P hbucket Gc y ell
  have hsigma0 : 0 ≤ sigma0 := Real.sqrt_nonneg _
  have hsigma : 0 ≤ sigma := Real.sqrt_nonneg _
  have hFnonneg : 0 ≤ frobeniusSq F := by
    unfold frobeniusSq
    positivity
  have hf0nonneg : 0 ≤ vectorSqNorm f0 := Structured.vectorSqNorm_nonneg f0
  have hfnonneg : 0 ≤ vectorSqNorm f := Structured.vectorSqNorm_nonneg f
  have hbase0 : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f0 := by
    positivity
  have hbase : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f := by
    positivity
  have htSq : (2 * t) ^ 2 ≤ sigma0 ^ 2 := by
    apply (sq_le_sq₀ (by positivity) hsigma0).2
    simpa only [sigma0, zeroCountClaim121Scale, P, Gc, y, F, f0]
      using htBase
  have hback' : sigma0 ^ 2 ≤ 2 * sigma ^ 2 + 2 * W := by
    dsimp only [sigma0, sigma]
    rw [Real.sq_sqrt hbase0, Real.sq_sqrt hbase]
    simpa only [P, Gc, y, F, f0, f, W] using hback
  have hmoment' : W < t ^ 2 := by simpa only [W, P, Gc] using hmoment
  have hhalf : sigma0 / 2 ≤ sigma := by
    nlinarith [sq_nonneg (sigma - sigma0 / 2)]
  simpa only [sigma0, sigma, P, Gc, y, F, f0, f,
    zeroCountClaim121Scale, countVectorClaim121Scale] using hhalf

/-- Lower law-of-total-probability bound for the count-vector mixture. -/
lemma countVectorMass_mul_le_weighted_conditioned
    {α κ : Type*} [Fintype α] [DecidableEq α]
    [Fintype κ] [DecidableEq κ]
    (P : BucketPartition α κ)
    (Good : BucketCountVector P → Prop)
    (cond : BucketCountVector P → ℝ) {lower : ℝ}
    (hcondNonneg : ∀ ell, 0 ≤ cond ell)
    (hcond : ∀ ell, Good ell → lower ≤ cond ell) :
    countVectorMass P Good * lower ≤
      ∑ ell : BucketCountVector P,
        countVectorWeight P ell * cond ell := by
  rw [countVectorMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ell hell
  have hweight : 0 ≤ countVectorWeight P ell :=
    countVectorWeight_nonneg P ell
  by_cases hgood : Good ell
  · rw [if_pos hgood]
    exact mul_le_mul_of_nonneg_left (hcond ell hgood) hweight
  · rw [if_neg hgood, zero_mul]
    exact mul_nonneg hweight (hcondNonneg ell)

/-- The uniform signed fixed-slice lower certificate consumed by the outer
count-vector averaging argument. -/
def UniformConditionedClaim121Lower
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (delta B M kappa s : ℝ) : Prop :=
  ∀ (ell : Fin (Fintype.card D.BlockIndex) → ℕ)
    (f : Fin (Fintype.card D.Covered) → ℝ),
    IsNearBalanced delta D.finCoveredPartition ell →
    HasKSSSBalancedCoefficients delta D.finCoveredPartition f
      (bucketCenteredAdjacency D.finCoveredPartition.bucket
        hbucket.choose (D.finCoveredGraph G)) →
    ∃ hleft : Nonempty (ProductSlicePoint D.finCoveredPartition ell),
      letI := hleft
      let F := bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose (D.finCoveredGraph G)
      let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
      0 < sigma ∧ ∀ z : ℝ,
        0 ≤ s * z → s * z ≤ M * sigma →
        kappa / sigma ≤
          Esseen.smallBall
            (Esseen.finiteUniformLaw
              (ProductSlicePoint D.finCoveredPartition ell)
              (productSliceQuadratic D.finCoveredPartition ell
                (-trace F) f F)) B z

/-- Exact inner lower averaging step.  A uniform signed Claim 12.1
certificate on every good count vector is transferred to the ambient
conditioned window and then averaged with the exact count-vector weights. -/
theorem conditionedCountVector_weighted_claim121_lower
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {delta B M kappa s S p target : ℝ}
    (hkappa : 0 < kappa) (hS : 0 < S)
    (hclaim : UniformConditionedClaim121Lower
      D G hbucket delta B M kappa s)
    (Good : BucketCountVector D.finCoveredPartition → Prop)
    (hmass : p ≤ countVectorMass D.finCoveredPartition Good)
    (hnear : ∀ ell, Good ell →
      IsNearBalanced delta D.finCoveredPartition (fun j ↦ (ell j).val))
    (hcoeff : ∀ ell, Good ell →
      HasKSSSBalancedCoefficients delta D.finCoveredPartition
        (Structured.wStar
          (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
          (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O))
          (productSliceDelta D.finCoveredPartition hbucket.choose
            (fun j ↦ (ell j).val)))
        (bucketCenteredAdjacency D.finCoveredPartition.bucket
          hbucket.choose (D.finCoveredGraph G)))
    (htarget0 : ∀ ell, Good ell →
      0 ≤ s * conditionedCountVectorTargetOffset
        D G e0 c O hbucket target ell)
    (htargetM : ∀ ell, Good ell →
      s * conditionedCountVectorTargetOffset
          D G e0 c O hbucket target ell ≤
        M * countVectorClaim121Scale D G c O hbucket ell)
    (hscaleUpper : ∀ ell, Good ell →
      countVectorClaim121Scale D G c O hbucket ell ≤ S) :
    p * (kappa / S) ≤
      ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability
            D G e0 c O B target ell := by
  let P := D.finCoveredPartition
  let cond : BucketCountVector P → ℝ := fun ell ↦
    conditionedCountVectorWindowProbability D G e0 c O B target ell
  have hcondNonneg : ∀ ell, 0 ≤ cond ell := by
    intro ell
    dsimp only [cond]
    exact conditionedCountVectorWindowProbability_nonneg
      D G e0 c O B target ell
  have hcondLower : ∀ ell, Good ell → kappa / S ≤ cond ell := by
    intro ell hell
    let Gc := D.finCoveredGraph G
    let cc := D.conditionedCoveredCoefficient G c O
    let E := GraphQuadratic.graphSliceConstant Gc
      (Probability.perturbedEdgePolynomial G e0 c O) cc
    let y := GraphQuadratic.graphEffectiveLinear Gc cc
    let F := bucketCenteredAdjacency P.bucket hbucket.choose Gc
    let dvec := productSliceDelta P hbucket.choose (fun j ↦ (ell j).val)
    let f := Structured.wStar
      (bucketProjectionMatrix P.bucket hbucket.choose)
      (RobustRank.graphAdjacencyMatrix Gc) y dvec
    let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
    obtain ⟨hleft, hsigma, hlower⟩ :=
      hclaim (fun j ↦ (ell j).val) f (hnear ell hell)
        (by simpa only [P, Gc, cc, y, F, dvec, f] using hcoeff ell hell)
    let := hleft
    have hsigmaEq : sigma =
        countVectorClaim121Scale D G c O hbucket ell := by
      rfl
    have hsigmaUpper : sigma ≤ S := by
      rw [hsigmaEq]
      exact hscaleUpper ell hell
    have hdenom : kappa / S ≤ kappa / sigma :=
      div_le_div_of_nonneg_left hkappa.le hsigma hsigmaUpper
    let shift := Structured.conditionalShift E
      (RobustRank.graphAdjacencyMatrix Gc) y dvec + trace F
    have hshift : target - shift =
        conditionedCountVectorTargetOffset
          D G e0 c O hbucket target ell := by
      have hdecomp := conditionalShift_eq_base_add_countVectorShifts
        P hbucket Gc E y ell
      dsimp only [shift, dvec]
      rw [hdecomp]
      dsimp only [conditionedCountVectorTargetOffset,
        conditionedCountVectorBaseCenter, P, Gc, cc, E, y, F]
      ring
    have hsmall : kappa / S ≤
        Esseen.smallBall
          (Esseen.finiteUniformLaw
            (ProductSlicePoint P (fun j ↦ (ell j).val))
            (productSliceQuadratic P (fun j ↦ (ell j).val)
              (-trace F) f F)) B (target - shift) := by
      apply hdenom.trans
      rw [hshift]
      apply hlower
      · exact htarget0 ell hell
      · have htargetM' :
            s * conditionedCountVectorTargetOffset
                D G e0 c O hbucket target ell ≤ M * sigma := by
          rw [hsigmaEq]
          exact htargetM ell hell
        simpa only [sigma, F, f, P] using htargetM'
    have hambient := conditionedProductSlice_window_lower_of_claim121_at
      D G e0 c hO hbucket (fun j ↦ (ell j).val)
        (x := target) hsmall
    simpa only [P, cond, Gc, cc, E, y, F, f, dvec, shift,
      conditionedCountVectorWindowProbability] using hambient
  have hweighted := countVectorMass_mul_le_weighted_conditioned
    P Good cond hcondNonneg hcondLower
  calc
    p * (kappa / S) ≤
        countVectorMass P Good * (kappa / S) := by
      apply mul_le_mul_of_nonneg_right hmass
      positivity
    _ ≤ ∑ ell : BucketCountVector P,
        countVectorWeight P ell * cond ell := hweighted
    _ = ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability
            D G e0 c O B target ell := by rfl

/-- Source-shaped inner structured lower bound.  The good outer event is a
signed linear-shift interval, a small Claim 12.2 shift moment, and near
balance.  Its mass and the fixed-slice Claim 12.1 certificate are the only
probabilistic inputs. -/
theorem conditionedCountVector_weighted_claim121_lower_of_outer_event
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {delta B M kappa s U radius t lowerScale S p target : ℝ}
    (hM : 0 ≤ M) (hkappa : 0 < kappa) (hs : s = 1 ∨ s = -1)
    (ht : 0 ≤ t) (hS : 0 < S)
    (hband0 : 0 ≤ U - radius - t)
    (hbandM : U + radius + t ≤
      M * lowerScale)
    (hshiftScale : 2 * t ≤ S)
    (hzeroScale :
      2 * zeroCountClaim121Scale D G c O hbucket ≤ S)
    (hclaim : UniformConditionedClaim121Lower
      D G hbucket delta B M kappa s)
    (hlowerScale : ∀ ell : BucketCountVector D.finCoveredPartition,
      countVectorShiftMoment D.finCoveredPartition hbucket
          (D.finCoveredGraph G) ell < t ^ 2 →
      lowerScale ≤ countVectorClaim121Scale D G c O hbucket ell)
    (hcoeffNear : ∀ ell : BucketCountVector D.finCoveredPartition,
      IsNearBalanced delta D.finCoveredPartition (fun j ↦ (ell j).val) →
      HasKSSSBalancedCoefficients delta D.finCoveredPartition
        (Structured.wStar
          (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
          (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O))
          (productSliceDelta D.finCoveredPartition hbucket.choose
            (fun j ↦ (ell j).val)))
        (bucketCenteredAdjacency D.finCoveredPartition.bucket
          hbucket.choose (D.finCoveredGraph G)))
    (hmass : p ≤ countVectorMass D.finCoveredPartition (fun ell ↦
      |countVectorLinearShift D.finCoveredPartition hbucket
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O)) ell -
        (conditionedCountVectorBaseCenter D G e0 c O hbucket target -
          s * U)| ≤ radius ∧
      countVectorShiftMoment D.finCoveredPartition hbucket
          (D.finCoveredGraph G) ell < t ^ 2 ∧
      IsNearBalanced delta D.finCoveredPartition
        (fun j ↦ (ell j).val))) :
    p * (kappa / S) ≤
      ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability
            D G e0 c O B target ell := by
  let Good : BucketCountVector D.finCoveredPartition → Prop := fun ell ↦
    |countVectorLinearShift D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O)) ell -
      (conditionedCountVectorBaseCenter D G e0 c O hbucket target -
        s * U)| ≤ radius ∧
    countVectorShiftMoment D.finCoveredPartition hbucket
        (D.finCoveredGraph G) ell < t ^ 2 ∧
    IsNearBalanced delta D.finCoveredPartition (fun j ↦ (ell j).val)
  apply conditionedCountVector_weighted_claim121_lower
    D G e0 c hO hbucket hkappa hS hclaim Good
    (by simpa only [Good] using hmass)
  · intro ell hell
    exact hell.2.2
  · intro ell hell
    exact hcoeffNear ell hell.2.2
  · intro ell hell
    have hbounds := conditionedCountVectorTargetOffset_signed_bounds
      D G e0 c O hbucket target s U radius t hs ell hell.1
      hell.2.1.le ht
    exact hband0.trans hbounds.1
  · intro ell hell
    have hbounds := conditionedCountVectorTargetOffset_signed_bounds
      D G e0 c O hbucket target s U radius t hs ell hell.1
      hell.2.1.le ht
    exact hbounds.2.trans (hbandM.trans
      (mul_le_mul_of_nonneg_left (hlowerScale ell hell.2.1) hM))
  · intro ell hell
    have hgeometry := countVectorClaim121Scale_geometry
      D G c O hbucket ell
    rcases hgeometry.2 with hshift | hzero
    · have hWnonneg := countVectorShiftMoment_nonneg
        D.finCoveredPartition hbucket (D.finCoveredGraph G) ell
      have hsqrtSq : Real.sqrt
          (countVectorShiftMoment D.finCoveredPartition hbucket
            (D.finCoveredGraph G) ell) ^ 2 =
          countVectorShiftMoment D.finCoveredPartition hbucket
            (D.finCoveredGraph G) ell := Real.sq_sqrt hWnonneg
      have hWlt : countVectorShiftMoment D.finCoveredPartition hbucket
          (D.finCoveredGraph G) ell < t ^ 2 := hell.2.1
      have hsqrt : Real.sqrt
          (countVectorShiftMoment D.finCoveredPartition hbucket
            (D.finCoveredGraph G) ell) ≤ t := by
        nlinarith [hWlt, Real.sqrt_nonneg
          (countVectorShiftMoment D.finCoveredPartition hbucket
            (D.finCoveredGraph G) ell)]
      exact hshift.trans
        ((mul_le_mul_of_nonneg_left hsqrt (by norm_num)).trans hshiftScale)
    · exact hzero.2.trans hzeroScale

/-- Complete fixed-remainder lower pipeline with all constants exposed.  It
combines the outer Berry--Esseen interval, Claim 12.2, near-balance, the
uniform signed Claim 12.1 lower estimate, and the exact count-vector
mixture. -/
theorem conditionedCountVector_window_average_lower_explicit
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    {K H A eps Mlin R eta delta B Mclaim kappa s U t
      lowerScale S nearBad target : ℝ}
    (hclaim122 : ConditionedClaim122Bound D G c O hbucket K)
    (hq : 0 < Fintype.card D.Covered)
    (hH : 0 ≤ H) (hA : 0 < A)
    (hc0 : ∀ i, 0 ≤ D.conditionedCoveredCoefficient G c O i)
    (hcH : ∀ i, D.conditionedCoveredCoefficient G c O i ≤
      H * (Fintype.card D.Covered : ℝ))
    (hedge : A * (Fintype.card D.Covered : ℝ) ^ 2 ≤
      ((D.finCoveredGraph G).edgeFinset.card : ℝ))
    (heps : 0 < eps)
    (hepssigma : eps ≤ Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient
        D.finCoveredPartition hbucket
        (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
          (D.conditionedCoveredCoefficient G c O)))))
    (hMlin : 0 ≤ Mlin)
    (hcenter :
      |conditionedCountVectorBaseCenter D G e0 c O hbucket target - s * U| ≤
        Mlin * Real.sqrt
          (vectorSqNorm (countVectorLinearCoefficient
            D.finCoveredPartition hbucket
            (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
              (D.conditionedCoveredCoefficient G c O)))))
    (hcoeffScale : (H + 1) * (Fintype.card D.Covered : ℝ) ≤ eps)
    (hR : 4 ≤ R)
    (hratioScale :
      2 * (R * eps) *
          (|conditionedCountVectorBaseCenter D G e0 c O hbucket target -
              s * U| + R * eps) ≤
        vectorSqNorm (countVectorLinearCoefficient
          D.finCoveredPartition hbucket
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O))))
    (herror :
      ((3 / 2 : ℝ) * (H + 1) * Real.pi ^ 4 / A) *
        (1 / Real.sqrt (Fintype.card D.Covered : ℝ)) ≤ eta)
    (ht : 0 < t)
    (hFnorm : ‖bucketCenteredAdjacency
        D.finCoveredPartition.bucket hbucket.choose
        (D.finCoveredGraph G)‖ ≤ 60000 * eps)
    (hnearBad : countVectorMass D.finCoveredPartition (fun ell ↦
      ¬ IsNearBalanced delta D.finCoveredPartition
        (fun j ↦ (ell j).val)) ≤ nearBad)
    (hMclaim : 0 ≤ Mclaim) (hkappa : 0 < kappa)
    (hs : s = 1 ∨ s = -1) (hS : 0 < S)
    (hband0 : 0 ≤ U - 30000 * eps - t)
    (hbandM : U + 30000 * eps + t ≤ Mclaim * lowerScale)
    (hshiftScale : 2 * t ≤ S)
    (hzeroScale : 2 * zeroCountClaim121Scale D G c O hbucket ≤ S)
    (hclaim121 : UniformConditionedClaim121Lower
      D G hbucket delta B Mclaim kappa s)
    (hlowerScale : ∀ ell : BucketCountVector D.finCoveredPartition,
      countVectorShiftMoment D.finCoveredPartition hbucket
          (D.finCoveredGraph G) ell < t ^ 2 →
      lowerScale ≤ countVectorClaim121Scale D G c O hbucket ell)
    (hcoeffNear : ∀ ell : BucketCountVector D.finCoveredPartition,
      IsNearBalanced delta D.finCoveredPartition (fun j ↦ (ell j).val) →
      HasKSSSBalancedCoefficients delta D.finCoveredPartition
        (Structured.wStar
          (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
          (RobustRank.graphAdjacencyMatrix (D.finCoveredGraph G))
          (GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
            (D.conditionedCoveredCoefficient G c O))
          (productSliceDelta D.finCoveredPartition hbucket.choose
            (fun j ↦ (ell j).val)))
        (bucketCenteredAdjacency D.finCoveredPartition.bucket
          hbucket.choose (D.finCoveredGraph G))) :
    let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
      (D.conditionedCoveredCoefficient G c O)
    let V := vectorSqNorm
      (countVectorLinearCoefficient D.finCoveredPartition hbucket y)
    (((eps / Real.sqrt V) *
          (Real.exp (-((Mlin + 1) ^ 2) / 2) / 12 -
            Esseen.relativeEsseenConstant * (2 / R + eta)) -
        (K * Real.sqrt (Fintype.card D.Covered) * (60000 * eps)) /
          t ^ 2) - nearBad) * (kappa / S) ≤
      ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability
            D G e0 c O B target ell := by
  dsimp only
  let P := D.finCoveredPartition
  let y := GraphQuadratic.graphEffectiveLinear (D.finCoveredGraph G)
    (D.conditionedCoveredCoefficient G c O)
  let L : BucketCountVector P → ℝ := fun ell ↦
    countVectorLinearShift P hbucket y ell
  let W : BucketCountVector P → ℝ := fun ell ↦
    countVectorShiftMoment P hbucket (D.finCoveredGraph G) ell
  let center := conditionedCountVectorBaseCenter
    D G e0 c O hbucket target - s * U
  let main : ℝ :=
    (eps / Real.sqrt
      (vectorSqNorm (countVectorLinearCoefficient P hbucket y))) *
      (Real.exp (-((Mlin + 1) ^ 2) / 2) / 12 -
        Esseen.relativeEsseenConstant * (2 / R + eta))
  let shiftBad : ℝ :=
    (K * Real.sqrt (Fintype.card D.Covered) * (60000 * eps)) / t ^ 2
  have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
  have houter := countVectorMass_graphLinearShift_smallMoment_lower
    D G c O hbucket hclaim122 hq hH hA hc0 hcH hedge heps hepssigma
      hMlin hcenter hcoeffScale hR hratioScale herror htSq hFnorm
  have houter' : main - shiftBad ≤ countVectorMass P (fun ell ↦
      |L ell - center| ≤ 30000 * eps ∧ W ell < t ^ 2) := by
    simpa only [P, y, L, W, center, main, shiftBad] using houter
  let E : BucketCountVector P → Prop := fun ell ↦
    |L ell - center| ≤ 30000 * eps ∧ W ell < t ^ 2
  let Bad : BucketCountVector P → Prop := fun ell ↦
    ¬ IsNearBalanced delta P (fun j ↦ (ell j).val)
  have hgoodRaw := countVectorMass_lower_sub_bad P E Bad houter'
    (by simpa only [P, Bad] using hnearBad)
  have hgood : (main - shiftBad) - nearBad ≤
      countVectorMass P (fun ell ↦
        |L ell - center| ≤ 30000 * eps ∧ W ell < t ^ 2 ∧
          IsNearBalanced delta P (fun j ↦ (ell j).val)) := by
    apply hgoodRaw.trans_eq
    apply congrArg (countVectorMass P)
    funext ell
    apply propext
    dsimp only [E, Bad]
    tauto
  apply conditionedCountVector_weighted_claim121_lower_of_outer_event
    D G e0 c hO hbucket hMclaim hkappa hs ht.le hS hband0 hbandM
      hshiftScale hzeroScale hclaim121 hlowerScale hcoeffNear
  simpa only [P, y, L, W, center, main, shiftBad] using hgood

/-- Conditional expectation of the ambient graph polynomial after fixing
the RLCD remainder subset and averaging the covered coordinates. -/
noncomputable def remainderConditionalMean
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    (R : Finset (D.remainder : Set (Fin n))) : ℝ :=
  let O := BoundedWindow.subtypeSubsetImage D.remainder R
  GraphQuadratic.graphSliceConstant (D.finCoveredGraph G)
    (Probability.perturbedEdgePolynomial G e0 c O)
    (D.conditionedCoveredCoefficient G c O)

/-- The named remainder conditional mean is exactly the inner covered-cube
expectation. -/
lemma remainderConditionalMean_eq_coveredExpectation
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    (R : Finset (D.remainder : Set (Fin n))) :
    remainderConditionalMean D G e0 c R =
      Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset (Fin (Fintype.card D.Covered)) ↦
          Probability.perturbedEdgePolynomial G e0 c
            (BoundedWindow.subtypeSubsetImage D.remainder R ∪
              D.finCoveredSubsetImage S)) := by
  let O := BoundedWindow.subtypeSubsetImage D.remainder R
  have hO : O ⊆ D.remainder :=
    BoundedWindow.subtypeSubsetImage_subset D.remainder R
  rw [remainderConditionalMean,
    GraphQuadratic.graphSliceConstant_eq_expectation_half]
  apply congrArg (Probability.expectation (1 / 2 : ℝ))
  funext S
  exact (D.perturbedEdgePolynomial_union_finCoveredSubsetImage
    G e0 c hO S).symm

/-- Averaging the remainder conditional mean recovers the ambient mean. -/
lemma expectation_remainderConditionalMean
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ) :
    Probability.expectation (1 / 2 : ℝ)
        (remainderConditionalMean D G e0 c) =
      Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e0 c) := by
  rw [show remainderConditionalMean D G e0 c = fun R ↦
      Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset (Fin (Fintype.card D.Covered)) ↦
          Probability.perturbedEdgePolynomial G e0 c
            (BoundedWindow.subtypeSubsetImage D.remainder R ∪
              D.finCoveredSubsetImage S)) by
    funext R
    exact remainderConditionalMean_eq_coveredExpectation D G e0 c R]
  exact D.expectation_half_remainder_covered_fubini
    (Probability.perturbedEdgePolynomial G e0 c)

/-- Finite conditional Jensen: the remainder conditional mean has no more
variance than the original graph polynomial. -/
lemma variance_remainderConditionalMean_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ) :
    Probability.variance (1 / 2 : ℝ)
        (remainderConditionalMean D G e0 c) ≤
      Probability.variance (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e0 c) := by
  let mu := Probability.expectation (1 / 2 : ℝ)
    (Probability.perturbedEdgePolynomial G e0 c)
  unfold Probability.variance
  rw [expectation_remainderConditionalMean]
  change Probability.expectation (1 / 2 : ℝ) (fun R ↦
      (remainderConditionalMean D G e0 c R - mu) ^ 2) ≤
    Probability.expectation (1 / 2 : ℝ) (fun U ↦
      (Probability.perturbedEdgePolynomial G e0 c U - mu) ^ 2)
  rw [← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  have hpoint (R : Finset (D.remainder : Set (Fin n))) :
      (remainderConditionalMean D G e0 c R - mu) ^ 2 ≤
        Concentration.uniformExpectation
          (fun S : Finset (Fin (Fintype.card D.Covered)) ↦
            (Probability.perturbedEdgePolynomial G e0 c
              (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                D.finCoveredSubsetImage S) - mu) ^ 2) := by
    rw [remainderConditionalMean_eq_coveredExpectation,
      ← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite,
      ← Switching.uniformExpectation_sub_const]
    exact Switching.sq_uniformExpectation_le_uniformExpectation_sq _
  calc
    Concentration.uniformExpectation (fun R ↦
        (remainderConditionalMean D G e0 c R - mu) ^ 2) ≤
      Concentration.uniformExpectation (fun R ↦
        Concentration.uniformExpectation
          (fun S : Finset (Fin (Fintype.card D.Covered)) ↦
            (Probability.perturbedEdgePolynomial G e0 c
              (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                D.finCoveredSubsetImage S) - mu) ^ 2)) :=
      Switching.uniformExpectation_mono hpoint
    _ = Probability.expectation (1 / 2 : ℝ) (fun U ↦
        (Probability.perturbedEdgePolynomial G e0 c U - mu) ^ 2) := by
      rw [BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
      simp_rw [BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
      simpa only [mu] using
      D.expectation_half_remainder_covered_fubini
        (fun U ↦
          (Probability.perturbedEdgePolynomial G e0 c U - mu) ^ 2)

/-- Chebyshev control of noncentral remainder conditionings. -/
lemma uniformProbability_remainderConditionalMean_far_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    {T : ℝ} (hT : 0 < T) :
    Concentration.uniformProbability
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          T ≤ |remainderConditionalMean D G e0 c R -
            Probability.expectation (1 / 2 : ℝ)
              (Probability.perturbedEdgePolynomial G e0 c)|) ≤
      Probability.variance (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G e0 c) / T ^ 2 := by
  have hcheb := Probability.chebyshev_sq_bound
    (V := (D.remainder : Set (Fin n)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hT
    (remainderConditionalMean D G e0 c)
  rw [RLCD.BucketDecomposition.eventProbability_half_eq_uniformProbability]
    at hcheb
  have hvar := variance_remainderConditionalMean_le D G e0 c
  calc
    Concentration.uniformProbability
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          T ≤ |remainderConditionalMean D G e0 c R -
            Probability.expectation (1 / 2 : ℝ)
              (Probability.perturbedEdgePolynomial G e0 c)|) =
      Concentration.uniformProbability
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          T ^ 2 ≤ (remainderConditionalMean D G e0 c R -
            Probability.expectation (1 / 2 : ℝ)
              (remainderConditionalMean D G e0 c)) ^ 2) := by
        apply congrArg Concentration.uniformProbability
        funext R
        apply propext
        rw [expectation_remainderConditionalMean]
        constructor
        · intro h
          simpa only [sq_abs] using
            (sq_le_sq₀ hT.le (abs_nonneg _)).2 h
        · intro h
          have hsq : T ^ 2 ≤
              |remainderConditionalMean D G e0 c R -
                Probability.expectation (1 / 2 : ℝ)
                  (Probability.perturbedEdgePolynomial G e0 c)| ^ 2 := by
            simpa only [sq_abs] using h
          exact (sq_le_sq₀ hT.le (abs_nonneg _)).mp hsq
    _ ≤ Probability.variance (1 / 2 : ℝ)
        (remainderConditionalMean D G e0 c) / T ^ 2 := hcheb
    _ ≤ Probability.variance (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e0 c) / T ^ 2 := by
      exact div_le_div_of_nonneg_right hvar (sq_nonneg T)

/-- At the natural graph-polynomial scale, conditional Jensen and the
degree-three variance estimate give a dimension-free outer tail bound. -/
lemma uniformProbability_remainderConditionalMean_far_scale_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    {A K : ℝ} (hn : 0 < n) (hA : 1 ≤ A) (hK : 0 < K)
    (hc : ∀ v, |c v| ≤ A * n) :
    Concentration.uniformProbability
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          K * A * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
            |remainderConditionalMean D G e0 c R -
              Probability.expectation (1 / 2 : ℝ)
                (Probability.perturbedEdgePolynomial G e0 c)|) ≤
      1 / K ^ 2 := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hT : 0 < K * A * (n : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  refine (uniformProbability_remainderConditionalMean_far_le
    D G e0 c hT).trans ?_
  have hvar := Switching.variance_perturbedEdgePolynomial_half_le
    G e0 c A hA hc
  calc
    Probability.variance (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G e0 c) /
        (K * A * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 ≤
      (A ^ 2 * (n : ℝ) ^ 3) /
        (K * A * (n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
          exact div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 1 / K ^ 2 := by
      rw [mul_pow, mul_pow, GraphQuadratic.n_rpow_three_halves_sq]
      field_simp

/-- The fixed-remainder translated center is controlled by the ambient
target displacement, the conditional-mean displacement, the bounded trace,
and the chosen signed offset. -/
lemma abs_conditionedCountVectorBaseCenter_sub_signed_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    (R : Finset (D.remainder : Set (Fin n)))
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (target s U : ℝ) (hs : s = 1 ∨ s = -1) :
    |conditionedCountVectorBaseCenter D G e0 c
          (BoundedWindow.subtypeSubsetImage D.remainder R)
          hbucket target - s * U| ≤
      |target - Probability.expectation (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G e0 c)| +
        |remainderConditionalMean D G e0 c R -
          Probability.expectation (1 / 2 : ℝ)
            (Probability.perturbedEdgePolynomial G e0 c)| +
        (Fintype.card D.Covered : ℝ) + |U| := by
  let O := BoundedWindow.subtypeSubsetImage D.remainder R
  let mu := Probability.expectation (1 / 2 : ℝ)
    (Probability.perturbedEdgePolynomial G e0 c)
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose (D.finCoveredGraph G)
  have htrace : |trace F| ≤ (Fintype.card D.Covered : ℝ) := by
    simpa only [trace, Fintype.card_fin] using
      LinearLCDCancellation.abs_trace_le_card_of_entry_le_one F
        (abs_bucketCenteredAdjacency_le_one D.finCoveredPartition hbucket
          (D.finCoveredGraph G))
  have hsabs : |s * U| = |U| := by
    rcases hs with rfl | rfl <;> simp
  have hsum :
      |(target - mu) +
          (mu - remainderConditionalMean D G e0 c R) +
          (-trace F) + (-(s * U))| ≤
        |target - mu| +
          |mu - remainderConditionalMean D G e0 c R| +
          |trace F| + |s * U| := by
    calc
      |(target - mu) +
          (mu - remainderConditionalMean D G e0 c R) +
          (-trace F) + (-(s * U))| ≤
          |(target - mu) +
            (mu - remainderConditionalMean D G e0 c R) +
            (-trace F)| + |-(s * U)| := abs_add_le _ _
      _ ≤ (|(target - mu) +
            (mu - remainderConditionalMean D G e0 c R)| +
            |-trace F|) + |-(s * U)| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|target - mu| +
            |mu - remainderConditionalMean D G e0 c R|) +
            |-trace F|) + |-(s * U)| := by gcongr; exact abs_add_le _ _
      _ = |target - mu| +
          |mu - remainderConditionalMean D G e0 c R| +
          |trace F| + |s * U| := by simp
  rw [show conditionedCountVectorBaseCenter D G e0 c O hbucket target -
      s * U =
      (target - mu) + (mu - remainderConditionalMean D G e0 c R) +
        (-trace F) + (-(s * U)) by
    rw [remainderConditionalMean]
    dsimp only [conditionedCountVectorBaseCenter, O, F, mu]
    ring]
  calc
    |(target - mu) + (mu - remainderConditionalMean D G e0 c R) +
        (-trace F) + (-(s * U))| ≤
      |target - mu| + |mu - remainderConditionalMean D G e0 c R| +
        |trace F| + |s * U| := hsum
    _ ≤ |target - mu| + |mu - remainderConditionalMean D G e0 c R| +
        (Fintype.card D.Covered : ℝ) + |s * U| := by gcongr
    _ = |target - Probability.expectation (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G e0 c)| +
        |remainderConditionalMean D G e0 c R -
          Probability.expectation (1 / 2 : ℝ)
            (Probability.perturbedEdgePolynomial G e0 c)| +
        (Fintype.card D.Covered : ℝ) + |U| := by
      rw [abs_sub_comm mu, hsabs]

/-- A pointwise lower bound on a finite uniform event averages with exactly
the probability of that event. -/
lemma uniformProbability_mul_le_uniformExpectation
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (f : Omega → ℝ) (Good : Omega → Prop) {L : ℝ}
    (hf : ∀ omega, 0 ≤ f omega)
    (hgood : ∀ omega, Good omega → L ≤ f omega) :
    Concentration.uniformProbability Good * L ≤
      Concentration.uniformExpectation f := by
  classical
  calc
    Concentration.uniformProbability Good * L =
        Concentration.uniformExpectation
          (fun omega ↦ if Good omega then L else 0) := by
      rw [Concentration.uniformExpectation,
        Concentration.uniformProbability, Finset.sum_ite]
      simp only [Finset.sum_const_zero, Finset.sum_const,
        nsmul_eq_mul]
      ring
    _ ≤ Concentration.uniformExpectation f := by
      apply Switching.uniformExpectation_mono
      intro omega
      by_cases homega : Good omega
      · simpa only [homega, if_true] using hgood omega homega
      · simpa only [homega, if_false] using hf omega

/-- Local pointwise identification between the raw structured mixture and
the named conditional count-vector sum.  This lower module deliberately
does not import the later upper-asymptotic module where the same bridge is
used in the opposite direction. -/
lemma structuredCountVectorRaw_eq_conditionedSum_lower
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) [instAdj : DecidableRel G.Adj]
    (e0 : ℝ) (c : Fin n → ℝ)
    (R : Finset (D.remainder : Set (Fin n))) (B target : ℝ) :
    (∑ ell : BucketCountVector D.finCoveredPartition,
        (Fintype.card
            (ProductSlicePoint D.finCoveredPartition
              (fun j ↦ (ell j).val)) : ℝ) /
            Fintype.card (Finset (Fin (Fintype.card D.Covered))) *
          Concentration.uniformProbability
            (fun S : ProductSlicePoint D.finCoveredPartition
                (fun j ↦ (ell j).val) ↦
              |Probability.perturbedEdgePolynomial G e0 c
                  (BoundedWindow.subtypeSubsetImage D.remainder R ∪
                    D.finCoveredSubsetImage S.1) - target| ≤ B)) =
      ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability D G e0 c
            (BoundedWindow.subtypeSubsetImage D.remainder R)
            B target ell := by
  have hinst : instAdj = Classical.decRel G.Adj := Subsingleton.elim _ _
  cases hinst
  apply Finset.sum_congr rfl
  intro ell _hell
  rw [countVectorWeight, conditionedCountVectorWindowProbability]

/-- Exact lower averaging over the RLCD remainder.  It converts a uniform
fixed-remainder count-vector lower bound on `Good` into the ambient Bernoulli
window probability, losing only the complement probability of `Good`. -/
lemma eventProbability_half_structured_lower_of_good_remainders
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e0 : ℝ) (c : Fin n → ℝ) (B target : ℝ)
    (Good : Finset (D.remainder : Set (Fin n)) → Prop)
    {L bad : ℝ} (hL : 0 ≤ L)
    (hbad : Concentration.uniformProbability (fun R ↦ ¬ Good R) ≤ bad)
    (hlower : ∀ R, Good R →
      L ≤ ∑ ell : BucketCountVector D.finCoveredPartition,
        countVectorWeight D.finCoveredPartition ell *
          conditionedCountVectorWindowProbability D G e0 c
            (BoundedWindow.subtypeSubsetImage D.remainder R)
            B target ell) :
    (1 - bad) * L ≤
      Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
        |Probability.perturbedEdgePolynomial G e0 c U - target| ≤ B) := by
  let f : Finset (D.remainder : Set (Fin n)) → ℝ := fun R ↦
    ∑ ell : BucketCountVector D.finCoveredPartition,
      countVectorWeight D.finCoveredPartition ell *
        conditionedCountVectorWindowProbability D G e0 c
          (BoundedWindow.subtypeSubsetImage D.remainder R) B target ell
  have hf : ∀ R, 0 ≤ f R := by
    intro R
    dsimp only [f]
    exact Finset.sum_nonneg fun ell _ ↦ mul_nonneg
      (countVectorWeight_nonneg D.finCoveredPartition ell)
      (conditionedCountVectorWindowProbability_nonneg
        D G e0 c (BoundedWindow.subtypeSubsetImage D.remainder R)
          B target ell)
  have hpartition := Switching.uniformProbability_add_compl Good
  have hgoodProb : 1 - bad ≤ Concentration.uniformProbability Good := by
    linarith
  have haverage : (1 - bad) * L ≤
      Concentration.uniformExpectation f := by
    exact (mul_le_mul_of_nonneg_right hgoodProb hL).trans
      (uniformProbability_mul_le_uniformExpectation f Good hf
        (by simpa only [f] using hlower))
  have hmixture :
      Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
          |Probability.perturbedEdgePolynomial G e0 c U - target| ≤ B) =
        Concentration.uniformExpectation f := by
    rw [D.eventProbability_half_eq_structured_countVector_mixture]
    rw [← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
    apply congrArg Concentration.uniformExpectation
    funext R
    exact structuredCountVectorRaw_eq_conditionedSum_lower D G e0 c R B target
  exact haverage.trans_eq hmixture.symm

/-- The exact outer event used by the structured lower averaging: all
covered degrees are typical and the conditional mean is central at the
natural `n^(3/2)` scale. -/
def IsGoodLowerRemainder
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    (A K : ℝ) (R : Finset (D.remainder : Set (Fin n))) : Prop :=
  (∀ i : Fin (Fintype.card D.Covered),
    |(AKSGraph.degreeInto G (D.finCoveredEquiv i).1
          (BoundedWindow.subtypeSubsetImage D.remainder R) : ℝ) -
        (AKSGraph.degreeInto G (D.finCoveredEquiv i).1
          D.remainder : ℝ) / 2| < Real.sqrt n) ∧
  |remainderConditionalMean D G e0 c R -
      Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e0 c)| <
    K * A * (n : ℝ) ^ ((3 : ℝ) / 2)

/-- Union bound for the complement of `IsGoodLowerRemainder`.  The first
input is precisely the exceptional-set estimate from `StructuredTypical`;
the second is supplied by conditional Jensen and Chebyshev above. -/
lemma uniformProbability_not_isGoodLowerRemainder_le
    {n k : ℕ} {d0 : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d0 k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (c : Fin n → ℝ)
    (A K degreeBad centralBad : ℝ)
    (hdegree : Concentration.uniformProbability
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          D.remainderSubsetEquivOutsideAssignment R ∈
            D.badRemainderConditionings G (Real.sqrt n)) ≤ degreeBad)
    (hcentral : Concentration.uniformProbability
        (fun R : Finset (D.remainder : Set (Fin n)) ↦
          K * A * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
            |remainderConditionalMean D G e0 c R -
              Probability.expectation (1 / 2 : ℝ)
                (Probability.perturbedEdgePolynomial G e0 c)|) ≤
          centralBad) :
    Concentration.uniformProbability (fun R ↦
        ¬ IsGoodLowerRemainder D G e0 c A K R) ≤
      degreeBad + centralBad := by
  let DegreeBad : Finset (D.remainder : Set (Fin n)) → Prop := fun R ↦
    D.remainderSubsetEquivOutsideAssignment R ∈
      D.badRemainderConditionings G (Real.sqrt n)
  let CentralBad : Finset (D.remainder : Set (Fin n)) → Prop := fun R ↦
    K * A * (n : ℝ) ^ ((3 : ℝ) / 2) ≤
      |remainderConditionalMean D G e0 c R -
        Probability.expectation (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G e0 c)|
  have hsubset : ∀ R,
      ¬ IsGoodLowerRemainder D G e0 c A K R →
        DegreeBad R ∨ CentralBad R := by
    intro R hR
    rw [IsGoodLowerRemainder, not_and_or] at hR
    rcases hR with hdeg | hcent
    · left
      dsimp only [DegreeBad]
      rw [RLCD.BucketDecomposition.badRemainderConditionings,
        Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      push Not at hdeg
      obtain ⟨i, hi⟩ := hdeg
      refine ⟨i, ?_⟩
      simpa only [D.outsideAssignmentSet_remainderSubsetEquiv R] using hi
    · right
      dsimp only [CentralBad]
      exact le_of_not_gt hcent
  calc
    Concentration.uniformProbability (fun R ↦
        ¬ IsGoodLowerRemainder D G e0 c A K R) ≤
      Concentration.uniformProbability (fun R ↦
        DegreeBad R ∨ CentralBad R) :=
          Concentration.uniformProbability_mono hsubset
    _ ≤ Concentration.uniformProbability DegreeBad +
        Concentration.uniformProbability CentralBad :=
      BooleanSlices.uniformProbability_or_le DegreeBad CentralBad
    _ ≤ degreeBad + centralBad := by
      exact add_le_add (by simpa only [DegreeBad] using hdegree)
        (by simpa only [CentralBad] using hcentral)

end GaussianQuadratic
end Erdos88
