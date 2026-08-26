/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.ForestPartitionPartCount
import ErdosProblems.Erdos547b.RoundedScales

/-!
# Eventual hierarchy bounds for the Zhao forest partition

Choosing component size `floor (rho*n)` makes the number of components
bounded independently of `n`.  The proof below keeps the rounding explicit
and gives the two exact real inequalities consumed by Claims 6.8 and 6.10.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.TreePartition

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoRoundedScales

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V}

/-- With component size `floor (rho*n)`, the product of the part count and
`rho` is strictly below six.  This deliberately coarse constant absorbs the
one-unit floor and division losses. -/
theorem numParts_mul_lt_six
    (rho : ℝ) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card V = n + 1)
    (P : ZhaoForestPartition T globalRoot (lowerScale (rho * n))) :
    (P.numParts : ℝ) * rho < 6 := by
  let s := lowerScale (rho * n)
  let q := (Fintype.card V + s) / (s + 1)
  have hparts : P.numParts ≤ 2 * q := by
    simpa only [s, q] using numParts_le_two_mul_rootBound P
  have hqpos : 0 < q := by
    apply Nat.div_pos
    · have hcardPos : 0 < Fintype.card V := by omega
      omega
    · exact Nat.succ_pos s
  have hsLower : rho * n < (s : ℝ) + 1 := by
    simpa only [s] using lt_lowerScale_cast_add_one (rho * n)
  have hsUpper : (s : ℝ) ≤ rho * n := by
    simpa only [s] using lowerScale_cast_le (by positivity : 0 ≤ rho * n)
  have hsLeN : (s : ℝ) ≤ n := by
    have hmul := mul_le_mul_of_nonneg_right hrhoOne
      (show (0 : ℝ) ≤ n by positivity)
    nlinarith
  have hdivNat : q * (s + 1) ≤ Fintype.card V + s := by
    exact Nat.div_mul_le_self _ _
  have hdiv : (q : ℝ) * ((s : ℝ) + 1) ≤
      (Fintype.card V : ℝ) + s := by
    exact_mod_cast hdivNat
  have hright : (Fintype.card V : ℝ) + s ≤ 2 * n + 1 := by
    have hcardR : (Fintype.card V : ℝ) = n + 1 := by
      exact_mod_cast hcard
    rw [hcardR]
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hqrho : (q : ℝ) * rho < 3 := by
    have hstrict := mul_lt_mul_of_pos_left hsLower hqR
    nlinarith
  have hpartsR : (P.numParts : ℝ) ≤ 2 * q := by exact_mod_cast hparts
  have hrho0 : 0 ≤ rho := hrho.le
  nlinarith

/-- The exact two hierarchy estimates used in the source once the final
order threshold makes `rho * sigma * n` larger than twelve. -/
theorem eventual_hierarchy_bounds
    (rho sigma : ℝ) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (_hsigma : 0 ≤ sigma)
    (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card V = n + 1)
    (P : ZhaoForestPartition T globalRoot (lowerScale (rho * n)))
    (hlarge : 12 < rho * sigma * n) :
    2 * (P.numParts : ℝ) < 1 + sigma * n ∧
      3 * (P.numParts : ℝ) < 1 + 2 * sigma * n := by
  have hp := numParts_mul_lt_six rho hrho hrhoOne n hn hcard P
  have hnR : (0 : ℝ) ≤ n := by positivity
  constructor <;> nlinarith

end Erdos547b.TreePartition

#print axioms Erdos547b.TreePartition.numParts_mul_lt_six
#print axioms Erdos547b.TreePartition.eventual_hierarchy_bounds
