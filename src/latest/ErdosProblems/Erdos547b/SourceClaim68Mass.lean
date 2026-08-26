/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim68FromHost

/-!
# Claim 6.8's actual major-half nontrivial branch mass

The fresh-partition root count pays both hierarchy losses. The proved
host leaf bound supplies the remaining premise of the exact source count.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim68Mass

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceClaim68FromHost Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceFreshPartitionBounds
open Erdos547b.ZhaoClaim68ConcreteLeaves Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim68

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem root_count_sqrt_margin (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (count : ℕ) (hcount : (count : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize) :
    3 * (count : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q := by
  subst hostN
  obtain ⟨_, _, _, hd, he, hd1⟩ := reservoir_cleanup_bounds hα hα1
  have he3 : 3 * epsilon α ≤ fourthRoot α ^ 2 := by
    linarith only [hd, he, sq_nonneg (fourthRoot α)]
  have he3R : 3 * (epsilon α : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 := by exact_mod_cast he3
  have hN := (degreeForm_source_bounds hα hα1 W horder).2.2
  have hd1R : (degreeError α : ℝ) ≤ 1 := by exact_mod_cast hd1
  have hdq := mul_le_mul_of_nonneg_right hd1R (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hNq : (W.clusterSize : ℝ) ≤ q := by
    nlinarith only [hN, hdq, (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  have he0 : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hcq := hcount.trans (mul_le_mul_of_nonneg_left hNq he0)
  have hcoef := mul_le_mul_of_nonneg_right he3R (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hcq, hcoef]

variable (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] (hT : T.IsTree)
variable {globalRoot : U} (P : ZhaoForestPartition T globalRoot (freshBranchBound α W.clusterSize))

include Q S hT in
theorem nontrivialHalfMass_lower
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hcard : Fintype.card U = q + 1)
    (hnot : ¬T.IsContained G) :
    (q : ℝ) / 2 - 12 * (fourthRoot α : ℝ) ^ 2 * q < (nontrivialHalfMass P : ℝ) := by
  have hl := originalLevelOneLeaves_lt_of_not_copy W Q S hT P hα hα1 hhost horder hcard hnot
  have hroots : (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact freshPartition_root_bound hα hα1 W horder hcard P
  have hc := root_count_sqrt_margin W hα hα1 hhost horder P.numParts hroots
  have htq : 0 ≤ (fourthRoot α : ℝ) ^ 2 * q := by positivity
  have hd : (0 : ℝ) ≤ degreeError α := by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le
  have h := claim6_8_nontrivialHalfMass_lower P (degreeError α : ℝ) hd q hcard
    (by rw [sqrt_degreeError]; exact hl)
    (by rw [sqrt_degreeError]; linarith only [hc, (Nat.cast_nonneg P.numParts : (0 : ℝ) ≤ P.numParts)])
    (by rw [sqrt_degreeError]; linarith only [hc, htq])
  simpa only [sqrt_degreeError] using h

end Erdos547b.ZhaoSourceClaim68Mass

#print axioms Erdos547b.ZhaoSourceClaim68Mass.root_count_sqrt_margin
#print axioms Erdos547b.ZhaoSourceClaim68Mass.nontrivialHalfMass_lower
