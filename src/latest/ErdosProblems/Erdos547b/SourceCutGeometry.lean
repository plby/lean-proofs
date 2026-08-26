/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceOrdinaryCut
import ErdosProblems.Erdos547b.PaddedMatchingCut
import ErdosProblems.Erdos547b.SourceMidpointNumerics

/-! # Physical cut sides and a rounded balanced-cut movement budget -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceCutGeometry

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoSection6Dichotomy
open Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoPaddedMatchingCut
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceNearFullNumerics
open Erdos547b.ZhaoSourceNearFullFromHost Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoSourceMidpointNumerics
open Erdos547b.ZhaoLemma611Claim618Adapter

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

def leftSide : Finset (Fin hostN) := clusterUnion (padAssignment (assignment W)) O.D.V1
def rightSide : Finset (Fin hostN) :=
  exceptionalVertices (padAssignment (assignment W)) ∪ clusterUnion (padAssignment (assignment W)) O.D.V2

def moveBudget : ℕ := ⌈(8 * (eta α : ℝ) + (degreeError α : ℝ)) * q + W.clusterSize⌉₊

theorem cut_partition : Disjoint (leftSide W Q S O) (rightSide W Q S O) ∧
    leftSide W Q S O ∪ rightSide W Q S O = Finset.univ := by
  obtain ⟨hdisj, hcover, _⟩ := reducedCut_of_decomposition O.D
  constructor
  · exact Finset.disjoint_union_right.mpr
      ⟨(exceptional_disjoint_clusterUnion (padAssignment (assignment W)) O.D.V1).symm,
        clusterUnion_disjoint (padAssignment (assignment W)) hdisj⟩
  · unfold leftSide rightSide
    rw [← Finset.union_assoc, Finset.union_comm (clusterUnion _ O.D.V1), Finset.union_assoc,
      ← clusterUnion_union_of_union, hcover]
    exact exceptional_union_clusterUnion_univ _

theorem leftSide_card : (leftSide W Q S O).card = O.D.V1.card * W.clusterSize := by
  apply card_decomposition_V1_clusterUnion (assignment W) O.D W.clusterSize
  intro i
  rw [clusterVertices_partitionAssignment]
  exact W.equal_clusters i.val i.property

theorem moveBudget_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (moveBudget W : ℝ) ≤ (8 * (eta α : ℝ) + 2 * (degreeError α : ℝ)) * q := by
  have he : (0 : ℝ) ≤ eta α := by exact_mod_cast (parameter_pos hα).2.2.1.le
  have hd : (0 : ℝ) ≤ degreeError α := by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le
  have hN : (W.clusterSize : ℝ) ≤ (degreeError α : ℝ) * q / 500 := by
    subst hostN
    exact (degreeForm_source_bounds hα hα1 W horder).2.2
  have hscale := degree_scale_large hα hα1 horder
  have hceil := Nat.ceil_lt_add_one (by positivity :
    0 ≤ (8 * (eta α : ℝ) + (degreeError α : ℝ)) * q + W.clusterSize)
  change (moveBudget W : ℝ) < _ at hceil
  nlinarith only [hceil, hN, hscale]

theorem leftSide_near_half (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (leftSide W Q S O).card ≤ q + moveBudget W ∧
      q ≤ (leftSide W Q S O).card + moveBudget W := by
  obtain ⟨he, heSmall, _, _⟩ := parameter_bounds hα hα1
  have hd : (0 : ℝ) ≤ degreeError α := by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le
  have hN : (0 : ℝ) ≤ W.clusterSize := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hL : ((leftSide W Q S O).card : ℝ) = (O.D.V1.card : ℝ) * W.clusterSize := by
    exact_mod_cast leftSide_card W Q S O
  obtain ⟨hV1, hV1up, _, _⟩ := support_bounds W Q S O
  have hV1upR : (O.D.V1.card : ℝ) ≤ paddedHalf (Index W) := by exact_mod_cast hV1up
  obtain ⟨hvolLo, hvolHi⟩ := sharp_paddedVolume W hα hα1 hhost horder
  have hcoef : 0 ≤ 1 - 8 * (eta α : ℝ) := by linarith only [heSmall]
  have hlow1 := mul_le_mul_of_nonneg_right hV1 hN
  have hlow2 := mul_le_mul_of_nonneg_left hvolLo hcoef
  have hupp := mul_le_mul_of_nonneg_right hV1upR hN
  have hb : (8 * (eta α : ℝ) + (degreeError α : ℝ)) * q + W.clusterSize ≤ (moveBudget W : ℝ) :=
    Nat.le_ceil _
  have hh : 0 ≤ (8 * (eta α : ℝ) + (degreeError α : ℝ)) * q := by positivity
  have hboth : ((leftSide W Q S O).card : ℝ) ≤ q + (moveBudget W : ℝ) ∧
      (q : ℝ) ≤ (leftSide W Q S O).card + (moveBudget W : ℝ) := by
    constructor
    · linarith only [hL, hupp, hvolHi, hb, hh]
    · have hcross : 0 ≤ (eta α : ℝ) * (degreeError α : ℝ) * q := by positivity
      nlinarith only [hL, hlow1, hlow2, hb, hN, hcross]
  exact ⟨by exact_mod_cast hboth.1, by exact_mod_cast hboth.2⟩

end Erdos547b.ZhaoSourceCutGeometry

#print axioms Erdos547b.ZhaoSourceCutGeometry.cut_partition
#print axioms Erdos547b.ZhaoSourceCutGeometry.leftSide_card
#print axioms Erdos547b.ZhaoSourceCutGeometry.moveBudget_le
#print axioms Erdos547b.ZhaoSourceCutGeometry.leftSide_near_half
