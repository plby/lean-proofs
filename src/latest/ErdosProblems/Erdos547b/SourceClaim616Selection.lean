/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCrossingClusters
import ErdosProblems.Erdos547b.SourceFreshChunkBounds

/-!
# Literal source selection and layer budgets in Claim 6.16

The selected forest is chosen after the actual incident matching. The
ceiling and fresh-branch overshoot are retained. This is source selection,
not yet the three-layer graph embedding of the selected forest.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceClaim616Selection

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoSourceCrossingClusters Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceNearFullNumerics Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim616 Erdos547b.ZhaoClaim616SourceBridge Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoLemma59Part2Full

theorem layer_parameter_gates {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    6 * (eta α : ℝ) + 6 * (gamma α : ℝ) + (epsilon α : ℝ) < 1 / 2 ∧
      4 * (gamma α : ℝ) + (epsilon α : ℝ) < 3 / 2 ∧ (epsilon α : ℝ) ≤ 1 := by
  have hu := parameter_upper_bounds hα hα1
  have hp := parameter_pos hα
  have hd : degreeError α ≤ eta α / 1000 := by exact_mod_cast (parameter_bounds hα hα1).2.2.1
  have heSmall : (eta α : ℝ) < 1 / 16 := (parameter_bounds hα hα1).2.1
  have hgSmall : gamma α ≤ eta α / 1000 := by linarith only [hu.2.2.2.2.2.1, hd, hp.2.2.1]
  have hepSmall : epsilon α ≤ eta α / 1000 := by linarith only [hu.2.2.2.2.2.2, hgSmall, hp.2.2.1]
  have hg : (gamma α : ℝ) ≤ (eta α : ℝ) / 1000 := by exact_mod_cast hgSmall
  have hep : (epsilon α : ℝ) ≤ (eta α : ℝ) / 1000 := by exact_mod_cast hepSmall
  constructor
  · linarith only [heSmall, hg, hep]
  constructor <;> linarith only [heSmall, hg, hep]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb) (C : Finset (EvenPadding (Index W)))

def selectionTarget : ℕ := ⌈(∑ e ∈ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e) +
  (crossingScale W : ℝ) * W.clusterSize / 2⌉₊

variable {U : Type*} [Fintype U] [DecidableEq U]
variable {T : SimpleGraph U} [DecidableRel T.Adj] {root : U} {small : ℕ}
variable (P : ZhaoForestPartition T root small)

theorem exists_selectedForest
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (hCcard : C.card = crossingScale W)
    (hsmall : ∀ i, (branchForest P).branches.size i ≤ freshBranchBound α W.clusterSize)
    (hmass : 3 * (crossingScale W : ℝ) * W.clusterSize ≤ largeHalfMass P) :
    ∃ F : SelectedF0Within (branchForest P) (halfBranches P)
        (selectionTarget W Q S O C) (freshBranchBound α W.clusterSize),
      (∑ e ∈ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e) +
          (crossingScale W : ℝ) * W.clusterSize / 2 ≤
        (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) ∧
      (levelOneDemand F.toSelectedF0.forest : ℝ) ≤
        (1 - 2 * (eta α : ℝ) - 2 * (gamma α : ℝ)) * crossingScale W * W.clusterSize ∧
      (deepDemand F.toSelectedF0.forest : ℝ) ≤
        (1 - (gamma α : ℝ)) * (4 * crossingScale W) * W.clusterSize := by
  subst hostN
  obtain ⟨hr, _, _, _, _⟩ := scale_bounds W Q S O hα hα1 rfl horder
  have hr1 : (1 : ℝ) ≤ crossingScale W := by exact_mod_cast hr
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hεN := epsilon_mul_clusterSize_gt_two hα hα1 W horder
  have hε : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  obtain ⟨hgates, hdeep, he1⟩ := layer_parameter_gates hα hα1
  have hNtwo : (2 : ℝ) < W.clusterSize := hεN.trans_le (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hN.le)
  have hrN : (2 : ℝ) < (crossingScale W : ℝ) * W.clusterSize := by
    nlinarith only [hr1, hNtwo, hN]
  have hmpos : 0 < freshBranchBound α W.clusterSize := by
    have hfloor : 1 ≤ freshBranchBound α W.clusterSize := Nat.le_floor (by linarith only [hεN])
    omega
  have hm : (freshBranchBound α W.clusterSize : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize / 2 :=
    Nat.floor_le (by positivity)
  have hovershoot : 1 + (freshBranchBound α W.clusterSize : ℝ) ≤
      (epsilon α : ℝ) * crossingScale W * W.clusterSize := by
    have hrεN := mul_le_mul_of_nonneg_right hr1 (show 0 ≤ (epsilon α : ℝ) * W.clusterSize by positivity)
    nlinarith only [hrεN, hm, hεN]
  have hMcard : (MatchingDecomposition.MzeroEdges O.D C).card ≤ crossingScale W :=
    (MatchingDecomposition.Mzero_edge_card_le O.D C).trans_eq hCcard
  have hMcardR : ((MatchingDecomposition.MzeroEdges O.D C).card : ℝ) ≤ crossingScale W := by exact_mod_cast hMcard
  have hA := (sideWeight_sum_le W Q S 0 (MatchingDecomposition.MzeroEdges O.D C)).trans
    (mul_le_mul_of_nonneg_left hMcardR (by positivity : 0 ≤ 2 * (W.clusterSize : ℝ)))
  have hnonneg : 0 ≤ (∑ e ∈ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e) +
      (crossingScale W : ℝ) * W.clusterSize / 2 := by
    exact add_nonneg (Finset.sum_nonneg (fun e _ => sideWeight_nonneg W Q S 0 e)) (by positivity)
  have htarget : (selectionTarget W Q S O C : ℝ) <
      (∑ e ∈ MatchingDecomposition.MzeroEdges O.D C, sideWeight W Q S 0 e) +
        (crossingScale W : ℝ) * W.clusterSize / 2 + 1 := Nat.ceil_lt_add_one hnonneg
  have havailable : selectionTarget W Q S O C ≤ largeHalfMass P := by
    have hR : (selectionTarget W Q S O C : ℝ) ≤ largeHalfMass P := by
      nlinarith only [htarget, hA, hrN, hmass]
    exact_mod_cast hR
  obtain ⟨F⟩ := exists_selectedHalfF0 P hmpos hsmall havailable
  have hlower : (selectionTarget W Q S O C : ℝ) ≤
      (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) := by exact_mod_cast F.lower
  have hupper : (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) <
      (selectionTarget W Q S O C : ℝ) + freshBranchBound α W.clusterSize := by exact_mod_cast F.upper
  have hthree : 3 * (levelOneDemand F.toSelectedF0.forest : ℝ) ≤
      (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) := by
    exact_mod_cast F.toSelectedF0.three_mul_levelOne_le_edgeDemand
  have hdeepMass : (deepDemand F.toSelectedF0.forest : ℝ) ≤
      (OrderedBranchForest.edgeDemand F.toSelectedF0.forest : ℝ) := by
    exact_mod_cast F.toSelectedF0.deepDemand_le_edgeDemand
  have hscale : 0 ≤ (crossingScale W : ℝ) * W.clusterSize := by positivity
  have hgateScale := mul_le_mul_of_nonneg_right hgates.le hscale
  have hdeepScale := mul_le_mul_of_nonneg_right hdeep.le hscale
  refine ⟨F, (Nat.le_ceil _).trans hlower, ?_, ?_⟩
  · nlinarith only [hthree, hupper, htarget, hA, hovershoot, hgateScale]
  · nlinarith only [hdeepMass, hupper, htarget, hA, hovershoot, hdeepScale]

end Erdos547b.ZhaoSourceClaim616Selection

#print axioms Erdos547b.ZhaoSourceClaim616Selection.layer_parameter_gates
#print axioms Erdos547b.ZhaoSourceClaim616Selection.exists_selectedForest
