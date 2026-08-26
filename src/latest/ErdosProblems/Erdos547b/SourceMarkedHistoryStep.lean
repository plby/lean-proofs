/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePrivateGroupSupports
import ErdosProblems.Erdos547b.SourceMarkedGroupCapacity
import ErdosProblems.Erdos547b.MarkedPrefixLoads

/-!
# An online marked-branch step from actual previous branch images

The occupied set is constructed from the previous copies. All occupancy
bounds are derived from source orders and prescribed marks. The only
current-root input is its genuine good-group count, not an embedding premise.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedHistoryStep

open Finset SimpleGraph
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourcePrivatePairGeometry Erdos547b.ZhaoSourceMarkedAvailableSets
open Erdos547b.ZhaoSourceMarkedGroupCapacity Erdos547b.ZhaoSourceMarkedGroupStep
open Erdos547b.ZhaoMarkedPrefixLoads Erdos547b.ZhaoMarkedTripleLoads
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)
variable {C : Finset (EvenPadding (Index W))} (P : Geometry W Q S O C)

variable {J : Type*} [Fintype J] (A : J → Type*) [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
variable (T : ∀ j, SimpleGraph (A j)) (root : ∀ j, A j) (special : ∀ j, Finset (A j))
variable (copy : ∀ j, (T j).Copy (embeddingHost W)) (assign : J → {c // c ∈ C})

def historyImage (j : J) : Finset (Fin hostN) := Finset.univ.image (copy j)

omit [Fintype J] in
theorem history_image_bounds
    (hroot : ∀ j, copy j (root j) ∈ whole W (P.center (assign j)))
    (hmark : ∀ j a, a ∈ special j → copy j a ∈ whole W (P.center (assign j)))
    (hother : ∀ j a, a ≠ root j → a ∉ special j → copy j a ∈ P.pairs W Q S O (assign j))
    (hsize : ∀ j, 3 ≤ Fintype.card (A j)) :
    (∀ j, historyImage W A T copy j ⊆ P.support W Q S O (assign j)) ∧
    (∀ j, 3 * (historyImage W A T copy j ∩ whole W (P.center (assign j))).card ≤
      Fintype.card (A j) + 3 * (special j).card) := by
  have hothers : ∀ j a, a ≠ root j → a ∉ special j →
      copy j a ∈ P.pairs W Q S O (assign j) ∪ ∅ := by
    intro j a har ham
    exact Finset.mem_union_left _ (hother j a har ham)
  constructor
  · intro j
    have h := image_subset_three_sets (copy j) (root j) (special j)
      (whole W (P.center (assign j))) (P.pairs W Q S O (assign j)) ∅
      (hroot j) (hmark j) (hothers j)
    simpa only [historyImage, Geometry.support, Finset.union_empty] using h
  · intro j
    exact three_mul_intermediate_load_le (copy j) (root j) (special j)
      (whole W (P.center (assign j))) (P.pairs W Q S O (assign j)) ∅
      (hroot j) (hmark j) (hothers j) (P.center_disjoint_pairs W Q S O _ _)
      (Finset.disjoint_empty_right _) (hsize j)

theorem history_occupied_bounds (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (base : Finset (Fin hostN)) (hbase : ∀ x, Disjoint base (P.support W Q S O x))
    (hroot : ∀ j, copy j (root j) ∈ whole W (P.center (assign j)))
    (hmark : ∀ j a, a ∈ special j → copy j a ∈ whole W (P.center (assign j)))
    (hother : ∀ j a, a ≠ root j → a ∉ special j → copy j a ∈ P.pairs W Q S O (assign j))
    (hsize : ∀ j, 3 ≤ Fintype.card (A j))
    (hmarks : (∑ j, ((special j).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize)
    (x : {c // c ∈ C})
    (hmass : (groupLoad assign (fun j => Fintype.card (A j)) x : ℝ) ≤ capacity α W.clusterSize) :
    ((used base (historyImage W A T copy) ∩ whole W (P.center x)).card : ℝ) ≤
        (1 - 2 * (eta α : ℝ) - 3 * (gamma α : ℝ)) * W.clusterSize ∧
      (used base (historyImage W A T copy) ∩ P.pairs W Q S O x).card ≤ 3 * W.clusterSize := by
  obtain ⟨himage, hlocal⟩ := history_image_bounds W Q S O P A T root special copy assign
    hroot hmark hother hsize
  have hmarksLocal : (groupLoad assign (fun j => (special j).card) x : ℝ) ≤
      (epsilon α : ℝ) * W.clusterSize := by
    apply le_trans _ hmarks
    exact_mod_cast groupLoad_le_total assign (fun j => (special j).card) x
  have hC := used_center_bound base (historyImage W A T copy)
    (fun x => whole W (P.center x)) (P.pairs W Q S O) assign
    (fun j => Fintype.card (A j)) (fun j => (special j).card)
    hbase (P.supports_disjoint W Q S O) himage hlocal x
  have hPairs := used_inter_card_le base (historyImage W A T copy) (P.support W Q S O)
    assign (fun j => Fintype.card (A j)) hbase (P.supports_disjoint W Q S O) himage
    (fun j => (Finset.card_image_le).trans_eq (Finset.card_univ))
    x (P.pairs W Q S O x) Finset.subset_union_right
  exact occupied_bounds hα hα1 W.clusterSize _ _ _ _ hmass hmarksLocal hC hPairs

variable {B : Type*} [Fintype B] [DecidableEq B]

theorem exists_historyStep (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hC : 0 < C.card)
    (base : Finset (Fin hostN)) (hbase : ∀ x, Disjoint base (P.support W Q S O x))
    (hroot : ∀ j, copy j (root j) ∈ whole W (P.center (assign j)))
    (hmark : ∀ j a, a ∈ special j → copy j a ∈ whole W (P.center (assign j)))
    (hother : ∀ j a, a ≠ root j → a ∉ special j → copy j a ∈ P.pairs W Q S O (assign j))
    (hsize : ∀ j, 3 ≤ Fintype.card (A j))
    (hmarks : (∑ j, ((special j).card : ℝ)) ≤ (epsilon α : ℝ) * W.clusterSize)
    (htotal : (∑ j, (Fintype.card (A j) : ℝ)) ≤
      (5 / 2 + (epsilon α : ℝ)) * C.card * W.clusterSize)
    (z : Fin hostN) (bad : Finset {c // c ∈ C}) (hbad : 16 * bad.card ≤ C.card)
    (hparent : ∀ x, x ∉ bad → (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
      (((whole W (P.center x)).filter ((embeddingHost W).Adj z)).card : ℝ))
    (tree : SimpleGraph B) (htree : tree.IsTree) (r : B) (marks : Finset B)
    (hcolor : ∀ a ∈ marks, htree.coloringTwoOfVert r a = 0)
    (hsmall : Fintype.card B ≤ freshBranchBound α W.clusterSize) :
    ∃ (x : {c // c ∈ C}) (i : Fin 4) (f : tree.Copy (embeddingHost W)),
      (groupLoad assign (fun j => Fintype.card (A j)) x : ℝ) + Fintype.card B ≤ capacity α W.clusterSize ∧
      (embeddingHost W).Adj z (f r) ∧
      (∀ a, f a ∉ used base (historyImage W A T copy)) ∧
      (∀ a ∈ insert r marks, f a ∈ whole W (P.center x) ∧
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          ((Q.A₀.filter ((embeddingHost W).Adj (f a))).card : ℝ)) ∧
      (∀ a, a ≠ r → a ∉ marks → f a ∈
        if htree.coloringTwoOfVert r a = 0 then whole W (P.Y (x, i)) else whole W (P.X (x, i))) ∧
      ((Finset.univ.image f) ∩ whole W (P.center x)).card ≤ 1 + marks.card ∧
      Finset.univ.image f ⊆ P.support W Q S O x := by
  have hsum : (∑ x : {c // c ∈ C}, (groupLoad assign (fun j => Fintype.card (A j)) x : ℝ)) =
      ∑ j, (Fintype.card (A j) : ℝ) := by
    exact_mod_cast sum_groupLoad assign (fun j => Fintype.card (A j))
  obtain ⟨x, hx, hroom⟩ := exists_good_group_with_room hα hα1
    (by simpa only [Fintype.card_coe] using hC) W.clusterSize W.clusterSize_pos
    (groupLoad assign (fun j => Fintype.card (A j))) bad
    (by simpa only [Fintype.card_coe] using hbad)
    (by simpa only [hsum, Fintype.card_coe] using htotal)
  have hmass : (groupLoad assign (fun j => Fintype.card (A j)) x : ℝ) ≤ capacity α W.clusterSize :=
    le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) hroom
  obtain ⟨husedC, husedPairs⟩ := history_occupied_bounds W Q S O P A T root special copy assign
    hα hα1 base hbase hroot hmark hother hsize hmarks x hmass
  obtain ⟨i, f, hfattach, hfresh, hmarked, hordinary, hload, hsupport⟩ := exists_groupStep W Q
    hα hα1 (P.center x) (fun i => P.X (x, i)) (fun i => P.Y (x, i))
    (P.center_adj x) (fun i => P.center_X (x, i)) (fun i => P.Y_X (x, i))
    (fun i => P.center_pair_disjoint x (x, i))
    (fun i j hij => P.pairs_disjoint (x, i) (x, j) (fun h => hij (congrArg Prod.snd h)))
    (used base (historyImage W A T copy)) z (hparent x hx) husedC husedPairs tree htree r marks hcolor hsmall
  refine ⟨x, i, f, ?_, hfattach, hfresh, ?_, hordinary, hload,
    hsupport.trans (P.three_sets_subset_support W Q S O x i)⟩
  · have hsmallR : (Fintype.card B : ℝ) ≤ freshBranchBound α W.clusterSize := by exact_mod_cast hsmall
    linarith only [hroom, hsmallR]
  · intro a ha
    exact ⟨(Finset.mem_sdiff.mp (hmarked a ha).1).1, (hmarked a ha).2⟩

end Erdos547b.ZhaoSourceMarkedHistoryStep

#print axioms Erdos547b.ZhaoSourceMarkedHistoryStep.history_occupied_bounds
#print axioms Erdos547b.ZhaoSourceMarkedHistoryStep.exists_historyStep
