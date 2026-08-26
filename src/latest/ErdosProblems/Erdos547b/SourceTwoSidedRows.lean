/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.TwoSidedRootRowsPreparation
import ErdosProblems.Erdos547b.SourceDegreeFormRootRows

/-! # A genuine source witness retaining lower physical-row estimates -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceTwoSidedRows

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSection6Dichotomy Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoClusterPairPruning Erdos547b.ZhaoSourceRootTruncation
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoTwoSidedRootRowsPreparation

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

structure TwoSidedSource (Q : Certificate W) where
  clean : CleanSourceWitness W Q
  badA : Finset (Index W)
  badB : Finset (Index W)
  badA_card : (badA.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * Fintype.card (Index W)
  badB_card : (badB.card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * Fintype.card (Index W)
  lowerA : ∀ j : Index W, j ≠ Q.A → j ≠ Q.B → j ∉ badA →
    (((host W).edgeDensity (clusterVertices (assignment W) Q.A) (clusterVertices (assignment W) j) : ℝ) -
      (epsilon α : ℝ)) * W.clusterSize ≤ (degreeInto clean.source clean.zA (clusterVertices (assignment W) j) : ℝ)
  lowerB : ∀ j : Index W, j ≠ Q.A → j ≠ Q.B → j ∉ badB →
    (((host W).edgeDensity (clusterVertices (assignment W) Q.B) (clusterVertices (assignment W) j) : ℝ) -
      (epsilon α : ℝ)) * W.clusterSize ≤ (degreeInto clean.source clean.zB (clusterVertices (assignment W) j) : ℝ)

private theorem uniform_real_of_rat
    {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    {ε : ℚ} {X Y : Finset V} (h : H.IsUniform ε X Y) :
    H.IsUniform (ε : ℝ) X Y := by
  intro X' hX' Y' hY' hXlarge hYlarge
  have hXQ : (X.card : ℚ) * ε ≤ (X'.card : ℚ) := by exact_mod_cast hXlarge
  have hYQ : (Y.card : ℚ) * ε ≤ (Y'.card : ℚ) := by exact_mod_cast hYlarge
  exact_mod_cast h hX' hY' hXQ hYQ

theorem exists_twoSidedSource
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (Q : Certificate W)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    Nonempty (TwoSidedSource W Q) := by
  subst hostN
  let _ : DecidableRel W.graph.Adj := W.graph_decidable
  let J : Finset (Index W) := Finset.univ \ {Q.A, Q.B}
  have hJ : ∀ j ∈ J, j ≠ Q.A ∧ j ≠ Q.B := by
    intro j hj
    simpa only [J, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, not_or] using hj
  have hcluster (i : Index W) : clusterVertices (assignment W) i = i.1 :=
    clusterVertices_partitionAssignment W.exceptional W.partition i
  have hclusterCard (i : Index W) :
      (clusterVertices (assignment W) i).card = W.clusterSize := by
    rw [hcluster]
    exact W.equal_clusters i.1 i.2
  have huniform (i j : Index W) :
      (host W).IsUniform (epsilon α : ℝ)
        (clusterVertices (assignment W) i) (clusterVertices (assignment W) j) := by
    apply uniform_real_of_rat
    apply uniform_pair (assignment W) W.graph (large W)
    rw [hcluster, hcluster]
    exact W.pair_uniform i j
  obtain ⟨hδposQ, hδmargin⟩ := rootTypicality_margin hα hα1
  have hδpos : (0 : ℝ) < rootTypicality α := by exact_mod_cast hδposQ
  have hδsmallQ : 2 * rootTypicality α < 2 * fourthRoot α ^ 2 := by
    linarith only [hδmargin, sq_nonneg (fourthRoot α)]
  have hδsmall : 2 * (rootTypicality α : ℝ) < 2 * (fourthRoot α : ℝ) ^ 2 := by
    exact_mod_cast hδsmallQ
  have hNpos : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hpool (i : Index W) (pool : Finset (Fin (2 * q)))
      (hpoolCard : pool.card = sourceQuota W) :
      2 * (rootTypicality α : ℝ) * (clusterVertices (assignment W) i).card < pool.card := by
    rw [hclusterCard, hpoolCard]
    calc
      2 * (rootTypicality α : ℝ) * W.clusterSize <
          (2 * (fourthRoot α : ℝ) ^ 2) * W.clusterSize :=
        mul_lt_mul_of_pos_right hδsmall hNpos
      _ ≤ (sourceQuota W : ℝ) := Nat.le_ceil _
  have hεsquare : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  obtain ⟨zA, hzA, zB, hzB, DA, hDA, DB, hDB, hroots, hmassA, hmassB,
      hsource, hdegreeLoss, hupperA, hupperB, LA, hLA, LB, hLB,
      hDAcard, hDBcard, hLAcard, hLBcard, hlowerA, hlowerB⟩ :=
    exists_two_clean_both_roots (assignment W) (host W) Q.A Q.B Q.adj.ne Q.A₀ Q.B₀
      Q.A₀_subset Q.B₀_subset J hJ W.clusterSize
      (fun i _ => (hclusterCard i).le) (epsilon α : ℝ) (rootTypicality α : ℝ)
      hδpos hεsquare (fun j _ => huniform Q.A j) (fun j _ => huniform Q.B j)
      (hpool Q.A Q.A₀ Q.A₀_card) (hpool Q.B Q.B₀ Q.B₀_card)
  let Hsource := truncateRoot (truncateRoot (host W) zA (clusterUnion (assignment W) DA))
    zB (clusterUnion (assignment W) DB)
  let extraLoss := max (clusterUnion (assignment W) DA).card
    (clusterUnion (assignment W) DB).card + 2
  have hJcard : J.card ≤ W.partition.parts.card := by
    have h := Finset.card_le_univ J
    simpa only [Index, Fintype.card_coe] using h
  have hJcardR : (J.card : ℝ) ≤ W.partition.parts.card := by exact_mod_cast hJcard
  have hJscale : (rootTypicality α : ℝ) * J.card * W.clusterSize ≤
      (rootTypicality α : ℝ) * W.partition.parts.card * W.clusterSize := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJcardR hδpos.le) (by positivity)
  have hmax : (max (clusterUnion (assignment W) DA).card
      (clusterUnion (assignment W) DB).card : ℝ) ≤
        (rootTypicality α : ℝ) * J.card * W.clusterSize := by
    exact max_le hmassA hmassB
  have hlossSmall : (extraLoss : ℝ) < (fourthRoot α : ℝ) ^ 2 * q := by
    have hbudget := root_truncation_budget hα hα1 W horder
    dsimp only [extraLoss]
    push_cast
    linarith only [hmax, hJscale, hbudget]
  let C : CleanSourceWitness W Q :=
    { source := Hsource
      zA := zA
      zB := zB
      zA_mem := hzA
      zB_mem := hzB
      distinct := hroots
      extraLoss := extraLoss
      source_le := hsource
      degree_loss := by convert hdegreeLoss using 1
      extraLoss_small := hlossSmall
      upperA := by
        intro j hjA hjB
        convert hupperA j (by simp [J, hjA, hjB]) using 1 <;> congr!
      upperB := by
        intro j hjA hjB
        convert hupperB j (by simp [J, hjA, hjB]) using 1 <;> congr! }
  have hcount (X Y : Finset (Index W))
      (hX : (X.card : ℝ) ≤ (rootTypicality α : ℝ) * J.card)
      (hY : (Y.card : ℝ) ≤ (rootTypicality α : ℝ) * J.card) :
      ((X ∪ Y).card : ℝ) ≤ 2 * (rootTypicality α : ℝ) * Fintype.card (Index W) := by
    have hu : ((X ∪ Y).card : ℝ) ≤ (X.card : ℝ) + Y.card := by exact_mod_cast Finset.card_union_le X Y
    have hJall : (J.card : ℝ) ≤ Fintype.card (Index W) := by exact_mod_cast Finset.card_le_univ J
    have hscale := mul_le_mul_of_nonneg_left hJall (by positivity : 0 ≤ 2 * (rootTypicality α : ℝ))
    linarith only [hu, hX, hY, hscale]
  refine ⟨{
    clean := C
    badA := DA ∪ LA
    badB := DB ∪ LB
    badA_card := hcount DA LA hDAcard hLAcard
    badB_card := hcount DB LB hDBcard hLBcard
    lowerA := ?_
    lowerB := ?_ }⟩
  · intro j hjA hjB hj
    have h := hlowerA j (Finset.mem_sdiff.mpr ⟨by simp [J, hjA, hjB], hj⟩)
    rw [hclusterCard] at h
    convert h using 1 <;> congr!
  · intro j hjA hjB hj
    have h := hlowerB j (Finset.mem_sdiff.mpr ⟨by simp [J, hjA, hjB], hj⟩)
    rw [hclusterCard] at h
    convert h using 1 <;> congr!

end Erdos547b.ZhaoSourceTwoSidedRows

#print axioms Erdos547b.ZhaoSourceTwoSidedRows.exists_twoSidedSource

