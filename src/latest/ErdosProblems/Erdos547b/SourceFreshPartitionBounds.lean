/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreshChunkBounds
import ErdosProblems.Erdos547b.ForestPartitionPartCount
import ErdosProblems.Erdos547b.Claim616HierarchyClassification

/-!
# Root-count and branch-size bounds at the actual fresh scale

Choose the tree partition at `floor (epsilon*N/2)`. The existing source
order threshold pays its total root count, using the actual degree-form
cover. No larger-scale partition is silently treated as a fresh one.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFreshPartitionBounds

open Finset SimpleGraph Erdos547b.TreePartition
open Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceFreshChunkBounds Erdos547b.ZhaoClaim616HierarchyClassification
open Erdos547b.ZhaoClaim617BranchCount Erdos547b.ZhaoClaim68BranchAdapter

theorem degreeForm_q_le_mul_clusterSize
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) : (q : ℝ) ≤ (M : ℝ) * W.clusterSize := by
  have hE := (degreeForm_source_bounds hα hα1 W hq).1
  have hd : (degreeError α : ℝ) ≤ 1 := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
  have hEq : (W.exceptional.card : ℝ) ≤ q := by
    have h := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    linarith only [hE, h]
  have hcover : (W.exceptional.card : ℝ) + (W.partition.parts.card : ℝ) * W.clusterSize = 2 * q := by
    exact_mod_cast exceptional_add_clusters_eq_host W
  have hparts : W.partition.parts.card ≤ M := W.cleaned_le_ordinary.trans W.upper_parts
  have hmul : (W.partition.parts.card : ℝ) * W.clusterSize ≤ (M : ℝ) * W.clusterSize := by
    exact_mod_cast Nat.mul_le_mul_right W.clusterSize hparts
  linarith only [hEq, hcover, hmul]

theorem degreeForm_epsilon_sq_clusterSize_gt
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    100 * ((M : ℝ) + 1) < (epsilon α : ℝ) ^ 2 * W.clusterSize := by
  have he := (parameter_pos hα).2.2.2.2.2.2.2
  obtain ⟨_, _, _, _, heSmall, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have heOne : epsilon α ≤ 1 := by linarith only [heSmall, hdOne]
  have hfour : epsilon α ^ 4 ≤ epsilon α ^ 2 := by
    calc
      epsilon α ^ 4 = epsilon α ^ 2 * epsilon α ^ 2 := by ring
      _ ≤ epsilon α ^ 2 * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ he.le heOne) (sq_nonneg _)
      _ = _ := mul_one _
  have hlargeQ := (orderThreshold_product hα hq).trans_le
    (mul_le_mul_of_nonneg_right hfour (Nat.cast_nonneg q))
  have hlarge : (1000000 : ℝ) * ((M : ℝ) + 1) ^ 2 < (epsilon α : ℝ) ^ 2 * q := by
    exact_mod_cast hlargeQ
  have hqMN := degreeForm_q_le_mul_clusterSize hα hα1 W hq
  have hscaled := mul_le_mul_of_nonneg_left hqMN (sq_nonneg (epsilon α : ℝ))
  by_contra hnot
  have hsmall : (epsilon α : ℝ) ^ 2 * W.clusterSize ≤ 100 * ((M : ℝ) + 1) := le_of_not_gt hnot
  have hM := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  nlinarith only [hlarge, hscaled, hM, sq_nonneg (M : ℝ), (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]

/-- Integer division and floor losses in the two-parity root count. -/
theorem root_count_at_freshScale (ε : ℝ) (N M q count : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hN : 0 < N)
    (hq : (q : ℝ) ≤ (M : ℝ) * N) (hstrong : 100 * ((M : ℝ) + 1) < ε ^ 2 * N)
    (hcount : count ≤ 2 * ((q + 1 + ⌊ε * N / 2⌋₊) / (⌊ε * N / 2⌋₊ + 1))) :
    (count : ℝ) ≤ ε * N := by
  let m : ℕ := ⌊ε * N / 2⌋₊
  have hm : (m : ℝ) ≤ ε * N / 2 := Nat.floor_le (by positivity)
  have hmLower : ε * N / 2 ≤ (m : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hprodNat : count * (m + 1) ≤ 2 * (q + 1 + m) := by
    calc
      count * (m + 1) ≤ (2 * ((q + 1 + m) / (m + 1))) * (m + 1) :=
        Nat.mul_le_mul_right _ hcount
      _ = 2 * (((q + 1 + m) / (m + 1)) * (m + 1)) := by ring
      _ ≤ 2 * (q + 1 + m) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
  have hprod : (count : ℝ) * ((m : ℝ) + 1) ≤ 2 * ((q : ℝ) + 1 + m) := by
    exact_mod_cast hprodNat
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hstrongN := mul_lt_mul_of_pos_right hstrong hNpos
  have hεN : ε * N ≤ (N : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hε1 hNpos.le
  have hroom : 2 * ((q : ℝ) + 1 + m) < ε * N * (ε * N / 2) := by
    nlinarith only [hstrongN, hεN, hm, hq, hNone,
      mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) hNpos.le]
  by_contra hnot
  have hgt : ε * N < (count : ℝ) := lt_of_not_ge hnot
  have hmul := mul_le_mul_of_nonneg_left hmLower (Nat.cast_nonneg count : (0 : ℝ) ≤ count)
  have hstrict := mul_lt_mul_of_pos_right hgt (by positivity : 0 < ε * N / 2)
  linarith only [hprod, hroom, hmul, hstrict]

/-- The actual tree partition's root count fits the actual root-exclusion
budget at the same scale as all of its small branches. -/
theorem freshPartition_root_bound
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q)
    {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U} [DecidableRel T.Adj]
    (hcard : Fintype.card U = q + 1) {root : U}
    (P : ZhaoForestPartition T root (freshBranchBound α W.clusterSize)) :
    (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize := by
  have he : (0 : ℝ) < epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2
  obtain ⟨_, _, _, _, heSmall, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have heOne : epsilon α ≤ 1 := by linarith only [heSmall, hdOne]
  apply root_count_at_freshScale (epsilon α : ℝ) W.clusterSize M q P.numParts he
    (by exact_mod_cast heOne) W.clusterSize_pos
    (degreeForm_q_le_mul_clusterSize hα hα1 W hq)
    (degreeForm_epsilon_sq_clusterSize_gt hα hα1 W hq)
  simpa only [hcard, freshBranchBound] using numParts_le_two_mul_rootBound P

/-- A single actual partition supplies both the branch scale and the root
budget required by the sequential source embedding. -/
theorem exists_freshPartition
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q)
    {U : Type*} [Fintype U] [DecidableEq U] (T : SimpleGraph U) [DecidableRel T.Adj]
    (hT : T.IsTree) (hcard : Fintype.card U = q + 1) (root : U) :
    ∃ P : ZhaoForestPartition T root (freshBranchBound α W.clusterSize),
      (P.numParts : ℝ) ≤ (epsilon α : ℝ) * W.clusterSize ∧
      ∀ j,
        (branchForest P).branches.size j ≤ freshBranchBound α W.clusterSize := by
  obtain ⟨P⟩ := exists_zhaoForestPartition T root (freshBranchBound α W.clusterSize) hT
  exact ⟨P, freshPartition_root_bound hα hα1 W hq hcard P,
    canonical_branch_size_le_small P⟩

end Erdos547b.ZhaoSourceFreshPartitionBounds

#print axioms Erdos547b.ZhaoSourceFreshPartitionBounds.degreeForm_q_le_mul_clusterSize
#print axioms Erdos547b.ZhaoSourceFreshPartitionBounds.degreeForm_epsilon_sq_clusterSize_gt
#print axioms Erdos547b.ZhaoSourceFreshPartitionBounds.root_count_at_freshScale
#print axioms Erdos547b.ZhaoSourceFreshPartitionBounds.freshPartition_root_bound
#print axioms Erdos547b.ZhaoSourceFreshPartitionBounds.exists_freshPartition
