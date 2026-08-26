/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceFreshChunkEmbedding
import ErdosProblems.Erdos547b.SourceDegreeFormBounds

/-!
# Source-parameter gates for fresh regular-pair chunks

The actual cluster size is large enough for the integral branch scale.
The permanent cleanup, parent eligibility, and internal greedy margins
then follow from the proved source parameter schedule.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceFreshChunkBounds

open Finset SimpleGraph
open Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormBounds

def freshDeletionBudget (α : ℚ) (N : ℕ) : ℕ := ⌈2 * (epsilon α : ℝ) * N⌉₊
def freshBranchBound (α : ℚ) (N : ℕ) : ℕ := ⌊(epsilon α : ℝ) * N / 2⌋₊

/-- A lower cluster-size bound, complementary to the earlier cleanup
upper bounds. It follows from the same explicit finite order threshold. -/
theorem epsilon_mul_clusterSize_gt_two
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) : (2 : ℝ) < (epsilon α : ℝ) * W.clusterSize := by
  obtain ⟨_, _, _, _, _, _, _, heQ⟩ := parameter_pos hα
  obtain ⟨_, _, _, _, heSmall, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have heOne : epsilon α ≤ 1 := by linarith only [heSmall, hdOne]
  have heFour : epsilon α ^ 4 ≤ epsilon α := pow_succ_le_self heQ.le heOne 3
  have heR : (0 : ℝ) < epsilon α := by exact_mod_cast heQ
  obtain ⟨hE, _, _⟩ := degreeForm_source_bounds hα hα1 W hq
  have hdR : (degreeError α : ℝ) ≤ 1 := by exact_mod_cast hdOne
  have hEq : (W.exceptional.card : ℝ) ≤ q := by
    have h := mul_le_mul_of_nonneg_right hdR (show (0 : ℝ) ≤ q by positivity)
    linarith only [hE, h]
  have hcover : (W.exceptional.card : ℝ) + (W.partition.parts.card : ℝ) * W.clusterSize =
      2 * q := by
    exact_mod_cast exceptional_add_clusters_eq_host W
  have hparts : W.partition.parts.card ≤ M := W.cleaned_le_ordinary.trans W.upper_parts
  have hmul : (W.partition.parts.card : ℝ) * W.clusterSize ≤ (M : ℝ) * W.clusterSize := by
    exact_mod_cast Nat.mul_le_mul_right W.clusterSize hparts
  have hqMN : (q : ℝ) ≤ (M : ℝ) * W.clusterSize := by linarith only [hEq, hcover, hmul]
  have horderQ := orderThreshold_product hα hq
  have heqQ : epsilon α ^ 4 * (q : ℚ) ≤ epsilon α * q :=
    mul_le_mul_of_nonneg_right heFour (by positivity)
  have hlarge : (1000000 : ℝ) * ((M : ℝ) + 1) ^ 2 < (epsilon α : ℝ) * q := by
    exact_mod_cast horderQ.trans_le heqQ
  have htwice : 2 * (M : ℝ) < (1000000 : ℝ) * ((M : ℝ) + 1) ^ 2 := by
    nlinarith only [sq_nonneg (M : ℝ), show (0 : ℝ) ≤ M by positivity]
  have hscaled := mul_le_mul_of_nonneg_left hqMN heR.le
  by_contra hnot
  have hsmall : (epsilon α : ℝ) * W.clusterSize ≤ 2 := le_of_not_gt hnot
  have hsmallM := mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ M by positivity)
  nlinarith only [hlarge, htwice, hscaled, hsmallM]

/-- The four elementary rounding and regular-pair gates. -/
theorem fresh_chunk_numerics (ε γ d : ℝ) (N : ℕ)
    (hε : 0 < ε) (hγ : 0 < γ) (hd : 0 < d)
    (hγOne : γ ≤ 1) (hdOne : d ≤ 1)
    (hproduct : 10 * ε ≤ d * γ) (hscale : 2 ≤ ε * N) :
    let L : ℕ := ⌈2 * ε * N⌉₊
    let m : ℕ := ⌊ε * N / 2⌋₊
    0 < m ∧ (2 : ℝ) + 3 * m ≤ 3 * (ε * N) ∧
      (L : ℝ) + 2 ≤ (γ - 3 * ε) * N ∧
      (m : ℝ) + ε * N + 1 ≤ (d - ε) * (γ * N - L) := by
  dsimp only
  have hN : (0 : ℝ) ≤ N := by positivity
  have hL : (⌈2 * ε * N⌉₊ : ℝ) ≤ 3 * ε * N := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2 * ε * N by positivity)
    linarith only [hc, hscale]
  have hm : (⌊ε * N / 2⌋₊ : ℝ) ≤ ε * N / 2 := Nat.floor_le (by positivity)
  have hmpos : 0 < ⌊ε * N / 2⌋₊ := by
    have hfloor : (1 : ℕ) ≤ ⌊ε * N / 2⌋₊ := Nat.le_floor (by linarith only [hscale])
    omega
  have heγ : 10 * ε ≤ γ := by
    have h := mul_le_mul_of_nonneg_right hdOne hγ.le
    linarith only [hproduct, h]
  have hed : 10 * ε ≤ d := by
    have h := mul_le_mul_of_nonneg_left hγOne hd.le
    linarith only [hproduct, h]
  have heγN := mul_le_mul_of_nonneg_right heγ hN
  have heprodN := mul_le_mul_of_nonneg_right hproduct hN
  have hroom : γ * (N : ℝ) / 2 ≤ γ * N - (⌈2 * ε * N⌉₊ : ℝ) := by
    linarith only [hL, heγN, show 0 ≤ ε * N by positivity]
  have hfactor : d / 2 ≤ d - ε := by linarith only [hed, hε]
  have hmargin : d * γ * N / 4 ≤
      (d - ε) * (γ * N - (⌈2 * ε * N⌉₊ : ℝ)) := by
    calc
      d * γ * N / 4 = (d / 2) * (γ * N / 2) := by ring
      _ ≤ (d - ε) * (γ * N - (⌈2 * ε * N⌉₊ : ℝ)) :=
        mul_le_mul hfactor hroom (by positivity) (by linarith only [hfactor, hd])
  refine ⟨hmpos, ?_, ?_, ?_⟩
  · linarith only [hm, hscale]
  · nlinarith only [hL, heγN, hscale]
  · nlinarith only [hm, hscale, heprodN, hmargin]

/-- No additional finite-size gate is needed at the actual source witness. -/
theorem degreeForm_fresh_chunk_gates
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    let N := W.clusterSize
    let L := freshDeletionBudget α N
    let m := freshBranchBound α N
    0 < m ∧ (2 : ℝ) + 3 * m ≤ 3 * ((epsilon α : ℝ) * N) ∧
      (L : ℝ) + 2 ≤ ((gamma α : ℝ) - 3 * (epsilon α : ℝ)) * N ∧
      (m : ℝ) + (epsilon α : ℝ) * N + 1 ≤
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * ((gamma α : ℝ) * N - L) := by
  obtain ⟨_, _, _, _, _, hd, hg, he⟩ := parameter_pos hα
  obtain ⟨_, _, _, _, _, hγd, _⟩ := parameter_upper_bounds hα hα1
  obtain ⟨_, _, _, _, _, hdOne⟩ := reservoir_cleanup_bounds hα hα1
  have hγOne : gamma α ≤ 1 := by linarith only [hγd, hdOne]
  have hcutOne : densityCutoff α ≤ 1 := by
    unfold densityCutoff
    linarith only [hdOne]
  exact fresh_chunk_numerics (epsilon α : ℝ) (gamma α : ℝ) (densityCutoff α : ℝ)
    W.clusterSize (by exact_mod_cast he) (by exact_mod_cast hg) (by exact_mod_cast hd)
    (by exact_mod_cast hγOne) (by exact_mod_cast hcutOne)
    (by exact_mod_cast (regularity_product_margin hα hα1).le)
    (epsilon_mul_clusterSize_gt_two hα hα1 W hq).le

end Erdos547b.ZhaoSourceFreshChunkBounds

#print axioms Erdos547b.ZhaoSourceFreshChunkBounds.epsilon_mul_clusterSize_gt_two
#print axioms Erdos547b.ZhaoSourceFreshChunkBounds.fresh_chunk_numerics
#print axioms Erdos547b.ZhaoSourceFreshChunkBounds.degreeForm_fresh_chunk_gates
