/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.ConcentratedEmbedding

/-!
# Quantitative consequences of an all-direction host moment

These lemmas connect the all-direction moment furnished by the two DRC
iterations with the total-weight, diagonal, and influence inputs of the
concentrated partition theorem.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace PreparedHost

attribute [local instance] Classical.propDecidable

noncomputable section

universe u

theorem card_eraseCoord {ι : Type u} [Fintype ι] [DecidableEq ι] (b : ι) :
    Fintype.card (Pruning.eraseCoord b) = Fintype.card ι - 1 := by
  simpa [Pruning.eraseCoord] using
    (Fintype.card_subtype_compl (fun i : ι => i = b))

/-- A dimension-`D` constant-coordinate moment controls the raw sum in any
smaller finite dimension. -/
theorem raw_const_le_card_pow_mul
    {N D θ s : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (U T : Finset (Fin N)) (hU : U.Nonempty)
    (hdim : Fintype.card ι ≤ D) (hε : 0 ≤ ε)
    (hmoment : FiniteDefect.moment G θ s (fun _ : Fin D => U) T ≤ ε) :
    HostTools.rawFamilyMoment G θ s (fun _ : ι => U) T ≤
      (N : ℝ) ^ Fintype.card ι * ε := by
  have hmomentι : FiniteDefect.familyMoment G θ s (fun _ : ι => U) T ≤ ε := by
    rw [HostPartition.familyMoment_const_eq_moment_card]
    exact (HostTools.moment_mono_dimension G hU T θ s hdim).trans hmoment
  have hcardNat : (FiniteDefect.familyTuples (fun _ : ι => U)).card ≤
      N ^ Fintype.card ι := by
    rw [FiniteDefect.card_familyTuples]
    simp only [Finset.prod_const, Finset.card_univ]
    exact Nat.pow_le_pow_left (by simpa using Finset.card_le_univ U) _
  have hcardReal : ((FiniteDefect.familyTuples (fun _ : ι => U)).card : ℝ) ≤
      (N : ℝ) ^ Fintype.card ι := by
    exact_mod_cast hcardNat
  rw [HostTools.rawFamilyMoment_eq_card_mul_moment]
  calc
    ((FiniteDefect.familyTuples (fun _ : ι => U)).card : ℝ) *
        FiniteDefect.familyMoment G θ s (fun _ : ι => U) T ≤
      ((FiniteDefect.familyTuples (fun _ : ι => U)).card : ℝ) * ε :=
        mul_le_mul_of_nonneg_left hmomentι (by positivity)
    _ ≤ (N : ℝ) ^ Fintype.card ι * ε :=
      mul_le_mul_of_nonneg_right hcardReal hε

/-- The one-coordinate-deleted raw sum has the expected `N^(k-1)` scale. -/
theorem raw_eraseCoord_le
    {N D θ s : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (U T : Finset (Fin N)) (hU : U.Nonempty)
    (hdim : Fintype.card ι ≤ D) (hε : 0 ≤ ε)
    (hmoment : FiniteDefect.moment G θ s (fun _ : Fin D => U) T ≤ ε)
    (b : ι) :
    HostTools.rawFamilyMoment G θ s
        (fun _ : Pruning.eraseCoord b => U) T ≤
      (N : ℝ) ^ (Fintype.card ι - 1) * ε := by
  have heraseDim : Fintype.card (Pruning.eraseCoord b) ≤ D := by
    rw [card_eraseCoord]
    omega
  simpa [card_eraseCoord] using
    (raw_const_le_card_pow_mul G U T hU heraseDim hε hmoment)

/-- Restricting tuple coordinates and decreasing their weights can only
decrease the incident weight at every host vertex. -/
theorem incident_le_of_domination
    {N θ s : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (base : ι → Finset (Fin N)) (U T : Finset (Fin N))
    (weight : (ι → Fin N) → ℝ)
    (hbase : ∀ i, base i ⊆ U)
    (hweight : ∀ g ∈ FiniteDefect.familyTuples base,
      0 ≤ weight g ∧ weight g ≤ FiniteDefect.defectPower G θ g T s)
    (v : Fin N) :
    PartitionConcentration.incident (FiniteDefect.familyTuples base) weight v ≤
      Pruning.incidentWeight (G := G) (ι := ι) θ s U T v := by
  unfold PartitionConcentration.incident Pruning.incidentWeight
  have hsub : (FiniteDefect.familyTuples base).filter
      (fun g => Pruning.tupleUses g v) ⊆
      (FiniteDefect.familyTuples (fun _ : ι => U)).filter
        (fun g => Pruning.tupleUses g v) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    refine ⟨?_, hg.2⟩
    rw [FiniteDefect.mem_familyTuples] at hg ⊢
    intro i
    exact hbase i (hg.1 i)
  calc
    (∑ g ∈ (FiniteDefect.familyTuples base).filter
        (fun g => Pruning.tupleUses g v), weight g) ≤
      ∑ g ∈ (FiniteDefect.familyTuples base).filter
        (fun g => Pruning.tupleUses g v),
        FiniteDefect.defectPower G θ g T s := by
      apply Finset.sum_le_sum
      intro g hg
      exact (hweight g (Finset.mem_filter.mp hg).1).2
    _ ≤ ∑ g ∈ (FiniteDefect.familyTuples (fun _ : ι => U)).filter
        (fun g => Pruning.tupleUses g v),
        FiniteDefect.defectPower G θ g T s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro g hg hnot
      exact FiniteDefect.defectPower_nonneg G θ g T s

/-- All-direction moment bound, including the precise repeated-coordinate
error, for a restricted coordinate product and dominated defect weights. -/
theorem weightedMean_raw_le_of_all_direction
    {P : Type*} [Fintype P] [DecidableEq P]
    {N D θ s : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (q : P → ℝ) (prescribed : ι → P)
    (base : ι → Finset (Fin N)) (U T : Finset (Fin N))
    (weight : (ι → Fin N) → ℝ)
    (hU : U.Nonempty) (hdim : Fintype.card ι ≤ D)
    (hq : ∀ p, 0 ≤ q p) (hqsum : ∑ p, q p ≤ 1)
    (hε : 0 ≤ ε)
    (hbase : ∀ i, base i ⊆ U)
    (hweight : ∀ g ∈ FiniteDefect.familyTuples base,
      0 ≤ weight g ∧ weight g ≤ FiniteDefect.defectPower G θ g T s)
    (hmoment : FiniteDefect.moment G θ s (fun _ : Fin D => U) T ≤ ε) :
    Erdos136.McDiarmid.weightedMean
        (fun _ : Fin N => HostPartition.labelWeight q)
        (PartitionConcentration.rawStatistic
          (FiniteDefect.familyTuples base) prescribed weight) ≤
      (∏ i, q (prescribed i)) *
          ((N : ℝ) ^ Fintype.card ι * ε) +
        (Fintype.card ι : ℝ) ^ 2 *
          ((N : ℝ) ^ (Fintype.card ι - 1) * ε) := by
  let S := FiniteDefect.familyTuples base
  let S₀ := FiniteDefect.familyTuples (fun _ : ι => U)
  let weight₀ : (ι → Fin N) → ℝ := fun g =>
    FiniteDefect.defectPower G θ g T s
  have hsub : S ⊆ S₀ := by
    intro g hg
    rw [FiniteDefect.mem_familyTuples] at hg ⊢
    exact fun i => hbase i (hg i)
  have hraw : (∑ g ∈ S₀, weight₀ g) ≤
      (N : ℝ) ^ Fintype.card ι * ε := by
    exact raw_const_le_card_pow_mul G U T hU hdim hε hmoment
  have hdiag : ∀ a b : ι, a ≠ b →
      (∑ g ∈ S₀.filter (fun g => g a = g b), weight₀ g) ≤
        (N : ℝ) ^ (Fintype.card ι - 1) * ε := by
    intro a b hab
    exact (Pruning.diagonalRaw_le G hab θ s U T).trans
      (raw_eraseCoord_le G U T hU hdim hε hmoment b)
  exact PartitionConcentration.weightedMean_rawStatistic_le_of_domination
    q S S₀ prescribed weight weight₀
    ((N : ℝ) ^ Fintype.card ι * ε)
    ((N : ℝ) ^ (Fintype.card ι - 1) * ε)
    hq hqsum (fun g hg => (hweight g hg).1)
    (fun g hg => FiniteDefect.defectPower_nonneg G θ g T s)
    hsub (fun g hg => (hweight g hg).2) hraw (by positivity) hdiag

/-! ## Uniform common-neighbour lower bound from a high moment -/

theorem commonNeighbors_card_gt_of_familyMoment
    {N θ s M : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : ι → Finset (Fin N)) (T : Finset (Fin N))
    (hM : 0 < M) (hMθ : M < θ) (hε : 0 ≤ ε)
    (hmoment : FiniteDefect.familyMoment G θ s A T ≤ ε)
    (hsmall : ((FiniteDefect.familyTuples A).card : ℝ) * ε <
      ((θ : ℝ) / M) ^ s)
    (g : ι → Fin N) (hg : g ∈ FiniteDefect.familyTuples A) :
    M < (FiniteDefect.commonNeighbors G g T).card := by
  let m := (FiniteDefect.commonNeighbors G g T).card
  have hraw : HostTools.rawFamilyMoment G θ s A T ≤
      ((FiniteDefect.familyTuples A).card : ℝ) * ε := by
    rw [HostTools.rawFamilyMoment_eq_card_mul_moment]
    exact mul_le_mul_of_nonneg_left hmoment (by positivity)
  have hsingle : FiniteDefect.defectPower G θ g T s ≤
      HostTools.rawFamilyMoment G θ s A T := by
    unfold HostTools.rawFamilyMoment
    exact Finset.single_le_sum
      (fun z hz => FiniteDefect.defectPower_nonneg G θ z T s) hg
  by_contra hnot
  have hmM : m ≤ M := Nat.le_of_not_gt hnot
  have hmθ : m < θ := hmM.trans_lt hMθ
  have hθNat : 0 < θ := by omega
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθNat
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hdefLower : (θ : ℝ) / M ≤ FiniteDefect.defect G θ g T := by
    by_cases hm0 : m = 0
    · have hempty : FiniteDefect.commonNeighbors G g T = ∅ :=
        Finset.card_eq_zero.mp hm0
      rw [FiniteDefect.defect_eq_sentinel_of_empty G hθNat hempty]
      have hdivθ : (θ : ℝ) / M ≤ θ := by
        exact div_le_self hθR.le (by exact_mod_cast hM)
      exact hdivθ.trans (le_mul_of_one_le_right hθR.le (by norm_num))
    · have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
      rw [FiniteDefect.defect_eq_div_of_pos_card_lt G
        (Nat.pos_of_ne_zero hm0) hmθ]
      exact div_le_div_of_nonneg_left hθR.le hmR
        (by exact_mod_cast hmM)
  have hdefPos : 0 < FiniteDefect.defect G θ g T :=
    (div_pos hθR hMR).trans_le hdefLower
  have hpower : ((θ : ℝ) / M) ^ s ≤
      FiniteDefect.defectPower G θ g T s := by
    unfold FiniteDefect.defectPower
    rw [if_neg hdefPos.ne']
    exact pow_le_pow_left₀ (by positivity) hdefLower s
  exact (not_lt_of_ge (hpower.trans (hsingle.trans hraw))) hsmall

/-- An all-direction dimension-`D` moment supplies the uniform common-
neighbour lower bound in every smaller restricted product. -/
theorem commonNeighbors_card_gt_of_all_direction
    {N D θ s M : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (base : ι → Finset (Fin N)) (U T : Finset (Fin N))
    (hN : 1 ≤ N) (hU : U.Nonempty) (hdim : Fintype.card ι ≤ D)
    (hbase : ∀ i, base i ⊆ U)
    (hM : 0 < M) (hMθ : M < θ) (hε : 0 ≤ ε)
    (hmoment : FiniteDefect.moment G θ s (fun _ : Fin D => U) T ≤ ε)
    (hsmall : (N : ℝ) ^ D * ε < ((θ : ℝ) / M) ^ s)
    (g : ι → Fin N) (hg : g ∈ FiniteDefect.familyTuples base) :
    M < (FiniteDefect.commonNeighbors G g T).card := by
  have hmomentι : FiniteDefect.familyMoment G θ s (fun _ : ι => U) T ≤ ε := by
    rw [HostPartition.familyMoment_const_eq_moment_card]
    exact (HostTools.moment_mono_dimension G hU T θ s hdim).trans hmoment
  have hcardNat : (FiniteDefect.familyTuples (fun _ : ι => U)).card ≤
      N ^ Fintype.card ι := by
    rw [FiniteDefect.card_familyTuples]
    simp only [Finset.prod_const, Finset.card_univ]
    exact Nat.pow_le_pow_left (by simpa using Finset.card_le_univ U) _
  have hpowNat : N ^ Fintype.card ι ≤ N ^ D :=
    Nat.pow_le_pow_right hN hdim
  have hcardReal :
      ((FiniteDefect.familyTuples (fun _ : ι => U)).card : ℝ) ≤ (N : ℝ) ^ D := by
    exact_mod_cast hcardNat.trans hpowNat
  have hsmallι :
      ((FiniteDefect.familyTuples (fun _ : ι => U)).card : ℝ) * ε <
        ((θ : ℝ) / M) ^ s :=
    (mul_le_mul_of_nonneg_right hcardReal hε).trans_lt hsmall
  have hgU : g ∈ FiniteDefect.familyTuples (fun _ : ι => U) := by
    rw [FiniteDefect.mem_familyTuples] at hg ⊢
    exact fun i => hbase i (hg i)
  exact commonNeighbors_card_gt_of_familyMoment G (fun _ : ι => U) T
    hM hMθ hε hmomentι hsmallι g hgU

end
end PreparedHost
end Erdos163
