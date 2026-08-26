/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616

/-!
# The sharp balanced-cut averaging step for Claim 6.16

Retaining the light-set cardinality gives the source coefficient ten.
The coarser bound charging all vertices as light would not suffice.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoClaim616SharpCrossing

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoClaim616 Erdos547b.ZhaoStability

theorem card_crossHeavy_ge_of_balanced_cut
    {K : Type*} [Fintype K] [DecidableEq K]
    (R : SimpleGraph K) [DecidableRel R.Adj] (S T : Finset K) (r k : ℕ)
    (hS : S.card ≤ k) (hST : S.card + T.card = 2 * k) (hr : 9 * r ≤ k)
    (hcross : 10 * r * k < (R.interedges S T).card) :
    r ≤ (crossHeavy R S T (9 * r)).card := by
  let H := crossHeavy R S T (9 * r)
  by_contra hnot
  change ¬r ≤ H.card at hnot
  have hHr : H.card ≤ r := by omega
  have hHS : H ⊆ S := crossHeavy_subset R S T (9 * r)
  have hcard := Finset.card_sdiff_add_card_eq_card hHS
  have hsum : (R.interedges S T).card =
      (∑ x ∈ H, degreeInto R x T) + ∑ x ∈ S \ H, degreeInto R x T := by
    rw [← sum_degreeInto_eq_card_interedges]
    have h := Finset.sum_sdiff hHS (f := fun x => degreeInto R x T)
    omega
  have hheavy : (∑ x ∈ H, degreeInto R x T) ≤ H.card * T.card :=
    Finset.sum_le_card_nsmul H (fun x => degreeInto R x T) T.card
      (fun x _ => degreeInto_le_card R x T)
  have hlight : (∑ x ∈ S \ H, degreeInto R x T) ≤ (S \ H).card * (9 * r) := by
    apply Finset.sum_le_card_nsmul
    intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    have hxH := (Finset.mem_sdiff.mp hx).2
    have hlt : ¬9 * r ≤ degreeInto R x T := by
      simpa only [H, crossHeavy, Finset.mem_filter, hxS, true_and] using hxH
    omega
  have hbound : (R.interedges S T).card ≤ H.card * T.card + (S \ H).card * (9 * r) := by omega
  have hSTr : (S.card : ℝ) + T.card = 2 * k := by exact_mod_cast hST
  have hSr : (S.card : ℝ) ≤ k := by exact_mod_cast hS
  have hrr : 9 * (r : ℝ) ≤ k := by exact_mod_cast hr
  have hHrr : (H.card : ℝ) ≤ r := by exact_mod_cast hHr
  have hcardR : ((S \ H).card : ℝ) + H.card = S.card := by exact_mod_cast hcard
  have hboundR : ((R.interedges S T).card : ℝ) ≤
      (H.card : ℝ) * T.card + ((S \ H).card : ℝ) * (9 * (r : ℝ)) := by exact_mod_cast hbound
  have hcrossR : 10 * (r : ℝ) * k < (R.interedges S T).card := by exact_mod_cast hcross
  have hcoef : 0 ≤ (T.card : ℝ) - 9 * r := by linarith only [hSTr, hSr, hrr]
  have hmulH := mul_le_mul_of_nonneg_right hHrr hcoef
  have hmulS := mul_le_mul_of_nonneg_left hSr (show 0 ≤ 8 * (r : ℝ) by positivity)
  nlinarith only [hSTr, hcardR, hboundR, hcrossR, hmulH, hmulS, sq_nonneg (r : ℝ)]

theorem exists_cluster_set_avoiding_of_heavy
    {K : Type*} [Fintype K] [DecidableEq K]
    (R : SimpleGraph K) [DecidableRel R.Adj]
    (L : Finset K) (miss r : ℕ) (C67 : Claim67Certificate R L miss)
    (Min Mout : R.Subgraph) (forbidden : Finset K)
    (hsupport : matchingSupport C67.M = matchingSupport Min ∪ matchingSupport Mout)
    (hV1O : matchingSupport Min ⊆ C67.O)
    (hbudget : miss + forbidden.card ≤ r)
    (hmany : r ≤ (crossHeavy R (matchingSupport Min)
      (Finset.univ \ matchingSupport Min) (9 * r)).card) :
    ∃ C : Finset K, C ⊆ matchingSupport Min ∧ C ⊆ C67.O ∧ C.card = r ∧
      ∀ x ∈ C, 8 * r ≤ degreeInto R x
        ((Finset.univ \ matchingSupport Min) ∩ (matchingSupport Mout \ forbidden)) := by
  obtain ⟨C, hCH, hCcard⟩ := Finset.exists_subset_card_eq hmany
  have hCV1 := hCH.trans (crossHeavy_subset R (matchingSupport Min)
    (Finset.univ \ matchingSupport Min) (9 * r))
  have hCO := hCV1.trans hV1O
  refine ⟨C, hCV1, hCO, hCcard, ?_⟩
  intro x hxC
  have hxdegree : 9 * r ≤ degreeInto R x (Finset.univ \ matchingSupport Min) :=
    (Finset.mem_filter.mp (hCH hxC)).2
  have hmissOut : ((R.neighborFinset x ∩ (Finset.univ \ matchingSupport Min)) \
      matchingSupport Mout).card ≤ miss :=
    card_neighbors_V2_missed_by_out_le R C67.M Min Mout _ x miss hsupport
      (by
        rw [Finset.disjoint_left]
        exact fun _ hy hz => (Finset.mem_sdiff.mp hy).2 hz)
      (C67.neighbors_missed x (hCO hxC))
  apply degreeInto_available_ge R x (Finset.univ \ matchingSupport Min)
    (matchingSupport Mout) forbidden miss forbidden.card (8 * r)
  · omega
  · exact hmissOut
  · exact le_refl _

theorem exists_cluster_set_of_heavy
    {K : Type*} [Fintype K] [DecidableEq K]
    (R : SimpleGraph K) [DecidableRel R.Adj]
    (L : Finset K) (miss r : ℕ) (C67 : Claim67Certificate R L miss)
    (Min Mout Mb : R.Subgraph)
    (hsupport : matchingSupport C67.M = matchingSupport Min ∪ matchingSupport Mout)
    (hV1O : matchingSupport Min ⊆ C67.O)
    (hbudget : miss + (matchingSupport Mb).card ≤ r)
    (hmany : r ≤ (crossHeavy R (matchingSupport Min)
      (Finset.univ \ matchingSupport Min) (9 * r)).card) :
    ∃ C : Finset K, C ⊆ matchingSupport Min ∧ C ⊆ C67.O ∧ C.card = r ∧
      ∀ x ∈ C, 8 * r ≤ degreeInto R x
        ((Finset.univ \ matchingSupport Min) ∩ (matchingSupport Mout \ matchingSupport Mb)) :=
  exists_cluster_set_avoiding_of_heavy R L miss r C67 Min Mout (matchingSupport Mb)
    hsupport hV1O hbudget hmany

end Erdos547b.ZhaoClaim616SharpCrossing

#print axioms Erdos547b.ZhaoClaim616SharpCrossing.card_crossHeavy_ge_of_balanced_cut
#print axioms Erdos547b.ZhaoClaim616SharpCrossing.exists_cluster_set_of_heavy
