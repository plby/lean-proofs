/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceNearFullFilters
import ErdosProblems.Erdos547b.SourceOptionalReservation

/-!
# Actual near-full source matching with its optional B-reservation

The original graph matching is capped only after all literal source
filters and the two distinguished clusters have been removed. Its
quantitative support and row bounds use the same padded finite target.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceNearFullMatching

open Finset SimpleGraph
open Erdos547b.ZhaoSourceNearFullFilters Erdos547b.ZhaoSourceNearFullNumerics
open Erdos547b.ZhaoSourceOptionalReservation Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceLargeExceptionalForcing Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoEvenReducedPadding

theorem capped_weight_gt {E : Type*} [DecidableEq E] (F : Finset E) (w : E → ℝ)
    (cap : ℕ) (target bound : ℝ) (htarget : 0 ≤ target)
    (hfull : target < ∑ e ∈ F, w e) (hcap : target < (cap : ℝ) * bound)
    (hper : ∀ e ∈ F, bound < w e) :
    target < ∑ e ∈ cappedSubfamily F cap, w e := by
  by_cases hsmall : F.card ≤ cap
  · simpa only [cappedSubfamily, dif_pos hsmall] using hfull
  · have hc : (cappedSubfamily F cap).card = cap := by
      rw [card_cappedSubfamily, Nat.min_eq_right (by omega)]
    have hpos : 0 < cap := by
      by_contra h
      have hz : cap = 0 := by omega
      subst cap
      norm_num at hcap
      linarith only [hcap, htarget]
    have hn : (cappedSubfamily F cap).Nonempty := Finset.card_pos.mp (by rw [hc]; exact hpos)
    calc
      target < (cap : ℝ) * bound := hcap
      _ = ∑ _e ∈ cappedSubfamily F cap, bound := by simp [hc]
      _ < ∑ e ∈ cappedSubfamily F cap, w e :=
        Finset.sum_lt_sum_of_nonempty hn (fun e he => hper e (cappedSubfamily_subset F cap he))

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

def lowerCount : ℕ := ⌈(1 - 8 * (eta α : ℝ)) * paddedHalf (Index W)⌉₊
def reserveEdgeCap : ℕ := ⌊2 * (fourthRoot α : ℝ) * paddedHalf (Index W)⌋₊

abbrev Decomposition := MatchingDecomposition (padFinset (large W)) Q.claim67.O
  (missed W) Q.claim67 (lowerCount W) (paddedHalf (Index W))
  (2 * paddedHalf (Index W) - lowerCount W) (2 * reserveEdgeCap W)
  (fun F => ∑ e ∈ F, sideWeight W Q S 0 e)

structure Output (fb : ℝ) where
  reserved : ReservedMatching W Q S fb
  D : Decomposition W Q S
  min_subset : D.minEdges ⊆ cleanAway W Q S reserved.edges
  reserved_eq : D.mbEdges = reserved.edges
  target_eq : D.targetA = targetA W

theorem lowerCount_le (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    lowerCount W ≤ paddedHalf (Index W) := by
  apply Nat.ceil_le.mpr
  have he := (parameter_bounds hα hα1).1
  have hk : (0 : ℝ) ≤ paddedHalf (Index W) := Nat.cast_nonneg _
  nlinarith only [mul_nonneg he.le hk]

theorem exists_output (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q)
    (hu : ((unbalancedAway W Q S 0).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W))
    (hx : ((nonextremeAway W Q S 0).card : ℝ) < (eta α : ℝ) * paddedHalf (Index W))
    (fb : ℝ) (hfb : 0 ≤ fb) : Nonempty (Output W Q S fb) := by
  obtain ⟨B⟩ := exists_reservedMatching W Q S hα hα1 hhost horder fb hfb
  let F := cleanAway W Q S B.edges
  let E := cappedSubfamily F (paddedHalf (Index W) / 2)
  have hEF : E ⊆ F := cappedSubfamily_subset _ _
  have hEbAll := B.subset_away.trans (edgesAwayFromDistinguished_subset _ _ _ _)
  obtain ⟨htarget, _, hcap⟩ := actual_matching_gates W hα hα1 hhost horder
  have he := (parameter_bounds hα hα1).1
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hper : ∀ e ∈ F, (W.clusterSize : ℝ) * (2 - 3 * (eta α : ℝ)) < sideWeight W Q S 0 e := by
    intro e heF
    have hd := sourceCleanEdges_density Q.claim67.M (padFinset (large W)) Q.claim67.O
      (rootDensity W S) (Sum.inl Q.A) (eta α : ℝ) he B.edges (Finset.mem_inter.mp heF).1
    exact mul_lt_mul_of_pos_left hd.2.2 hN
  have hweight : targetA W < ∑ e ∈ E, sideWeight W Q S 0 e :=
    capped_weight_gt F (sideWeight W Q S 0) (paddedHalf (Index W) / 2) (targetA W)
      (W.clusterSize * (2 - 3 * (eta α : ℝ))) htarget
      (cleanAway_weight_gt W Q S hα hα1 hhost horder hu hx B.edges hEbAll B.count_bound)
      hcap hper
  have hnonempty : E.Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hz, Finset.sum_empty] at hweight
    linarith only [hweight, htarget]
  have hcountUpper : 2 * E.card ≤ paddedHalf (Index W) := by
    have hc : E.card ≤ paddedHalf (Index W) / 2 := (card_cappedSubfamily _ _).trans_le (min_le_right _ _)
    omega
  have hcountLower : lowerCount W ≤ 2 * E.card := by
    apply Nat.ceil_le.mpr
    have hupper := sideWeight_sum_le W Q S 0 E
    have hcoef : 0 ≤ 1 - 8 * (eta α : ℝ) := by
      linarith only [(parameter_bounds hα hα1).2.1]
    have htargetK := mul_le_mul_of_nonneg_left
      (le_max_right (q : ℝ) ((paddedHalf (Index W) : ℝ) * W.clusterSize)) hcoef
    change (1 - 8 * (eta α : ℝ)) * ((paddedHalf (Index W) : ℝ) * W.clusterSize) ≤ targetA W at htargetK
    have hreal : (1 - 8 * (eta α : ℝ)) * paddedHalf (Index W) < 2 * (E.card : ℝ) := by
      nlinarith only [hupper, hweight, htargetK, hN]
    exact_mod_cast hreal.le
  have hreserve : B.edges.card ≤ reserveEdgeCap W := by
    apply Nat.le_floor
    have hk : (awayEdges W Q).card ≤ paddedHalf (Index W) :=
      (Finset.card_le_card (edgesAwayFromDistinguished_subset _ _ _ _)).trans
        (allMatchingEdges_card_le_paddedHalf Q.claim67.M Q.claim67.isMatching (padFinset (large W)))
    have hkR : ((awayEdges W Q).card : ℝ) ≤ paddedHalf (Index W) := by exact_mod_cast hk
    exact B.count_bound.trans (mul_le_mul_of_nonneg_left hkR
      (by exact_mod_cast mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) (parameter_pos hα).2.2.2.1.le))
  have hdisj : Disjoint E B.edges := Finset.disjoint_of_subset_left
    (hEF.trans Finset.inter_subset_left)
    (sourceCleanEdges_disjoint_reserved Q.claim67.M (padFinset (large W)) Q.claim67.O
      (rootDensity W S) (Sum.inl Q.A) (eta α : ℝ) B.edges)
  let D : Decomposition W Q S := {
    minEdges := E
    mbEdges := B.edges
    min_nonempty := hnonempty
    min_endpoint_O := by
      intro e heE c
      have hc := (Finset.mem_filter.mp (Finset.mem_inter.mp (hEF heE)).1).2
      fin_cases c
      · exact hc.1
      · exact hc.2
    min_card_lower := hcountLower
    min_card_upper := hcountUpper
    complement_card_upper := by
      rw [card_evenPadding]
      change 2 * paddedHalf (Index W) - 2 * E.card ≤ 2 * paddedHalf (Index W) - lowerCount W
      omega
    targetA := targetA W
    degreeA_target_lower := hweight
    degreeA_lower := htarget.trans_lt hweight
    mb_subset := by
      intro e heB
      exact Finset.mem_sdiff.mpr ⟨hEbAll heB, fun heE => Finset.disjoint_left.mp hdisj heE heB⟩
    mb_card := Nat.mul_le_mul_left 2 hreserve }
  exact ⟨⟨B, D, hEF, rfl, rfl⟩⟩

theorem Output.degreeA_order {fb : ℝ} (O : Output W Q S fb)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    (1 - 8 * (eta α : ℝ)) * q < ∑ e ∈ O.D.minEdges, sideWeight W Q S 0 e := by
  have hc : 0 ≤ 1 - 8 * (eta α : ℝ) := by linarith only [(parameter_bounds hα hα1).2.1]
  have h := O.D.degreeA_target_lower
  rw [O.target_eq] at h
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _) hc).trans_lt h

theorem Output.min_subset_away {fb : ℝ} (O : Output W Q S fb) :
    O.D.minEdges ⊆ awayEdges W Q := O.min_subset.trans Finset.inter_subset_right

theorem Output.min_density {fb : ℝ} (O : Output W Q S fb)
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) {e : MatchingEdge Q.claim67.M} (he : e ∈ O.D.minEdges) :
    1 - 2 * (eta α : ℝ) < sideDensity W Q S 0 e 0 ∧
      1 - 2 * (eta α : ℝ) < sideDensity W Q S 0 e 1 := by
  have h := sourceCleanEdges_density Q.claim67.M (padFinset (large W)) Q.claim67.O
    (rootDensity W S) (Sum.inl Q.A) (eta α : ℝ) (parameter_bounds hα hα1).1
    O.reserved.edges (Finset.mem_inter.mp (O.min_subset he)).1
  exact ⟨h.1, h.2.1⟩

end Erdos547b.ZhaoSourceNearFullMatching

#print axioms Erdos547b.ZhaoSourceNearFullMatching.capped_weight_gt
#print axioms Erdos547b.ZhaoSourceNearFullMatching.exists_output
#print axioms Erdos547b.ZhaoSourceNearFullMatching.Output.degreeA_order
#print axioms Erdos547b.ZhaoSourceNearFullMatching.Output.min_density
