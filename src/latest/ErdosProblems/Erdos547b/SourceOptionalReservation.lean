/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceSmallReservation

/-!
# The actual optional positive B-reservation

Filtering zero-contribution edges preserves its precise capacity, while
retaining the actual-volume cardinal allowance and root avoidance.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceOptionalReservation

open Finset SimpleGraph
open Erdos547b.ZhaoSourceSmallReservation Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoLemma611Full

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)

structure ReservedMatching (fb : ℝ) where
  edges : Finset (MatchingEdge Q.claim67.M)
  subset_away : edges ⊆ awayEdges W Q
  count_bound : (edges.card : ℝ) ≤ 2 * (fourthRoot α : ℝ) * (awayEdges W Q).card
  weight_bound : ∀ u : Fin 2, (∑ e ∈ edges, sideWeight W Q S u e) ≤ 4 * (fourthRoot α : ℝ) * q
  small_lower : fb < (fourthRoot α : ℝ) * q →
    fb + 3 * (gamma α : ℝ) * q ≤ ∑ e ∈ edges, sideWeight W Q S 1 e
  small_upper : fb < (fourthRoot α : ℝ) * q →
    (∑ e ∈ edges, sideWeight W Q S 1 e) < fb + 3 * (gamma α : ℝ) * q + 2 * W.clusterSize
  positive : ∀ e ∈ edges, 0 < sideWeight W Q S 1 e
  large_empty : ¬fb < (fourthRoot α : ℝ) * q → edges = ∅

theorem exists_reservedMatching (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) (fb : ℝ) (hfb : 0 ≤ fb) :
    Nonempty (ReservedMatching W Q S fb) := by
  have ht : (0 : ℝ) ≤ fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1.le
  by_cases hsmall : fb < (fourthRoot α : ℝ) * q
  · obtain ⟨Eb, hEb, hlo, hup, hcount, _, hweight⟩ :=
      exists_smallReservation W Q S hα hα1 hhost horder 1 fb hfb hsmall.le
    let F := Eb.filter fun e => 0 < sideWeight W Q S 1 e
    have hsub : F ⊆ Eb := Finset.filter_subset _ _
    have heq : (∑ e ∈ F, sideWeight W Q S 1 e) = ∑ e ∈ Eb, sideWeight W Q S 1 e := by
      apply Finset.sum_subset hsub
      intro e he hn
      have hnot : ¬0 < sideWeight W Q S 1 e := fun h => hn (Finset.mem_filter.mpr ⟨he, h⟩)
      exact le_antisymm (le_of_not_gt hnot) (sideWeight_nonneg W Q S 1 e)
    refine ⟨{
      edges := F
      subset_away := hsub.trans hEb
      count_bound := ?_
      weight_bound := ?_
      small_lower := fun _ => heq.symm ▸ hlo
      small_upper := fun _ => heq.symm ▸ hup
      positive := fun _ he => (Finset.mem_filter.mp he).2
      large_empty := fun h => (h hsmall).elim }⟩
    · have hcard : (F.card : ℝ) ≤ Eb.card := by exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans hcount
    · intro u
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun e _ _ => sideWeight_nonneg W Q S u e)).trans (hweight u)
  · exact ⟨{
      edges := ∅
      subset_away := Finset.empty_subset _
      count_bound := by simp only [Finset.card_empty, Nat.cast_zero]; positivity
      weight_bound := by intro u; simp only [Finset.sum_empty]; positivity
      small_lower := fun h => (hsmall h).elim
      small_upper := fun h => (hsmall h).elim
      positive := by simp
      large_empty := fun _ => rfl }⟩

end Erdos547b.ZhaoSourceOptionalReservation

#print axioms Erdos547b.ZhaoSourceOptionalReservation.exists_reservedMatching
