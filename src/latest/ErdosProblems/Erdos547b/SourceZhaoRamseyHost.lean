/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceEC2FromHost
import ErdosProblems.Erdos547b.EC1
import ErdosProblems.Erdos547b.StabilityPropertyFull

/-! # Unconditional sufficiently-large tree containment on the Ramsey host -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceZhaoRamseyHost

open Finset SimpleGraph Erdos547b.ZhaoStability
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceClaim61Entry
open Erdos547b.ZhaoSourceNearFullFromHost Erdos547b.ZhaoSourceEC2FromHost
open Erdos547b.ZhaoStabilityPropertyFull Erdos547b.ZhaoSparseAssembly

theorem eventual_tree_containment :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ G : SimpleGraph (Fin (2 * n - 2)),
      n - 1 ≤ #(Finset.univ.filter fun v => n - 1 ≤ G.degree v) →
      ∀ T : SimpleGraph (Fin n), T.IsTree → T.IsContained G := by
  classical
  obtain ⟨c, hc, _hc1, n₁, hdense⟩ := Erdos547b.EC1Scratch.zhaoDenseCutEmbeddingProperty
  let β : ℚ := min c (min sparseCap (1 / 4))
  have hβ : 0 < β := lt_min hc (lt_min sparseCap_pos (by norm_num))
  have hβc : β ≤ c := min_le_left _ _
  have hβcap : β ≤ sparseCap := (min_le_right _ _).trans (min_le_left _ _)
  have hβ1 : β ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨max n₁ (max (largeThreshold + 1) (sourceRamseyThreshold β)), ?_⟩
  intro n hn G hlarge T hT
  have hn₁ : n₁ ≤ n := (le_max_left _ _).trans hn
  have hnSparse : largeThreshold + 1 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnSource : sourceRamseyThreshold β ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  by_cases hEC1 : ZhaoExtremalCaseOne β G
  · exact (hdense n hn₁ G hlarge (extremalCaseOne_mono_parameter hβc hEC1)) n T hT le_rfl
  by_contra hnot
  obtain ⟨W, hW⟩ := exists_source_claim61 hβ hβ1 G hnSource hlarge
  rcases hW with hEC | hQ
  · exact hEC1 hEC
  obtain ⟨Q⟩ := hQ
  have horder : orderThreshold β (Erdos547b.ZhaoDegreeForm.degreeFormBound
      (epsilon β) (requestedClusters β)) ≤ n - 1 := by
    unfold sourceRamseyThreshold at hnSource
    omega
  have hn2 : 2 ≤ n := by
    have hh := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    omega
  obtain ⟨S⟩ := exists_clean_source W hβ hβ1 Q (by omega) horder
  let root : Fin n := ⟨0, by omega⟩
  obtain ⟨P, hroots, hsmall, O, _hminor⟩ :=
    exists_partition_and_output_of_notEC1 hT G W Q S hβ hβ1 horder hlarge hEC1
      (Fintype.card_fin n) hnot root
  have hEC2 := pruned_extremalCaseTwo_of_notEC1 G W Q S hT P O hβ hβ1 horder hlarge hEC1
    (Fintype.card_fin n) hnot hsmall hroots
  have hcontains := containsAllTrees_of_pruned_extremalCaseTwo G β hβ hβcap hnSparse hlarge hEC2
  exact hnot (hcontains n T hT le_rfl)

end Erdos547b.ZhaoSourceZhaoRamseyHost

#print axioms Erdos547b.ZhaoSourceZhaoRamseyHost.eventual_tree_containment
