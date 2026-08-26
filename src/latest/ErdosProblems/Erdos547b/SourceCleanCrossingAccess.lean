/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCrossingClusters

/-!
# Root-avoiding available matching edges for the three-layer embedding

The selected intermediate clusters have at least four times the rounded
scale distinct available matching edges. These are actual original
matching edges outside both allocated families and both root clusters.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceCleanCrossingAccess

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoSourceCrossingClusters Erdos547b.ZhaoSourceNearFullMatching
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceExceptionalRowBounds
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoStability Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim616 Erdos547b.ZhaoClaim616SharpCrossing

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

def rootIncidentVertices : Finset (EvenPadding (Index W)) :=
  (distinguishedIncidentEdges Q.claim67.M (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)).biUnion
    (fun e => {edgeVertex W Q e 0, edgeVertex W Q e 1})

def forbiddenVertices := matchingSupport O.D.Mb ∪ rootIncidentVertices W Q
def availableVertices := O.D.V2 ∩ (matchingSupport O.D.Mout \ forbiddenVertices W Q S O)
def availableEdges := ((allMatchingEdges Q.claim67.M \ O.D.minEdges) \ O.D.mbEdges) ∩ awayEdges W Q

theorem rootIncidentVertices_card_le : (rootIncidentVertices W Q).card ≤ 4 := by
  have hi := distinguishedIncidentEdges_card_le_two Q.claim67.M Q.claim67.isMatching
    (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B)
  have hcard := Finset.card_biUnion_le_card_mul
    (distinguishedIncidentEdges Q.claim67.M (padFinset (large W)) (Sum.inl Q.A) (Sum.inl Q.B))
    (fun e => {edgeVertex W Q e 0, edgeVertex W Q e 1}) 2
    (fun e _ => by
      simpa only [Finset.card_singleton] using
        Finset.card_insert_le (edgeVertex W Q e 0) {edgeVertex W Q e 1})
  change (rootIncidentVertices W Q).card ≤ _ at hcard
  omega

theorem forbiddenVertices_card_le :
    (forbiddenVertices W Q S O).card ≤ (matchingSupport O.D.Mb).card + 4 :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (rootIncidentVertices_card_le W Q) _)

theorem available_covered : ∀ v ∈ availableVertices W Q S O,
    ∃ e ∈ availableEdges W Q S O, v = edgeVertex W Q e 0 ∨ v = edgeVertex W Q e 1 := by
  intro v hv
  have hvOut := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).1
  have hvNot := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).2
  obtain ⟨e, he, hends⟩ := (mem_matchingSupport O.D.Mout v).mp hvOut
  change e ∈ allMatchingEdges Q.claim67.M \ O.D.minEdges at he
  change v = edgeVertex W Q e 0 ∨ v = edgeVertex W Q e 1 at hends
  have hnotMb : e ∉ O.D.mbEdges := by
    intro heMb
    apply hvNot
    apply Finset.mem_union_left
    apply (mem_matchingSupport O.D.Mb v).mpr
    exact ⟨e, heMb, hends⟩
  have hnotIncident : e ∉ distinguishedIncidentEdges Q.claim67.M (padFinset (large W))
      (Sum.inl Q.A) (Sum.inl Q.B) := by
    intro heI
    apply hvNot
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨e, heI, ?_⟩
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hends
  exact ⟨e, Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨he, hnotMb⟩,
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp he).1, hnotIncident⟩⟩, hends⟩

theorem availableEdges_subset_away : availableEdges W Q S O ⊆ awayEdges W Q := Finset.inter_subset_right

theorem exists_cleanCrossingClusters
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    ∃ C : Finset (EvenPadding (Index W)), C ⊆ O.D.V1 ∧ C ⊆ Q.claim67.O ∧
      C.card = crossingScale W ∧
      ∀ x ∈ C,
        8 * crossingScale W ≤ degreeInto (padGraph (reduced W)) x (availableVertices W Q S O) ∧
        4 * crossingScale W ≤ (matchingAccessEdges (padGraph (reduced W))
          (availableEdges W Q S O) (edgeVertex W Q) x (availableVertices W Q S O)).card := by
  obtain ⟨_, _, hscale, h9, hbudget⟩ := scale_bounds W Q S O hα hα1 hhost horder
  have hST : O.D.V1.card + O.D.V2.card = 2 * paddedHalf (Index W) := by
    rw [O.D.V2_card, card_evenPadding]
    change O.D.V1.card + (2 * paddedHalf (Index W) - O.D.V1.card) = 2 * paddedHalf (Index W)
    have h := O.D.V1_card_upper
    omega
  have hcrossNat : 10 * crossingScale W * paddedHalf (Index W) <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card := by
    have hscaled := mul_le_mul_of_nonneg_right hscale
      (Nat.cast_nonneg (paddedHalf (Index W)) : (0 : ℝ) ≤ paddedHalf (Index W))
    have hR : 10 * (crossingScale W : ℝ) * paddedHalf (Index W) <
        ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card := by nlinarith only [hscaled, hcross]
    exact_mod_cast hR
  have hheavy := card_crossHeavy_ge_of_balanced_cut (padGraph (reduced W)) O.D.V1 O.D.V2
    (crossingScale W) (paddedHalf (Index W)) O.D.V1_card_upper hST h9 hcrossNat
  have hforbid := forbiddenVertices_card_le W Q S O
  obtain ⟨C, hCV1, hCO, hCcard, hdegree⟩ :=
    exists_cluster_set_avoiding_of_heavy (padGraph (reduced W)) (padFinset (large W))
      (missed W) (crossingScale W) Q.claim67 O.D.Min O.D.Mout (forbiddenVertices W Q S O)
      O.D.support_union O.D.V1_subset_O (by omega) hheavy
  refine ⟨C, hCV1, hCO, hCcard, ?_⟩
  intro x hx
  have hd : 8 * crossingScale W ≤ degreeInto (padGraph (reduced W)) x (availableVertices W Q S O) := hdegree x hx
  exact ⟨hd, four_mul_le_card_matchingAccessEdges (padGraph (reduced W))
    (availableEdges W Q S O) (edgeVertex W Q) x (availableVertices W Q S O)
    (crossingScale W) (available_covered W Q S O) hd⟩

end Erdos547b.ZhaoSourceCleanCrossingAccess

#print axioms Erdos547b.ZhaoSourceCleanCrossingAccess.available_covered
#print axioms Erdos547b.ZhaoSourceCleanCrossingAccess.exists_cleanCrossingClusters
