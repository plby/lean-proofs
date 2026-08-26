/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCleanCrossingAccess

/-!
# Four private actual matching pairs for every crossing cluster

Finite Hall gives a simultaneous injective assignment. The allowed
edges are the literal cleaned access sets, not independent host pairs.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourcePrivateCrossingPairs

open Finset SimpleGraph
open Erdos547b.ZhaoSourceCleanCrossingAccess Erdos547b.ZhaoSourceCrossingClusters
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceActualChunkEmbedding Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full Erdos547b.ZhaoClaim616

theorem exists_injective_slots {C E : Type*} [Fintype C] [DecidableEq C] [DecidableEq E]
    (allowed : C → Finset E) (m : ℕ)
    (hallowed : ∀ c, Fintype.card C * m ≤ (allowed c).card) :
    ∃ f : C × Fin m → E, Function.Injective f ∧ ∀ p, f p ∈ allowed p.1 := by
  let choices : C × Fin m → Finset E := fun p => allowed p.1
  apply (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp
  intro F
  by_cases hF : F = ∅
  · simp [hF]
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    calc
      F.card ≤ Fintype.card (C × Fin m) := Finset.card_le_univ _
      _ = Fintype.card C * m := by simp only [Fintype.card_prod, Fintype.card_fin]
      _ ≤ (choices p).card := hallowed p.1
      _ ≤ (F.biUnion choices).card := Finset.card_le_card (Finset.subset_biUnion_of_mem choices hp)

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

theorem exists_private_pairs
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (hcross : (rho α : ℝ) * (paddedHalf (Index W) : ℝ) ^ 2 <
      ((padGraph (reduced W)).interedges O.D.V1 O.D.V2).card) :
    ∃ C : Finset (EvenPadding (Index W)), C ⊆ O.D.V1 ∧ C ⊆ Q.claim67.O ∧
      C.card = crossingScale W ∧
      ∃ f : {x // x ∈ C} × Fin 4 → MatchingEdge Q.claim67.M,
        Function.Injective f ∧ ∀ p,
          f p ∈ matchingAccessEdges (padGraph (reduced W)) (availableEdges W Q S O)
            (edgeVertex W Q) p.1.1 (availableVertices W Q S O) := by
  obtain ⟨C, hCV1, hCO, hCcard, haccess⟩ := exists_cleanCrossingClusters W Q S O
    hα hα1 hhost horder hcross
  refine ⟨C, hCV1, hCO, hCcard, ?_⟩
  apply exists_injective_slots
    (fun x : {x // x ∈ C} => matchingAccessEdges (padGraph (reduced W))
      (availableEdges W Q S O) (edgeVertex W Q) x.1 (availableVertices W Q S O)) 4
  intro x
  simpa only [Fintype.card_coe, hCcard, Nat.mul_comm] using (haccess x.1 x.2).2

end Erdos547b.ZhaoSourcePrivateCrossingPairs

#print axioms Erdos547b.ZhaoSourcePrivateCrossingPairs.exists_injective_slots
#print axioms Erdos547b.ZhaoSourcePrivateCrossingPairs.exists_private_pairs
