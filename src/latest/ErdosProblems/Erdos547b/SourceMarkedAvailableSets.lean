/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedTripleEmbedding
import ErdosProblems.Erdos547b.MarkedTripleLoads
import ErdosProblems.Erdos547b.SourceParentCleanup

/-!
# Actual available sets for an occupied marked-branch extension

The intermediate loss is charged only to occupied vertices of that
cluster. The pair loss is charged only to the four private pairs.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedAvailableSets

open Finset SimpleGraph
open Erdos547b.ZhaoSourceMarkedTripleEmbedding Erdos547b.ZhaoMarkedTripleLoads
open Erdos547b.ZhaoSourceParentCleanup Erdos547b.ZhaoSourceEmbeddingHost
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm Erdos547b.ZhaoEvenReducedPadding

theorem filtered_available_card_bound {V : Type*} [DecidableEq V]
    (C used bad : Finset V) (p : V → Prop) [DecidablePred p] :
    (C.filter p).card ≤ ((C.filter p) \ (used ∪ bad)).card + (used ∩ C).card + bad.card := by
  have hsub : C.filter p ⊆ ((C.filter p) \ (used ∪ bad)) ∪ (used ∩ C) ∪ bad := by
    intro v hv
    by_cases hu : v ∈ used
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_inter.mpr ⟨hu, (Finset.mem_filter.mp hv).1⟩))
    by_cases hb : v ∈ bad
    · exact Finset.mem_union_right _ hb
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨hv, by simpa only [Finset.mem_union, not_or] using And.intro hu hb⟩))
  have hcard := Finset.card_le_card hsub
  have hfirst := Finset.card_union_le ((C.filter p) \ (used ∪ bad)) (used ∩ C)
  have hsecond := Finset.card_union_le (((C.filter p) \ (used ∪ bad)) ∪ (used ∩ C)) bad
  omega

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

abbrev whole (C : Index W) := clusterVertices (assignment W) C

theorem whole_card (C : Index W) : (whole W C).card = W.clusterSize := by
  change (clusterVertices (partitionAssignment W.exceptional W.partition) C).card = W.clusterSize
  rw [clusterVertices_partitionAssignment]
  exact W.equal_clusters C.1 C.2

def intermediateAvailable (C : Index W) (used : Finset (Fin hostN)) (z : Fin hostN) :=
  ((whole W C).filter ((embeddingHost W).Adj z)) \ (used ∪ badToward W Q (Sum.inl C) 0)

theorem intermediateAvailable_card_ge (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (C : Index W) (used : Finset (Fin hostN)) (z : Fin hostN)
    (hparent : (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
      (((whole W C).filter ((embeddingHost W).Adj z)).card : ℝ))
    (hused : ((used ∩ whole W C).card : ℝ) ≤
      (1 - 2 * (eta α : ℝ) - 3 * (gamma α : ℝ)) * W.clusterSize) :
    (gamma α : ℝ) * W.clusterSize ≤ (intermediateAvailable W Q C used z).card := by
  have hbad := card_badToward_le W Q hα hα1 (Sum.inl C) 0
  change ((badToward W Q (Sum.inl C) 0).card : ℝ) ≤ (epsilon α : ℝ) * (whole W C).card at hbad
  rw [whole_card] at hbad
  have hbound := filtered_available_card_bound (whole W C) used (badToward W Q (Sum.inl C) 0)
    ((embeddingHost W).Adj z)
  have hboundR : (((whole W C).filter ((embeddingHost W).Adj z)).card : ℝ) ≤
      (intermediateAvailable W Q C used z).card + (used ∩ whole W C).card +
        (badToward W Q (Sum.inl C) 0).card := by exact_mod_cast hbound
  have he := (parameter_margin hα hα1 W.clusterSize).1.le
  have heN := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  linarith only [hparent, hused, hbad, hboundR, heN]

def privatePairUnion (X Y : Fin 4 → Index W) : Finset (Fin hostN) :=
  Finset.univ.biUnion fun i => whole W (X i) ∪ whole W (Y i)

theorem exists_available_private_pair (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (X Y : Fin 4 → Index W) (used : Finset (Fin hostN))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (whole W (X i) ∪ whole W (Y i))
      (whole W (X j) ∪ whole W (Y j)))
    (hused : (used ∩ privatePairUnion W X Y).card ≤ 3 * W.clusterSize) :
    ∃ i : Fin 4,
      (gamma α : ℝ) * W.clusterSize ≤ ((whole W (X i) \ used).card : ℝ) ∧
      (gamma α : ℝ) * W.clusterSize ≤ ((whole W (Y i) \ used).card : ℝ) := by
  let sides : Fin 4 → Fin 2 → Finset (Fin hostN) := fun i c => if c = 0 then whole W (X i) else whole W (Y i)
  have hγQ : 4 * gamma α ≤ 1 := by
    have hu := parameter_upper_bounds hα hα1
    linarith only [hu.2.2.2.2.2.1, (reservoir_cleanup_bounds hα hα1).2.2.2.2.2]
  have hγR : (4 : ℝ) * (gamma α : ℝ) ≤ 1 := by exact_mod_cast hγQ
  have hcard : ∀ i c, (sides i c).card = W.clusterSize := by
    intro i c
    dsimp only [sides]
    split_ifs <;> exact whole_card W _
  have hdisj : ∀ i j, i ≠ j → Disjoint (sides i 0 ∪ sides i 1) (sides j 0 ∪ sides j 1) := by
    intro i j hij
    simpa only [sides, if_pos rfl, if_neg (show (1 : Fin 2) ≠ 0 by decide)] using hdisjoint i j hij
  obtain ⟨i, hi⟩ := exists_private_pair_with_two_large_sides sides (used ∩ privatePairUnion W X Y)
    W.clusterSize (gamma α : ℝ) (by linarith only [hγR]) hcard hdisj hused
  have hsub (j : Fin 4) (c : Fin 2) : sides j c ⊆ privatePairUnion W X Y := by
    intro v hv
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ _, ?_⟩
    dsimp only [sides] at hv
    split_ifs at hv
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ hv
  have heq (c : Fin 2) : sides i c \ (used ∩ privatePairUnion W X Y) = sides i c \ used := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hv, hn⟩
      exact ⟨hv, fun hu => hn ⟨hu, hsub i c hv⟩⟩
    · rintro ⟨hv, hn⟩
      exact ⟨hv, fun h => hn h.1⟩
  have h0 := hi 0
  have h1 := hi 1
  rw [heq] at h0 h1
  exact ⟨i, by simpa only [sides, if_pos rfl] using h0,
    by simpa only [sides, if_neg (show (1 : Fin 2) ≠ 0 by decide)] using h1⟩

end Erdos547b.ZhaoSourceMarkedAvailableSets

#print axioms Erdos547b.ZhaoSourceMarkedAvailableSets.filtered_available_card_bound
#print axioms Erdos547b.ZhaoSourceMarkedAvailableSets.intermediateAvailable_card_ge
#print axioms Erdos547b.ZhaoSourceMarkedAvailableSets.exists_available_private_pair
