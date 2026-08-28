import ErdosProblems.Erdos577.WeightedThirteenMissedTables
import ErdosProblems.Erdos577.MultiScores

/-! Four common-neighbor exchanges, each leaving a triangle and two complete blocks. -/

namespace Erdos577.WeightedThirteen.ThirdModel.CommonTable

open Finset

def commonIndex (tag : Fin 4) : Fin 16 := ![12, 12, 14, 14] tag

def newIndex (tag : Fin 4) : Fin 16 := ![9, 10, 9, 10] tag

def missedTag (tag : Fin 4) : Fin 4 := ![0, 2, 0, 2] tag

def firstBlock (tag : Fin 4) : Finset (Fin 16) := {commonIndex tag, 0, 1, newIndex tag}

abbrev secondBlock (second : Bool) : Finset (Fin 16) := MissedTable.secondBlock second 0

abbrev thirdBlock (second : Bool) (tag : Fin 4) : Finset (Fin 16) :=
  MissedTable.firstBlock second (missedTag tag)

def triangle (second : Bool) (tag : Fin 4) : Finset (Fin 16) :=
  if tag < 2 then {low second, 13, 14} else {low second, 13, 12}

def remainder (second : Bool) (tag : Fin 4) : Finset (Fin 16) := insert 15 (triangle second tag)

lemma remainder_card (second : Bool) (tag : Fin 4) : (remainder second tag).card = 4 := by
  cases second <;> fin_cases tag <;> decide +kernel

lemma remainder_triangle (second : Bool) (tag : Fin 4) :
    TriangleIn (graph second) (remainder second tag) := by
  refine ⟨triangle second tag, ?_, ?_⟩
  · exact subset_insert _ _
  · cases second <;> fin_cases tag <;> decide +kernel

lemma first_second_disjoint (second : Bool) (tag : Fin 4) :
    Disjoint (firstBlock tag) (secondBlock second) := by
  cases second <;> fin_cases tag <;> decide +kernel

lemma third_disjoint (second : Bool) (tag : Fin 4) :
    Disjoint (firstBlock tag ∪ secondBlock second) (thirdBlock second tag) := by
  cases second <;> fin_cases tag <;> decide +kernel

lemma complement (second : Bool) (tag : Fin 4) :
    univ \ ((firstBlock tag ∪ secondBlock second) ∪ thirdBlock second tag) =
      remainder second tag := by
  cases second <;> fin_cases tag <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {second : Bool}

lemma first_quad (f : (graph second).Copy G) (tag : Fin 4)
    (hx : G.Adj (f (commonIndex tag)) (f 0))
    (hv : G.Adj (f (commonIndex tag)) (f (newIndex tag))) :
    QuadOn G ((firstBlock tag).image f) := by
  simp only [firstBlock, image_insert, image_singleton]
  apply QuadOn.of_vertices
    (fun he ↦ (by fin_cases tag <;> decide : commonIndex tag ≠ 1) (f.injective he))
    (fun he ↦ (by fin_cases tag <;> decide : (0 : Fin 16) ≠ newIndex tag) (f.injective he))
  · exact hx
  · exact f.toHom.map_rel' (by cases second <;> decide +kernel : (graph second).Adj 0 1)
  · exact f.toHom.map_rel'
      (by cases second <;> fin_cases tag <;> decide +kernel : (graph second).Adj 1 (newIndex tag))
  · exact hv.symm

def parts (f : (graph second).Copy G) (tag : Fin 4)
    (hx : G.Adj (f (commonIndex tag)) (f 0))
    (hv : G.Adj (f (commonIndex tag)) (f (newIndex tag))) :
    BlockPartition G (((firstBlock tag).image f ∪ (secondBlock second).image f) ∪
      (thirdBlock second tag).image f) :=
  ((BlockPartition.single (first_quad f tag hx hv)).union
    (BlockPartition.single ((MissedTable.second_quad second 0).image f))
    ((disjoint_image f.injective).mpr (first_second_disjoint second tag))).union
    (BlockPartition.single ((MissedTable.first_quad second (missedTag tag)).image f)) (by
      rw [← image_union]
      exact (disjoint_image (show Function.Injective (f : Fin 16 → V) from f.injective)).mpr
        (third_disjoint second tag))

lemma covered_subset (f : (graph second).Copy G) (tag : Fin 4) :
    ((firstBlock tag).image f ∪ (secondBlock second).image f) ∪
      (thirdBlock second tag).image f ⊆ univ.image f := by
  rw [← image_union, ← image_union]
  exact image_subset_image (subset_univ _)

lemma remainder_image (f : (graph second).Copy G) (tag : Fin 4) :
    (remainder second tag).image f = univ.image f \
      (((firstBlock tag).image f ∪ (secondBlock second).image f) ∪
        (thirdBlock second tag).image f) := by
  have hinj : Function.Injective (f : Fin 16 → V) := f.injective
  rw [← image_union, ← image_union, ← image_sdiff _ _ hinj, complement]

lemma remainder_image_card (f : (graph second).Copy G) (tag : Fin 4) :
    ((remainder second tag).image f).card = 4 := by
  have hinj : Function.Injective (f : Fin 16 → V) := f.injective
  rw [card_image_of_injective _ hinj, remainder_card]

variable [DecidableRel G.Adj]

lemma edges_ge_sixteen (f : (graph second).Copy G) (tag : Fin 4)
    (hx : G.Adj (f (commonIndex tag)) (f 0))
    (hv : G.Adj (f (commonIndex tag)) (f (newIndex tag))) :
    16 ≤ (parts f tag hx hv).weightSum (edgeCount G) := by
  have hfour := (first_quad f tag hx hv).four_le_edgeCount
  unfold parts
  rw [BlockPartition.weightSum_union, BlockPartition.weightSum_union]
  simp only [BlockPartition.weightSum_single,
    MissedTable.first_image_score, MissedTable.second_image_score]
  omega

lemma complete_ge_two (f : (graph second).Copy G) (tag : Fin 4)
    (hx : G.Adj (f (commonIndex tag)) (f 0))
    (hv : G.Adj (f (commonIndex tag)) (f (newIndex tag))) :
    2 ≤ (parts f tag hx hv).weightSum (fun s ↦ if edgeCount G s = 6 then 1 else 0) := by
  unfold parts
  rw [BlockPartition.weightSum_union, BlockPartition.weightSum_union]
  simp only [BlockPartition.weightSum_single,
    MissedTable.first_image_score, MissedTable.second_image_score, ↓reduceIte]
  omega

end Erdos577.WeightedThirteen.ThirdModel.CommonTable
