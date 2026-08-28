import ErdosProblems.Erdos577.WeightedThirteenThirdModel
import ErdosProblems.Erdos577.MatchingData

/-! The four explicit matching remainders and their three complementary blocks. -/

namespace Erdos577.WeightedThirteen.ThirdModel.MissedTable

open Finset

def firstBlock (second : Bool) (tag : Fin 4) : Finset (Fin 16) :=
  if tag = 3 then {8, 9, 10, 11}
  else if tag = 2 then {own second, 8, 9, 11} else {own second, 8, 10, 11}

def secondBlock (second : Bool) (tag : Fin 4) : Finset (Fin 16) :=
  if tag = 3 then {2, 4, 6, 3} else {own (!second), 4, low (!second), 6}

def thirdBlock (second : Bool) : Finset (Fin 16) := {low second, 12, 13, 14}

def matchingVertices (second : Bool) (tag : Fin 4) : Fin 4 → Fin 16 :=
  ![![15, 0, 1, 9], ![0, 1, 9, 15], ![0, 1, 10, 15], ![0, 1, 15, low (!second)]] tag

def eventIndex (second : Bool) (tag : Fin 4) : Fin 16 := ![0, 9, 10, low (!second)] tag

lemma matching_injective (second : Bool) (tag : Fin 4) :
    Function.Injective (matchingVertices second tag) := by
  cases second <;> fin_cases tag <;> decide +kernel

def matchingEmbedding (second : Bool) (tag : Fin 4) : Fin 4 ↪ Fin 16 :=
  ⟨matchingVertices second tag, matching_injective second tag⟩

lemma first_quad (second : Bool) (tag : Fin 4) : QuadOn (graph second) (firstBlock second tag) :=
  QuadOn.of_degreeIn (by cases second <;> fin_cases tag <;> decide +kernel)
    (by cases second <;> fin_cases tag <;> decide +kernel)

lemma second_quad (second : Bool) (tag : Fin 4) :
    QuadOn (graph second) (secondBlock second tag) :=
  QuadOn.of_degreeIn (by cases second <;> fin_cases tag <;> decide +kernel)
    (by cases second <;> fin_cases tag <;> decide +kernel)

lemma third_quad (second : Bool) : QuadOn (graph second) (thirdBlock second) :=
  QuadOn.of_degreeIn (by cases second <;> decide +kernel)
    (by cases second <;> decide +kernel)

lemma first_score (second : Bool) (tag : Fin 4) :
    edgeCount (graph second) (firstBlock second tag) = 6 := by
  cases second <;> fin_cases tag <;> decide +kernel

lemma second_score (second : Bool) (tag : Fin 4) :
    edgeCount (graph second) (secondBlock second tag) = 6 := by
  cases second <;> fin_cases tag <;> decide +kernel

lemma first_second_disjoint (second : Bool) (tag : Fin 4) :
    Disjoint (firstBlock second tag) (secondBlock second tag) := by
  cases second <;> fin_cases tag <;> decide +kernel

lemma third_disjoint (second : Bool) (tag : Fin 4) :
    Disjoint (firstBlock second tag ∪ secondBlock second tag) (thirdBlock second) := by
  cases second <;> fin_cases tag <;> decide +kernel

lemma complement (second : Bool) (tag : Fin 4) :
    univ \ ((firstBlock second tag ∪ secondBlock second tag) ∪ thirdBlock second) =
      tupleSupport (matchingEmbedding second tag) := by
  cases second <;> fin_cases tag <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {second : Bool}

def matching (f : (graph second).Copy G) (tag : Fin 4)
    (hevent : G.Adj (f 15) (f (eventIndex second tag))) : TwoEdges G where
  vertices := (matchingEmbedding second tag).trans f.toEmbedding
  firstEdge := by
    fin_cases tag
    · exact hevent
    all_goals
      exact f.toHom.map_rel' (by cases second <;> decide +kernel : (graph second).Adj 0 1)
  secondEdge := by
    fin_cases tag
    · exact f.toHom.map_rel' (by cases second <;> decide +kernel : (graph second).Adj 1 9)
    · exact hevent.symm
    · exact hevent.symm
    · exact hevent

lemma matching_support (f : (graph second).Copy G) (tag : Fin 4)
    (hevent : G.Adj (f 15) (f (eventIndex second tag))) :
    (matching f tag hevent).support =
      (tupleSupport (matchingEmbedding second tag)).image f := by
  change univ.image (fun i ↦ f (matchingEmbedding second tag i)) =
    (univ.image (matchingEmbedding second tag)).image f
  rw [image_image]
  rfl

variable [DecidableRel G.Adj]

lemma first_image_score (f : (graph second).Copy G) (tag : Fin 4) :
    edgeCount G ((firstBlock second tag).image f) = 6 := by
  have hlo := edgeCount_image_le f (firstBlock second tag)
  rw [first_score] at hlo
  exact le_antisymm ((first_quad second tag).image f).edgeCount_le_six hlo

lemma second_image_score (f : (graph second).Copy G) (tag : Fin 4) :
    edgeCount G ((secondBlock second tag).image f) = 6 := by
  have hlo := edgeCount_image_le f (secondBlock second tag)
  rw [second_score] at hlo
  exact le_antisymm ((second_quad second tag).image f).edgeCount_le_six hlo

end Erdos577.WeightedThirteen.ThirdModel.MissedTable
