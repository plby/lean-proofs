import ErdosProblems.Erdos118.Reused591.ExactGoodSequence
import ErdosProblems.Erdos118.Reused591.CanonicalSequence

namespace Erdos118.Reused591

namespace Erdos591.Negative.Exact

open Ordinal

/-!
The literal tagged coordinate sequence for a source-good word.  Unlike the
older gap-coded sequence, the numerical values here are the actual entries
of the Handbook good sequence.  The only tags set initially are the root and
level markers; `boxLast` additionally marks the final coordinate.
-/

def taggedLevel (a : List ℕ) : List TaggedCoord :=
  ⟨a.length, true⟩ :: a.map fun n ↦ ⟨n, false⟩

def taggedWord (s : G2) : List TaggedCoord :=
  ⟨s.length, true⟩ :: s.flatMap taggedLevel

@[simp] theorem taggedLevel_values (a : List ℕ) :
    (taggedLevel a).map TaggedCoord.value = levelWord a := by
  simp [taggedLevel, levelWord, Function.comp_def]

@[simp] theorem taggedWord_values (s : G2) :
    (taggedWord s).map TaggedCoord.value = word s := by
  simp [taggedWord, word, List.map_flatMap, Function.comp_def]

@[simp] theorem taggedWord_ne_nil (s : G2) : taggedWord s ≠ [] := by
  simp [taggedWord]

/-- The actual coordinate sequence on which the interlacing graph is
evaluated. -/
def sequence (s : G) : List TaggedCoord := boxLast (taggedWord s.1)

theorem sequence_ne_nil (s : G) : sequence s ≠ [] := by
  rw [sequence, boxLast_ne_nil_iff]
  exact taggedWord_ne_nil s.1

@[simp] theorem sequence_values (s : G) :
    (sequence s).map TaggedCoord.value = word s.1 := by
  rw [sequence, boxLast_values, taggedWord_values]

theorem sequence_pairwise (s : G) :
    (sequence s).Pairwise (fun a b ↦ a.value < b.value) := by
  apply pairwise_boxLast_value
  have hs : ((taggedWord s.1).map TaggedCoord.value).Pairwise (· < ·) := by
    simpa only [taggedWord_values] using s.2
  simpa only [List.pairwise_map] using hs

/-- The Hajnal--Larson interlacing graph on the literal good-sequence
carrier. -/
def graph : SimpleGraph G := interlacingGraph sequence

theorem graph_no_six :
    ¬ ∃ S : Set G, graph.IsClique S ∧ Cardinal.mk S = 6 := by
  exact interlacingGraph_no_six_clique sequence

noncomputable def relIso :
    ((· < ·) : G → G → Prop) ≃r
      ((· < ·) : (ω ^ (ω ^ 2)).ToType →
        (ω ^ (ω ^ 2)).ToType → Prop) := by
  apply Classical.choice
  apply Ordinal.type_eq.mp
  rw [type_G, Ordinal.type_toType]

/-- The density statement is the sole remaining combinatorial input for the
negative relation on the now-correct source carrier. -/
theorem negative_six_of_density
    (hhit : MeetsEveryFullSet
      ((· < ·) : G → G → Prop)
      (ω ^ (ω ^ 2) : Ordinal.{0}) graph) :
    ¬ OrdinalCardinalRamsey
      (ω ^ (ω ^ 2) : Ordinal.{0})
      (ω ^ (ω ^ 2) : Ordinal.{0})
      (6 : Cardinal.{0}) := by
  exact not_ordinalCardinalRamsey_of_model
    (X := G)
    (r := ((· < ·) : G → G → Prop))
    (alpha := (ω ^ (ω ^ 2) : Ordinal.{0}))
    (n := 6) relIso graph graph_no_six hhit

end Erdos591.Negative.Exact

end Erdos118.Reused591
