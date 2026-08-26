import ErdosProblems.Erdos19.VizingCore

/-! # Missing colors with a full degree-sized palette -/

namespace Erdos19.Vizing

open Finset

attribute [local instance] Classical.propDecidable

variable {V K : Type*} [Fintype V] [Fintype K]

theorem exists_missing_of_colored_neighbors (G : SimpleGraph V) (C : PartialColoring V K)
    (v : V) (S : Finset V)
    (hS : ∀ w a, G.Adj v w → C s(v, w) = some a → w ∈ S)
    (hcard : S.card < Fintype.card K) : ∃ a, Missing G C v a := by
  classical
  by_contra hnone
  have hpresent : ∀ a : K, ∃ w, G.Adj v w ∧ C s(v, w) = some a := by
    intro a
    have hmissing : ¬Missing G C v a := fun h ↦ hnone ⟨a, h⟩
    exact Classical.not_not.mp ((missing_iff_not_exists G C v a).not.mp hmissing)
  choose f hf using hpresent
  let select : K → S := fun a ↦ ⟨f a, hS (f a) a (hf a).1 (hf a).2⟩
  have hinj : Function.Injective select := by
    intro a b hab
    have hfval : f a = f b := congrArg Subtype.val hab
    have hcol : C s(v, f a) = some b := hfval ▸ (hf b).2
    exact Option.some.inj ((hf a).2.symm.trans hcol)
  have hle := Fintype.card_le_of_injective select hinj
  have hle' : Fintype.card K ≤ S.card := by simpa only [Fintype.card_coe] using hle
  exact (Nat.not_lt_of_ge hle') hcard

theorem exists_missing_of_degree_lt (G : SimpleGraph V) (C : PartialColoring V K)
    (v : V) (hdegree : G.degree v < Fintype.card K) : ∃ a, Missing G C v a := by
  apply exists_missing_of_colored_neighbors G C v (G.neighborFinset v)
  · intro w _ hvw _
    exact (G.mem_neighborFinset v w).mpr hvw
  · simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdegree

/-- A vertex incident with an uncolored edge misses a color even when its
degree equals the palette size. -/
theorem exists_missing_of_uncolored (G : SimpleGraph V) (C : PartialColoring V K)
    (v w : V) (hvw : G.Adj v w) (hzero : C s(v, w) = none)
    (hdegree : G.degree v ≤ Fintype.card K) : ∃ a, Missing G C v a := by
  classical
  apply exists_missing_of_colored_neighbors G C v ((G.neighborFinset v).erase w)
  · intro z a hvz hcolor
    apply mem_erase.mpr
    refine ⟨?_, (G.mem_neighborFinset v z).mpr hvz⟩
    intro hzw
    subst z
    rw [hzero] at hcolor
    contradiction
  · have hw : w ∈ G.neighborFinset v := (G.mem_neighborFinset v w).mpr hvw
    have hpos : 0 < (G.neighborFinset v).card := card_pos.mpr ⟨w, hw⟩
    rw [card_erase_of_mem hw]
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hpos ⊢
    omega

#print axioms exists_missing_of_degree_lt
#print axioms exists_missing_of_uncolored

end Erdos19.Vizing
