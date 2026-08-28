import ErdosProblems.Erdos577.WeightedPawPatterns
import ErdosProblems.Erdos577.UpperCounts
import ErdosProblems.Erdos577.PawIndexedFactors
import ErdosProblems.Erdos577.QuadSets
import ErdosProblems.Erdos577.PawInduced

/-! Local data and inside bounds for the opposite-leaf cases (16) and (17). -/

namespace Erdos577.WeightedOpposite

open Finset

def mask (seventeen : Bool) : ℕ := if seventeen then 15701 else 32085

def graph (seventeen : Bool) : SimpleGraph (Fin 8) := PawModel.graph 1 (mask seventeen)

instance (seventeen : Bool) : DecidableRel (graph seventeen).Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph 1 (mask seventeen)).Adj)

def fiveSet : Finset (Fin 8) := {0, 1, 3, 5, 7}

lemma inside_count (seventeen : Bool) : contacts (graph seventeen) fiveSet univ ≤ 19 := by
  cases seventeen <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Rows (seventeen : Bool) (p : Paw G) (q : Quadrilateral G) : Prop :=
  ¬G.Adj (q 1) (q 3) ∧ WeightedPawBlock.Row p q 0 5 ∧
    WeightedPawBlock.Row p q 2 13 ∧ WeightedPawBlock.Row p q 3 (if seventeen then 3 else 7)

lemma Rows.center_factor (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q)
    (hcenter : G.Adj p.center (q 1) ∨ G.Adj p.center (q 3)) :
    LocalFactor G (p.support ∪ q.support) := by
  have hne (i j : Fin 4) : p.vertices i ≠ q j := by
    intro he
    exact disjoint_left.mp hd ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩)
      ((q.mem_support _).mpr ⟨j, he.symm⟩)
  have h00 : G.Adj p.leaf (q 0) := (h.2.1 0).mpr (by decide)
  have h02 : G.Adj p.leaf (q 2) := (h.2.1 2).mpr (by decide)
  have h22 : G.Adj (p.vertices 2) (q 2) := (h.2.2.1 2).mpr (by decide)
  have h23 : G.Adj (p.vertices 2) (q 3) := (h.2.2.1 3).mpr (by decide)
  have h30 : G.Adj (p.vertices 3) (q 0) := (h.2.2.2 0).mpr (by cases seventeen <;> decide)
  have h31 : G.Adj (p.vertices 3) (q 1) := (h.2.2.2 1).mpr (by cases seventeen <;> decide)
  rcases hcenter with hcenter | hcenter
  · apply p.factor_of_index_partition q hd {0, 1, 5, 6} {2, 3, 4, 7} (by decide)
    · simp only [image_insert, image_singleton]
      change QuadOn G {p.vertices 0, p.vertices 1, q 1, q 2}
      exact QuadOn.of_vertices (hne 0 1) (hne 1 2) p.pendant hcenter (q.adjacent 1) h02.symm
    · simp only [image_insert, image_singleton]
      change QuadOn G {p.vertices 2, p.vertices 3, q 0, q 3}
      exact QuadOn.of_vertices (hne 2 0) (hne 3 3) p.edge23 h30 (q.adjacent 3).symm h23.symm
  · apply p.factor_of_index_partition q hd {0, 1, 7, 4} {2, 3, 5, 6} (by decide)
    · simp only [image_insert, image_singleton]
      change QuadOn G {p.vertices 0, p.vertices 1, q 3, q 0}
      exact QuadOn.of_vertices (hne 0 3) (hne 1 0) p.pendant hcenter (q.adjacent 3) h00.symm
    · simp only [image_insert, image_singleton]
      change QuadOn G {p.vertices 2, p.vertices 3, q 1, q 2}
      exact QuadOn.of_vertices (hne 2 1) (hne 3 2) p.edge23 h31 (q.adjacent 1) h22.symm

lemma Rows.center_absent (seventeen : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows seventeen p q)
    (hn : ¬LocalFactor G (p.support ∪ q.support)) :
    ¬G.Adj p.center (q 1) ∧ ¬G.Adj p.center (q 3) :=
  ⟨fun he ↦ hn (h.center_factor seventeen p q hd (Or.inl he)),
    fun he ↦ hn (h.center_factor seventeen p q hd (Or.inr he))⟩

end Erdos577.WeightedOpposite
