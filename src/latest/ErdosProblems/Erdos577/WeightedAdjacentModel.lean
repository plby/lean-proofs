import ErdosProblems.Erdos577.WeightedPawPatterns
import ErdosProblems.Erdos577.UpperCounts
import ErdosProblems.Erdos577.PawSplitFactors
import ErdosProblems.Erdos577.PawInduced

/-! The two exact adjacent-leaf cases (18) and (20), and their maximal local graphs. -/

namespace Erdos577.WeightedAdjacent

open Finset

def mask (twenty : Bool) : ℕ := if twenty then 24003 else 20419

def graph (twenty : Bool) : SimpleGraph (Fin 8) := PawModel.graph 1 (mask twenty)

instance (twenty : Bool) : DecidableRel (graph twenty).Adj :=
  inferInstanceAs (DecidableRel (PawModel.graph 1 (mask twenty)).Adj)

def pathSet : Finset (Fin 8) := {5, 0, 1, 3}

lemma inside_count (twenty : Bool) : contacts (graph twenty) pathSet univ ≤ 15 := by
  cases twenty <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Rows (twenty : Bool) (p : Paw G) (q : Quadrilateral G) : Prop :=
  PawBlock.OnlyFirst q ∧ WeightedPawBlock.Row p q 0 3 ∧
    WeightedPawBlock.Row p q 2 (if twenty then 13 else 15) ∧
    WeightedPawBlock.Row p q 3 (if twenty then 5 else 4)

lemma Rows.center_absent (twenty : Bool) (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (h : Rows twenty p q)
    (hn : ¬LocalFactor G (p.support ∪ q.support)) :
    ¬G.Adj p.center (q 0) ∧ ¬G.Adj p.center (q 1) := by
  have h00 : G.Adj p.leaf (q 0) := (h.2.1 0).mpr (by decide)
  have h01 : G.Adj p.leaf (q 1) := (h.2.1 1).mpr (by decide)
  have h23 : G.Adj (p.vertices 2) (q 3) := (h.2.2.1 3).mpr (by cases twenty <;> decide)
  have h32 : G.Adj (p.vertices 3) (q 2) := (h.2.2.2 2).mpr (by cases twenty <;> decide)
  exact ⟨fun he ↦ hn (p.center_contact_factor q hd h00 h01 h23 h32 (Or.inl he)),
    fun he ↦ hn (p.center_contact_factor q hd h00 h01 h23 h32 (Or.inr he))⟩

end Erdos577.WeightedAdjacent
