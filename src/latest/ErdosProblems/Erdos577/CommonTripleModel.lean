import ErdosProblems.Erdos577.MatchingGain
import ErdosProblems.Erdos577.CommonReplacement
import ErdosProblems.Erdos577.PawNineModel

/-! Nine-vertex models for Wang's common-triple lemma.

Only the leaf, the two noncentral triangle vertices, and the extra
vertex have encoded rows. No center-to-block edge is assumed or used.
-/

namespace Erdos577.CommonTriple

open Finset

def basePairs (diagonal : Fin 4) : Finset (Fin 9 × Fin 9) :=
  {(0, 1), (1, 2), (1, 3), (2, 3), (4, 5), (5, 6), (6, 7), (4, 7)} ∪
    (if diagonal.val.testBit 0 then {(4, 6)} else ∅) ∪
    (if diagonal.val.testBit 1 then {(5, 7)} else ∅)

def rowVertex (i : Fin 4) : Fin 9 := ![0, 2, 3, 8] i

def rowIndex (a : Fin 9) : ℕ := if a = 0 then 0 else if a = 2 then 1 else if a = 3 then 2 else 3

def relation (diagonal : Fin 4) (m : ℕ) (a b : Fin 9) : Prop :=
  (a, b) ∈ basePairs diagonal ∨
    ((a = 0 ∨ a = 2 ∨ a = 3 ∨ a = 8) ∧ 4 ≤ b.val ∧ b.val < 8 ∧
      m.testBit (4 * rowIndex a + (b.val - 4)) = true)

instance (diagonal : Fin 4) (m : ℕ) : DecidableRel (relation diagonal m) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

def graph (diagonal : Fin 4) (m : ℕ) : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel (relation diagonal m)

instance (diagonal : Fin 4) (m : ℕ) : DecidableRel (graph diagonal m).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (relation diagonal m)).Adj)

def quad : Finset (Fin 9) := {4, 5, 6, 7}

def core : Finset (Fin 9) := {0, 1, 2, 3, 4, 5, 6, 7}

def Positive (diagonal : Fin 4) (m : ℕ) : Prop :=
  CommonReplacement (graph diagonal m) 2 3 8 quad ∨
    TwoEdgeReduction (graph diagonal m) core (Unattached.oldEdges diagonal + 2)

lemma graph_mono (diagonal : Fin 4) {small large : ℕ} (h : large &&& small = small) :
    graph diagonal small ≤ graph diagonal large := by
  have hb (i : ℕ) (hi : small.testBit i = true) : large.testBit i = true := by
    have he := congrArg (fun n : ℕ ↦ n.testBit i) h
    simpa only [Nat.testBit_and, hi, Bool.and_true] using he
  have hr {a b : Fin 9} (h : relation diagonal small a b) : relation diagonal large a b := by
    rcases h with h | ⟨ha, hb', hb8, hbit⟩
    · exact Or.inl h
    · exact Or.inr ⟨ha, hb', hb8, hb _ hbit⟩
  intro a b hab
  rcases (SimpleGraph.fromRel_adj _ _ _).mp hab with ⟨hne, h | h⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl (hr h)⟩
  · exact (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inr (hr h)⟩

lemma Positive.mono {diagonal : Fin 4} {small large : ℕ}
    (hs : Positive diagonal small) (h : large &&& small = small) : Positive diagonal large := by
  let f := SimpleGraph.Copy.ofLE (graph diagonal small) (graph diagonal large)
    (graph_mono diagonal h)
  rcases hs with hs | hs
  · left
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id, id_eq] using hs.image f
  · right
    simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

def Hypotheses (m : ℕ) : Prop :=
  9 ≤ PathExchange.crossCount m ∧
    ((PawNine.rowCount m 0 = 1 ∧ PawNine.rowCount m 1 = 3 ∧
      ∀ j : Fin 4, m.testBit (4 + j.val) = m.testBit (8 + j.val)) ∨
      (PawNine.rowCount m 0 = 0 ∧ 7 ≤ PawNine.rowCount m 1 + PawNine.rowCount m 2))

instance (m : ℕ) : Decidable (Hypotheses m) := inferInstanceAs (Decidable (_ ∧ _))

def Conclusion (m : ℕ) : Prop :=
  PathExchange.crossCount m = 9 ∧ ∃ r : Fin 4,
    (∀ j : Fin 4, j ≠ 0 → m.testBit (4 + (j + r).val) = true ∧
      m.testBit (8 + (j + r).val) = true) ∧ m.testBit (12 + (2 + r).val) = true

instance (m : ℕ) : Decidable (Conclusion m) := inferInstanceAs (Decidable (_ ∧ _))

end Erdos577.CommonTriple
