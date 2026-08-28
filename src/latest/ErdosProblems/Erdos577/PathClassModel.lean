import ErdosProblems.Erdos577.PathLossModel
import ErdosProblems.Erdos577.PathLabels
import ErdosProblems.Erdos577.CliqueLabels

/-! Exact row patterns and common-neighbor replacements for Wang's path classification. -/

namespace Erdos577.PathClass

open Finset
open scoped BigOperators

def Positive (m : ℕ) : Prop := ScoredExchange (PathLoss.graph 3 m) univ 6

lemma Positive.mono {small large : ℕ} (hs : Positive small) (h : large &&& small = small) :
    Positive large := by
  let f := SimpleGraph.Copy.ofLE (PathLoss.graph 3 small) (PathLoss.graph 3 large)
    (PathLoss.graph_mono 3 h)
  change ScoredExchange (PathLoss.graph 3 large) univ 6
  simpa only [f, SimpleGraph.Copy.coe_ofLE, image_id] using hs.image f

def rowIndex (reverse : Bool) (i : Fin 4) : Fin 4 := if reverse then i.rev else i

def bit (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i j : Fin 4) : Bool :=
  m.testBit (4 * (rowIndex reverse i).val + (cols j).val)

def rowCount (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i : Fin 4) : ℕ :=
  ∑ j : Fin 4, (bit m reverse cols i j).toNat

/-- A common column of rows j,l can be removed while row i still has two
contacts to the remaining complete triple. -/
def Replacement (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i j l : Fin 4) : Prop :=
  ∃ u : Fin 4, bit m reverse cols j u = true ∧ bit m reverse cols l u = true ∧
    2 ≤ ∑ v : Fin 4, if v ≠ u then (bit m reverse cols i v).toNat else 0

instance (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) (i j l : Fin 4) :
    Decidable (Replacement m reverse cols i j l) :=
  inferInstanceAs (Decidable (∃ u : Fin 4,
    bit m reverse cols j u = true ∧ bit m reverse cols l u = true ∧
      2 ≤ ∑ v : Fin 4, if v ≠ u then (bit m reverse cols i v).toNat else 0))

def PatternA (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  (∀ j : Fin 4, bit m reverse cols 0 j = true ∨ bit m reverse cols 2 j = true → j ≠ 3) ∧
    3 ≤ rowCount m reverse cols 1 ∧ rowCount m reverse cols 3 = 0

instance (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (PatternA m reverse cols) := inferInstanceAs (Decidable (_ ∧ _))

def CommonA (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
    Replacement m reverse cols (Fin.castAdd 1 i) (Fin.castAdd 1 j) (Fin.castAdd 1 l)

instance (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (CommonA m reverse cols) := inferInstanceAs (Decidable
      (∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l →
        Replacement m reverse cols (Fin.castAdd 1 i) (Fin.castAdd 1 j) (Fin.castAdd 1 l)))

def PatternB (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  (∀ j : Fin 4, bit m reverse cols 0 j = true ∨ bit m reverse cols 3 j = true → j = 0 ∨ j = 1) ∧
    ∀ j : Fin 4, bit m reverse cols 1 j = true ∨ bit m reverse cols 2 j = true → j ≠ 3

instance (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (PatternB m reverse cols) := inferInstanceAs (Decidable (_ ∧ _))

def CommonB (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) : Prop :=
  ∃ i : Fin 4, (i = 1 ∨ i = 2) ∧ rowCount m reverse cols i = 3 ∧
    ∀ j l : Fin 4, j ≠ i → l ≠ i → j ≠ l → Replacement m reverse cols i j l

instance (m : ℕ) (reverse : Bool) (cols : Fin 4 ↪ Fin 4) :
    Decidable (CommonB m reverse cols) := inferInstanceAs (Decidable
      (∃ i : Fin 4, (i = 1 ∨ i = 2) ∧ rowCount m reverse cols i = 3 ∧
        ∀ j l : Fin 4, j ≠ i → l ≠ i → j ≠ l → Replacement m reverse cols i j l))

def Classified (m : ℕ) : Prop :=
  PathExchange.crossCount m ≤ 10 ∧ ∃ reverse : Bool, ∃ cols : Fin 4 ↪ Fin 4,
    (PatternA m reverse cols ∧ CommonA m reverse cols) ∨
      (PatternB m reverse cols ∧ CommonB m reverse cols)

end Erdos577.PathClass
