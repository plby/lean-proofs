import ErdosProblems.Erdos577.PawModel
import ErdosProblems.Erdos577.DenseOutsideModel

/-! Necessary row conditions for Wang's nine-triangle-contact paw lemma. -/

namespace Erdos577.PawNine

open scoped BigOperators

def rowCount (m : ℕ) (i : Fin 4) : ℕ :=
  ∑ j : Fin 4, (m.testBit (4 * i.val + j.val)).toNat

/-- A universally replaceable triangle row has three contacts and meets
every column whose old internal degree is two. -/
def GoodRow (diagonal : Fin 4) (m : ℕ) (i : Fin 3) : Prop :=
  3 ≤ rowCount m (Fin.natAdd 1 i) ∧
    ∀ j : Fin 4, diagonal.val.testBit (j.val % 2) = false →
      m.testBit (4 * (i.val + 1) + j.val) = true

instance (diagonal : Fin 4) (m : ℕ) (i : Fin 3) : Decidable (GoodRow diagonal m i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def HasGoodRow (diagonal : Fin 4) (m : ℕ) : Prop := ∃ i : Fin 3, GoodRow diagonal m i

instance (diagonal : Fin 4) (m : ℕ) : Decidable (HasGoodRow diagonal m) :=
  inferInstanceAs (Decidable (∃ i : Fin 3, GoodRow diagonal m i))

end Erdos577.PawNine
