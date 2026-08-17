import Mathlib

open Function

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1216

abbrev Tournament (n : Nat) := BitVec (n * n)

end Erdos1216

namespace Erdos1216

def Tournament.arc {n : Nat} (T : Tournament n) (i j : Fin n) : Bool :=
  if i = j then false
  else if i < j then T.getLsbD (i.1 * n + j.1)
  else !T.getLsbD (j.1 * n + i.1)

end Erdos1216

namespace Erdos1216

def HasTransitiveTournament {n : Nat} (T : Tournament n) (k : Nat) : Prop :=
  ∃ v : Fin k → Fin n, Injective v ∧
    ∀ i j : Fin k, i < j → T.arc (v i) (v j) = true

end Erdos1216

namespace Erdos1216

def Guaranteed (n k : Nat) : Prop :=
  k ≤ n ∧ ∀ T : Tournament n, HasTransitiveTournament T k

end Erdos1216

namespace Erdos1216

def f (n : Nat) : Nat :=
  Nat.findGreatest (Guaranteed n) n

end Erdos1216

namespace Erdos1216

def ProposedFormula : Prop :=
  ∀ n, 1 ≤ n → f n = Nat.log2 n + 1

end Erdos1216

namespace Erdos1216

theorem erdos_1216 : ¬ ProposedFormula := by
  sorry

end Erdos1216

end
