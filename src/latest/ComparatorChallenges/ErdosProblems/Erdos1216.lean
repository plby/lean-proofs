/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Function

namespace Erdos1216

abbrev Tournament (n : Nat) := BitVec (n * n)

def Tournament.arc {n : Nat} (T : Tournament n) (i j : Fin n) : Bool :=
  if i = j then false
  else if i < j then T.getLsbD (i.1 * n + j.1)
  else !T.getLsbD (j.1 * n + i.1)

def HasTransitiveTournament {n : Nat} (T : Tournament n) (k : Nat) : Prop :=
  ∃ v : Fin k → Fin n, Injective v ∧
    ∀ i j : Fin k, i < j → T.arc (v i) (v j) = true

def Guaranteed (n k : Nat) : Prop :=
  k ≤ n ∧ ∀ T : Tournament n, HasTransitiveTournament T k

open scoped Classical in
noncomputable def f (n : Nat) : Nat :=
  Nat.findGreatest (Guaranteed n) n

theorem not_erdos_1216 :
    ¬ (∀ n, 1 ≤ n → f n = Nat.log2 n + 1) := by
  sorry

end Erdos1216
