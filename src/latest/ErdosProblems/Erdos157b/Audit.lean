import ErdosProblems.Erdos157b

/-!
Independent statement and axiom checks for the binary construction.
This file is downstream of the primary theorem, not an input to its proof.
-/

example :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ ⦃a b c d : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → d ∈ A → a + b = c + d →
        (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n = a + b + c) :=
  Erdos157.Binary.erdos_157

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Erdos157.Binary.encodedSet_isSidon,
      ``Erdos157.Binary.exists_encoded_asymptoticBasis, ``Erdos157.Binary.erdos_157] do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms Erdos157.Binary.erdos_157
