import Wikipedia.GreenTao.All

/-!
# The Green--Tao theorem

The primes contain arithmetic progressions of every finite length. This is
the statement used by the upstream Lean evaluation, with its Szemerédi input
provided by `Wikipedia.SzemeredisTheorem`.
-/

namespace GreenTao

/-- **Green--Tao theorem**: the natural primes contain arbitrarily long
arithmetic progressions. -/
theorem green_tao :
    SzemeredisTheorem.ContainsArbitraryAPs
      {p : ℕ | Nat.Prime p} := by
  refine
    Wikipedia.SzemeredisTheorem.containsArbitraryAPs_primes_of_orderedRemoval_of_linearForms
      ?_ Wikipedia.SzemeredisTheorem.hasStandardCyclicMajorantLinearForms
  intro k hk
  have hrank : k - 1 = (k - 2) + 1 := by omega
  rw [hrank]
  exact
    Wikipedia.SzemeredisTheorem.hasUniformOrderedPatternRemoval_sourceFull
      k (k - 2) (by omega)

#print axioms green_tao

end GreenTao
