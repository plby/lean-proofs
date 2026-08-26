import ErdosProblems.Erdos593.TripleSystem.HighPairMatrix
import ErdosProblems.Erdos593.TripleSystem.ObligatoryAtoms

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Positive atoms from quadratic high-pair grids

This is the final finite extraction interface for the positive branch.  Its
hypothesis deliberately concerns only the host: every uncountably chromatic
host supplies high-codegree pairs across arbitrarily large finite bipartite
grids.  The Hall/matrix construction and the finite rainbow extraction are
reused from the preceding modules.
-/

namespace Erdos593

open scoped Cardinal

universe u

namespace TripleSystem

/-- If every uncountably chromatic host contains arbitrarily large complete
left/right grids of pairs with codegree at least `2q + q²`, then every
nontrivial balanced complete-bipartite private-vertex expansion is
obligatory. -/
theorem completeBipartiteExpansionAtom_isObligatory_of_quadratic_highPairs
    (n : Nat) (hn : 0 < n)
    (hgrid : ∀ (W D : Type u) [DecidableEq W] (H : TripleSystem W D),
      ℵ₀ < H.chromaticCardinal →
        ∀ q : Nat, ∃ left right : Fin q ↪ W,
          ∀ i j, HighPair H (2 * q + q * q) (left i) (right j)) :
    (privateVertexExpansion (completeBipartiteNN.{u} n)).IsObligatory := by
  simpa only [completeBipartiteExpansionAtom] using!
    (completeBipartiteExpansionAtom_isObligatory_of_witnessedMatrices n 2 hn
      (by decide) (by
        intro W D _ H hH q
        obtain ⟨left, right, hhigh⟩ := hgrid W D H hH q
        obtain ⟨M, _, _⟩ :=
          exists_witnessedBipartiteMatrix_of_quadratic_highPair left right hhigh
        exact ⟨M⟩))

end TripleSystem

end Erdos593
