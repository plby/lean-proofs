import ErdosProblems.Erdos593.Graph.CompleteBipartite
import ErdosProblems.Erdos593.TripleSystem.Expansion
import ErdosProblems.Erdos593.TripleSystem.Obligatory
import ErdosProblems.Erdos593.TripleSystem.RainbowExpansionEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Obligatory private-vertex-expansion atoms

This module is the foundational home for the balanced complete-bipartite
private-vertex-expansion atoms.  It intentionally contains no constructive
closure or bipartite-reduction imports, so the positive atom theorem can be
used by those downstream results without a dependency cycle.
-/

namespace Erdos593

open scoped Cardinal

universe u

namespace TripleSystem

/-- The private-vertex expansion of the balanced complete bipartite graph
`K_{n,n}` in the ambient universe. -/
abbrev completeBipartiteExpansionAtom (n : ℕ) :=
  privateVertexExpansion (completeBipartiteNN.{u} n)

/-- The `K_{0,0}` expansion atom is obligatory because both its points and
edge indices are empty. -/
theorem completeBipartiteExpansionAtom_zero_isObligatory :
    (completeBipartiteExpansionAtom.{u} 0).IsObligatory := by
  intro W D _ H _
  apply Nonempty.intro
  exact
    { vertex :=
        { toFun := fun x => isEmptyElim x
          inj' := fun x => isEmptyElim x }
      edge := fun e => isEmptyElim e
      map_edge := fun e => isEmptyElim e }

/-- A witnessed locally bounded bipartite matrix in a host contains the
corresponding positive balanced expansion atom once its finite rainbow
submatrix has been extracted. -/
theorem completeBipartiteExpansionAtom_appears_of_witnessedMatrices
    {W D : Type u} (H : TripleSystem W D) (n t : Nat)
    (hn : 0 < n) (ht : 0 < t)
    (hmat : ∀ q : Nat, Nonempty (WitnessedBipartiteMatrix H q t)) :
    (completeBipartiteExpansionAtom.{u} n).Appears H := by
  change Nonempty ((privateVertexExpansion
    (completeBipartiteNN.{u} n)).Embedding H)
  exact exists_rainbowEmbedding_of_witnessedMatrices H n t hn ht hmat

/-- The finite rainbow bridge reduces a positive atom theorem to the explicit
host-extraction obligation of producing witnessed matrices of every size. -/
theorem completeBipartiteExpansionAtom_isObligatory_of_witnessedMatrices
    (n t : Nat) (hn : 0 < n) (ht : 0 < t)
    (hmat : ∀ (W D : Type u) [DecidableEq W] (H : TripleSystem W D),
      ℵ₀ < H.chromaticCardinal →
        ∀ q : Nat, Nonempty (WitnessedBipartiteMatrix H q t)) :
    (completeBipartiteExpansionAtom.{u} n).IsObligatory := by
  intro W D _ H hH
  exact completeBipartiteExpansionAtom_appears_of_witnessedMatrices
    H n t hn ht (hmat W D H hH)

end TripleSystem

end Erdos593
