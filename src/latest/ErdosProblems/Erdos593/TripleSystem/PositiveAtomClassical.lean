import ErdosProblems.Erdos593.TripleSystem.LowCodegreeLayering
import ErdosProblems.Erdos593.TripleSystem.MinimalBadCore
import ErdosProblems.Erdos593.TripleSystem.ObligatoryIsolatedReduction
import ErdosProblems.Erdos593.TripleSystem.PositiveAtomColoringAssembly

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The classical positive-atom endpoint

This module closes the cardinal-minimal-counterexample argument once the
finite low-pair closure colouring assembly is available.  The public theorem
has the same-universe host convention built into `IsObligatory`: both the
vertex and edge types of a host for the `u`-universe atom lie in `Type u`.
-/

namespace Erdos593

open scoped Cardinal

universe u

namespace TripleSystem

/-- Every positive balanced complete-bipartite expansion atom is obligatory.

The proof is the classical cardinal-minimal argument.  If an uncountably
chromatic atom-free host existed, choose one of least vertex cardinality.  Its
strictly smaller restrictions are countably chromatic; its uncountable vertex
carrier admits a finite low-pair closure layering.  The positive-atom
colouring assembly then supplies a natural-number proper colouring of the
minimal host, contradicting its uncountable chromatic cardinal. -/
theorem completeBipartiteExpansionAtom_positive_isObligatory
    (n : Nat) (hn : 0 < n) :
    (completeBipartiteExpansionAtom.{u} n).IsObligatory := by
  intro W D _ H hunc
  classical
  by_contra hatomFree
  have hbad : exists kappa : Cardinal.{u},
      AtomFreeUncountablyChromaticCard
        (completeBipartiteExpansionAtom.{u} n) kappa := by
    refine ⟨Cardinal.mk W, W, D, H, rfl, hunc, hatomFree⟩
  obtain ⟨kappa, hkappa, hminimal⟩ :=
    exists_minimalAtomFreeUncountablyChromaticCard
      (completeBipartiteExpansionAtom.{u} n) hbad
  rcases hkappa with ⟨W0, D0, H0, hcard, hunc0, hfree0⟩
  let : DecidableEq W0 := Classical.decEq W0
  have hlocal : H0.LocallyCountablyChromaticBelow :=
    locallyCountablyChromaticBelow_of_minimalBad
      (completeBipartiteExpansionAtom.{u} n) H0 hcard hfree0 hminimal
  have hW0 : Cardinal.aleph0 < Cardinal.mk W0 :=
    lt_of_lt_of_le hunc0 H0.chromaticCardinal_le_mk_vertices
  obtain ⟨L⟩ := exists_lowPairClosureLayering_of_uncountable H0
    (2 * n + n * n) hW0
  obtain ⟨c, hc⟩ :=
    exists_natProperColoring_of_atomFree_of_lowPairClosureLayering
      hn hfree0 L hlocal
  let cCountable : W0 -> CountableColor.{u} := fun x => ULift.up (c x)
  have hcCountable : H0.IsProperColoring cCountable := by
    intro e
    obtain ⟨x, hx, y, hy, hxy⟩ := hc e
    refine ⟨x, hx, y, hy, ?_⟩
    intro hEq
    apply hxy
    simpa [cCountable] using! congrArg ULift.down hEq
  have hcount : H0.chromaticCardinal <= Cardinal.aleph0 :=
    H0.chromaticCardinal_le_aleph0_of_natColoring ⟨cCountable, hcCountable⟩
  exact (not_lt_of_ge hcount) hunc0

end TripleSystem

end Erdos593
