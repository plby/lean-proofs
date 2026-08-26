import ErdosProblems.Erdos593.TripleSystem.Embedding
import Mathlib.SetTheory.Cardinal.Order

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Colourings, appearance, and obligatoriness

This is the infinitary-facing vocabulary for Erdős Problem 593.  It is kept
compatible with the corresponding definitions in DeepMind's
`FormalConjecturesForMathlib/Combinatorics/Hypergraph/ThreeUniform.lean`, while
using this project's edge-indexed triple systems and non-induced embeddings.
No statement or implementation from that external Apache-2.0 project is
imported.
-/

namespace Erdos593

open scoped Cardinal

universe u v w

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

/-- A vertex colouring is proper when every hyperedge contains two vertices
of different colours. -/
def IsProperColoring {C : Type w} (c : V → C) : Prop :=
  ∀ e : E, ∃ x : V, F.Inc x e ∧ ∃ y : V, F.Inc y e ∧ c x ≠ c y

/-- The least cardinality of a colour type admitting a proper colouring. -/
noncomputable def chromaticCardinal : Cardinal.{u} :=
  sInf {k : Cardinal.{u} | ∃ C : Type u, #C = k ∧
    ∃ c : V → C, F.IsProperColoring c}

/-- `F` appears in `H` when it has a non-induced triple-system embedding. -/
def Appears {W : Type u} {D : Type v}
    (F : TripleSystem V E) (H : TripleSystem W D) : Prop :=
  Nonempty (F.Embedding H)

/-- Property B for a triple system. -/
def IsTwoColorable : Prop :=
  ∃ c : V → Fin 2, F.IsProperColoring c

/-- A finite source is obligatory when it appears in every triple system of
uncountable chromatic cardinality in the ambient universes. -/
def IsObligatory : Prop :=
  ∀ (W : Type u) (D : Type v) [DecidableEq W]
    (H : TripleSystem W D), ℵ₀ < H.chromaticCardinal → F.Appears H

theorem appears_refl : F.Appears F :=
  ⟨Embedding.refl F⟩

theorem Appears.trans {W : Type u} {D : Type v} {X : Type u} {A : Type v}
    {H : TripleSystem W D} {K : TripleSystem X A}
    (hFH : F.Appears H) (hHK : H.Appears K) : F.Appears K := by
  rcases hFH with ⟨f⟩
  rcases hHK with ⟨g⟩
  exact ⟨f.trans g⟩

end TripleSystem
end Erdos593
