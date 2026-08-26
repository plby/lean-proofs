-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Lift

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Definitional infrastructure for arXiv:2606.24882

This file sets up the structural definitions needed to state and prove the
results of

  Eric Li, *A Resolution of Erdős Problems 593 and 1177: Obligatory Triple
  Systems and Exact Spectra*, arXiv:2606.24882.

We reuse the `Hypergraph` framework from `ErdosProblems.Erdos1177.Lift` for *hosts*
(large, possibly infinite triple systems), and introduce a bundled type
`FTS` of *finite triple systems* for the sources of embeddings.

## Main definitions

* `Hypergraph.IsTripleSystem` — every edge has exactly three vertices.
* `Hypergraph.UncountablyChromatic` — not colourable with `ℵ₀` colours.
* `FTS` — a finite triple system (bundled finite vertex type + edge finset).
* `FTS.Embeds` — an injective, non-induced embedding of a finite triple
  system into a host hypergraph.
* `FTS.Obligatory` — occurs in every triple system of uncountable chromatic
  number.
* `FTS.Linear` — any two distinct edges meet in at most one vertex.
* `FTS.InSpec` / `FTS.FGnonempty` — the exact spectrum and the family
  `F_G(κ)`.
-/

open Cardinal Ordinal

namespace Erdos1177

universe u v

/-- A host hypergraph is a *triple system* if every edge has exactly three
vertices. -/
def Hypergraph.IsTripleSystem {V : Type*} (H : Hypergraph V) : Prop :=
  ∀ e ∈ H.edges, e.ncard = 3

/-- A host hypergraph is *uncountably chromatic* if it admits no proper
colouring by `ℵ₀` colours. -/
def Hypergraph.UncountablyChromatic {V : Type u} (H : Hypergraph V) : Prop :=
  ¬ H.ColorableBy ℵ₀

/-! ### Finite triple systems -/

/-- A *finite triple system*: a finite vertex type together with a finite set
of three-element edges. -/
structure FTS where
  /-- The (finite) vertex type. -/
  V : Type
  [finV : Fintype V]
  [decV : DecidableEq V]
  /-- The edges, each a three-element finset. -/
  edges : Finset (Finset V)
  /-- Every edge has exactly three vertices. -/
  card3 : ∀ e ∈ edges, e.card = 3

attribute [instance] FTS.finV FTS.decV

/-- A vertex of a finite triple system is *isolated* if it lies on no edge. -/
def FTS.Isolated (F : FTS) (x : F.V) : Prop :=
  ∀ e ∈ F.edges, x ∉ e

/-- `F` is *linear* if any two distinct edges meet in at most one vertex. -/
def FTS.Linear (F : FTS) : Prop :=
  ∀ e₁ ∈ F.edges, ∀ e₂ ∈ F.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

/-- An injective, non-induced embedding of a finite triple system `F` into a
host hypergraph `H`: an injective vertex map sending every edge of `F` to an
edge of `H`. -/
def FTS.Embeds (F : FTS) {W : Type u} (H : Hypergraph W) : Prop :=
  ∃ f : F.V → W, Function.Injective f ∧
    ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ H.edges

/-- `F` is *obligatory* if it occurs in every triple system of uncountable
chromatic number. -/
def FTS.Obligatory (F : FTS) : Prop :=
  ∀ {W : Type u} (H : Hypergraph W),
    H.IsTripleSystem → H.UncountablyChromatic → F.Embeds H

/-- The exact spectrum membership: `λ ∈ Spec(F)` iff `λ` is uncountable and
there is an exact-`λ`-chromatic `F`-free triple system. -/
def FTS.InSpec (F : FTS) (lam : Cardinal.{u}) : Prop :=
  ℵ₀ < lam ∧ ∃ (W : Type u) (H : Hypergraph W),
    H.IsTripleSystem ∧ H.HasChromatic lam ∧ ¬ F.Embeds H

/-- The family `F_G(κ)` is nonempty: there is an exact-`κ`-chromatic triple
system omitting `G`. -/
def FTS.FGnonempty (G : FTS) (kappa : Cardinal.{u}) : Prop :=
  ∃ (W : Type u) (H : Hypergraph W),
    H.IsTripleSystem ∧ H.HasChromatic kappa ∧ ¬ G.Embeds H

end Erdos1177
