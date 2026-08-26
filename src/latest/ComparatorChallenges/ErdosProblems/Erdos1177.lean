import Mathlib

open Cardinal

namespace Erdos1177

universe u

/-- A hypergraph is a set of vertex sets, its edges. -/
structure Hypergraph (V : Type u) where
  edges : Set (Set V)

/-- A proper coloring has no monochromatic edge. -/
def Hypergraph.ProperColoring {V : Type u} {C : Type*} (H : Hypergraph V)
    (c : V → C) : Prop :=
  ∀ e ∈ H.edges, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

def Hypergraph.ColorableBy {V : Type u} (H : Hypergraph V) (θ : Cardinal.{u}) :
    Prop :=
  ∃ c : V → θ.out, H.ProperColoring c

/-- Exact weak chromatic number, including colorability at the stated cardinal. -/
def Hypergraph.HasChromatic {V : Type u} (H : Hypergraph V) (κ : Cardinal.{u}) :
    Prop :=
  H.ColorableBy κ ∧ ∀ θ, θ < κ → ¬ H.ColorableBy θ

def Hypergraph.IsTripleSystem {V : Type*} (H : Hypergraph V) : Prop :=
  ∀ e ∈ H.edges, e.ncard = 3

/-- A finite triple system, including any isolated vertices. -/
structure FTS where
  V : Type
  [finV : Fintype V]
  [decV : DecidableEq V]
  edges : Finset (Finset V)
  card3 : ∀ e ∈ edges, e.card = 3

attribute [instance] FTS.finV FTS.decV

/-- Injective edge-preserving containment; extra host edges are allowed. -/
def FTS.Embeds (F : FTS) {W : Type u} (H : Hypergraph W) : Prop :=
  ∃ f : F.V → W, Function.Injective f ∧
    ∀ e ∈ F.edges, (f '' (↑e : Set F.V)) ∈ H.edges

/-- Nonemptiness of the exact-chromatic avoidance family. -/
def FTS.FGnonempty (G : FTS) (kappa : Cardinal.{u}) : Prop :=
  ∃ (W : Type u) (H : Hypergraph W),
    H.IsTripleSystem ∧ H.HasChromatic kappa ∧ ¬ G.Embeds H

/-- The three answers are yes, no, and yes, respectively. -/
theorem erdos_1177 :
    (∀ G : FTS, G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) →
      ∃ (W : Type u) (H : Hypergraph W),
        H.IsTripleSystem ∧ H.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
        ¬ G.Embeds H ∧ #W ≤
          (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u}))) ∧
    (∃ G H : FTS,
      G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
      H.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
        K.IsTripleSystem ∧ K.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
        ¬ G.Embeds K ∧ ¬ H.Embeds K) ∧
    (∀ (G : FTS) (κ : Cardinal.{u}), ℵ₀ < κ → G.FGnonempty κ →
      ∀ lam : Cardinal.{u}, ℵ₀ < lam → G.FGnonempty lam) := by
  sorry

end Erdos1177
