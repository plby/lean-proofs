-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.Defs

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Property `P` (the simultaneous edge-labelling input, §6.1)

We formalize the Erdős–Galvin–Hajnal property `P(S, I, κ)` of an edge
labelling `ℓ : E(S) → I` of a graph `S`, and prove the monotonicity lemma
`lem:P-monotone`.
-/

open Cardinal

namespace Erdos1177

universe u

/-- **Property `P(S, I, κ)`** for an edge labelling `ℓ : E(S) → I`.
For every colouring `c : V(S) → θ` with `θ < κ`, there is a colour `a` such
that, for every label `i ∈ I`, the colour class of `a` contains an edge
labelled `i`. -/
def SimpleGraph.PropertyP {S : Type u} (G : SimpleGraph S) {I : Type u}
    (ℓ : G.edgeSet → I) (κ : Cardinal.{u}) : Prop :=
  ∀ (θ : Cardinal.{u}), θ < κ → ∀ (c : S → θ.out),
    ∃ a : θ.out, ∀ i : I, ∃ (x y : S) (h : G.Adj x y),
      ℓ ⟨s(x, y), h⟩ = i ∧ c x = a ∧ c y = a

/-- **Monotonicity** (`lem:P-monotone`).  If `P(S, I, δ)` holds and
`κ ≤ δ`, then `P(S, I, κ)` holds. -/
theorem SimpleGraph.PropertyP.mono {S : Type u} {G : SimpleGraph S} {I : Type u}
    {ℓ : G.edgeSet → I} {κ δ : Cardinal.{u}} (h : SimpleGraph.PropertyP G ℓ δ)
    (hκδ : κ ≤ δ) :
    SimpleGraph.PropertyP G ℓ κ := by
  intro θ hθ c
  exact h θ (lt_of_lt_of_le hθ hκδ) c

end Erdos1177
