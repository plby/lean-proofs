import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Basic definitions for Erdős Problem 550

This file sets up the basic objects used throughout the formalisation of
*A Resolution of Erdős Problem 550 on Tree versus Complete Multipartite
Ramsey Numbers* (E. Li).

We work with the standard graph-Ramsey-number convention: a red–blue colouring
of the complete graph `K_N` is modelled by a single simple graph `G` on `Fin N`
(the *red* graph), the *blue* graph being its complement `Gᶜ`.  A *red copy* of a
graph `J` is a graph-containment `J ⊑ G`, and a *blue copy* of `L` is
`L ⊑ Gᶜ`.

`SimpleGraph.IsContained` (notation `⊑`) is the (non-induced) subgraph-copy
relation from Mathlib.
-/

open SimpleGraph

namespace Erdos550

/-- The (two-colour) Ramsey number `R(J, L)`: the least `N` such that every
red–blue colouring of `K_N` (modelled by a red graph `G` on `Fin N`) contains a
red copy of `J` or a blue copy of `L`. -/
noncomputable def ramsey {α β : Type*} (J : SimpleGraph α) (L : SimpleGraph β) : ℕ :=
  sInf {N | ∀ G : SimpleGraph (Fin N), J ⊑ G ∨ L ⊑ Gᶜ}

/-- The set of `N` that "witness" `R(J,L)`: those `N` for which every colouring of
`K_N` already contains a red `J` or a blue `L`. -/
def RamseyGood {α β : Type*} (J : SimpleGraph α) (L : SimpleGraph β) : Set ℕ :=
  {N | ∀ G : SimpleGraph (Fin N), J ⊑ G ∨ L ⊑ Gᶜ}

/-- The complete multipartite graph `K_{m 0, …, m (k-1)}` whose `i`-th independent
class has order `m i`. -/
noncomputable def Kmult (k : ℕ) (m : Fin k → ℕ) :
    SimpleGraph ((i : Fin k) × Fin (m i)) :=
  completeMultipartiteGraph (fun i => Fin (m i))

/-- The complete bipartite graph `K_{a,b}`. -/
abbrev Kbip (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) :=
  completeBipartiteGraph (Fin a) (Fin b)

/-- To bound a Ramsey number from above it suffices to exhibit a witness `N`. -/
theorem ramsey_le_of_mem {α β : Type*} (J : SimpleGraph α) (L : SimpleGraph β)
    {N : ℕ} (hN : N ∈ RamseyGood J L) : ramsey J L ≤ N :=
  Nat.sInf_le hN

/-- If the family of witnesses is nonempty, then `R(J,L)` is itself a witness:
every colouring of `K_{R(J,L)}` contains a red `J` or a blue `L`. -/
theorem ramsey_mem {α β : Type*} (J : SimpleGraph α) (L : SimpleGraph β)
    (hne : (RamseyGood J L).Nonempty) : ramsey J L ∈ RamseyGood J L :=
  Nat.sInf_mem hne

/-- Ramsey numbers against `Kmult k f` only depend on `f` (congruence under
function equality), avoiding dependent-type rewriting. -/
theorem ramsey_Kmult_congr {V : Type*} (T : SimpleGraph V) {k : ℕ}
    {f g : Fin k → ℕ} (h : f = g) : ramsey T (Kmult k f) = ramsey T (Kmult k g) := by
  subst h; rfl

end Erdos550
