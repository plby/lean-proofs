import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Order

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite closure layerings

This interface records the part of the closure construction needed by the
uncountable complete-bipartite forcing argument.  Its implementation will be
kept separate: in particular, the eventual construction must use
singular-cardinal-safe bounds for its countable closure stages.
-/

namespace Erdos593

universe u

/-- A rank decomposition closed under a finite closure operator on `r`-sets.

The fibres are required to be smaller than the ambient carrier.  The closure
condition says that whenever every member of an `r`-set is earlier than `v`,
then every output of the closure operator on that set is earlier than `v` as
well. -/
structure FiniteClosureLayering {V : Type u} (r : ℕ)
    (Φ : {s : Finset V // s.card = r} → Finset V)
    (I : Type u) [LinearOrder I] where
  rank : V → I
  fiber_lt : ∀ i, Cardinal.mk {x : V // rank x = i} < Cardinal.mk V
  earlier_closed : ∀ (v : V) (s : Finset V) (hs : s.card = r),
    (∀ x ∈ s, rank x < rank v) →
    ∀ y ∈ Φ ⟨s, hs⟩, rank y < rank v

namespace FiniteClosureLayering

variable {V : Type u} {r : ℕ}
variable {Φ : {s : Finset V // s.card = r} → Finset V}
variable {I : Type u} [LinearOrder I]

/-- A point cannot occur in the closure of an `r`-set all of whose points are
strictly earlier than it. -/
theorem not_mem_of_all_rank_lt
    (L : FiniteClosureLayering r Φ I) (v : V) (s : Finset V)
    (hs : s.card = r) (hsmaller : ∀ x ∈ s, L.rank x < L.rank v) :
    v ∉ Φ ⟨s, hs⟩ := by
  intro hv
  exact (lt_irrefl _ (L.earlier_closed v s hs hsmaller v hv))

end FiniteClosureLayering

end Erdos593
