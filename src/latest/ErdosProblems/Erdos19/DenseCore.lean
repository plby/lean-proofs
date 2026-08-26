import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

/-!
# A dense core with a greedily colorable remainder

Taking a largest induced subgraph of prescribed minimum degree gives the
peeling property needed in the large-edge reordering argument. This separates
the elementary ordering step from the hypergraph pair-volume estimates.
-/

namespace Erdos19

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V]

def IsDenseCore (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ∀ v ∈ S, k ≤ (S.filter (G.Adj v)).card

/-- Every nonempty uncolored subset outside `S` has a vertex with fewer
than `k` neighbors among itself and the already colored core `S`. -/
def IsPeelableOutside (G : SimpleGraph V) (A S : Finset V) (k : ℕ) : Prop :=
  ∀ T : Finset V, T ⊆ A \ S → T.Nonempty →
    ∃ v ∈ T, ((S ∪ T).filter (G.Adj v)).card < k

theorem exists_dense_core_with_peelable_remainder (G : SimpleGraph V)
    (A : Finset V) (k : ℕ) :
    ∃ S : Finset V, S ⊆ A ∧ IsDenseCore G S k ∧ IsPeelableOutside G A S k := by
  classical
  let candidates := A.powerset.filter fun S ↦ IsDenseCore G S k
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset A), ?_⟩⟩
    intro v hv
    exact (notMem_empty v hv).elim
  obtain ⟨S, hS, hmax⟩ := exists_max_image candidates Finset.card hnonempty
  have hSA : S ⊆ A := mem_powerset.mp (mem_filter.mp hS).1
  have hSdense : IsDenseCore G S k := (mem_filter.mp hS).2
  refine ⟨S, hSA, hSdense, ?_⟩
  intro T hT hTnonempty
  by_contra hnone
  push Not at hnone
  have hTA : T ⊆ A := fun v hv ↦ (mem_sdiff.mp (hT hv)).1
  have hdisjoint : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvT
    exact (mem_sdiff.mp (hT hvT)).2 hvS
  have hdense : IsDenseCore G (S ∪ T) k := by
    intro v hv
    rcases mem_union.mp hv with hvS | hvT
    · exact (hSdense v hvS).trans (card_le_card
        (filter_subset_filter _ subset_union_left))
    · exact hnone v hvT
  have hcand : S ∪ T ∈ candidates :=
    mem_filter.mpr ⟨mem_powerset.mpr (union_subset hSA hTA), hdense⟩
  have hle := hmax (S ∪ T) hcand
  rw [card_union_of_disjoint hdisjoint] at hle
  have hpos := card_pos.mpr hTnonempty
  omega

/-- Restricting the outside ground set preserves relative peelability. -/
theorem IsPeelableOutside.mono {G : SimpleGraph V} {A B S : Finset V} {k : ℕ}
    (h : IsPeelableOutside G A S k) (hBA : B ⊆ A) : IsPeelableOutside G B S k := by
  intro T hT hTnonempty
  apply h T _ hTnonempty
  intro v hv
  obtain ⟨hvB, hvS⟩ := mem_sdiff.mp (hT hv)
  exact mem_sdiff.mpr ⟨hBA hvB, hvS⟩

#print axioms exists_dense_core_with_peelable_remainder

end Erdos19
