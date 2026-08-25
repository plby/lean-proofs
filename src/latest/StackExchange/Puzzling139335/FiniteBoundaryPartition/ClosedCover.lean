import Mathlib.Topology.Connected.Basic

/-!
# Connected sets in finite closed covers

A finite closed cover whose members do not overlap on a preconnected set
cannot change its covering member along that set.
-/

open Set

namespace Puzzling139335

variable {X ι : Type*} [TopologicalSpace X] [Finite ι]
variable {S : Set X} {T : ι → Set X}

/-- A member of a finite closed cover that meets a preconnected set contains
the whole set, provided the cover members are disjoint on that set. -/
theorem subset_of_finite_closed_cover (hS : IsPreconnected S)
    (hclosed : ∀ i, IsClosed (T i)) (hcover : S ⊆ ⋃ i, T i)
    (hdis : Pairwise fun i j => Disjoint (S ∩ T i) (S ∩ T j))
    {i : ι} (hi : (S ∩ T i).Nonempty) : S ⊆ T i := by
  classical
  let V : Set X := ⋃ j : {j : ι // j ≠ i}, T j
  have hV : IsClosed V := isClosed_iUnion_of_finite fun j => hclosed j
  have hsplit : S ⊆ T i ∪ V := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (mem_iUnion_of_mem ⟨j, hji⟩ hj)
  intro x hx
  by_contra hxi
  have hxV : x ∈ V := (hsplit hx).resolve_left hxi
  obtain ⟨y, hyS, hyi, hyV⟩ :=
    isPreconnected_closed_iff.mp hS (T i) V (hclosed i) hV hsplit hi ⟨x, hx, hxV⟩
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hyV
  exact Set.disjoint_left.mp (hdis j.property.symm) ⟨hyS, hyi⟩ ⟨hyS, hyj⟩

/-- A connected set covered by finitely many closed sets that are pairwise
disjoint on it is contained in one covering member. -/
theorem exists_subset_of_finite_closed_cover (hS : IsConnected S)
    (hclosed : ∀ i, IsClosed (T i)) (hcover : S ⊆ ⋃ i, T i)
    (hdis : Pairwise fun i j => Disjoint (S ∩ T i) (S ∩ T j)) :
    ∃ i, S ⊆ T i := by
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  exact ⟨i, subset_of_finite_closed_cover hS.isPreconnected hclosed hcover hdis
    ⟨x, hx, hi⟩⟩

end Puzzling139335
