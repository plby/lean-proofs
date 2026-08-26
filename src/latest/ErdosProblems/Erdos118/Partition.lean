import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.RelIso.Set
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Exact ordinal partition relations for Erdős Problem 118

These are foundational equivalences and transport results, not the disproof.
The infinite homogeneous set is measured by `Ordinal.typeLT`, never by its
cardinality. The finite homogeneous set is measured by its cardinality.
-/

open Cardinal Ordinal

namespace Erdos118

universe u

/-- The usual relation `α → (β,n)²`, with an ordinal red target. -/
def Partition (α β : Ordinal.{u}) (n : ℕ) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ S, red.IsClique S ∧ typeLT S = β) ∨
      ∃ S, blue.IsClique S ∧ #S = n

/-- Cardinal and finite-set formulations of a finite clique agree. -/
theorem exists_cardinal_clique_iff {X : Type u} (G : SimpleGraph X) (n : ℕ) :
    (∃ S : Set X, G.IsClique S ∧ #S = n) ↔
      ∃ s : Finset X, G.IsNClique n s := by
  constructor
  · rintro ⟨S, hS, hcard⟩
    obtain ⟨s, hs, hn⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hcard
    exact ⟨s, hs.symm ▸ hS, hn⟩
  · rintro ⟨s, hs, hn⟩
    exact ⟨s, hs, by simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset, hn]⟩

theorem cliqueFree_iff_no_cardinal_clique {X : Type u}
    (G : SimpleGraph X) (n : ℕ) :
    G.CliqueFree n ↔ ¬ ∃ S : Set X, G.IsClique S ∧ #S = n := by
  rw [exists_cardinal_clique_iff]
  exact not_exists.symm

/-- Order type of the range of an order embedding, including proper ranges. -/
theorem type_range {X Y : Type u} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y] (e : X ↪o Y) :
    typeLT (Set.range e) = typeLT X := by
  let i : X ≃o Set.range e :=
    { toEquiv := Equiv.ofInjective e e.injective
      map_rel_iff' := e.le_iff_le }
  exact i.ordinalType_congr.symm

/-- A clique has the required order type exactly when it is the range of
an order embedding of that type. -/
theorem exists_clique_type_iff {X : Type u} [LinearOrder X] [WellFoundedLT X]
    (G : SimpleGraph X) (β : Ordinal.{u}) :
    (∃ S : Set X, G.IsClique S ∧ typeLT S = β) ↔
      ∃ e : β.ToType ↪o X, ∀ a b, a ≠ b → G.Adj (e a) (e b) := by
  constructor
  · rintro ⟨S, hS, htype⟩
    have heq : typeLT β.ToType = typeLT S := by
      rw [Ordinal.type_toType, htype]
    obtain ⟨i⟩ := Ordinal.type_eq.mp heq
    let j := OrderIso.ofRelIsoLT i
    refine ⟨j.toOrderEmbedding.trans (OrderEmbedding.subtype S), ?_⟩
    intro a b hab
    exact hS (j a).2 (j b).2 (fun h ↦ hab (j.injective (Subtype.ext h)))
  · rintro ⟨e, he⟩
    refine ⟨Set.range e, ?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
      exact he a b (fun h ↦ hab (congrArg e h))
    · rw [type_range, Ordinal.type_toType]

theorem exists_independent_type_iff {X : Type u}
    [LinearOrder X] [WellFoundedLT X] (G : SimpleGraph X) (β : Ordinal.{u}) :
    (∃ S : Set X, G.IsIndepSet S ∧ typeLT S = β) ↔
      ∃ e : β.ToType ↪o X, ∀ a b, a ≠ b → ¬ G.Adj (e a) (e b) := by
  constructor
  · intro h
    have hclique : ∃ S : Set X, Gᶜ.IsClique S ∧ typeLT S = β := by
      simpa only [SimpleGraph.isClique_compl] using h
    obtain ⟨e, he⟩ := (exists_clique_type_iff Gᶜ β).mp hclique
    exact ⟨e, fun a b hab ↦ ((G.compl_adj _ _).mp (he a b hab)).2⟩
  · rintro ⟨e, he⟩
    have hclique := (exists_clique_type_iff Gᶜ β).mpr
      ⟨e, fun a b hab ↦ (G.compl_adj _ _).mpr ⟨e.injective.ne hab, he a b hab⟩⟩
    simpa only [SimpleGraph.isClique_compl] using hclique

/-- One-graph formulation, retaining the exact red order type. -/
theorem partition_iff (α β : Ordinal.{u}) (n : ℕ) :
    Partition α β n ↔ ∀ G : SimpleGraph α.ToType,
      G.CliqueFree n → ∃ S, G.IsIndepSet S ∧ typeLT S = β := by
  constructor
  · intro h G hfree
    rcases h Gᶜ G isCompl_compl.symm with hred | hblue
    · simpa only [SimpleGraph.isClique_compl] using hred
    · exact ((cliqueFree_iff_no_cardinal_clique G n).mp hfree hblue).elim
  · intro h red blue hcompl
    by_cases hfree : blue.CliqueFree n
    · obtain ⟨S, hS, htype⟩ := h blue hfree
      refine Or.inl ⟨S, ?_, htype⟩
      rw [hcompl.eq_compl, SimpleGraph.isClique_compl]
      exact hS
    · exact Or.inr (not_not.mp
        (fun hno ↦ hfree ((cliqueFree_iff_no_cardinal_clique blue n).mpr hno)))

theorem partition_iff_orderEmbedding (α β : Ordinal.{u}) (n : ℕ) :
    Partition α β n ↔ ∀ G : SimpleGraph α.ToType,
      G.CliqueFree n → ∃ e : β.ToType ↪o α.ToType,
        ∀ a b, a ≠ b → ¬ G.Adj (e a) (e b) := by
  rw [partition_iff]
  simp only [exists_independent_type_iff]

/-- The graph criterion for a negative partition relation is an equivalence,
not a hypothesis asserting the desired counterexample exists. -/
theorem not_partition_iff (α β : Ordinal.{u}) (n : ℕ) :
    ¬ Partition α β n ↔ ∃ G : SimpleGraph α.ToType,
      G.CliqueFree n ∧ ∀ e : β.ToType ↪o α.ToType,
        ∃ a b, a ≠ b ∧ G.Adj (e a) (e b) := by
  rw [partition_iff_orderEmbedding]
  simp only [not_forall, not_exists, not_not, exists_prop]

theorem partition_mono_finite {α β : Ordinal.{u}} {m n : ℕ} (hmn : m ≤ n)
    (h : Partition α β n) : Partition α β m := by
  rw [partition_iff] at h ⊢
  intro G hfree
  exact h G (hfree.mono hmn)

theorem not_partition_mono_finite {α β : Ordinal.{u}} {m n : ℕ} (hmn : m ≤ n)
    (h : ¬ Partition α β m) : ¬ Partition α β n :=
  fun hp ↦ h (partition_mono_finite hmn hp)

/-- Pulling back a finite-clique-free graph along an injection preserves
finite clique exclusion. -/
theorem cliqueFree_comap {X Y : Type u} (G : SimpleGraph Y) {n : ℕ}
    (hG : G.CliqueFree n) (e : X ↪ Y) : (G.comap e).CliqueFree n := by
  classical
  intro s hs
  apply hG (s.map e)
  refine ⟨?_, by simpa using hs.card_eq⟩
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
  exact hs.isClique ha hb (fun hab ↦ hxy (congrArg e hab))

/-- Transport a concrete negative graph through an order isomorphism.
No coloring theorem is supplied as an assumption: both graph obligations
remain explicit and must be proved for the chosen construction. -/
theorem not_partition_of_model {X : Type u}
    [LinearOrder X] [WellFoundedLT X] {α β : Ordinal.{u}} {n : ℕ}
    (i : α.ToType ≃o X) (G : SimpleGraph X) (hfree : G.CliqueFree n)
    (hhit : ∀ e : β.ToType ↪o X, ∃ a b, a ≠ b ∧ G.Adj (e a) (e b)) :
    ¬ Partition α β n := by
  apply (not_partition_iff α β n).mpr
  refine ⟨G.comap i, cliqueFree_comap G hfree i.toEquiv.toEmbedding, ?_⟩
  intro e
  exact hhit (e.trans i.toOrderEmbedding)

/-- The correct local consequence of the positive contradiction hypothesis.
This does not strengthen the bound to an arbitrarily chosen reservoir. -/
theorem neighborhood_type_lt {α : Ordinal.{u}} (G : SimpleGraph α.ToType)
    (htri : G.CliqueFree 3)
    (hno : ¬ ∃ S, G.IsIndepSet S ∧ typeLT S = α) (x : α.ToType) :
    typeLT (G.neighborSet x) < α := by
  apply lt_of_le_of_ne
  · simpa only [Ordinal.type_toType] using Ordinal.type_set_le (G.neighborSet x)
  · intro heq
    exact hno ⟨G.neighborSet x, G.isIndepSet_neighborSet_of_triangleFree htri x,
      heq⟩

end Erdos118
