import ErdosProblems.Erdos118.Imported591.PieceIndiv

open Set Ordinal

namespace Erdos118.Negative.LexFiberBound

universe u

/-!
Order-type estimates for monotone maps, used by the large-level argument.
The fiber bound is an ordinary lexicographic-product embedding; it makes
no uniform-continuation assumption about a subset of an ordinal product.
-/

/-- Turn an order-type inequality into an order embedding. -/
noncomputable def embeddingOfTypeLE
    {X Y : Type u} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder Y] [WellFoundedLT Y]
    (h : typeLT X ≤ typeLT Y) : X ↪o Y := by
  let e := Classical.choice (Ordinal.type_le_iff'.mp h)
  exact OrderEmbedding.ofStrictMono e (fun _ _ hxy ↦ e.map_rel_iff.mpr hxy)

/-- A nondecreasing map with fibers of type at most `eta` bounds its
domain by `eta` times the order type of its codomain. -/
theorem type_le_mul_of_monotone
    {X I : Type u} [LinearOrder X] [WellFoundedLT X]
    [LinearOrder I] [WellFoundedLT I]
    (f : X → I) (hf : Monotone f) (eta : Ordinal.{u})
    (hfinite : ∀ i, typeLT {x : X | f x = i} ≤ eta) :
    typeLT X ≤ eta * typeLT I := by
  let e : (i : I) → {x : X | f x = i} ↪o eta.ToType :=
    fun i ↦ embeddingOfTypeLE (by simpa using hfinite i)
  have same_fiber (i j : I) (hij : i = j) (x : X)
      (hi : f x = i) (hj : f x = j) :
      e i ⟨x, hi⟩ = e j ⟨x, hj⟩ := by
    cases hij
    rfl
  let g : X → I ×ₗ eta.ToType :=
    fun x ↦ toLex (f x, e (f x) ⟨x, rfl⟩)
  have hg : StrictMono g := by
    intro x y hxy
    rcases (hf hxy.le).lt_or_eq with hlt | heq
    · exact Prod.Lex.lt_iff.mpr (Or.inl hlt)
    · apply Prod.Lex.lt_iff.mpr
      refine Or.inr ⟨heq, ?_⟩
      have hinner := (e (f y)).strictMono
        (show (⟨x, heq⟩ : {z : X | f z = f y}) < ⟨y, rfl⟩ from hxy)
      change e (f x) ⟨x, rfl⟩ < e (f y) ⟨y, rfl⟩
      rw [same_fiber (f x) (f y) heq x rfl heq]
      exact hinner
  calc
    typeLT X ≤ typeLT (I ×ₗ eta.ToType) :=
      (OrderEmbedding.ofStrictMono g hg).ltEmbedding.ordinal_type_le
    _ = eta * typeLT I := by
      change Ordinal.type
        (Prod.Lex ((· < ·) : I → I → Prop)
          ((· < ·) : eta.ToType → eta.ToType → Prop)) = _
      rw [Ordinal.type_prod_lex, Ordinal.type_toType]

open Erdos118.Schipperus.K4Core

theorem le_type_of_large
    {X : Type u} [LinearOrder X] [WellFoundedLT X]
    {eta : Ordinal.{u}} {s : Set X}
    (hs : Large eta.ToType s) : eta ≤ typeLT s := by
  simpa only [Ordinal.type_toType] using hs.some.ltEmbedding.ordinal_type_le

/-- For a finitely indivisible ordinal, two parts of smaller type have a
union of smaller type.  The parts need not be consecutive. -/
theorem type_lt_of_parts
    {X : Type u} [LinearOrder X] [WellFoundedLT X]
    (eta : Ordinal.{u}) (hind : FinitelyIndivisible eta.ToType)
    (s : Set X) (hs : typeLT s < eta) (hc : typeLT (sᶜ : Set X) < eta) :
    typeLT X < eta := by
  by_contra h
  have hle : eta ≤ typeLT X := le_of_not_gt h
  let e : eta.ToType ↪o X :=
    embeddingOfTypeLE (by simpa only [Ordinal.type_toType] using hle)
  have hlarge : Large eta.ToType (Set.univ : Set X) := by
    refine ⟨e.trans ?_⟩
    exact
      { toFun := fun x ↦ ⟨x, Set.mem_univ x⟩
        inj' := fun _ _ heq ↦ congrArg Subtype.val heq
        map_rel_iff' := by intro x y; rfl }
  rcases Large.inter_or_diff hind (s := s) hlarge with hS | hC
  · exact (not_le_of_gt hs)
      (le_type_of_large (hS.mono Set.inter_subset_right))
  · apply (not_le_of_gt hc)
    apply le_type_of_large
    exact hC.mono (by intro x hx; exact hx.2)

/-- A set-theoretic union version of `type_lt_of_parts`. -/
theorem type_union_lt
    {X : Type u} [LinearOrder X] [WellFoundedLT X]
    (eta : Ordinal.{u}) (hind : FinitelyIndivisible eta.ToType)
    (s t : Set X) (hs : typeLT s < eta) (ht : typeLT t < eta) :
    typeLT (s ∪ t : Set X) < eta := by
  let U : Set X := s ∪ t
  let P : Set U := {x | x.1 ∈ s}
  let eS : P ↪o s := OrderEmbedding.ofStrictMono
    (fun x ↦ ⟨x.1.1, x.2⟩) (fun _ _ hxy ↦ hxy)
  let eT : (Pᶜ : Set U) ↪o t := OrderEmbedding.ofStrictMono
    (fun x ↦ ⟨x.1.1, by
      rcases x.1.2 with hS | hT
      · exact (x.2 hS).elim
      · exact hT⟩) (fun _ _ hxy ↦ hxy)
  exact type_lt_of_parts eta hind P
    (eS.ltEmbedding.ordinal_type_le.trans_lt hs)
    (eT.ltEmbedding.ordinal_type_le.trans_lt ht)

end Erdos118.Negative.LexFiberBound
