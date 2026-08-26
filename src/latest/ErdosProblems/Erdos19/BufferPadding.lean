import ErdosProblems.Erdos19.PoolPadding

/-! # Disjoint artificial pools for simultaneous buffer capacities -/

namespace Erdos19.BufferPadding

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {V E I : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype I] [DecidableEq I]

def poolSize (p : I → ℕ) : ℕ := Fintype.card (Σ i : I, Fin (p i))

@[simp] theorem poolSize_eq_sum (p : I → ℕ) : poolSize p = ∑ i : I, p i := by
  simp [poolSize]

noncomputable def slotCode (p : I → ℕ) : (Σ i : I, Fin (p i)) ≃ Fin (poolSize p) :=
  Fintype.equivFin _

def buffer (p : I → ℕ) (B : Finset V) : Finset (V ⊕ Fin (poolSize p)) :=
  B.image Sum.inl

noncomputable def pool (p : I → ℕ) (i : I) : Finset (V ⊕ Fin (poolSize p)) :=
  univ.image fun j : Fin (p i) ↦ Sum.inr (slotCode p ⟨i, j⟩)

@[simp] theorem buffer_card (p : I → ℕ) (B : Finset V) : (buffer p B).card = B.card :=
  card_image_of_injective _ Sum.inl_injective

@[simp] theorem pool_card (p : I → ℕ) (i : I) :
    (pool (V := V) p i).card = p i := by
  rw [pool, card_image_of_injective]
  · simp
  · intro j k h
    have hpair := (slotCode p).injective (Sum.inr_injective h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2

theorem buffers_disjoint (p : I → ℕ) (B : I → Finset V)
    (hB : Pairwise fun i j ↦ Disjoint (B i) (B j)) :
    Pairwise fun i j ↦ Disjoint (buffer p (B i)) (buffer p (B j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
  obtain ⟨w, hw, hweq⟩ := mem_image.mp hy
  have hwv : w = v := Sum.inl_injective hweq
  exact disjoint_left.mp (hB hij) hv (hwv ▸ hw)

theorem pools_disjoint (p : I → ℕ) :
    Pairwise fun i j ↦ Disjoint (pool (V := V) p i) (pool p j) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨v, _, rfl⟩ := mem_image.mp hx
  obtain ⟨w, _, hweq⟩ := mem_image.mp hy
  have hpair := (slotCode p).injective (Sum.inr_injective hweq)
  exact hij (congrArg Sigma.fst hpair).symm

theorem pool_subset_dummy (H : FiniteHypergraph V E) (p : I → ℕ) (i : I) :
    pool p i ⊆ PoolPadding.dummyVertices H (poolSize p) := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := mem_image.mp hx
  exact mem_image.mpr ⟨slotCode p ⟨i, v⟩, mem_univ _, rfl⟩

theorem pool_subset_vertexSet (H : FiniteHypergraph V E) (p : I → ℕ) (i : I) :
    pool p i ⊆ (PoolPadding.withPool H (poolSize p)).vertexSet :=
  (pool_subset_dummy H p i).trans subset_union_right

theorem support_disjoint_pool (H : FiniteHypergraph V E) (p : I → ℕ) (e : E) (i : I) :
    Disjoint ((PoolPadding.withPool H (poolSize p)).support e) (pool p i) :=
  (PoolPadding.support_disjoint_dummy H (poolSize p) e).mono_right (pool_subset_dummy H p i)

theorem support_inter_buffer (H : FiniteHypergraph V E) (p : I → ℕ) (B : Finset V) (e : E) :
    (PoolPadding.withPool H (poolSize p)).support e ∩ buffer p B =
      (H.support e ∩ B).image Sum.inl := by
  exact (image_inter (H.support e) B Sum.inl_injective).symm

@[simp] theorem support_inter_buffer_card (H : FiniteHypergraph V E)
    (p : I → ℕ) (B : Finset V) (e : E) :
    ((PoolPadding.withPool H (poolSize p)).support e ∩ buffer p B).card =
      (H.support e ∩ B).card := by
  rw [support_inter_buffer, card_image_of_injective _ Sum.inl_injective]

theorem uncovered_buffer_card (H : FiniteHypergraph V E) (p : I → ℕ)
    (B : Finset V) (S : Finset E) :
    (buffer p B \ (S.biUnion fun e ↦
      (PoolPadding.withPool H (poolSize p)).support e ∩ buffer p B)).card =
      (B \ S.biUnion (fun e ↦ H.support e ∩ B)).card := by
  simp_rw [support_inter_buffer]
  rw [← Finset.biUnion_image]
  change (B.image Sum.inl \ (S.biUnion fun e ↦ H.support e ∩ B).image Sum.inl).card = _
  rw [← image_sdiff _ _ Sum.inl_injective, card_image_of_injective _ Sum.inl_injective]

#print axioms uncovered_buffer_card
#print axioms pools_disjoint

end Erdos19.BufferPadding
