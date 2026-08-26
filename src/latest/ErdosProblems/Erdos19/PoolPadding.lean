import ErdosProblems.Erdos19.CapacityColoring

/-! # Adding a finite unused vertex pool

Unlike uniformization, this construction leaves every support unchanged up to
an injective relabeling. Its extra vertices are reserved for capacity augmentation.
-/

namespace Erdos19.PoolPadding

open Finset Erdos76 Erdos76.FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

def realVertices (H : FiniteHypergraph V E) (p : ℕ) : Finset (V ⊕ Fin p) :=
  H.vertexSet.image Sum.inl

def dummyVertices (H : FiniteHypergraph V E) (p : ℕ) : Finset (V ⊕ Fin p) :=
  univ.image Sum.inr

def withPool (H : FiniteHypergraph V E) (p : ℕ) : FiniteHypergraph (V ⊕ Fin p) E where
  vertexSet := realVertices H p ∪ dummyVertices H p
  support e := (H.support e).image Sum.inl
  support_subset_vertexSet := by
    intro e x hx
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
    exact mem_union_left _ (mem_image.mpr ⟨v, H.support_subset_vertexSet e hv, rfl⟩)

@[simp] theorem card_realVertices (H : FiniteHypergraph V E) (p : ℕ) :
    (realVertices H p).card = H.vertexSet.card := card_image_of_injective _ Sum.inl_injective

@[simp] theorem card_dummyVertices (H : FiniteHypergraph V E) (p : ℕ) :
    (dummyVertices H p).card = p := by
  rw [dummyVertices, card_image_of_injective _ Sum.inr_injective]
  simp

theorem disjoint_real_dummy (H : FiniteHypergraph V E) (p : ℕ) :
    Disjoint (realVertices H p) (dummyVertices H p) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v, _, rfl⟩ := mem_image.mp hx
  obtain ⟨w, _, heq⟩ := mem_image.mp hy
  exact Sum.inr_ne_inl heq

@[simp] theorem vertexSet_card (H : FiniteHypergraph V E) (p : ℕ) :
    (withPool H p).vertexSet.card = H.vertexSet.card + p := by
  rw [withPool, card_union_of_disjoint (disjoint_real_dummy H p),
    card_realVertices, card_dummyVertices]

@[simp] theorem mem_support_inl (H : FiniteHypergraph V E) (p : ℕ) (e : E) (v : V) :
    Sum.inl v ∈ (withPool H p).support e ↔ v ∈ H.support e := by simp [withPool]

@[simp] theorem not_mem_support_inr (H : FiniteHypergraph V E) (p : ℕ) (e : E) (v : Fin p) :
    Sum.inr v ∉ (withPool H p).support e := by simp [withPool]

@[simp] theorem mem_real_inl (H : FiniteHypergraph V E) (p : ℕ) (v : V) :
    Sum.inl v ∈ realVertices H p ↔ v ∈ H.vertexSet := by simp [realVertices]

@[simp] theorem not_mem_real_inr (H : FiniteHypergraph V E) (p : ℕ) (v : Fin p) :
    Sum.inr v ∉ realVertices H p := by simp [realVertices]

theorem support_subset_real (H : FiniteHypergraph V E) (p : ℕ) (e : E) :
    (withPool H p).support e ⊆ realVertices H p := image_subset_image (H.support_subset_vertexSet e)

theorem support_disjoint_dummy (H : FiniteHypergraph V E) (p : ℕ) (e : E) :
    Disjoint ((withPool H p).support e) (dummyVertices H p) :=
  (disjoint_real_dummy H p).mono_left (support_subset_real H p e)

@[simp] theorem support_card (H : FiniteHypergraph V E) (p : ℕ) (e : E) :
    ((withPool H p).support e).card = (H.support e).card :=
  card_image_of_injective _ Sum.inl_injective

@[simp] theorem edgeDegree_inl (H : FiniteHypergraph V E) (p : ℕ) (v : V) :
    (withPool H p).edgeDegree (Sum.inl v) = H.edgeDegree v := by simp [edgeDegree]

@[simp] theorem edgeDegree_inr (H : FiniteHypergraph V E) (p : ℕ) (v : Fin p) :
    (withPool H p).edgeDegree (Sum.inr v) = 0 := by simp [edgeDegree]

@[simp] theorem edgePairDegree_inl_inl (H : FiniteHypergraph V E) (p : ℕ) (u v : V) :
    (withPool H p).edgePairDegree (Sum.inl u) (Sum.inl v) = H.edgePairDegree u v := by
  simp [edgePairDegree]

@[simp] theorem edgePairDegree_inr_left (H : FiniteHypergraph V E) (p : ℕ)
    (u : Fin p) (v : V ⊕ Fin p) :
    (withPool H p).edgePairDegree (Sum.inr u) v = 0 := by simp [edgePairDegree]

@[simp] theorem edgePairDegree_inr_right (H : FiniteHypergraph V E) (p : ℕ)
    (u : V ⊕ Fin p) (v : Fin p) :
    (withPool H p).edgePairDegree u (Sum.inr v) = 0 := by simp [edgePairDegree]

def restrictColoring (H : FiniteHypergraph V E) (p : ℕ) {A : Type*}
    (c : (withPool H p).conflictGraph.Coloring A) : H.conflictGraph.Coloring A :=
  SimpleGraph.Coloring.mk c (by
    intro e f hef
    apply c.valid
    refine ⟨hef.1, ?_⟩
    obtain ⟨v, hv, hv'⟩ := Finset.not_disjoint_iff.mp hef.2
    exact Finset.not_disjoint_iff.mpr
      ⟨Sum.inl v, (mem_support_inl H p e v).mpr hv, (mem_support_inl H p f v).mpr hv'⟩)

theorem real_covered_card (H : FiniteHypergraph V E) (p : ℕ) (S : Finset E) :
    (S.biUnion fun e ↦ (withPool H p).support e ∩ realVertices H p).card =
      (S.biUnion H.support).card := by
  have hinter (e : E) : (withPool H p).support e ∩ realVertices H p =
      (H.support e).image (Sum.inl : V → V ⊕ Fin p) :=
    Finset.inter_eq_left.mpr (support_subset_real H p e)
  simp_rw [hinter]
  have hset : (S.biUnion fun e ↦ (H.support e).image (Sum.inl : V → V ⊕ Fin p)) =
      (S.biUnion H.support).image Sum.inl := by
    ext x
    simp only [mem_biUnion, mem_image]
    constructor
    · rintro ⟨e, he, v, hv, rfl⟩
      exact ⟨v, ⟨e, he, hv⟩, rfl⟩
    · rintro ⟨v, ⟨e, he, hv⟩, rfl⟩
      exact ⟨e, he, v, hv, rfl⟩
  rw [hset, card_image_of_injective _ Sum.inl_injective]

theorem covered_card_le_of_uncovered_bound (H : FiniteHypergraph V E)
    (p : ℕ) (S : Finset E)
    (h : (realVertices H p).card - (dummyVertices H p).card ≤
      (realVertices H p \ (S.biUnion fun e ↦
        (withPool H p).support e ∩ realVertices H p)).card) :
    (S.biUnion H.support).card ≤ p := by
  have hsub : (S.biUnion fun e ↦ (withPool H p).support e ∩ realVertices H p) ⊆
      realVertices H p := by
    intro v hv
    obtain ⟨e, _, he⟩ := mem_biUnion.mp hv
    exact (mem_inter.mp he).2
  have hle := card_le_card hsub
  rw [card_sdiff_of_subset hsub, card_dummyVertices, real_covered_card] at h
  rw [real_covered_card] at hle
  omega

#print axioms covered_card_le_of_uncovered_bound

end Erdos19.PoolPadding
