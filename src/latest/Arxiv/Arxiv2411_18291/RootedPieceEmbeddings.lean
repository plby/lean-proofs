import Arxiv.Arxiv2411_18291.DisjointPieceEmbeddings
import Arxiv.Arxiv2411_18291.EmbeddingExtensions

/-!
# Embedding a frame while preserving its base map

Use the given base injection as the bijection on the root piece, and choose
bijections on the disjoint private pieces. Equal private sizes and compatible
root images then produce an embedding of the entire frame.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [DecidableEq W] [DecidableEq V]

omit [DecidableEq V] in
def rootedPieces (F : Finset W) (Q : I → Finset W) : Option I → Finset W :=
  fun i => i.elim F (fun j => Q j \ F)

omit [Fintype I] [DecidableEq V] in
theorem rootedPieces_pairwise (F : Finset W) (Q : I → Finset W)
    (hQ : Pairwise fun i j => Disjoint (Q i \ F) (Q j \ F)) :
    Pairwise fun i j => Disjoint (rootedPieces F Q i) (rootedPieces F Q j) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
          exact disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hy).2 hx)
  | some i =>
      cases j with
      | none => exact disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hx).2 hy)
      | some j => exact hQ (fun h => hij (congrArg some h))

omit [DecidableEq V] in
theorem rootedPieces_union (F : Finset W) (Q : I → Finset W) :
    univ.biUnion (rootedPieces F Q) = F ∪ univ.biUnion Q := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp hx
    cases i with
    | none => exact mem_union_left _ hi
    | some i => exact mem_union_right _ (mem_biUnion.mpr
        ⟨i, mem_univ _, (mem_sdiff.mp hi).1⟩)
  · intro hx
    rcases mem_union.mp hx with hF | hQ
    · exact mem_biUnion.mpr ⟨none, mem_univ _, hF⟩
    · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hQ
      by_cases hF : x ∈ F
      · exact mem_biUnion.mpr ⟨none, mem_univ _, hF⟩
      · exact mem_biUnion.mpr ⟨some i, mem_univ _, mem_sdiff.mpr ⟨hi, hF⟩⟩

omit [Fintype I] [DecidableEq W] [DecidableEq V] in
def rootEquivUsed {F : Finset W} (φ : F ↪ V) : F ≃ usedVertices φ :=
  Equiv.ofBijective (fun x => ⟨φ x, (mem_usedVertices φ _).mpr ⟨x, rfl⟩⟩) (by
    constructor
    · intro x y hxy
      exact φ.injective (congrArg Subtype.val hxy)
    · rintro ⟨v, hv⟩
      obtain ⟨x, hx⟩ := (mem_usedVertices φ v).mp hv
      exact ⟨x, Subtype.ext hx⟩)

theorem exists_rooted_piece_embedding {F : Finset W} (φ : F ↪ V)
    (Q : I → Finset W) (T : I → Finset V)
    (hQ : Pairwise fun i j => Disjoint (Q i \ F) (Q j \ F))
    (hT : Pairwise fun i j => Disjoint (T i \ usedVertices φ) (T j \ usedVertices φ))
    (hcard : ∀ i, (Q i \ F).card = (T i \ usedVertices φ).card)
    (hroot : ∀ i (x : F), x.val ∈ Q i → φ x ∈ T i) :
    ∃ f : ↥(F ∪ univ.biUnion Q) ↪ V,
      (∀ x : F, f ⟨x.val, mem_union_left _ x.property⟩ = φ x) ∧
      ∀ i (x : Q i), f ⟨x.val, mem_union_right _
        (mem_biUnion.mpr ⟨i, mem_univ _, x.property⟩)⟩ ∈ T i := by
  let e : ∀ i : Option I, rootedPieces F Q i ≃ rootedPieces (usedVertices φ) T i :=
    fun i => match i with
      | none => rootEquivUsed φ
      | some i => (Q i \ F).equivOfCardEq (hcard i)
  obtain ⟨g, hg⟩ := exists_embedding_of_disjoint_pieces
    (rootedPieces F Q) (rootedPieces (usedVertices φ) T)
      (rootedPieces_pairwise F Q hQ) (rootedPieces_pairwise (usedVertices φ) T hT) e
  let ι : ↥(F ∪ univ.biUnion Q) ↪ ↥(univ.biUnion (rootedPieces F Q)) :=
    ⟨fun x => ⟨x.val, by rw [rootedPieces_union]; exact x.property⟩,
      fun _ _ hxy => Subtype.ext
        (congrArg (fun x : ↥(univ.biUnion (rootedPieces F Q)) => x.val) hxy)⟩
  let f := ι.trans g
  have hf (x : F) : f ⟨x.val, mem_union_left _ x.property⟩ = φ x := hg none x
  refine ⟨f, hf, ?_⟩
  intro i x
  by_cases hxF : x.val ∈ F
  · have he : f ⟨x.val, mem_union_right _
        (mem_biUnion.mpr ⟨i, mem_univ _, x.property⟩)⟩ = φ ⟨x.val, hxF⟩ := hf ⟨x.val, hxF⟩
    rw [he]
    exact hroot i ⟨x.val, hxF⟩ x.property
  · let y : ↥(Q i \ F) := ⟨x.val, mem_sdiff.mpr ⟨x.property, hxF⟩⟩
    have he : f ⟨x.val, mem_union_right _
        (mem_biUnion.mpr ⟨i, mem_univ _, x.property⟩)⟩ = (e (some i) y).val := hg (some i) y
    rw [he]
    exact (mem_sdiff.mp (e (some i) y).property).1

end Arxiv2411_18291
