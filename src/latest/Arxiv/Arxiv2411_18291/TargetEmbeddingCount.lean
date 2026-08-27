import Arxiv.Arxiv2411_18291.EmbeddingExtensions

/-!
# Extensions mapping an edge to a prescribed target

The free vertices of the source edge map bijectively to the target vertices
outside the root image. There are at most `k!` such maps, where `k` is the
number of free vertices in that edge. Every other free vertex contributes
at most one factor of the ambient size.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [DecidableEq W] [DecidableEq V] {F : Finset W} {r : ℕ}

omit [DecidableEq W] [DecidableEq V] in
theorem EmbeddingExtension.map_roots (φ : F ↪ V) (f : EmbeddingExtension φ) :
    F.map f.val = usedVertices φ := by
  ext v
  simp only [mem_map, mem_usedVertices]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (f.property ⟨x, hx⟩).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, f.property x⟩

theorem EmbeddingExtension.map_free (φ : F ↪ V) (f : EmbeddingExtension φ)
    (s : Finset W) : (s \ F).map f.val = s.map f.val \ usedVertices φ := by
  rw [map_sdiff, EmbeddingExtension.map_roots φ f]

variable [Fintype W] [Fintype V]

def edgeTargetExtensions (φ : F ↪ V) (e : Block W r) (g : Block V r) :
    Finset (EmbeddingExtension φ) := univ.filter fun f => mapBlock f.val e = g

/-- The exact factorial in the paper's one-edge probability estimate. -/
theorem edgeTargetExtensions_card_le (φ : F ↪ V) (e : Block W r) (g : Block V r) :
    (edgeTargetExtensions φ e g).card ≤
      (e.val \ F).card.factorial *
        Fintype.card V ^ (Fintype.card W - F.card - (e.val \ F).card) := by
  classical
  let s := edgeTargetExtensions φ e g
  by_cases hs : s.Nonempty
  · obtain ⟨f₀, hf₀⟩ := hs
    let A := e.val \ F
    let T := g.val \ usedVertices φ
    have hf (f : s) : mapBlock f.val.val e = g := (mem_filter.mp f.property).2
    have himage (f : s) : A.map f.val.val = T := by
      dsimp [A, T]
      rw [EmbeddingExtension.map_free φ f.val]
      change (mapBlock f.val.val e).val \ usedVertices φ = _
      rw [hf f]
    have hT : T.card = A.card := by
      rw [← himage ⟨f₀, hf₀⟩, card_map]
    let record : s → ((A ↪ T) × (FreeVertices (F ∪ e.val) → V)) := fun f =>
      (⟨fun x => ⟨f.val.val x.val, by
          rw [← himage f]
          exact mem_map_of_mem _ x.property⟩,
        fun x y hxy => Subtype.ext (f.val.val.injective (congrArg Subtype.val hxy))⟩,
        fun x => f.val.val x.val)
    have hinj : Function.Injective record := by
      intro f g hfg
      apply Subtype.ext
      apply Subtype.ext
      apply DFunLike.ext
      intro x
      by_cases hxF : x ∈ F
      · exact (f.val.property ⟨x, hxF⟩).trans (g.val.property ⟨x, hxF⟩).symm
      · by_cases hxe : x ∈ e.val
        · have h := DFunLike.congr_fun (congrArg Prod.fst hfg) ⟨x, mem_sdiff.mpr ⟨hxe, hxF⟩⟩
          exact congrArg Subtype.val h
        · exact congrFun (congrArg Prod.snd hfg) ⟨x, by simp [hxF, hxe]⟩
    have hother : Fintype.card (FreeVertices (F ∪ e.val)) =
        Fintype.card W - F.card - A.card := by
      simp only [FreeVertices, Fintype.card_subtype_compl, Fintype.card_coe]
      have hc := card_sdiff_add_card e.val F
      rw [union_comm e.val F] at hc
      dsimp [A]
      omega
    have hc := Fintype.card_le_of_injective record hinj
    simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_embedding_eq,
      Fintype.card_fun, hT, hother, Nat.descFactorial_self] using hc
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ _
    rw [he, card_empty]
    exact Nat.zero_le _

end Arxiv2411_18291
