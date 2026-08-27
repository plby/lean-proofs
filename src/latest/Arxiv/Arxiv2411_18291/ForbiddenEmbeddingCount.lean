import Arxiv.Arxiv2411_18291.EmbeddingCountBounds
import Arxiv.Arxiv2411_18291.GraphBoundedness

/-!
# Embeddings hitting a bounded forbidden graph

Fix the images of every free vertex except one vertex of the edge under
consideration. The remaining image must lie in a neighborhood of the
forbidden graph. Summing this degree bound over the assignments of the
other vertices gives the forbidden-choice estimate for random greedy
extensions.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [DecidableEq W] {F : Finset W} {r : ℕ}

/-- The assignments retained after forgetting one vertex of an extension. -/
def forgetExtensionVertex (φ : F ↪ V) (x : W) (f : EmbeddingExtension φ) :
    FreeVertices (insert x F) → V := fun y => f.val y.val

theorem EmbeddingExtension.agree_off_of_forget_eq (φ : F ↪ V) (x : W)
    {f g : EmbeddingExtension φ}
    (h : forgetExtensionVertex φ x f = forgetExtensionVertex φ x g)
    {y : W} (hy : y ≠ x) : f.val y = g.val y := by
  by_cases hyF : y ∈ F
  · exact (f.property ⟨y, hyF⟩).trans (g.property ⟨y, hyF⟩).symm
  · exact congrFun h ⟨y, by simp [hy, hyF]⟩

theorem EmbeddingExtension.ext_of_forget_eq (φ : F ↪ V) (x : W)
    {f g : EmbeddingExtension φ}
    (h : forgetExtensionVertex φ x f = forgetExtensionVertex φ x g)
    (hx : f.val x = g.val x) : f = g := by
  apply Subtype.ext
  apply DFunLike.ext
  intro y
  by_cases hy : y = x
  · simpa only [hy] using hx
  · exact EmbeddingExtension.agree_off_of_forget_eq φ x h hy

/-- Delete a specified vertex of a nonempty uniform edge. -/
def eraseBlock (e : Block W (r + 1)) (x : W) (hx : x ∈ e.val) : Block W r :=
  ⟨e.val.erase x, by rw [card_erase_of_mem hx, e.property]; omega⟩

variable [DecidableEq V]

omit [DecidableEq W] [DecidableEq V] in
theorem mapBlock_eq_of_agree {f g : W ↪ V} (e : Block W r)
    (h : ∀ x ∈ e.val, f x = g x) : mapBlock f e = mapBlock g e := by
  apply Subtype.ext
  change e.val.map f = e.val.map g
  ext v
  simp only [mem_map]
  constructor <;> rintro ⟨x, hx, rfl⟩
  · exact ⟨x, hx, (h x hx).symm⟩
  · exact ⟨x, hx, h x hx⟩

theorem mapBlock_eq_extend_erase (f : W ↪ V) (e : Block W (r + 1))
    (x : W) (hx : x ∈ e.val) :
    ∃ hv : f x ∉ (mapBlock f (eraseBlock e x hx)).val,
      extendBlock (mapBlock f (eraseBlock e x hx)) (f x) hv = mapBlock f e := by
  have hv : f x ∉ (mapBlock f (eraseBlock e x hx)).val := by
    simp [mapBlock, eraseBlock]
  refine ⟨hv, Subtype.ext ?_⟩
  change insert (f x) ((e.val.erase x).map f) = e.val.map f
  rw [← map_insert, insert_erase hx]

variable [Fintype W] [Fintype V]

def forbiddenEdgeExtensions (φ : F ↪ V) (e : Block W (r + 1))
    (B : Hypergraph V (r + 1)) : Finset (EmbeddingExtension φ) :=
  univ.filter fun f => mapBlock f.val e ∈ B

/-- In a fiber, every forbidden extension is determined by one neighbor. -/
theorem forbiddenEdgeExtensions_fiber_le (φ : F ↪ V) (e : Block W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ)
    (hθ : 0 ≤ θ) (x : W) (hx : x ∈ e.val)
    (a : FreeVertices (insert x F) → V) :
    (((forbiddenEdgeExtensions φ e B).filter
      (fun f => forgetExtensionVertex φ x f = a)).card : ℝ) ≤ θ * Fintype.card V := by
  classical
  let s := (forbiddenEdgeExtensions φ e B).filter
    (fun f => forgetExtensionVertex φ x f = a)
  by_cases hs : s.Nonempty
  · obtain ⟨f₀, hf₀⟩ := hs
    let S := mapBlock f₀.val (eraseBlock e x hx)
    have hf₀a : forgetExtensionVertex φ x f₀ = a := (mem_filter.mp hf₀).2
    have hc : s.card ≤ (neighbors B S).card := by
      apply card_le_card_of_injOn (fun f : EmbeddingExtension φ => f.val x)
      · intro f hf
        obtain ⟨hfB, hfa⟩ := mem_filter.mp hf
        have hface : mapBlock f.val (eraseBlock e x hx) = S := by
          apply mapBlock_eq_of_agree
          intro y hy
          exact EmbeddingExtension.agree_off_of_forget_eq φ x (hfa.trans hf₀a.symm)
            (mem_erase.mp hy).1
        obtain ⟨hv, he⟩ := mapBlock_eq_extend_erase f.val e x hx
        have hn : f.val x ∈ neighbors B (mapBlock f.val (eraseBlock e x hx)) :=
          (mem_neighbors _ _ _).mpr ⟨hv, he.symm ▸ (mem_filter.mp hfB).2⟩
        simpa only [hface, Finset.mem_coe] using hn
      · intro f hf g hg hfg
        exact EmbeddingExtension.ext_of_forget_eq φ x
          ((mem_filter.mp hf).2.trans (mem_filter.mp hg).2.symm) hfg
    exact (by exact_mod_cast hc : (s.card : ℝ) ≤ (neighbors B S).card).trans
      (by rw [card_neighbors_eq_degree]; exact (hB S).le)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    change (s.card : ℝ) ≤ _
    rw [he, card_empty, Nat.cast_zero]
    exact mul_nonneg hθ (Nat.cast_nonneg _)

omit [DecidableEq W] in
/-- A single new edge excludes at most `θ * n^m` extensions. -/
theorem forbiddenEdgeExtensions_card_le (φ : F ↪ V) (e : Block W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ)
    (hθ : 0 ≤ θ) (he : ¬ e.val ⊆ F) :
    ((forbiddenEdgeExtensions φ e B).card : ℝ) ≤
      θ * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by
  classical
  obtain ⟨x, hxe, hxF⟩ := not_subset.mp he
  have hc : Fintype.card (FreeVertices (insert x F)) = Fintype.card W - F.card - 1 := by
    simp only [FreeVertices, Fintype.card_subtype_compl, Fintype.card_coe,
      card_insert_of_notMem hxF]
    omega
  have hpos : 1 ≤ Fintype.card W - F.card := by
    have hi := card_le_univ (insert x F)
    rw [card_insert_of_notMem hxF] at hi
    omega
  have hfib := card_eq_sum_card_fiberwise
    (s := forbiddenEdgeExtensions φ e B)
    (t := (univ : Finset (FreeVertices (insert x F) → V)))
    (f := forgetExtensionVertex φ x) (fun _ _ => mem_univ _)
  calc
    _ = ∑ a : FreeVertices (insert x F) → V,
        (((forbiddenEdgeExtensions φ e B).filter
          (fun f => forgetExtensionVertex φ x f = a)).card : ℝ) := by
      exact_mod_cast hfib
    _ ≤ ∑ _a : FreeVertices (insert x F) → V, θ * Fintype.card V :=
      sum_le_sum fun a _ => forbiddenEdgeExtensions_fiber_le φ e B hB hθ x hxe a
    _ = θ * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by
      simp only [sum_const, card_univ, Fintype.card_fun, hc, nsmul_eq_mul, Nat.cast_pow]
      conv_rhs => rw [← Nat.sub_add_cancel hpos, pow_succ]
      ring

end Arxiv2411_18291
