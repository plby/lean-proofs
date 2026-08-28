import ErdosProblems.Erdos577.TripleCoreUpper

/-! Transport the full U/V/C graph hypotheses, preserving the old score and C upper bound. -/

namespace Erdos577.UniversalTriple

open Finset

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [DecidableRel G.Adj] [DecidableRel H.Adj] in
lemma quad_image_difference (f : G.Copy H) {s t : Finset V} (hq : QuadOn G (s \ t)) :
    QuadOn H (s.image f \ t.image f) := by
  have hinj : Function.Injective (f : V → W) := f.injective
  have hh := hq.image f
  rwa [image_sdiff s t hinj] at hh

lemma score_image_difference (f : G.Copy H) {a s t : Finset V}
    (ha : edgeCount H (a.image f) = edgeCount G a) (hs : edgeCount G a ≤ edgeCount G (s \ t)) :
    edgeCount H (a.image f) ≤ edgeCount H (s.image f \ t.image f) := by
  have hinj : Function.Injective (f : V → W) := f.injective
  have hh := edgeCount_image_le f (s \ t)
  rw [image_sdiff s t hinj] at hh
  exact ha.le.trans (hs.trans hh)

variable {p : Paw G} {a : Finset V} {w u v : V}

omit [DecidableEq V] [DecidableEq W] [DecidableRel G.Adj] [DecidableRel H.Adj] in
lemma image_center (p : Paw G) (f : G.Copy H) : (p.image f).center = f p.center := rfl

omit [DecidableEq V] [DecidableEq W] [DecidableRel G.Adj] [DecidableRel H.Adj] in
lemma image_vertex (p : Paw G) (f : G.Copy H) (i : Fin 4) :
    (p.image f).vertices i = f (p.vertices i) := rfl

theorem UCase.image (s : UCase p a w u v) (f : G.Copy H)
    (ha : edgeCount H (a.image f) = edgeCount G a) :
    UCase (p.image f) (a.image f) (f w) (f u) (f v) := by
  have hinj : Function.Injective (f : V → W) := f.injective
  have hK : (p.image f).triangle ∪ a.image f = (p.triangle ∪ a).image f := by
    rw [Paw.image_triangle, image_union]
  have ht := SimpleGraph.is3Clique_triple_iff.mp s.triangle
  refine {
    triangle := SimpleGraph.is3Clique_triple_iff.mpr
      ⟨f.toHom.map_rel' ht.1, f.toHom.map_rel' ht.2.1, f.toHom.map_rel' ht.2.2⟩
    subset := by
      rw [hK]
      have hh := image_subset_image (f := (f : V → W)) s.subset
      rw [image_sdiff _ _ hinj] at hh
      simpa only [image_insert, image_singleton, image_center, image_vertex] using hh
    bridge := f.toHom.map_rel' s.bridge
    complement_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.complement_quad
    complement_score := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        score_image_difference f ha s.complement_score
    final_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.final_quad
    left_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.left_quad
    right_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.right_quad }

theorem VCase.image (s : VCase p a w u v) (f : G.Copy H)
    (ha : edgeCount H (a.image f) = edgeCount G a) :
    VCase (p.image f) (a.image f) (f w) (f u) (f v) := by
  have hinj : Function.Injective (f : V → W) := f.injective
  have hK : (p.image f).triangle ∪ a.image f = (p.triangle ∪ a).image f := by
    rw [Paw.image_triangle, image_union]
  have ht := SimpleGraph.is3Clique_triple_iff.mp s.triangle
  refine {
    triangle := SimpleGraph.is3Clique_triple_iff.mpr
      ⟨f.toHom.map_rel' ht.1, f.toHom.map_rel' ht.2.1, f.toHom.map_rel' ht.2.2⟩
    subset := by
      rw [hK]
      have hh := image_subset_image (f := (f : V → W)) s.subset
      rw [image_sdiff _ _ hinj] at hh
      simpa only [image_insert, image_singleton, image_center, image_vertex] using hh
    bridge := f.toHom.map_rel' s.bridge
    complement_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.complement_quad
    complement_score := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        score_image_difference f ha s.complement_score
    final_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.final_quad
    left_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.left_quad
    right_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.right_quad }

theorem CCase.image (s : CCase p a w u v) (f : G.Copy H)
    (ha : edgeCount H (a.image f) = edgeCount G a)
    (hadj : ∀ x ∈ p.triangle ∪ a, ∀ y ∈ p.triangle ∪ a,
      H.Adj (f x) (f y) → G.Adj x y) :
    CCase (p.image f) (a.image f) (f w) (f u) (f v) := by
  have hinj : Function.Injective (f : V → W) := f.injective
  have hK : (p.image f).triangle ∪ a.image f = (p.triangle ∪ a).image f := by
    rw [Paw.image_triangle, image_union]
  have ht := SimpleGraph.is3Clique_triple_iff.mp s.triangle
  refine {
    first_mem := mem_image.mpr ⟨u, s.first_mem, rfl⟩
    second_mem := mem_image.mpr ⟨v, s.second_mem, rfl⟩
    marked_mem := by
      have hh : f w ∈ ({u, v} : Finset V).image f := mem_image.mpr ⟨w, s.marked_mem, rfl⟩
      simpa only [image_insert, image_singleton, image_center, image_vertex] using hh
    triangle := SimpleGraph.is3Clique_triple_iff.mpr
      ⟨f.toHom.map_rel' ht.1, f.toHom.map_rel' ht.2.1, f.toHom.map_rel' ht.2.2⟩
    complement_quad := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        quad_image_difference f s.complement_quad
    complement_score := by
      rw [hK]
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        score_image_difference f ha s.complement_score
    core_budget := by
      rw [hK]
      have he := contacts_image_eq_of_adj H G (f : V → W) hinj {p.center, u, v}
        (p.triangle ∪ a) (fun x hx y hy ↦
          ⟨hadj x (s.core_subset hx) y hy, f.toHom.map_rel'⟩)
      simpa only [image_insert, image_singleton, image_center, image_vertex] using
        he.le.trans s.core_budget }

end Erdos577.UniversalTriple
