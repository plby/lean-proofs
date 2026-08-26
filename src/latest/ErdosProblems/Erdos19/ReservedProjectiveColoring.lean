import ErdosProblems.Erdos19.RestrictedClassTransport
import ErdosProblems.Erdos19.ReservedCoverExtension

/-! # A reserved palette containing only pair-compressed core edges -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_reserved_projective_coloring
    (H : SetHypergraph V) (hlinear : H.IsLinear) (n t k r : ℕ)
    (hvertices : Fintype.card V = n) (ht : 1024 ≤ t)
    (hkt : 64 * t ≤ projectiveScale n) (hk : n - n / t ≤ k)
    (hr : 0 < r) (hmin : ∀ e : H, r + 1 ≤ e.1.ncard)
    (S : Finset H) (hS : S.Nonempty) (hdense : IsDenseCore H.lineGraph S k)
    (hpeel : IsPeelableOutside H.lineGraph univ S k)
    (hcoremin : ∀ e ∈ S, projectiveScale n - projectiveScale n / t ≤ e.1.ncard)
    (reserved : Finset (Fin n))
    (hbudget : k + n * (n - 1) / ((8 * (n / t) + 1) * r) + reserved.card ≤ n) :
    ∃ color : H.EdgeColoring (Fin n),
      H.IsCoverBoundedColoring color (16 * (n / t)) ∧
      (∀ e : H, color.color e ∈ reserved → e ∈ S) ∧
      (∀ a ∈ reserved, ({e : H | color.color e = a} : Set H).ncard ≤ 2) := by
  have hn : 0 < n := by
    by_contra hnot
    have hscale : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) (by omega)
    omega
  have hscale : 65536 ≤ projectiveScale n := by omega
  have hmax := H.edge_size_lt_of_dense_projective_core hlinear n t k hvertices
    ht hkt hk S hS hdense hcoremin
  let J := H.restrictEdges (S : Set H)
  have hJmin (e : J) : projectiveScale n - projectiveScale n / 1024 ≤ e.1.ncard := by
    obtain ⟨f, hf, hfe⟩ := e.2
    rw [← hfe]
    exact (Nat.sub_le_sub_left (Nat.div_le_div_left ht (by norm_num)) _).trans
      (hcoremin f hf)
  have hJmax (e : J) : e.1.ncard ≤ 8 * (n / t) := by
    obtain ⟨f, _, hfe⟩ := e.2
    rw [← hfe]
    exact (hmax f).le
  obtain ⟨coreColor, hpair⟩ :=
    (J.pairCompressible_of_fixedFraction_projectiveScale_edges
      (H.restrictEdges_linear hlinear _) n hvertices hscale hJmin).exists_pair_bounded_coloring
  obtain ⟨c₀, hc₀, hcard₀, hcover₀⟩ :=
    H.exists_partial_coloring_with_class_control S n hn coreColor
  have hb₀ : H.IsCoverBoundedOn S c₀ (16 * (n / t)) := by
    intro a
    right
    have h := J.coveredVertices_le_of_class_bound coreColor a 2 (8 * (n / t))
      (hpair a) hJmax
    exact (Set.ncard_le_ncard (hcover₀ a)).trans (by simpa only [← Nat.mul_assoc] using h)
  have hhalf : 16 * (n / t) / 2 = 8 * (n / t) := by omega
  obtain ⟨color, hagree, hbounded, havoid⟩ := H.exists_reserved_cover_bounded_peelable_extension
    hlinear S n k r (16 * (n / t)) hr hmin (fun e ↦ by have h := hmax e; omega)
    hpeel reserved (by simpa only [hvertices, hhalf] using hbudget) c₀ hc₀ hb₀
  have hmem (e : H) (he : color.color e ∈ reserved) : e ∈ S := by
    by_contra hnot
    exact havoid e hnot he
  refine ⟨color, hbounded, hmem, ?_⟩
  intro a ha
  have hsub : ({e : H | color.color e = a} : Set H) ⊆
      {e : H | e ∈ S ∧ c₀ e = a} := by
    intro e he
    change color.color e = a at he
    have heS := hmem e (by simpa only [he] using ha)
    exact ⟨heS, (hagree e heS).symm.trans he⟩
  exact (Set.ncard_le_ncard hsub).trans ((hcard₀ a).trans (hpair a))

#print axioms exists_reserved_projective_coloring

end Erdos19.SetHypergraph
