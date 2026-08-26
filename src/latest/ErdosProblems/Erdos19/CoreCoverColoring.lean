import ErdosProblems.Erdos19.CoverBoundedExtension
import ErdosProblems.Erdos19.ProjectiveCoreSizeBound
import ErdosProblems.Erdos19.EdgeRestriction

/-! # A cover-bounded coloring of a dense projective core and its remainder -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_partial_coloring_of_restriction (H : SetHypergraph V)
    (S : Finset H) (n A : ℕ) (hn : 0 < n)
    (color : (H.restrictEdges (S : Set H)).EdgeColoring (Fin n))
    (hbounded : (H.restrictEdges (S : Set H)).IsCoverBoundedColoring color A) :
    ∃ c : H → Fin n, H.IsProperOn S c ∧ H.IsCoverBoundedOn S c A := by
  classical
  let J := H.restrictEdges (S : Set H)
  let E := H.restrictEdgesEquiv (S : Set H)
  let c : H → Fin n := fun e ↦ if he : e ∈ S then color (E ⟨e, he⟩) else ⟨0, hn⟩
  have hc (e : H) (he : e ∈ S) : c e = color (E ⟨e, he⟩) := by simp [c, he]
  refine ⟨c, ?_, ?_⟩
  · intro e he f hf hef hinter
    rw [hc e he, hc f hf]
    apply color.valid
    · intro h
      exact hef (congrArg Subtype.val (E.injective h))
    · simpa only [E, restrictEdgesEquiv_val] using hinter
  · intro a
    rcases hbounded a with hsmall | hcover
    · left
      let code : {e : H // e ∈ S ∧ c e = a} → {f : J // color f = a} :=
        fun e ↦ ⟨E ⟨e.1, e.2.1⟩, (hc e.1 e.2.1).symm.trans e.2.2⟩
      have hinj : Function.Injective code := by
        intro e f hef
        apply Subtype.ext
        have hh : (⟨e.1, e.2.1⟩ : (S : Set H)) = ⟨f.1, f.2.1⟩ :=
          E.injective (congrArg Subtype.val hef)
        exact congrArg (fun x : (S : Set H) ↦ x.1) hh
      have hcard := Fintype.card_le_of_injective code hinj
      simp only [← Nat.card_eq_fintype_card] at hcard
      change Nat.card ({e : H | e ∈ S ∧ c e = a} : Set H) ≤
        Nat.card ({f : J | color f = a} : Set J) at hcard
      have hcard' : ({e : H | e ∈ S ∧ c e = a} : Set H).ncard ≤
          ({f : J | color f = a} : Set J).ncard := by
        simpa only [Nat.card_coe_set_eq] using hcard
      exact hcard'.trans hsmall
    · right
      apply (Set.ncard_le_ncard (t := J.coveredVertices {f | color f = a}) ?_).trans hcover
      intro v hv
      obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
      obtain ⟨heS, hve⟩ := Set.mem_iUnion.mp he
      apply Set.mem_iUnion.mpr ⟨E ⟨e, heS.1⟩, ?_⟩
      apply Set.mem_iUnion.mpr ⟨(hc e heS.1).symm.trans heS.2, ?_⟩
      simpa only [E, restrictEdgesEquiv_val] using hve

theorem exists_cover_bounded_coloring_of_projective_core
    (H : SetHypergraph V) (hlinear : H.IsLinear) (n t k r : ℕ)
    (hvertices : Fintype.card V = n) (ht : 1024 ≤ t)
    (hkt : 64 * t ≤ projectiveScale n) (hk : n - n / t ≤ k)
    (hr : 0 < r) (hmin : ∀ e : H, r + 1 ≤ e.1.ncard)
    (S : Finset H) (hS : S.Nonempty) (hdense : IsDenseCore H.lineGraph S k)
    (hpeel : IsPeelableOutside H.lineGraph univ S k)
    (hcoremin : ∀ e ∈ S, projectiveScale n - projectiveScale n / t ≤ e.1.ncard)
    (hbudget : k + n * (n - 1) / ((8 * (n / t) + 1) * r) ≤ n) :
    ∃ color : H.EdgeColoring (Fin n),
      H.IsCoverBoundedColoring color (16 * (n / t)) := by
  have hn : 0 < n := by
    by_contra hnot
    have hscale : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) (by omega)
    omega
  have hscale : 65536 ≤ projectiveScale n := by omega
  have hmax := H.edge_size_lt_of_dense_projective_core hlinear n t k hvertices
    ht hkt hk S hS hdense hcoremin
  let J := H.restrictEdges (S : Set H)
  have hJmin (e : J) : projectiveScale n - projectiveScale n / t ≤ e.1.ncard := by
    obtain ⟨f, hf, hfe⟩ := e.2
    rw [← hfe]
    exact hcoremin f hf
  obtain ⟨color, hc⟩ := J.exists_cover_bounded_projective_coloring
    (H.restrictEdges_linear hlinear _) n t hvertices ht hscale hkt hJmin
  obtain ⟨c₀, hc₀, hb₀⟩ := H.exists_partial_coloring_of_restriction S n
    (16 * (n / t)) hn color hc
  have hhalf : 16 * (n / t) / 2 = 8 * (n / t) := by omega
  obtain ⟨color', _, hbound⟩ := H.exists_cover_bounded_peelable_extension hlinear S n k r
    (16 * (n / t)) hr hmin (fun e ↦ by have h := hmax e; omega) hpeel
    (by simpa only [hvertices, hhalf] using hbudget) c₀ hc₀ hb₀
  exact ⟨color', hbound⟩

#print axioms exists_cover_bounded_coloring_of_projective_core

end Erdos19.SetHypergraph
