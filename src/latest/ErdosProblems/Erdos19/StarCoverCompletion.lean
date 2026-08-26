import ErdosProblems.Erdos19.PartialStarExtension

/-! # Completing pairs with a small vertex cover

A reserve of `A + 2*d + 4*|U|` colors suffices when every existing color
covers at most `A` vertices, every vertex still incident with an uncolored
edge uses at most `d` reserved colors, and `U` meets all uncolored pairs.
The proof colors one star at a time using Hall's theorem.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_star_cover_extension (H : SetHypergraph V) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (n : ℕ) (hvertices : Fintype.card V = n)
    (reserved : Finset (Fin n)) (U : Finset V) (S T : Finset H)
    (hST : Disjoint S T) (hpair : ∀ e ∈ T, e.1.ncard = 2)
    (hvertexCover : ∀ e ∈ T, ∃ v ∈ U, v ∈ e.1)
    (c : H → Fin n) (hc : H.IsProperOn S c) (A d : ℕ)
    (hcover : ∀ a, (H.coveredVertices {e | e ∈ S ∧ c e = a}).ncard ≤ A)
    (hused : ∀ e ∈ T, ∀ v ∈ e.1, (reserved ∩ H.usedColorsOn S c v).card ≤ d)
    (hslack : A + 2 * d + 4 * U.card ≤ reserved.card) :
    ∃ c' : H → Fin n, (∀ e ∈ S, c' e = c e) ∧ H.IsProperOn (S ∪ T) c' := by
  classical
  induction U using Finset.induction_on generalizing S T c A d with
  | empty =>
    have hT : T = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨v, hv, _⟩ := hvertexCover e he
      exact notMem_empty v hv
    exact ⟨c, fun _ _ ↦ rfl, by simpa [hT] using hc⟩
  | @insert u U hu ih =>
    let star := T.filter fun e ↦ u ∈ e.1
    let rest := T \ star
    have hstarSub : star ⊆ T := filter_subset _ _
    have hstarCenter : ∀ e ∈ star, u ∈ e.1 := fun _ he ↦ (mem_filter.mp he).2
    have hrestSub : rest ⊆ T := sdiff_subset
    have hrestCenter : ∀ e ∈ rest, u ∉ e.1 := by
      intro e he hue
      exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨hrestSub he, hue⟩)
    have hrestCover : ∀ e ∈ rest, ∃ v ∈ U, v ∈ e.1 := by
      intro e he
      obtain ⟨v, hv, hve⟩ := hvertexCover e (hrestSub he)
      refine ⟨v, (mem_insert.mp hv).resolve_left ?_, hve⟩
      intro hvu
      exact hrestCenter e he (hvu ▸ hve)
    by_cases hnonempty : star.Nonempty
    · obtain ⟨e₀, he₀⟩ := hnonempty
      have hSstar : Disjoint S star := hST.mono_right hstarSub
      have hcenterUsed : (reserved ∩ H.usedColorsOn S c u).card ≤ d :=
        hused e₀ (hstarSub he₀) u (hstarCenter e₀ he₀)
      obtain ⟨color, hinj, havoid⟩ := H.exists_compatible_star_colors hlinear hmin
        S star hSstar u hstarCenter (fun e he ↦ hpair e (hstarSub he))
        n hvertices c reserved A d hcover hcenterUsed
        (fun e he v hv ↦ hused e (hstarSub he) v hv) (by omega)
      let c₁ := H.recolorOn star c color
      have hc₁ : H.IsProperOn (S ∪ star) c₁ :=
        H.recolorOn_proper S star hSstar c hc color hinj havoid
      have hcover₁ : ∀ a,
          (H.coveredVertices {e | e ∈ S ∪ star ∧ c₁ e = a}).ncard ≤ A + 2 :=
        H.recolorOn_coverage S star hSstar c color hinj 2 A
          (fun e he ↦ (hpair e (hstarSub he)).le) hcover
      have hused₁ : ∀ e ∈ rest, ∀ v ∈ e.1,
          (reserved ∩ H.usedColorsOn (S ∪ star) c₁ v).card ≤ d + 1 := by
        intro e he v hv
        have hvu : v ≠ u := fun h ↦ hrestCenter e he (h ▸ hv)
        exact H.recolorOn_reserved_degree hlinear S star hSstar c color reserved u v
          hvu hstarCenter d (hused e (hrestSub he) v hv)
      have hdisj : Disjoint (S ∪ star) rest := by
        apply disjoint_left.mpr
        intro e he her
        rcases mem_union.mp he with he | he
        · exact disjoint_left.mp hST he (hrestSub her)
        · exact (mem_sdiff.mp her).2 he
      have hslack₁ : (A + 2) + 2 * (d + 1) + 4 * U.card ≤ reserved.card := by
        rw [card_insert_of_notMem hu] at hslack
        omega
      obtain ⟨c', hagree, hc'⟩ := ih (S ∪ star) rest hdisj
        (fun e he ↦ hpair e (hrestSub he)) hrestCover c₁ hc₁ (A + 2) (d + 1)
        hcover₁ hused₁ hslack₁
      refine ⟨c', ?_, ?_⟩
      · intro e he
        exact (hagree e (mem_union_left _ he)).trans
          (H.recolorOn_agrees S star hSstar c color e he)
      · have hset : (S ∪ star) ∪ rest = S ∪ T := by
          rw [union_assoc, union_sdiff_of_subset hstarSub]
        simpa only [hset] using hc'
    · have hstarEmpty : star = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
      have hrest : rest = T := by simp [rest, hstarEmpty]
      have hsmallSlack : A + 2 * d + 4 * U.card ≤ reserved.card := by
        rw [card_insert_of_notMem hu] at hslack
        omega
      exact ih S T hST hpair (by simpa only [hrest] using hrestCover)
        c hc A d hcover hused hsmallSlack

theorem exists_coloring_of_star_cover (H : SetHypergraph V) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (n : ℕ) (hvertices : Fintype.card V = n)
    (reserved : Finset (Fin n)) (U : Finset V) (S T : Finset H)
    (hST : Disjoint S T) (hfull : S ∪ T = univ)
    (hpair : ∀ e ∈ T, e.1.ncard = 2)
    (hvertexCover : ∀ e ∈ T, ∃ v ∈ U, v ∈ e.1)
    (c : H → Fin n) (hc : H.IsProperOn S c) (A d : ℕ)
    (hcover : ∀ a, (H.coveredVertices {e | e ∈ S ∧ c e = a}).ncard ≤ A)
    (hused : ∀ e ∈ T, ∀ v ∈ e.1, (reserved ∩ H.usedColorsOn S c v).card ≤ d)
    (hslack : A + 2 * d + 4 * U.card ≤ reserved.card) :
    ∃ color : H.EdgeColoring (Fin n), ∀ e ∈ S, color e = c e := by
  obtain ⟨c', hagree, hc'⟩ := H.exists_star_cover_extension hlinear hmin n hvertices
    reserved U S T hST hpair hvertexCover c hc A d hcover hused hslack
  rw [hfull] at hc'
  exact ⟨⟨c', fun {e f} hef hinter ↦ hc' e (mem_univ _) f (mem_univ _) hef hinter⟩,
    hagree⟩

#print axioms exists_star_cover_extension
#print axioms exists_coloring_of_star_cover

end Erdos19.SetHypergraph
