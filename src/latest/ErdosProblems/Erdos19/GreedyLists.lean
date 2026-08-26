import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

/-! # Greedy coloring with forbidden colors -/

namespace Erdos19

open Finset

private theorem exists_partial_coloring_avoiding {E A : Type*}
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A] [Nonempty A]
    (G : SimpleGraph E) [DecidableRel G.Adj] (F : E → Finset A)
    (hsize : ∀ e, (univ.filter (G.Adj e)).card + (F e).card < Fintype.card A)
    (S : Finset E) :
    ∃ c : E → A, (∀ e ∈ S, c e ∉ F e) ∧
      ∀ e ∈ S, ∀ f ∈ S, G.Adj e f → c e ≠ c f := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ Classical.arbitrary A, by simp, by simp⟩
  | @insert e S heS ih =>
    obtain ⟨c, hcF, hc⟩ := ih
    let N := S.filter (G.Adj e)
    let used := N.image c ∪ F e
    have hused : used.card < Fintype.card A := by
      calc
        used.card ≤ (N.image c).card + (F e).card := card_union_le _ _
        _ ≤ N.card + (F e).card := Nat.add_le_add_right card_image_le _
        _ ≤ (univ.filter (G.Adj e)).card + (F e).card := by
          apply Nat.add_le_add_right
          apply card_le_card
          exact filter_subset_filter _ (subset_univ S)
        _ < Fintype.card A := hsize e
    obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card (show used.card < univ.card by
      simpa using hused)
    have haF : a ∉ F e := fun h ↦ ha (mem_union_right _ h)
    have hac : ∀ f ∈ S, G.Adj e f → a ≠ c f := by
      intro f hf hef heq
      apply ha
      exact mem_union_left _ (mem_image.mpr ⟨f, mem_filter.mpr ⟨hf, hef⟩, heq.symm⟩)
    refine ⟨Function.update c e a, ?_, ?_⟩
    · intro f hf
      by_cases hfe : f = e
      · simpa [hfe] using haF
      · have hfS : f ∈ S := (mem_insert.mp hf).resolve_left hfe
        simpa [Function.update_of_ne hfe] using hcF f hfS
    · intro f hf g hg hfg
      by_cases hfe : f = e
      · have hge : g ≠ e := fun h ↦ hfg.ne (hfe.trans h.symm)
        have hgS : g ∈ S := (mem_insert.mp hg).resolve_left hge
        have hadj : G.Adj e g := hfe ▸ hfg
        simpa [hfe, Function.update_of_ne hge] using hac g hgS hadj
      · have hfS : f ∈ S := (mem_insert.mp hf).resolve_left hfe
        by_cases hge : g = e
        · have hadj : G.Adj e f := hge ▸ hfg.symm
          simpa [hge, Function.update_of_ne hfe] using (hac f hfS hadj).symm
        · have hgS : g ∈ S := (mem_insert.mp hg).resolve_left hge
          simpa [Function.update_of_ne hfe, Function.update_of_ne hge] using
            hc f hfS g hgS hfg

/-- Greedy list coloring of a finite graph, expressed as forbidden sets in a
fixed finite palette. -/
theorem exists_coloring_avoiding_of_degree_add_forbidden_lt {E A : Type*}
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A] [Nonempty A]
    (G : SimpleGraph E) [DecidableRel G.Adj] (F : E → Finset A)
    (hsize : ∀ e, (univ.filter (G.Adj e)).card + (F e).card < Fintype.card A) :
    ∃ c : G.Coloring A, ∀ e, c e ∉ F e := by
  obtain ⟨c, hcF, hc⟩ := exists_partial_coloring_avoiding G F hsize univ
  refine ⟨SimpleGraph.Coloring.mk c (fun {e f} h ↦ hc e (mem_univ _) f (mem_univ _) h), ?_⟩
  exact fun e ↦ hcF e (mem_univ _)

#print axioms exists_coloring_avoiding_of_degree_add_forbidden_lt

end Erdos19
