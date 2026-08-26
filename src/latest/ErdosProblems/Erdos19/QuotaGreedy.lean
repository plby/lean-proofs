import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic

/-! # Greedy list coloring with a global quota per color -/

namespace Erdos19

open Finset

theorem saturated_colors_card_le {E A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset E) (c : E → A) (q : ℕ) (hq : 0 < q) :
    ((univ : Finset A).filter fun a ↦ q ≤ (S.filter fun e ↦ c e = a).card).card ≤ S.card / q := by
  classical
  let T := (univ : Finset A).filter fun a ↦ q ≤ (S.filter fun e ↦ c e = a).card
  apply (Nat.le_div_iff_mul_le hq).mpr
  calc
    T.card * q = ∑ _a ∈ T, q := by simp
    _ ≤ ∑ a ∈ T, (S.filter fun e ↦ c e = a).card := by
      exact sum_le_sum (fun a ha ↦ (mem_filter.mp ha).2)
    _ ≤ ∑ a : A, (S.filter fun e ↦ c e = a).card := sum_le_sum_of_subset (subset_univ _)
    _ = S.card := by simpa using sum_card_fiberwise_eq_card_filter S univ c

private theorem exists_partial_list_coloring_with_quota {E A : Type*}
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A] [Nonempty A]
    (G : SimpleGraph E) [DecidableRel G.Adj] (L : E → Finset A) (q : ℕ) (hq : 0 < q)
    (hroom : ∀ e, (univ.filter (G.Adj e)).card + Fintype.card E / q < (L e).card)
    (S : Finset E) :
    ∃ c : E → A, (∀ e ∈ S, c e ∈ L e) ∧
      (∀ e ∈ S, ∀ f ∈ S, G.Adj e f → c e ≠ c f) ∧
      (∀ a, (S.filter fun e ↦ c e = a).card ≤ q) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ ↦ Classical.arbitrary A, by simp, by simp, by simp⟩
  | @insert e S heS ih =>
    obtain ⟨c, hL, hc, hquota⟩ := ih
    let N := S.filter (G.Adj e)
    let T := (univ : Finset A).filter fun a ↦ q ≤ (S.filter fun v ↦ c v = a).card
    let used := N.image c ∪ T
    have hT : T.card ≤ Fintype.card E / q :=
      (saturated_colors_card_le S c q hq).trans (Nat.div_le_div_right (card_le_univ S))
    have hN : N.card ≤ (univ.filter (G.Adj e)).card :=
      card_le_card (filter_subset_filter _ (subset_univ S))
    have hused : used.card < (L e).card := by
      change (N.image c ∪ T).card < (L e).card
      have hu := card_union_le (N.image c) T
      have hi := card_image_le (f := c) (s := N)
      have hr := hroom e
      omega
    obtain ⟨a, haL, haused⟩ := exists_mem_notMem_of_card_lt_card hused
    have haT : a ∉ T := fun h ↦ haused (mem_union_right _ h)
    have hac : ∀ f ∈ S, G.Adj e f → a ≠ c f := by
      intro f hf hef heq
      exact haused (mem_union_left _ (mem_image.mpr ⟨f, mem_filter.mpr ⟨hf, hef⟩, heq.symm⟩))
    let next := Function.update c e a
    refine ⟨next, ?_, ?_, ?_⟩
    · intro f hf
      by_cases hfe : f = e
      · simpa only [next, hfe, Function.update_self] using haL
      · have hfS : f ∈ S := (mem_insert.mp hf).resolve_left hfe
        simpa only [next, Function.update_of_ne hfe] using hL f hfS
    · intro f hf g hg hfg
      by_cases hfe : f = e
      · have hge : g ≠ e := fun h ↦ hfg.ne (hfe.trans h.symm)
        have hgS : g ∈ S := (mem_insert.mp hg).resolve_left hge
        have hadj : G.Adj e g := hfe ▸ hfg
        simpa only [next, hfe, Function.update_self, Function.update_of_ne hge] using hac g hgS hadj
      · have hfS : f ∈ S := (mem_insert.mp hf).resolve_left hfe
        by_cases hge : g = e
        · have hadj : G.Adj e f := hge ▸ hfg.symm
          simpa only [next, hge, Function.update_self, Function.update_of_ne hfe] using (hac f hfS hadj).symm
        · have hgS : g ∈ S := (mem_insert.mp hg).resolve_left hge
          simpa only [next, Function.update_of_ne hfe, Function.update_of_ne hge] using hc f hfS g hgS hfg
    · intro b
      have hfilter : (S.filter fun v ↦ next v = b) = (S.filter fun v ↦ c v = b) := by
        apply filter_congr
        intro v hv
        have hve : v ≠ e := fun h ↦ heS (h ▸ hv)
        simp only [next, Function.update_of_ne hve]
      rw [filter_insert, hfilter]
      rw [show next e = a by simp [next]]
      by_cases hab : a = b
      · rw [if_pos hab, card_insert_of_notMem (fun h ↦ heS (mem_filter.mp h).1)]
        have hsmall : (S.filter fun v ↦ c v = a).card < q := by
          simpa only [T, mem_filter, mem_univ, true_and, not_le] using haT
        subst b
        omega
      · rw [if_neg hab]
        exact hquota b

theorem exists_list_coloring_with_quota {E A : Type*}
    [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A] [Nonempty A]
    (G : SimpleGraph E) [DecidableRel G.Adj] (L : E → Finset A) (q : ℕ) (hq : 0 < q)
    (hroom : ∀ e, (univ.filter (G.Adj e)).card + Fintype.card E / q < (L e).card) :
    ∃ c : G.Coloring A, (∀ e, c e ∈ L e) ∧
      ∀ a, ((univ : Finset E).filter fun e ↦ c e = a).card ≤ q := by
  obtain ⟨c, hL, hc, hquota⟩ := exists_partial_list_coloring_with_quota G L q hq hroom univ
  refine ⟨SimpleGraph.Coloring.mk c (fun {e f} h ↦ hc e (mem_univ _) f (mem_univ _) h), ?_, hquota⟩
  exact fun e ↦ hL e (mem_univ _)

#print axioms exists_list_coloring_with_quota

end Erdos19
