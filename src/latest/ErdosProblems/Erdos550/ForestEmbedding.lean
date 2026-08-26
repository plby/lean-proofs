import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Prescribed-root forest embedding (Lemma 5.1 of the paper)

This is the elementary arbitrary-tree embedding used after the stability step in
*A Resolution of Erdős Problem 550* (E. Li): the **prescribed-root forest
embedding lemma** (`\label{lem:rootedforest}`).

A rooted forest on the vertex type `α` is encoded by a `parent : α → Option α`
map (the roots are exactly the vertices `a` with `parent a = none`), together
with an acyclicity certificate `rank : α → ℕ` for which every parent has strictly
smaller rank than its child.  The forest edges are the pairs `{a, b}` with
`parent a = some b`.

If a host graph `J` has minimum degree at least `t - 1`, where `t = |α|` is the
number of forest vertices, then every injection of the roots into `V(J)` extends
to an embedding of the whole forest: there is an injective `f : α → V` agreeing
with the prescribed positions on the roots and sending every forest edge to an
edge of `J`.
-/

open SimpleGraph Finset

namespace Erdos550

/-
Counting step of the greedy embedding: if `f'` is an injective placement of
the `t = |α|` vertices and the image of `f' b` has degree `≥ t - 1`, then there
is a vertex `w` adjacent to `f' b` and distinct from the image of every vertex
other than `a` (so we may freely re-place `a` at `w`).
-/
theorem exists_free_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    {α : Type*} [Fintype α] [DecidableEq α]
    (f' : α → V) (hinj : Function.Injective f')
    (a b : α) (hab : a ≠ b)
    (hdeg : Fintype.card α - 1 ≤ J.degree (f' b)) :
    ∃ w, J.Adj (f' b) w ∧ ∀ x, x ≠ a → f' x ≠ w := by
  obtain ⟨w, hw⟩ : ∃ w ∈ J.neighborFinset (f' b), w ∉ Finset.image f' (Finset.univ.erase a) := by
    have h_card : (J.neighborFinset (f' b)).card > (Finset.image f' (Finset.univ.erase a)).card - 1 := by
      rw [ Finset.card_image_of_injective _ hinj ] ; simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
      rcases n : Fintype.card α with ( _ | _ | n ) <;> simp_all +arith +decide;
      · exact absurd n ( Nat.ne_of_gt ( Fintype.card_pos_iff.mpr ⟨ a ⟩ ) );
      · rw [ Fintype.card_eq_one_iff ] at n ; aesop;
    contrapose! h_card;
    refine' Nat.le_sub_one_of_lt ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ h_card, _ ⟩ ) );
    intro h; have := h ▸ SimpleGraph.notMem_neighborFinset_self J ( f' b ) ; simp_all +decide ;
    exact hab ( hinj this.symm );
  exact ⟨ w, by simpa using! hw.1, fun x hx hx' => hw.2 <| hx'.symm ▸ Finset.mem_image_of_mem _ ( Finset.mem_erase_of_ne_of_mem hx ( Finset.mem_univ _ ) ) ⟩

/-- **Prescribed-root forest embedding (Lemma 5.1).**

A rooted forest is encoded by a `parent` map (roots map to `none`) with an
acyclicity certificate `rank` (parents have strictly smaller rank).  If a graph
`J` on `t = |α|` vertices has minimum degree `≥ t - 1`, then any injection `f0`
of the roots extends to an embedding of the whole forest. -/
theorem rooted_forest_embedding {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (hdeg : ∀ v, Fintype.card α - 1 ≤ J.degree v)
    (f0 : α → V) (hf0inj : Function.Injective f0) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, parent a = none → f a = f0 a) ∧
      (∀ a b, parent a = some b → J.Adj (f a) (f b)) := by
  -- Strong induction over a downward-closed set `S` of "already-embedded" forest
  -- vertices, removing the maximal-rank vertex at each step.
  have key : ∀ S : Finset α, (∀ a ∈ S, ∀ b, parent a = some b → b ∈ S) →
      ∃ f : α → V, Function.Injective f ∧ (∀ a, parent a = none → f a = f0 a) ∧
        (∀ a ∈ S, ∀ b, parent a = some b → J.Adj (f a) (f b)) := by
    intro S
    induction S using Finset.strongInduction with
    | _ S ih =>
      intro hdc
      rcases S.eq_empty_or_nonempty with hSe | hSne
      · exact ⟨f0, hf0inj, fun _ _ => rfl, by subst hSe; simp⟩
      · -- pick the maximal-rank vertex `a` of `S`
        obtain ⟨a, haS, hamax⟩ := S.exists_max_image rank hSne
        have hsub : S.erase a ⊂ S := Finset.erase_ssubset haS
        have hdc' : ∀ x ∈ S.erase a, ∀ b, parent x = some b → b ∈ S.erase a := by
          intro x hx b hxb
          have hxS : x ∈ S := (Finset.mem_erase.1 hx).2
          have hbS : b ∈ S := hdc x hxS b hxb
          refine Finset.mem_erase.2 ⟨?_, hbS⟩
          rintro rfl
          have h1 := hrank x b hxb
          have h2 := hamax x hxS
          omega
        obtain ⟨f', hinj', hroot', hedge'⟩ := ih (S.erase a) hsub hdc'
        rcases hpa : parent a with _ | b
        · -- `a` is a root: `f'` already works for `S`
          refine ⟨f', hinj', hroot', ?_⟩
          intro x hxS c hxc
          rcases eq_or_ne x a with rfl | hxa
          · rw [hpa] at hxc; exact absurd hxc (by simp)
          · exact hedge' x (Finset.mem_erase.2 ⟨hxa, hxS⟩) c hxc
        · -- `a` is non-root with parent `b`; `b ∈ S.erase a`
          have hba : b ≠ a := by
            intro h; rw [h] at hpa; exact absurd (hrank a a hpa) (lt_irrefl _)
          have hbS : b ∈ S := hdc a haS b hpa
          have hbe : b ∈ S.erase a := Finset.mem_erase.2 ⟨hba, hbS⟩
          obtain ⟨w, hw, hwfree⟩ :=
            exists_free_neighbor J f' hinj' a b (Ne.symm hba) (hdeg (f' b))
          refine ⟨Function.update f' a w, ?_, ?_, ?_⟩
          · -- injectivity is preserved by moving `a` to a fresh vertex `w`
            intro x y hxy
            simp only [Function.update_apply] at hxy
            split_ifs at hxy with hx hy hy
            · rw [hx, hy]
            · exact absurd hxy.symm (hwfree y hy)
            · exact absurd hxy (hwfree x hx)
            · exact hinj' hxy
          · intro x hx
            rcases eq_or_ne x a with rfl | hxa
            · simp [hpa] at hx
            · rw [Function.update_of_ne hxa]; exact hroot' x hx
          · intro x hxS c hxc
            rcases eq_or_ne x a with rfl | hxa
            · rw [hpa] at hxc
              have hcb : b = c := by injection hxc
              subst hcb
              rw [Function.update_self, Function.update_of_ne hba]
              exact hw.symm
            · have hxe : x ∈ S.erase a := Finset.mem_erase.2 ⟨hxa, hxS⟩
              have hce : c ∈ S.erase a := hdc' x hxe c hxc
              have hca : c ≠ a := (Finset.mem_erase.1 hce).1
              rw [Function.update_of_ne hxa, Function.update_of_ne hca]
              exact hedge' x hxe c hxc
  obtain ⟨f, hinj, hroot, hedge⟩ := key Finset.univ (by intro a _ b _; exact Finset.mem_univ b)
  exact ⟨f, hinj, hroot, fun a b hab => hedge a (Finset.mem_univ a) b hab⟩

end Erdos550
