import Mathlib
import ErdosProblems.Erdos550.RegularPairTools
import ErdosProblems.Erdos550.ForestEmbedding

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rooted-forest embedding across a single regular pair (candidate-set engine)

This file develops the core *candidate-set* tree-embedding engine for a
**single** regular pair.

`Erdos550.rooted_forest_embedding` (Lemma 5.1) embeds a rooted forest into any
host of minimum degree `≥ |α| - 1`.  Here the host is a single `ε`-uniform
(regular) pair `(s, t)` of density `d = edgeDensity s t`, so there is no global
minimum-degree guarantee; instead we exploit that *almost every* vertex of each
side has large forward degree into the other side (the "good" vertices), and we
maintain the invariant that **every image is a good vertex**.  This is exactly
the candidate-set / greedy method, specialised to two clusters.

The rooted forest is encoded as in `rooted_forest_embedding`: `parent : α → Option α`
with an acyclicity certificate `rank`.  A bipartition `col : α → Bool` (`false ↦ s`,
`true ↦ t`) that is proper along forest edges assigns each vertex to a side.
Given the capacity condition `|α| + ε·|c| ≤ (d-ε)·|c|` for both sides `c ∈ {s,t}`,
every such rooted forest embeds so that each vertex lands in its prescribed side
and every forest edge maps to an edge of `G`.

The two analytic ingredients are proved in
`RequestProject/RegularPairTools.lean`:
* `isUniform_exists_good_unused` / `isUniform_exists_good_unused_right` — root
  placement (a good, unused vertex exists on each side);
* `isUniform_good_fresh_neighbor` / `isUniform_good_fresh_neighbor_right` — the
  extension step (a good, unused *neighbour* of an already-placed good vertex).
-/

open SimpleGraph Finset

namespace Erdos550

/-- **Single-regular-pair rooted-forest embedding (candidate-set engine).**

Let `(s, t)` be an `ε`-uniform pair in `G` (`0 < ε ≤ 1`, both sides nonempty,
disjoint), with density `d = G.edgeDensity s t`.  Let a rooted forest on `α` be
given by `parent`/`rank` (as in `rooted_forest_embedding`) together with a
side-assignment `col : α → Bool` (`false ↦ s`, `true ↦ t`) proper along edges.
If the capacity bound `|α| + ε·|c| ≤ (d-ε)·|c|` holds for both `c ∈ {|s|,|t|}`,
then there is an injective `f : α → V` sending every vertex into its side and
every forest edge to an edge of `G`. -/
theorem regularPair_forest_embedding
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {s t : Finset V}
    (hs : s.Nonempty) (ht : t.Nonempty)
    (huni : G.IsUniform ε s t)
    {α : Type*} [Fintype α] [DecidableEq α]
    (parent : α → Option α) (rank : α → ℕ)
    (hrank : ∀ a b, parent a = some b → rank b < rank a)
    (col : α → Bool)
    (hcol : ∀ a b, parent a = some b → col a ≠ col b)
    (hcapS : (Fintype.card α : ℝ) + ε * (s.card : ℝ)
        ≤ ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ))
    (hcapT : (Fintype.card α : ℝ) + ε * (t.card : ℝ)
        ≤ ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ)) :
    ∃ f : α → V, Function.Injective f ∧
      (∀ a, f a ∈ (if col a then t else s)) ∧
      (∀ a b, parent a = some b → G.Adj (f a) (f b)) := by
  have hd1 : (G.edgeDensity s t : ℝ) ≤ 1 := mod_cast SimpleGraph.edgeDensity_le_one G s t
  have key : ∀ S : Finset α, (∀ a ∈ S, ∀ b, parent a = some b → b ∈ S) →
      ∃ f : α → V, Function.Injective f ∧
        (∀ a ∈ S, f a ∈ (if col a then t else s) ∧
          ((G.edgeDensity s t : ℝ) - ε) * ((if col a then s else t).card : ℝ)
            ≤ (((if col a then s else t).filter (fun b => G.Adj (f a) b)).card : ℝ)) ∧
        (∀ a ∈ S, ∀ b, parent a = some b → G.Adj (f a) (f b)) := by
    intro S
    induction S using Finset.strongInduction with
    | _ S ih =>
    intro hSdc
    rcases eq_or_ne S ∅ with hSe | hSne
    · -- Empty: use any injective placeholder.
      subst hSe
      have hcard : Fintype.card α ≤ Fintype.card V := by
        have h1 : (Fintype.card α : ℝ) ≤ ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ) :=
          le_trans (le_add_of_nonneg_right (by positivity)) hcapS
        have h2 : ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ) ≤ (s.card : ℝ) :=
          mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith)
        have h3 : (s.card : ℝ) ≤ (Fintype.card V : ℝ) := mod_cast Finset.card_le_univ s
        exact_mod_cast le_trans h1 (le_trans h2 h3)
      obtain ⟨eα⟩ := Trunc.exists_rep (Fintype.truncEquivFin α)
      obtain ⟨eV⟩ := Trunc.exists_rep (Fintype.truncEquivFin V)
      refine ⟨fun a => eV.symm (Fin.castLE hcard (eα a)), ?_, ?_, ?_⟩
      · intro x y hxy
        exact eα.injective (Fin.castLE_injective _ (eV.symm.injective hxy))
      · intro a ha; exact absurd ha (Finset.notMem_empty a)
      · intro a ha; exact absurd ha (Finset.notMem_empty a)
    · -- Nonempty: place the maximal-rank vertex last.
      have hSnonempty : S.Nonempty := Finset.nonempty_of_ne_empty hSne
      obtain ⟨a, haS, hamax⟩ := S.exists_max_image rank hSnonempty
      have hdc' : ∀ x ∈ S.erase a, ∀ b, parent x = some b → b ∈ S.erase a := by
        intro x hx b hxb
        have hxS : x ∈ S := (Finset.mem_erase.1 hx).2
        have hbS : b ∈ S := hSdc x hxS b hxb
        refine Finset.mem_erase.2 ⟨?_, hbS⟩
        rintro rfl
        exact absurd (hrank x b hxb) (by have := hamax x hxS; omega)
      obtain ⟨f', hf'inj, hf'good, hf'adj⟩ := ih (S.erase a) (Finset.erase_ssubset haS) hdc'
      have hαpos : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
      set U : Finset V := Finset.image f' (Finset.univ.erase a) with hUdef
      have hUcard : (U.card : ℝ) < (Fintype.card α : ℝ) := by
        have h1 : U.card ≤ (Finset.univ.erase a).card := Finset.card_image_le
        have h2 : (Finset.univ.erase a).card = Fintype.card α - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
        have hle : (U.card : ℝ) ≤ (Fintype.card α : ℝ) - 1 := by
          have h3 : U.card ≤ Fintype.card α - 1 := h1.trans_eq h2
          have hc : (U.card : ℝ) ≤ ((Fintype.card α - 1 : ℕ) : ℝ) := mod_cast h3
          rwa [Nat.cast_sub hαpos, Nat.cast_one] at hc
        linarith
      have hmemU : ∀ x, x ≠ a → f' x ∈ U := by
        intro x hx
        exact Finset.mem_image_of_mem f' (Finset.mem_erase.2 ⟨hx, Finset.mem_univ x⟩)
      -- generic injectivity finisher (given `w ∉ U`)
      have injUpdate : ∀ w : V, w ∉ U → Function.Injective (Function.update f' a w) := by
        intro w hwU x y hxy
        simp only [Function.update_apply] at hxy
        split_ifs at hxy with hx hy hy
        · rw [hx, hy]
        · exfalso; apply hwU; rw [hxy]; exact hmemU y hy
        · exfalso; apply hwU; rw [← hxy]; exact hmemU x hx
        · exact hf'inj hxy
      rcases hpar : parent a with _ | b
      · -- ROOT case: parent a = none
        by_cases hca : col a = true
        · -- root, col a = true : place in t
          have hUt : (U.card : ℝ) + ε * (t.card : ℝ) < (t.card : ℝ) := by
            have hle : ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ) ≤ (t.card : ℝ) :=
              mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith)
            linarith [hcapT]
          obtain ⟨w, hwt, hwU, hwgood⟩ :=
            isUniform_exists_good_unused_right G hε0 hε1 hs ht huni hUt
          refine ⟨Function.update f' a w, injUpdate w hwU, ?_, ?_⟩
          · intro x hxS
            rcases eq_or_ne x a with rfl | hxa
            · rw [Function.update_self]
              exact ⟨by simpa [hca] using! hwt, by simpa [hca] using! hwgood⟩
            · rw [Function.update_of_ne hxa]
              exact hf'good x (Finset.mem_erase.2 ⟨hxa, hxS⟩)
          · intro x hxS c hxc
            rcases eq_or_ne x a with rfl | hxa
            · rw [hpar] at hxc; simp at hxc
            · have hxe : x ∈ S.erase a := Finset.mem_erase.2 ⟨hxa, hxS⟩
              have hce : c ∈ S.erase a := hdc' x hxe c hxc
              have hca' : c ≠ a := (Finset.mem_erase.1 hce).1
              rw [Function.update_of_ne hxa, Function.update_of_ne hca']
              exact hf'adj x hxe c hxc
        · -- root, col a = false : place in s
          have hcaf : col a = false := by simpa using! hca
          have hUs : (U.card : ℝ) + ε * (s.card : ℝ) < (s.card : ℝ) := by
            have hle : ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ) ≤ (s.card : ℝ) :=
              mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith)
            linarith [hcapS]
          obtain ⟨w, hws, hwU, hwgood⟩ :=
            isUniform_exists_good_unused G hε0 hε1 hs ht huni hUs
          refine ⟨Function.update f' a w, injUpdate w hwU, ?_, ?_⟩
          · intro x hxS
            rcases eq_or_ne x a with rfl | hxa
            · rw [Function.update_self]
              exact ⟨by simpa [hcaf] using! hws, by simpa [hcaf] using! hwgood⟩
            · rw [Function.update_of_ne hxa]
              exact hf'good x (Finset.mem_erase.2 ⟨hxa, hxS⟩)
          · intro x hxS c hxc
            rcases eq_or_ne x a with rfl | hxa
            · rw [hpar] at hxc; simp at hxc
            · have hxe : x ∈ S.erase a := Finset.mem_erase.2 ⟨hxa, hxS⟩
              have hce : c ∈ S.erase a := hdc' x hxe c hxc
              have hca' : c ≠ a := (Finset.mem_erase.1 hce).1
              rw [Function.update_of_ne hxa, Function.update_of_ne hca']
              exact hf'adj x hxe c hxc
      · -- PARENT case: parent a = some b
        have hba : b ≠ a := by
          intro h; have hlt := hrank a b hpar; rw [h] at hlt; exact lt_irrefl _ hlt
        have hbS : b ∈ S := hSdc a haS b hpar
        have hbe : b ∈ S.erase a := Finset.mem_erase.2 ⟨hba, hbS⟩
        have hcolab : col a ≠ col b := hcol a b hpar
        by_cases hca : col a = true
        · -- col a = true, col b = false : b sits in s, place a in t
          have hcbf : col b = false := by
            rcases hcb : col b with _ | _
            · rfl
            · rw [hca, hcb] at hcolab; exact absurd rfl hcolab
          have hbgood : ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ)
              ≤ ((t.filter (fun x => G.Adj (f' b) x)).card : ℝ) := by
            have h2 := (hf'good b hbe).2
            simpa [hcbf] using! h2
          have hUt : (U.card : ℝ) + ε * (t.card : ℝ)
              < ((G.edgeDensity s t : ℝ) - ε) * (t.card : ℝ) := by
            linarith [hcapT]
          obtain ⟨w, hwt, hadjw, hwU, hwgood⟩ :=
            isUniform_good_fresh_neighbor G hε0 hε1 hs ht huni hbgood hUt
          refine ⟨Function.update f' a w, injUpdate w hwU, ?_, ?_⟩
          · intro x hxS
            rcases eq_or_ne x a with rfl | hxa
            · rw [Function.update_self]
              exact ⟨by simpa [hca] using! hwt, by simpa [hca] using! hwgood⟩
            · rw [Function.update_of_ne hxa]
              exact hf'good x (Finset.mem_erase.2 ⟨hxa, hxS⟩)
          · intro x hxS c hxc
            rcases eq_or_ne x a with rfl | hxa
            · have hcb : c = b := by rw [hpar] at hxc; exact (Option.some.inj hxc).symm
              subst hcb
              rw [Function.update_self, Function.update_of_ne hba]
              exact hadjw.symm
            · have hxe : x ∈ S.erase a := Finset.mem_erase.2 ⟨hxa, hxS⟩
              have hce : c ∈ S.erase a := hdc' x hxe c hxc
              have hca' : c ≠ a := (Finset.mem_erase.1 hce).1
              rw [Function.update_of_ne hxa, Function.update_of_ne hca']
              exact hf'adj x hxe c hxc
        · -- col a = false, col b = true : b sits in t, place a in s
          have hcaf : col a = false := by simpa using! hca
          have hcbt : col b = true := by
            rcases hcb : col b with _ | _
            · rw [hcaf, hcb] at hcolab; exact absurd rfl hcolab
            · rfl
          have hbgood : ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ)
              ≤ ((s.filter (fun x => G.Adj (f' b) x)).card : ℝ) := by
            have h2 := (hf'good b hbe).2
            simpa [hcbt] using! h2
          have hUs : (U.card : ℝ) + ε * (s.card : ℝ)
              < ((G.edgeDensity s t : ℝ) - ε) * (s.card : ℝ) := by
            linarith [hcapS]
          obtain ⟨w, hws, hadjw, hwU, hwgood⟩ :=
            isUniform_good_fresh_neighbor_right G hε0 hε1 hs ht huni hbgood hUs
          refine ⟨Function.update f' a w, injUpdate w hwU, ?_, ?_⟩
          · intro x hxS
            rcases eq_or_ne x a with rfl | hxa
            · rw [Function.update_self]
              exact ⟨by simpa [hcaf] using! hws, by simpa [hcaf] using! hwgood⟩
            · rw [Function.update_of_ne hxa]
              exact hf'good x (Finset.mem_erase.2 ⟨hxa, hxS⟩)
          · intro x hxS c hxc
            rcases eq_or_ne x a with rfl | hxa
            · have hcb : c = b := by rw [hpar] at hxc; exact (Option.some.inj hxc).symm
              subst hcb
              rw [Function.update_self, Function.update_of_ne hba]
              exact hadjw.symm
            · have hxe : x ∈ S.erase a := Finset.mem_erase.2 ⟨hxa, hxS⟩
              have hce : c ∈ S.erase a := hdc' x hxe c hxc
              have hca' : c ≠ a := (Finset.mem_erase.1 hce).1
              rw [Function.update_of_ne hxa, Function.update_of_ne hca']
              exact hf'adj x hxe c hxc
  obtain ⟨f, hinj, hgood, hadj⟩ := key Finset.univ (by intro a _ b _; exact Finset.mem_univ b)
  exact ⟨f, hinj, fun a => (hgood a (Finset.mem_univ a)).1,
    fun a b hab => hadj a (Finset.mem_univ a) b hab⟩

end Erdos550
