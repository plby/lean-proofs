/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 608.
Informal authors: Zoltán Füredi, Zeinab Maleki; construction described by
Andrzej Grzesik, Ping Hu, and Jan Volec.
Formal authors: Claude Fable 5, Emerson Hsieh.
Source: https://github.com/teorth/erdosproblems/pull/365
https://github.com/primateria/erdos608/tree/b50849234b8de6cb5c642b5cb0479cab2e9e9908
Original Lean version: 4.27.0.
Original Mathlib revision: a3a10db0e9d66acbebf76c5e6a135066525ac900 (v4.27.0).
-/
import ErdosProblems.Erdos608.Construction

set_option linter.mathlibStandardSet false

/-
Erdős 608 — pentagonal edges of the Füredi–Maleki graph (lemma-ladder items
L3a and L4 of runs/phase2/erdos-608/CONSTRUCTION.md).

* L3a (`not_onC5_AB`): no pentagon of `FM m` meets part A; in particular no
  A×B edge lies on a pentagon.  Reduced to a finite tag computation
  (`tag_pentagon_no_zero`, 4⁵ cases by `decide`): adjacency forces
  consecutive tags or a loop step at 3, and a closed 5-walk on the pattern
  path 0–1–2–3-with-loop-at-3 uses an odd number of loop steps, hence visits
  3; a round trip 3 → 0 → 3 alone costs six non-loop steps — one more than a
  pentagon has.
* L4 (`pentEdges_ncard`): `(pentEdges (FM m)).ncard = 169·m² − 5·m` for
  `1 ≤ m`: the pentagonal edges are exactly the edges outside the A×B block
  (L3a gives ⊆, L3b's `onC5_bc`/`onC5_cd`/`onC5_dd` give ⊇), and the A×B
  block has `28·m²` edges.
-/

namespace Erdos608

/-! ## L3a: no pentagon meets part A -/

lemma tag_le_three {m : ℕ} (v : V m) : tag v ≤ 3 := by
  rcases v with a | b | c | d <;> simp

/-- `tag`, packaged as `Fin 4` (for `decide`-friendly statements). -/
def tagF {m : ℕ} (v : V m) : Fin 4 := ⟨tag v, by have := tag_le_three v; omega⟩

@[simp] lemma tagF_val {m : ℕ} (v : V m) : (tagF v).val = tag v := rfl

/-- Finite-arithmetic core of L3a: the five adjacency-shaped constraints of a
closed 5-walk on the tag pattern (path `0–1–2–3` with a loop at `3`) rule out
tag `0` at every position. -/
lemma tag_pentagon_no_zero :
    ∀ t₀ t₁ t₂ t₃ t₄ : Fin 4,
      (t₁.val = t₀.val + 1 ∨ t₀.val = t₁.val + 1 ∨ (t₀.val = 3 ∧ t₁.val = 3)) →
      (t₂.val = t₁.val + 1 ∨ t₁.val = t₂.val + 1 ∨ (t₁.val = 3 ∧ t₂.val = 3)) →
      (t₃.val = t₂.val + 1 ∨ t₂.val = t₃.val + 1 ∨ (t₂.val = 3 ∧ t₃.val = 3)) →
      (t₄.val = t₃.val + 1 ∨ t₃.val = t₄.val + 1 ∨ (t₃.val = 3 ∧ t₄.val = 3)) →
      (t₀.val = t₄.val + 1 ∨ t₄.val = t₀.val + 1 ∨ (t₄.val = 3 ∧ t₀.val = 3)) →
      t₀.val ≠ 0 ∧ t₁.val ≠ 0 ∧ t₂.val ≠ 0 ∧ t₃.val ≠ 0 ∧ t₄.val ≠ 0 := by
  decide

/-- No vertex of a pentagon of `FM m` lies in part A (tag `0`). -/
lemma pent_tags_ne_zero {m : ℕ} {v₀ v₁ v₂ v₃ v₄ : V m}
    (h01 : (FM m).Adj v₀ v₁) (h12 : (FM m).Adj v₁ v₂) (h23 : (FM m).Adj v₂ v₃)
    (h34 : (FM m).Adj v₃ v₄) (h40 : (FM m).Adj v₄ v₀) :
    tag v₀ ≠ 0 ∧ tag v₁ ≠ 0 ∧ tag v₂ ≠ 0 ∧ tag v₃ ≠ 0 ∧ tag v₄ ≠ 0 :=
  tag_pentagon_no_zero (tagF v₀) (tagF v₁) (tagF v₂) (tagF v₃) (tagF v₄)
    (FM_adj.mp h01).1 (FM_adj.mp h12).1 (FM_adj.mp h23).1
    (FM_adj.mp h34).1 (FM_adj.mp h40).1

/-- **L3a.** No A×B edge of `FM m` lies on a pentagon. -/
lemma not_onC5_AB (m : ℕ) (a : Fin (4*m)) (b : Fin (7*m)) :
    ¬ Erdos608.OnC5 (FM m) s(Sum.inl a, Sum.inr (Sum.inl b)) := by
  rintro ⟨v₀, v₁, v₂, v₃, v₄, -, -, -, -, -, -, -, -, -, -,
    h01, h12, h23, h34, h40, hedge⟩
  obtain ⟨ht0, ht1, ht2, ht3, ht4⟩ := pent_tags_ne_zero h01 h12 h23 h34 h40
  have hmem : (Sum.inl a : V m) ∈ s(Sum.inl a, (Sum.inr (Sum.inl b) : V m)) :=
    Sym2.mem_iff.mpr (Or.inl rfl)
  rcases hedge with h | h | h | h | h <;> rw [h] at hmem <;>
      rcases Sym2.mem_iff.mp hmem with rfl | rfl
  · exact ht0 rfl
  · exact ht1 rfl
  · exact ht1 rfl
  · exact ht2 rfl
  · exact ht2 rfl
  · exact ht3 rfl
  · exact ht3 rfl
  · exact ht4 rfl
  · exact ht4 rfl
  · exact ht0 rfl

/-! ## L4: the A×B block and the pentagonal-edge count -/

/-- The A×B edges of `FM m`, as a `Finset` of `Sym2` pairs. -/
def ABblock (m : ℕ) : Finset (Sym2 (V m)) :=
  (Finset.univ ×ˢ Finset.univ).image
    (fun p : Fin (4*m) × Fin (7*m) => s(Sum.inl p.1, Sum.inr (Sum.inl p.2)))

lemma mem_ABblock (m : ℕ) (a : Fin (4*m)) (b : Fin (7*m)) :
    s(Sum.inl a, (Sum.inr (Sum.inl b) : V m)) ∈ ABblock m :=
  Finset.mem_image.mpr
    ⟨(a, b), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩

lemma mem_ABblock_iff {m : ℕ} {e : Sym2 (V m)} :
    e ∈ ABblock m ↔
      ∃ (a : Fin (4*m)) (b : Fin (7*m)), e = s(Sum.inl a, Sum.inr (Sum.inl b)) := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, -, rfl⟩ := Finset.mem_image.mp h
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact mem_ABblock m a b

lemma ABpair_injective (m : ℕ) :
    Function.Injective (fun p : Fin (4*m) × Fin (7*m) =>
      s(Sum.inl p.1, (Sum.inr (Sum.inl p.2) : V m))) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain rfl := Sum.inl_injective h1
    obtain rfl := Sum.inl_injective (Sum.inr_injective h2)
    rfl
  · exact absurd h1 (by simp)

lemma ABblock_card (m : ℕ) : (ABblock m).card = 28 * m ^ 2 := by
  rw [ABblock, Finset.card_image_of_injective _ (ABpair_injective m),
    Finset.card_product]
  simp only [Finset.card_univ, Fintype.card_fin]
  ring

/-- Every edge of `FM m` outside the A×B block lies on a pentagon (the L3b
witnesses; the 16-way tag case analysis rules every other shape out). -/
lemma onC5_of_not_AB (m : ℕ) (hm : 1 ≤ m) (x y : V m)
    (he : (FM m).Adj x y) (hAB : s(x, y) ∉ ABblock m) :
    Erdos608.OnC5 (FM m) s(x, y) := by
  obtain ⟨htag, hne⟩ := FM_adj.mp he
  rcases x with a | b | c | d <;> rcases y with a' | b' | c' | d' <;>
      simp only [tag_A, tag_B, tag_C, tag_D] at htag <;>
      try (exfalso; omega)
  · exact absurd (mem_ABblock m a b') hAB
  · rw [Sym2.eq_swap] at hAB
    exact absurd (mem_ABblock m a' b) hAB
  · exact onC5_bc m hm b c'
  · rw [Sym2.eq_swap]
    exact onC5_bc m hm b' c
  · exact onC5_cd m hm c d'
  · rw [Sym2.eq_swap]
    exact onC5_cd m hm c' d
  · exact onC5_dd m hm d d' (by simpa using hne)

/-- The pentagonal edges of `FM m` are exactly the edges outside the A×B
block. -/
lemma pentEdges_FM (m : ℕ) (hm : 1 ≤ m) :
    pentEdges (FM m) = (FM m).edgeSet \ ↑(ABblock m) := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [pentEdges, Set.mem_ofPred_eq, Set.mem_sdiff, Finset.mem_coe]
    constructor
    · rintro ⟨he, hc5⟩
      refine ⟨he, fun hAB => ?_⟩
      obtain ⟨a, b, hab⟩ := mem_ABblock_iff.mp hAB
      rw [hab] at hc5
      exact not_onC5_AB m a b hc5
    · rintro ⟨he, hAB⟩
      -- `s(x, y) ∈ edgeSet` is definitionally `Adj x y` (`mem_edgeSet` is `Iff.rfl`)
      exact ⟨he, onC5_of_not_AB m hm x y he hAB⟩

/-- **L4.** The Füredi–Maleki graph has `169·m² − 5·m` pentagonal edges. -/
lemma pentEdges_ncard (m : ℕ) (hm : 1 ≤ m) :
    (Erdos608.pentEdges (FM m)).ncard = 169 * m ^ 2 - 5 * m := by
  have hsub : ↑(ABblock m) ⊆ (FM m).edgeSet := by
    intro e he
    obtain ⟨a, b, rfl⟩ := mem_ABblock_iff.mp (Finset.mem_coe.mp he)
    exact adj_AB a b
  rw [pentEdges_FM m hm, Set.ncard_sdiff hsub, edgeSet_ncard,
    Set.ncard_coe_finset, ABblock_card]
  have h1 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  generalize m ^ 2 = t at h1 ⊢
  omega

end Erdos608
