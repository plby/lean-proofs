/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 639.
https://www.erdosproblems.com/forum/thread/639

Informal authors:
- Peter Keevash
- Benny Sudakov

Formal authors:
- Aristotle
- Parcly Taxel

URLs:
- https://www.erdosproblems.com/forum/thread/639#post-6189
- https://gist.githubusercontent.com/Parcly-Taxel/f9a6a963d1057880633e4034294aa98e/raw/885ce8aa2d80d8ac598b98126de3321b5b8842ff/Erdos639.lean
- https://live.lean-lang.org/#url=https%3A%2F%2Fgist.githubusercontent.com%2FParcly-Taxel%2Ff9a6a963d1057880633e4034294aa98e%2Fraw%2F885ce8aa2d80d8ac598b98126de3321b5b8842ff%2FErdos639.lean&project=mathlib-v4.28.0
-/
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

namespace Erdos639


lemma Nat.sq_even_div_four {n : ℕ} : (2 * n) ^ 2 / 4 = n ^ 2 := by grind
lemma Nat.sq_odd_div_four {n : ℕ} : (2 * n + 1) ^ 2 / 4 = n * (n + 1) := by grind

variable {V : Type*} {C : Sym2 V → Fin 2} {u v w x y z : V}

variable (C) in
/-- The definition of an edge (represented by its endpoints)
**n**ot being **i**n a **m**onochromatic **t**riangle. `NIMT x x` is always `False`. -/
def NIMT (x y : V) : Prop :=
  x ≠ y ∧ ¬∃ z, x ≠ z ∧ y ≠ z ∧ C s(x, y) = C s(x, z) ∧ C s(x, y) = C s(y, z)

namespace NIMT

lemma symm (hxy : NIMT C x y) : NIMT C y x := by
  grind [NIMT]

lemma irrefl : ¬NIMT C x x := by
  simp [NIMT]

lemma resolve (hxy : NIMT C x y) (hxz : x ≠ z) (hyz : y ≠ z) (hc : C s(x, y) = C s(x, z)) :
    C s(x, y) ≠ C s(y, z) ∧ C s(x, z) ≠ C s(y, z) := by
  rw [← hc, and_self]
  contrapose! hxy
  simp_rw [NIMT, not_and_or, not_not]
  tauto

end NIMT

variable (C) in
/-- A triangle of `NIMT` edges and the object intensely studied in Keevash and Sudakov's proof. -/
structure AFrame where
  /-- The A-frame's vertices – `x` is considered the head -/
  (x y z : V)
  /-- `xy` is `NIMT` -/
  nxy : NIMT C x y
  /-- `xz` is `NIMT` -/
  nxz : NIMT C x z
  /-- `yz` is `NIMT` -/
  nyz : NIMT C y z
  /-- `xz` is coloured differently from `yz` -/
  cxy : C s(x, z) ≠ C s(y, z)
  /-- `xy` is coloured differently from `yz` -/
  cxz : C s(x, y) ≠ C s(y, z)

-- An edge is "blue" with respect to an A-frame if its colour matches that of `yz`
-- and "red" if its colour matches that of `xy` and `xz`.

namespace AFrame

variable (A : AFrame C)

lemma cyz : C s(A.x, A.y) = C s(A.x, A.z) := by
  grind [A.cxy, A.cxz]

/-- All edges from `x` to outside the A-frame are blue. -/
lemma blue_xw (hw : w ∉ [A.x, A.y, A.z]) : C s(A.x, w) = C s(A.y, A.z) := by
  have h := A.nyz
  contrapose! h
  obtain ⟨hwx, hwy, hwz⟩ : A.x ≠ w ∧ A.y ≠ w ∧ A.z ≠ w := by grind
  have r₁ := A.nxy.resolve hwx hwy (by grind [A.cxz])
  have r₂ := A.nxz.resolve hwx hwz (by grind [A.cxy])
  grind [NIMT]

variable (nxw : NIMT C A.x w ∧ A.y ≠ w ∧ A.z ≠ w)

include nxw

/-- Suppose `xw` is a fourth `NIMT` edge.
Then for all fifth vertices `v`, `xv` is blue and `wv` is red. -/
lemma blue_xv_red_wv (hv : v ∉ [w, A.x, A.y, A.z]) :
    C s(A.x, v) = C s(A.x, w) ∧ C s(w, v) ≠ C s(A.x, w) := by
  obtain hw : w ∉ [A.x, A.y, A.z] := by grind [NIMT]
  have bxw := A.blue_xw hw
  rw [List.mem_cons, not_or, ← Ne.eq_def] at hv
  have bxv := A.blue_xw hv.2
  grind [nxw.1.resolve (show A.x ≠ v by grind) hv.1.symm (by grind)]

/-- Suppose `xw` is a fourth `NIMT` edge.
Then for all edges `uv` not incident to `wxyz`, `uv` is not `NIMT`. -/
lemma not_NIMT_uv (hu : u ∉ [w, A.x, A.y, A.z]) (hv : v ∉ [w, A.x, A.y, A.z]) : ¬NIMT C u v := by
  have eu := A.blue_xv_red_wv nxw hu
  have ev := A.blue_xv_red_wv nxw hv
  rw [NIMT, not_and_not_right]
  intro nuv
  by_cases huv : C s(u, v) = C s(A.x, w)
  · use A.x; grind
  · use w; grind

open Set in
/-- Suppose `xw` is a fourth `NIMT` edge and there are at least six vertices.
Then for all fifth vertices `v`, at least one of `xv` and `wv` is not `NIMT`. -/
lemma not_NIMT_xv_or_not_NIMT_wv (hc : 6 ≤ ENat.card V) (hv : v ∉ [w, A.x, A.y, A.z]) :
    ¬NIMT C A.x v ∨ ¬NIMT C w v := by
  rw [← encard_univ] at hc
  have lb : encard {v, w, A.x, A.y, A.z} ≤ 5 := by
    change _ ≤ (1 + 1 + 1 + 1 + 1 : ℕ∞)
    iterate 4 refine (encard_insert_le ..).trans (add_le_add_left ?_ 1)
    simp
  have nec : 1 ≤ (univ \ {v, w, A.x, A.y, A.z}).encard := by
    rw [encard_diff (subset_univ _) (by simp), show (1 : ℕ∞) = 6 - 5 by rfl]
    exact tsub_le_tsub hc lb
  rw [one_le_encard_iff_nonempty, ← compl_eq_univ_diff] at nec
  obtain ⟨u, hu⟩ := nec
  replace hu : u ≠ v ∧ u ∉ [w, A.x, A.y, A.z] := by grind
  obtain ⟨huv, hu⟩ := hu
  have eu := A.blue_xv_red_wv nxw hu
  have ev := A.blue_xv_red_wv nxw hv
  simp_rw [NIMT, not_and_not_right]
  by_cases huv : C s(u, v) = C s(A.x, w)
  · exact .inl fun _ ↦ ⟨u, by grind⟩
  · exact .inr fun _ ↦ ⟨u, by grind⟩

end AFrame

open Finset

namespace SimpleGraph

open _root_.SimpleGraph

variable (C) in
/-- The graph consisting of all `NIMT` edges with respect to the given edge 2-colouring. -/
def nimt : SimpleGraph V where
  Adj := NIMT C
  symm _ _ e := e.symm
  loopless := ⟨fun _ ↦ NIMT.irrefl⟩

lemma nimt_adj : (nimt C).Adj x y ↔ NIMT C x y := Iff.rfl

/-- Given a set `s` of vertices and another vertex `x` such that all edges from `x` to `s`
are the same colour, `nimt C` restricted to `s` is triangle-free. -/
lemma cliqueFree_induce_nimt {c : Fin 2} {s : Set V} (hx : x ∉ s) (hc : ∀ y ∈ s, C s(x, y) = c) :
    ((nimt C).induce s).CliqueFree 3 := by
  unfold CliqueFree
  by_contra! h
  obtain ⟨Q, hQ⟩ := h
  classical rw [is3Clique_iff] at hQ
  obtain ⟨⟨u, mu⟩, ⟨v, mv⟩, ⟨w, mw⟩, huv, huw, hvw, rfl⟩ := hQ
  simp_rw [comap_adj, Function.Embedding.subtype_apply, nimt_adj] at huv huw hvw
  have ruv : C s(u, v) ≠ c := by
    unfold NIMT at huv
    contrapose! huv
    exact fun _ ↦ ⟨x, by grind⟩
  have ruw : C s(u, w) ≠ c := by
    unfold NIMT at huw
    contrapose! huw
    exact fun _ ↦ ⟨x, by grind⟩
  have rvw : C s(v, w) ≠ c := by
    unfold NIMT at hvw
    contrapose! hvw
    exact fun _ ↦ ⟨x, by grind⟩
  grind [huv.resolve huw.1 hvw.1 (by grind)]

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (V) in
/-- An abbreviation for the fixed number of vertices `n` in the graph. -/
abbrev n : ℕ := Fintype.card V

/-- **Mantel's theorem**, Turán's theorem specialised to triangles. -/
lemma _root_.SimpleGraph.CliqueFree.card_edgeFinset_le_3
    (cf : G.CliqueFree 3) : #G.edgeFinset ≤ n V ^ 2 / 4 := by
  have key : _ ≤ (n V ^ 2 - (n V % 2) ^ 2) * (2 - 1) / (2 * 2) + (n V % 2).choose 2 :=
    cf.card_edgeFinset_le
  rw [← card_edgeFinset_turanGraph] at key
  have key2 := @mul_card_edgeFinset_turanGraph_le (n V) 2
  lia

variable [DecidableEq V]

open Function.Embedding in
lemma card_filter_edgeFinset_eq_card_induce (s : Finset V) :
    #{x ∈ G.edgeFinset | ∀ v ∈ x, v ∈ s} = #(G.induce s).edgeFinset := by
  rw [← card_map (sym2Map (subtype _))]
  congr
  ext e
  cases e using Sym2.inductionOn with | _ a b
  suffices G.Adj a b ∧ a ∈ s ∧ b ∈ s ↔
      ∃ a' ∈ s, ∃ b', G.Adj a' b' ∧ b' ∈ s ∧ (a' = a ∧ b' = b ∨ a' = b ∧ b' = a) by
    simpa [subtype, Sym2.exists]
  simp only [and_or_left, exists_or, ↓existsAndEq]
  tauto

lemma card_edgeFinset_decomp (s : Finset V) :
    #G.edgeFinset = #(G.induce s).edgeFinset + #{e ∈ s ×ˢ sᶜ | G.Adj e.1 e.2} +
      #(G.induce (sᶜ : Finset V)).edgeFinset := by
  rw [← card_filter_add_card_filter_not (∀ v ∈ ·, v ∈ s)]
  nth_rw 2 [← card_filter_add_card_filter_not (∀ v ∈ ·, v ∈ sᶜ), add_comm]
  rw [← add_assoc]
  congr!
  · exact card_filter_edgeFinset_eq_card_induce _
  · let f (e : V × V) := s(e.1, e.2)
    have fio : Set.InjOn f ({e ∈ s ×ˢ sᶜ | G.Adj e.1 e.2} : Finset _) := by
      rintro ⟨v₁, v₂⟩ mv ⟨w₁, w₂⟩ mw h
      grind [mem_compl]
    rw [← card_image_of_injOn fio]
    congr
    ext e
    cases e using Sym2.inductionOn with | _ a b
    simp_rw [mem_image, mem_filter, f, Prod.exists, mem_edgeFinset, mem_edgeSet]
    suffices (G.Adj a b ∧ (a ∈ s → b ∉ s)) ∧ (a ∉ s → b ∈ s) ↔
        (a ∈ s ∧ b ∉ s) ∧ G.Adj a b ∨ (b ∈ s ∧ a ∉ s) ∧ G.Adj b a by simpa [and_or_left, exists_or]
    tauto
  · rw [filter_filter, ← card_filter_edgeFinset_eq_card_induce]
    congr! with e
    cases e using Sym2.inductionOn with | _ a b
    simp_all

instance : DecidableRel (NIMT C) := by
  unfold NIMT
  infer_instance

instance : DecidableRel (nimt C).Adj :=
  inferInstanceAs <| DecidableRel (NIMT C)

/-- Given an A-frame `xyz` in an edge 2-colouring of `K_n` where `n ≥ 6`
and a fourth `NIMT` edge `xw`, there can be at most `3n-6` `NIMT` edges. -/
lemma card_edgeFinset_nimt_le_of_NIMT_xw
    (hn : 6 ≤ n V) (A : AFrame C) (nxw : NIMT C A.x w ∧ A.y ≠ w ∧ A.z ≠ w) :
    #(nimt C).edgeFinset ≤ 3 * n V - 6 := by
  have c4 : #{w, A.x, A.y, A.z} = 4 := by grind [nxw.1.1, A.nxy.1, A.nxz.1, A.nyz.1]
  rw [show 3 * n V - 6 = 6 + 3 * (n V - 4) + 0 by lia, card_edgeFinset_decomp {w, A.x, A.y, A.z}]
  gcongr
  · apply card_edgeFinset_le_card_choose_two.trans_eq
    rw [← Set.toFinset_card, toFinset_coe, c4]
    rfl
  · rw [product_eq_biUnion_right, card_filter, sum_biUnion fun _ _ _ _ _ ↦ by simp; grind]
    calc
      _ ≤ ∑ x ∈ {w, A.x, A.y, A.z}ᶜ, 3 := sum_le_sum fun v mv ↦ ?_
      _ = 3 * (n V - 4) := by rw [sum_const, smul_eq_mul, card_compl, c4, mul_comm]
    rw [sum_image (by simp)]
    iterate 3 rw [sum_insert (by grind)]
    simp_rw [sum_singleton, nimt_adj]
    replace mv : v ∉ [w, A.x, A.y, A.z] := by grind [mem_compl]
    replace hn : 6 ≤ ENat.card V := by rwa [ENat.card_eq_coe_fintype_card, Nat.ofNat_le_cast]
    grind [A.not_NIMT_xv_or_not_NIMT_wv nxw hn mv]
  · rw [Nat.le_zero, card_eq_zero, edgeFinset_eq_empty]
    ext ⟨u, hu⟩ ⟨v, hv⟩
    simp_rw [comap_adj, nimt_adj, Function.Embedding.subtype_apply, bot_adj, iff_false]
    exact A.not_NIMT_uv nxw (by grind [mem_compl]) (by grind [mem_compl])

/-- Given an A-frame `xyz` and strictly more than `n^2 / 4` edges with `n ≥ 10`,
all edges from `x` to outside the A-frame are not `NIMT`. -/
lemma not_NIMT_xw_of_lt_card_edgeFinset_nimt
    (hn : 10 ≤ n V) (A : AFrame C) (hw : A.y ≠ w ∧ A.z ≠ w)
    (he : n V ^ 2 / 4 < #(nimt C).edgeFinset) : ¬NIMT C A.x w := by
  contrapose! he
  apply (card_edgeFinset_nimt_le_of_NIMT_xw (by lia) A ⟨he, hw⟩).trans
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := (n V).even_or_odd
  · rw [hk, ← two_mul, Nat.sq_even_div_four, show 3 * (2 * k) - 6 = 6 * (k - 1) by lia]
    calc
      _ ≤ (k + 1) * (k - 1) := by gcongr; lia
      _ ≤ _ := by rw [← Nat.pow_two_sub_pow_two]; lia
  · rw [hk, Nat.sq_odd_div_four, show 3 * (2 * k + 1) - 6 = 6 * k - 3 by lia]
    calc
      _ ≤ (k + 1) * k - 3 := by gcongr; lia
      _ ≤ _ := by lia

/-- Given an A-frame `xyz` and strictly more than `n^2 / 4` edges,
there are at least `n-1` `NIMT` edges between `xyz` and the other vertices. -/
lemma card_filter_NIMT_prod_compl_ge
    (hn : 10 ≤ n V) (A : AFrame C) (he : n V ^ 2 / 4 < #(nimt C).edgeFinset) :
    n V - 1 ≤ #{e ∈ {A.x, A.y, A.z} ×ˢ {A.x, A.y, A.z}ᶜ | NIMT C e.1 e.2} := by
  set T : Finset V := {A.x, A.y, A.z}
  have c3 : #T = 3 := by grind [A.nxy.1, A.nxz.1, A.nyz.1]
  have decomp := card_edgeFinset_decomp (G := nimt C) T
  simp_rw [nimt_adj] at decomp
  have ub1 : #((nimt C).induce T).edgeFinset ≤ 3 := by
    apply card_edgeFinset_le_card_choose_two.trans_eq
    rw [← Set.toFinset_card, toFinset_coe, c3]
    rfl
  have cf : ((nimt C).induce (Tᶜ : Finset V)).CliqueFree 3 :=
    cliqueFree_induce_nimt (x := A.x) (c := C s(A.y, A.z)) (by simp [T])
      fun w mw ↦ A.blue_xw (by grind [mem_compl])
  have ub2 : #((nimt C).induce (Tᶜ : Finset V)).edgeFinset ≤ (n V - 3) ^ 2 / 4 := by
    convert cf.card_edgeFinset_le_3
    simp_rw [SetLike.coe_sort_coe, Fintype.card_coe, card_compl, c3]
  suffices n V - 3 + 2 ≤ (n V - 3 + 3) ^ 2 / 4 - (n V - 3) ^ 2 / 4 - 3 by lia
  lia

/-- There are at least two vertices `w` other than `x` for which `wy` and `wz` are `NIMT`.

Proved by Aristotle -/
lemma card_filter_NIMT_compl_ge
    (hn : 10 ≤ n V) (A : AFrame C) (he : n V ^ 2 / 4 < #(nimt C).edgeFinset) :
    2 ≤ #{w ∈ {A.x, A.y, A.z}ᶜ | NIMT C w A.y ∧ NIMT C w A.z} := by
  have cr := card_filter_NIMT_prod_compl_ge hn A he
  rw [card_filter, sum_product, sum_insert (by simp [A.nxy.1, A.nxz.1]),
    sum_insert (by simp [A.nyz.1]), sum_singleton] at cr
  simp_rw [← card_filter] at cr
  have x0 : #({w ∉ {A.x, A.y, A.z} | NIMT C A.x w}) = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    exact fun w mw ↦ not_NIMT_xw_of_lt_card_edgeFinset_nimt hn A (by grind [mem_compl]) he
  rw [x0, zero_add] at cr
  have tb (P : V → Prop) [DecidablePred P] : #({w ∉ {A.x, A.y, A.z} | P w}) ≤ n V - 3 := by
    apply (card_filter_le ..).trans_eq
    grind [card_compl, A.nxy.1, A.nxz.1, A.nyz.1]
  simp_rw [show ∀ w, NIMT C w A.y ∧ NIMT C w A.z ↔ NIMT C A.y w ∧ NIMT C A.z w by grind [NIMT.symm]]
  have iep := card_union_add_card_inter
    {w ∉ {A.x, A.y, A.z} | NIMT C A.y w} {w ∉ {A.x, A.y, A.z} | NIMT C A.z w}
  rw [← filter_or, ← filter_and] at iep
  grind

/-- Given an A-frame `xyz` and strictly more than `n^2 / 4` edges,
if `wz` and `wy` are `NIMT` they must be red (and hence `wyz` is an A-frame). -/
lemma red_wz_wy_of_NIMT
    (hn : 10 ≤ n V) (A : AFrame C) (hw : NIMT C w A.y ∧ NIMT C w A.z)
    (he : n V ^ 2 / 4 < #(nimt C).edgeFinset) :
    C s(w, A.z) ≠ C s(A.y, A.z) ∧ C s(w, A.y) ≠ C s(A.y, A.z) := by
  obtain rfl | hwx := eq_or_ne w A.x
  · exact ⟨A.cxy, A.cxz⟩
  by_contra h
  simp_rw [not_and_or, not_ne_iff] at h
  wlog hwy : C s(w, A.y) = C s(A.y, A.z) generalizing A
  · let A' : AFrame C :=
      ⟨A.x, A.z, A.y, A.nxz, A.nxy, A.nyz.symm, by grind [A.cxz], by grind [A.cxy]⟩
    grind [this A' hw.symm (by grind)]
  by_cases hwz : C s(w, A.z) = C s(A.y, A.z)
  · grind [A.nyz.resolve hw.1.1.symm hw.2.1.symm (by grind)]
  let B : AFrame C := ⟨A.y, w, A.z, hw.1.symm, A.nyz, hw.2, by grind, by grind⟩
  refine not_NIMT_xw_of_lt_card_edgeFinset_nimt hn B ?_ he A.nxy.symm
  exact ⟨hwx, A.nxz.1.symm⟩

/-- An extracted part of `erdos639_pre`. -/
lemma card_edgeFinset_induce_le_seven (hn : v ≠ w ∧ w ≠ x ∧ x ≠ v)
    (n₁ : ¬NIMT C v w) (n₂ : ¬NIMT C w x) (n₃ : ¬NIMT C x v) :
    #((nimt C).induce ({v, w, x, y, z} : Finset V)).edgeFinset ≤ 7 := by
  set S : Finset V := {v, w, x, y, z}
  let v' : { u // u ∈ (S : Set V) } := ⟨v, by simp [S]⟩
  let w' : { u // u ∈ (S : Set V) } := ⟨w, by simp [S]⟩
  let x' : { u // u ∈ (S : Set V) } := ⟨x, by simp [S]⟩
  have key : ((nimt C).induce S).edgeFinset ⊆
      (⊤ : SimpleGraph S).edgeFinset \ {s(v', w'), s(w', x'), s(x', v')} := fun e me ↦ by
    simp_rw [mem_sdiff, mem_insert, mem_singleton, not_or]
    refine ⟨mem_of_subset ?_ me, ?_, ?_, ?_⟩
    · rw [edgeFinset_subset_edgeFinset]
      exact le_top
    all_goals
      by_contra! h
      subst h
      simp_all [v', w', x', nimt_adj, Function.Embedding.subtype]
  apply (card_le_card key).trans
  have sub : {s(v', w'), s(w', x'), s(x', v')} ⊆ (⊤ : SimpleGraph S).edgeFinset := by
    simp_rw [insert_subset_iff, singleton_subset_iff, mem_edgeFinset, mem_edgeSet, top_adj,
      v', w', x', ← Subtype.coe_ne_coe]
    exact hn
  have c3 : #{s(v', w'), s(w', x'), s(x', v')} = 3 := by grind
  rw [card_sdiff_of_subset sub, c3, card_edgeFinset_top_eq_card_choose_two]
  apply Nat.sub_le_of_le_add
  rw [show 7 + 3 = Nat.choose 5 2 by rfl]
  apply Nat.choose_le_choose
  rw [Fintype.card_coe]
  exact card_le_five

/-- If an A-frame exists in an edge 2-colouring of `K_n` with `n ≥ 10`,
there can be at most `n^2 / 4` `NIMT` edges. -/
lemma erdos639_pre (hn : 10 ≤ n V) (A : AFrame C) : #(nimt C).edgeFinset ≤ n V ^ 2 / 4 := by
  by_contra! he
  have ox := card_filter_NIMT_compl_ge hn A he
  rw [le_card_iff_exists_subset_card] at ox
  obtain ⟨ox, sox, cox⟩ := ox
  rw [card_eq_two] at cox
  obtain ⟨v, w, hvw, rfl⟩ := cox
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_filter, mem_compl] at sox
  have rvzy := red_wz_wy_of_NIMT hn A sox.1.2 he
  have rwzy := red_wz_wy_of_NIMT hn A sox.2.2 he
  let Λ : AFrame C := ⟨v, A.y, A.z, sox.1.2.1, sox.1.2.2, A.nyz, rvzy.1, rvzy.2⟩
  let Δ : AFrame C := ⟨w, A.y, A.z, sox.2.2.1, sox.2.2.2, A.nyz, rwzy.1, rwzy.2⟩
  let S : Finset V := {v, w, A.x, A.y, A.z}
  have c5 : #S = 5 := by grind [A.nxy.1, A.nxz.1, A.nyz.1]
  apply absurd he
  rw [not_lt, card_edgeFinset_decomp S]
  calc
    _ ≤ 7 + 2 * (n V - 5) + (n V - 5) ^ 2 / 4 := by
      gcongr
      · have n₁ := not_NIMT_xw_of_lt_card_edgeFinset_nimt (w := w) hn Λ (by grind) he
        have n₂ := not_NIMT_xw_of_lt_card_edgeFinset_nimt (w := A.x) hn Δ
          (by grind [A.nxy.1, A.nxz.1]) he
        have n₃ := not_NIMT_xw_of_lt_card_edgeFinset_nimt (w := v) hn A (by grind) he
        exact card_edgeFinset_induce_le_seven (by grind) n₁ n₂ n₃
      · unfold S
        rw [product_eq_biUnion_right, card_filter, sum_biUnion fun _ _ _ _ _ ↦ by simp; grind]
        calc
          _ ≤ ∑ x ∈ Sᶜ, 2 := sum_le_sum fun u mu ↦ ?_
          _ = _ := by rw [sum_const, smul_eq_mul, card_compl, c5, mul_comm]
        replace mu : u ∉ [v, w, A.x, A.y, A.z] := by grind [mem_compl]
        rw [sum_image (by simp)]
        simp_rw [nimt_adj]
        rw [sum_insert (by grind)]
        have n₁ := not_NIMT_xw_of_lt_card_edgeFinset_nimt (w := u) hn Λ (by grind) he
        simp_rw [Λ] at n₁
        simp_rw [n₁, ite_false, zero_add]
        rw [sum_insert (by grind)]
        have n₂ := not_NIMT_xw_of_lt_card_edgeFinset_nimt (w := u) hn Δ (by grind) he
        simp_rw [Δ] at n₂
        simp_rw [n₂, ite_false, zero_add]
        rw [sum_insert (by grind [A.nxy.1, A.nxz.1])]
        have n₃ := not_NIMT_xw_of_lt_card_edgeFinset_nimt (w := u) hn A (by grind) he
        simp_rw [n₃, ite_false, zero_add]
        rw [sum_pair (by grind [A.nyz.1])]
        lia
      · have cf : ((nimt C).induce (Sᶜ : Finset V)).CliqueFree 3 :=
          cliqueFree_induce_nimt (x := A.x) (c := C s(A.y, A.z)) (by simp [S]) fun u mu ↦
            A.blue_xw (by grind [mem_compl])
        convert cf.card_edgeFinset_le_3
        simp_rw [SetLike.coe_sort_coe, Fintype.card_coe, card_compl, c5]
    _ ≤ _ := by
      conv_rhs => rw [show n V = n V - 5 + 5 by lia]
      obtain ⟨k, hk⟩ | ⟨k, hk⟩ := (n V - 5).even_or_odd
      · rw [hk, ← two_mul, Nat.sq_even_div_four, show 2 * k + 5 = 2 * (k + 2) + 1 by lia,
          Nat.sq_odd_div_four]
        lia
      · rw [hk, Nat.sq_odd_div_four, show 2 * k + 1 + 5 = 2 * (k + 3) by lia, Nat.sq_even_div_four]
        lia

/-- If there are strictly greater than `n^2 / 4` `NIMT` edges, an A-frame always exists.

Proved by Aristotle -/
lemma nonempty_aframe_of_card_edgeFinset_gt (he : n V ^ 2 / 4 < #(nimt C).edgeFinset) :
    Nonempty (AFrame C) := by
  rw [← not_le] at he
  replace he := CliqueFree.card_edgeFinset_le_3.mt he
  simp_rw [CliqueFree, not_forall, not_not] at he
  obtain ⟨Q, hQ⟩ := he
  rw [is3Clique_iff] at hQ
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := hQ
  rw [nimt_adj] at hab hac hbc
  by_cases e₁ : C s(a, b) = C s(a, c)
  · exact ⟨⟨a, b, c, hab, hac, hbc, by grind [NIMT], by grind [NIMT]⟩⟩
  · by_cases e₂ : C s(a, b) = C s(b, c)
    · exact ⟨⟨b, c, a, hbc, hab.symm, hac.symm, by grind, by grind⟩⟩
    · exact ⟨⟨c, a, b, hac.symm, hbc.symm, hab, by grind, by grind⟩⟩

/-- **Erdős Problem 639.**
Any edge 2-colouring of `K_n` with `n ≥ 10` has at most `n^2 / 4` `NIMT` edges. -/
theorem erdos639 (hn : 10 ≤ n V) : #(nimt C).edgeFinset ≤ n V ^ 2 / 4 := by
  by_contra! he
  obtain ⟨A⟩ := nonempty_aframe_of_card_edgeFinset_gt he
  grind [erdos639_pre hn A]

#print axioms erdos639
-- 'Erdos639.SimpleGraph.erdos639' depends on axioms: [propext, Classical.choice, Quot.sound]

end SimpleGraph

end Erdos639
