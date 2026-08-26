/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1091.Voss
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange

/-!
# The finite cycle routing in Voss's lasso argument

The routes are those listed in the three-chord cycle-routing lemma of
`tex/1091.tex`.  A route is represented by an injective finite sequence of
vertices.  This interface separates the integer interval calculations from
the conversion to Mathlib walks and their unordered chord edges.
-/

open SimpleGraph

namespace Erdos1091.Voss.Routing

universe u

/-- An injective sequence of `n+1` vertices with consecutive adjacencies. -/
structure IndexedPath {V : Type u} (G : SimpleGraph V) (n : ℕ) where
  vertex : Fin (n + 1) → V
  injective : Function.Injective vertex
  adjacent : ∀ i : Fin n, G.Adj (vertex i.castSucc) (vertex i.succ)

namespace IndexedPath

variable {V : Type u} {G : SimpleGraph V} {n : ℕ}

theorem chain (P : IndexedPath G n) : (List.ofFn P.vertex).IsChain G.Adj := by
  rw [List.isChain_ofFn]
  intro i hi
  exact P.adjacent ⟨i, by omega⟩

/-- Convert an indexed path to the ordinary walk with its displayed ends. -/
def toWalk (P : IndexedPath G n) : G.Walk (P.vertex 0) (P.vertex (Fin.last n)) :=
  (Walk.ofSupport (List.ofFn P.vertex) (by simp) P.chain).copy
    (by exact List.head_ofFn _) (by exact List.getLast_ofFn_succ P.vertex)

@[simp] theorem support_toWalk (P : IndexedPath G n) :
    P.toWalk.support = List.ofFn P.vertex := by
  exact (Walk.support_copy _ _ _).trans (Walk.support_ofSupport _ _)

@[simp] theorem length_toWalk (P : IndexedPath G n) : P.toWalk.length = n := by
  have h := P.toWalk.length_support
  rw [support_toWalk, List.length_ofFn] at h
  omega

theorem isPath_toWalk (P : IndexedPath G n) : P.toWalk.IsPath := by
  apply Walk.IsPath.mk'
  rw [support_toWalk, List.nodup_ofFn]
  exact P.injective

@[simp] theorem getVert_toWalk (P : IndexedPath G n) (i : Fin (n + 1)) :
    P.toWalk.getVert i.val = P.vertex i := by
  rw [Walk.getVert_eq_support_getElem P.toWalk (by simp; omega)]
  simp only [support_toWalk, List.getElem_ofFn]

theorem mem_support_toWalk (P : IndexedPath G n) (i : Fin (n + 1)) :
    P.vertex i ∈ P.toWalk.support := by
  rw [support_toWalk]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

/-- Distinct nonconsecutive positions joined by an ambient edge give a
chord of the indexed path. -/
theorem isChord_of_separated (P : IndexedPath G n) (i j : Fin (n + 1))
    (hadj : G.Adj (P.vertex i) (P.vertex j))
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) :
    P.toWalk.IsChord s(P.vertex i, P.vertex j) := by
  refine ⟨hadj, ?_, P.mem_support_toWalk i, P.mem_support_toWalk j⟩
  intro he
  obtain ⟨k, hk, he⟩ := P.toWalk.mk_mem_edges_iff_exists.mp he
  have hkn : k < n := by simpa using hk
  let a : Fin (n + 1) := ⟨k, by omega⟩
  let b : Fin (n + 1) := ⟨k + 1, by omega⟩
  have hka : P.toWalk.getVert k = P.vertex a := P.getVert_toWalk a
  have hkb : P.toWalk.getVert (k + 1) = P.vertex b := P.getVert_toWalk b
  rw [hka, hkb, Sym2.eq_iff] at he
  rcases he with ⟨hai, hbj⟩ | ⟨haj, hbi⟩
  · have ha := congrArg Fin.val (P.injective hai)
    have hb := congrArg Fin.val (P.injective hbj)
    exact hij (by simpa [a, b] using ha.symm ▸ hb)
  · have ha := congrArg Fin.val (P.injective haj)
    have hb := congrArg Fin.val (P.injective hbi)
    exact hji (by simpa [a, b] using ha.symm ▸ hb)

/-- Four displayed positions can certify two distinct path chords. -/
theorem two_chords (P : IndexedPath G n) (i j k l : Fin (n + 1))
    (hijAdj : G.Adj (P.vertex i) (P.vertex j))
    (hklAdj : G.Adj (P.vertex k) (P.vertex l))
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val)
    (hkl : k.val + 1 ≠ l.val) (hlk : l.val + 1 ≠ k.val)
    (hne : s(i, j) ≠ s(k, l)) :
    ∃ e f : Sym2 V, e ≠ f ∧ P.toWalk.IsChord e ∧ P.toWalk.IsChord f := by
  refine ⟨s(P.vertex i, P.vertex j), s(P.vertex k, P.vertex l), ?_,
    P.isChord_of_separated i j hijAdj hij hji,
    P.isChord_of_separated k l hklAdj hkl hlk⟩
  intro he
  apply hne
  rcases Sym2.eq_iff.mp he with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨P.injective hi, P.injective hj⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨P.injective hi, P.injective hj⟩)

end IndexedPath

/-- The rim and the three specified chords, expressed without dependent indices. -/
def IndexAdj (n j k l a b : ℕ) : Prop :=
  a + 1 = b ∨ b + 1 = a ∨
  (a = n ∧ b = 0) ∨ (b = n ∧ a = 0) ∨
  (a = n ∧ b = j) ∨ (b = n ∧ a = j) ∨
  (a = 1 ∧ b = k) ∨ (b = 1 ∧ a = k) ∨
  (a = j + 1 ∧ b = l) ∨ (b = j + 1 ∧ a = l)

/-- Select a displayed edge before invoking linear arithmetic.  Keeping the
disjunction outside `omega` avoids an unnecessary exponential case split. -/
macro "route_edge" : tactic => `(tactic|
  first
  | exact Or.inl (by omega)
  | exact Or.inr (Or.inl (by omega))
  | exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))
  | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))))))
  | exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))))))))
/-- The numerical restrictions forced by the three edges being cycle chords. -/
structure Configuration (n j k l : ℕ) : Prop where
  n_ge : 3 ≤ n
  j_ge : 1 ≤ j
  j_le : j + 2 ≤ n
  k_ge : 3 ≤ k
  k_le : k ≤ n
  l_le : l ≤ n
  l_ne_left : l ≠ j
  l_ne_mid : l ≠ j + 1
  l_ne_right : l ≠ j + 2

/-- A finite route, with all arithmetic obligations visible as propositions. -/
structure NumericRoute (n t : ℕ) (A : ℕ → ℕ → Prop) where
  length : ℕ
  vertex : ℕ → ℕ
  bounded : ∀ i ≤ length, vertex i ≤ n
  injective : ∀ i ≤ length, ∀ h ≤ length, vertex i = vertex h → i = h
  first : vertex 0 = t
  last : vertex length = 0
  adjacent : ∀ i < length, A (vertex i) (vertex (i + 1))

namespace NumericRoute

/-- Two distinct, nonconsecutive pairs of positions joined by ambient edges. -/
def HasTwoChords {n t : ℕ} {A : ℕ → ℕ → Prop} (R : NumericRoute n t A) : Prop :=
  ∃ p q r s : ℕ, p ≤ R.length ∧ q ≤ R.length ∧ r ≤ R.length ∧ s ≤ R.length ∧
    A (R.vertex p) (R.vertex q) ∧ A (R.vertex r) (R.vertex s) ∧
    p + 1 ≠ q ∧ q + 1 ≠ p ∧ r + 1 ≠ s ∧ s + 1 ≠ r ∧
    (p ≠ r ∨ q ≠ s) ∧ (p ≠ s ∨ q ≠ r)

variable {V : Type u} {G : SimpleGraph V} {n t : ℕ} {A : ℕ → ℕ → Prop}

/-- Interpret a numerical route in any injectively labelled ambient graph. -/
def toIndexedPath (R : NumericRoute n t A) (v : Fin (n + 1) → V)
    (hv : Function.Injective v)
    (hA : ∀ a b : Fin (n + 1), A a.val b.val → G.Adj (v a) (v b)) :
    IndexedPath G R.length where
  vertex i := v ⟨R.vertex i.val, by have := R.bounded i.val (by omega); omega⟩
  injective := by
    intro i j he
    apply Fin.ext
    exact R.injective i.val (by omega) j.val (by omega) (congrArg Fin.val (hv he))
  adjacent i := hA _ _ (R.adjacent i.val i.isLt)

theorem exists_walk (R : NumericRoute n t A) (hR : R.HasTwoChords)
    (htn : t ≤ n) (v : Fin (n + 1) → V) (hv : Function.Injective v)
    (hA : ∀ a b : Fin (n + 1), A a.val b.val → G.Adj (v a) (v b)) :
    ∃ P : G.Walk (v ⟨t, by omega⟩) (v 0), P.IsPath ∧
      (∀ w ∈ P.support, ∃ i, v i = w) ∧
      ∃ e f : Sym2 V, e ≠ f ∧ P.IsChord e ∧ P.IsChord f := by
  let P := R.toIndexedPath v hv hA
  have hfirst : P.vertex 0 = v ⟨t, by omega⟩ := by
    change v ⟨R.vertex 0, _⟩ = _
    congr 1
    exact Fin.ext R.first
  have hlast : P.vertex (Fin.last R.length) = v 0 := by
    change v ⟨R.vertex R.length, _⟩ = _
    congr 1
    exact Fin.ext R.last
  let Q := P.toWalk.copy hfirst hlast
  have hsup : Q.support = P.toWalk.support := Walk.support_copy _ _ _
  have hedge : Q.edges = P.toWalk.edges := Walk.edges_copy _ _ _
  refine ⟨Q, (Walk.isPath_copy _ _ _).mpr P.isPath_toWalk, ?_, ?_⟩
  · intro w hw
    rw [hsup, IndexedPath.support_toWalk, List.mem_ofFn] at hw
    obtain ⟨i, hi⟩ := hw
    exact ⟨⟨R.vertex i.val, by have := R.bounded i.val (by omega); omega⟩, hi⟩
  obtain ⟨p, q, r, s, hp, hq, hr, hs, hpq, hrs, hpq', hqp', hrs', hsr', hne, hne'⟩ := hR
  let a : Fin (R.length + 1) := ⟨p, by omega⟩
  let b : Fin (R.length + 1) := ⟨q, by omega⟩
  let c : Fin (R.length + 1) := ⟨r, by omega⟩
  let d : Fin (R.length + 1) := ⟨s, by omega⟩
  have hadj₁ : G.Adj (P.vertex a) (P.vertex b) := hA _ _ hpq
  have hadj₂ : G.Adj (P.vertex c) (P.vertex d) := hA _ _ hrs
  have hpair : s(a, b) ≠ s(c, d) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · have := congrArg Fin.val hac
      have := congrArg Fin.val hbd
      dsimp [a, b, c, d] at *
      omega
    · have := congrArg Fin.val had
      have := congrArg Fin.val hbc
      dsimp [a, b, c, d] at *
      omega
  obtain ⟨e, f, hef, he, hf⟩ :=
    P.two_chords a b c d hadj₁ hadj₂ hpq' hqp' hrs' hsr' hpair
  refine ⟨e, f, hef, ?_, ?_⟩
  · simpa only [Walk.IsChord, hsup, hedge] using he
  · simpa only [Walk.IsChord, hsup, hedge] using hf

end NumericRoute

namespace Configuration

variable {n j k l : ℕ} (h : Configuration n j k l)

/-- Descending a consecutive part of the rim. -/
def down (_h : Configuration n j k l) (t : ℕ) (ht : t ≤ n) :
    NumericRoute n t (IndexAdj n j k l) where
  length := t
  vertex i := t - i
  bounded := by intros; omega
  injective := by intros; omega
  first := by omega
  last := by omega
  adjacent := by intro i hi; unfold IndexAdj; omega

theorem down_two_chords_of_j_eq_one (hj : j = 1) :
    (h.down n le_rfl).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  refine ⟨0, n, n - 2, n - l, ?_⟩
  dsimp [NumericRoute.HasTwoChords, down]
  unfold IndexAdj
  omega

theorem down_two_chords_of_two_le_j (hj : 2 ≤ j) :
    (h.down n le_rfl).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  refine ⟨0, n - j, n - 1, n - k, ?_⟩
  dsimp [NumericRoute.HasTwoChords, down]
  unfold IndexAdj
  omega

theorem down_two_chords_of_internal {t : ℕ} (ht : t ≤ n)
    (hj : 2 ≤ j) (hkt : k < t) (hvk : j + 1 ≤ k)
    (hlt : l ≤ t) (hkv : k ≠ j + 1) :
    (h.down t ht).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  refine ⟨t - 1, t - k, t - (j + 1), t - l, ?_⟩
  dsimp [NumericRoute.HasTwoChords, down]
  unfold IndexAdj
  omega

/-- Ascend from `t` to `n`, then close to zero. -/
def upZero (_h : Configuration n j k l) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) :
    NumericRoute n t (IndexAdj n j k l) where
  length := n - t + 1
  vertex i := if i ≤ n - t then t + i else 0
  bounded := by intro i hi; split_ifs <;> omega
  injective := by intro i hi a ha he; split_ifs at he <;> omega
  first := by simp
  last := by simp
  adjacent := by intro i hi; split_ifs <;> route_edge

theorem upZero_two_chords {t : ℕ} (ht : 1 ≤ t) (htj : t ≤ j)
    (hl : l = 0 ∨ t ≤ l) :
    (h.upZero t ht (by have := h.j_le; omega)).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  by_cases hl0 : l = 0
  · refine ⟨n - t, j - t, j + 1 - t, n - t + 1, ?_⟩
    simp (disch := omega) only [upZero, if_pos, if_neg]
    unfold IndexAdj
    omega
  refine ⟨n - t, j - t, j + 1 - t, if l = 0 then n - t + 1 else l - t, ?_⟩
  simp (disch := omega) only [upZero, if_pos, if_neg]
  unfold IndexAdj
  omega

/-- The route `(t up j, n down (j+1), l down 0)`. -/
def upDownDown (t : ℕ) (ht : 1 ≤ t) (htj : t ≤ j)
    (hl : 1 ≤ l) (hlt : l < t) : NumericRoute n t (IndexAdj n j k l) where
  length := n - t + l + 1
  vertex i := if i ≤ j - t then t + i
    else if i ≤ n - t then n + j - t + 1 - i else n - t + l + 1 - i
  bounded := by
    have := h.j_le
    intro i hi
    split_ifs <;> omega
  injective := by
    have := h.j_le
    intro i hi a ha he
    split_ifs at he <;> omega
  first := by simp
  last := by
    have := h.j_le
    split_ifs <;> omega
  adjacent := by
    have := h.j_le
    intro i hi
    split_ifs <;> route_edge

theorem upDownDown_two_chords {t : ℕ} (ht : 1 ≤ t) (htj : t ≤ j)
    (hl : 1 ≤ l) (hlt : l < t) :
    (h.upDownDown t ht htj hl hlt).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  refine ⟨j - t, n - t, j - t + 1, n - t + l + 1, ?_⟩
  simp (disch := omega) only [upDownDown, if_pos, if_neg]
  unfold IndexAdj
  omega

/-- The route `(t down 1, n, 0)` when the first chord joins `n` to `1`. -/
def downOneZero (_h : Configuration n j k l) (t : ℕ) (hj : j = 1)
    (ht : 2 ≤ t) (htn : t < n) :
    NumericRoute n t (IndexAdj n j k l) where
  length := t + 1
  vertex i := if i < t then t - i else if i = t then n else 0
  bounded := by intro i hi; split_ifs <;> omega
  injective := by intro i hi a ha he; split_ifs at he <;> omega
  first := by split_ifs <;> omega
  last := by simp
  adjacent := by intro i hi; split_ifs <;> route_edge

theorem downOneZero_two_chords {t : ℕ} (hj : j = 1) (ht : 2 ≤ t)
    (htn : t < n) (hlt : l ≤ t) :
    (h.downOneZero t hj ht htn).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  by_cases hl0 : l = 0
  · refine ⟨t - 2, t + 1, t - 1, t + 1, ?_⟩
    simp (disch := omega) only [downOneZero, if_pos, if_neg]
    unfold IndexAdj
    omega
  · refine ⟨t - 2, t - l, t - 1, t + 1, ?_⟩
    simp (disch := omega) only [downOneZero, if_pos, if_neg]
    unfold IndexAdj
    omega

/-- The route `(t down (j+1), l up n, j down 0)`. -/
def downUpDown (t : ℕ) (hjt : j + 1 ≤ t) (htl : t < l) :
    NumericRoute n t (IndexAdj n j k l) where
  length := t + n - l + 1
  vertex i := if i < t - j then t - i
    else if i ≤ t - j + n - l then l + i - (t - j) else t + n - l + 1 - i
  bounded := by
    have := h.l_le
    intro i hi
    split_ifs <;> omega
  injective := by
    have := h.l_le
    intro i hi a ha he
    split_ifs at he <;> omega
  first := by split_ifs <;> omega
  last := by
    have := h.l_le
    split_ifs <;> omega
  adjacent := by
    have := h.l_le
    intro i hi
    split_ifs <;> route_edge

theorem downUpDown_two_chords {t : ℕ} (hjt : j + 1 ≤ t) (htl : t < l) :
    (h.downUpDown t hjt htl).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  refine ⟨t - j - 1, t + n - l + 1 - j, t - j + n - l, t + n - l + 1, ?_⟩
  simp (disch := omega) only [downUpDown, if_pos, if_neg]
  unfold IndexAdj
  omega

/-- The route `(t up n, j down 0)`. -/
def upDown (t : ℕ) (hjt : j + 1 ≤ t) (htn : t ≤ n) :
    NumericRoute n t (IndexAdj n j k l) where
  length := n - t + j + 1
  vertex i := if i ≤ n - t then t + i else n - t + j + 1 - i
  bounded := by
    have := h.j_le
    intro i hi
    split_ifs <;> omega
  injective := by intro i hi a ha he; split_ifs at he <;> omega
  first := by simp
  last := by split_ifs <;> omega
  adjacent := by intro i hi; split_ifs <;> route_edge

theorem upDown_two_chords {t : ℕ} (hj : 2 ≤ j) (hjt : j + 1 ≤ t)
    (htn : t ≤ n) (hk : k ≤ j ∨ t ≤ k) :
    (h.upDown t hjt htn).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  rcases hk with hk | hk
  · refine ⟨n - t + j, n - t + j + 1 - k, n - t, n - t + j + 1, ?_⟩
    simp (disch := omega) only [upDown, if_pos, if_neg]
    unfold IndexAdj
    omega
  · refine ⟨n - t + j, k - t, n - t, n - t + j + 1, ?_⟩
    simp (disch := omega) only [upDown, if_pos, if_neg]
    unfold IndexAdj
    omega

/-- The final route `(t down (j+1), 1 up j, n, 0)`. -/
def downUpZero (t : ℕ) (hjt : j + 1 < t) (htn : t < n) (hk : k = j + 1) :
    NumericRoute n t (IndexAdj n j k l) where
  length := t + 1
  vertex i := if i < t - j then t - i
    else if i < t then i - (t - j) + 1 else if i = t then n else 0
  bounded := by
    have := h.j_ge
    intro i hi
    split_ifs <;> omega
  injective := by
    have := h.j_ge
    intro i hi a ha he
    split_ifs at he <;> omega
  first := by split_ifs <;> omega
  last := by simp (disch := omega)
  adjacent := by
    have := h.j_ge
    intro i hi
    split_ifs <;> route_edge

theorem downUpZero_two_chords {t : ℕ} (hj : 2 ≤ j) (hjt : j + 1 < t)
    (htn : t < n) (hk : k = j + 1) :
    (h.downUpZero t hjt htn hk).HasTwoChords := by
  rcases h with ⟨hn, hjg, hjl, hkg, hkl, hll, hllft, hlmid, hlrt⟩
  refine ⟨t - j - 1, t - 1, t - j, t + 1, ?_⟩
  simp (disch := omega) only [downUpZero, if_pos, if_neg]
  unfold IndexAdj
  omega

/-- Voss's routing table covers every nonzero cycle vertex, for arbitrary
cycle length.  No bound on the number of vertices is used in this proof. -/
theorem exists_numericRoute (h : Configuration n j k l) (t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ n) :
    ∃ R : NumericRoute n t (IndexAdj n j k l), R.HasTwoChords := by
  have hjg := h.j_ge
  have hjl := h.j_le
  by_cases htnEq : t = n
  · subst t
    refine ⟨h.down n le_rfl, ?_⟩
    by_cases hj : j = 1
    · exact h.down_two_chords_of_j_eq_one hj
    · exact h.down_two_chords_of_two_le_j (by omega)
  have htn' : t < n := by omega
  by_cases htj : t ≤ j
  · by_cases hl : l = 0 ∨ t ≤ l
    · exact ⟨h.upZero t ht htn, h.upZero_two_chords ht htj hl⟩
    · exact ⟨h.upDownDown t ht htj (by omega) (by omega),
        h.upDownDown_two_chords ht htj (by omega) (by omega)⟩
  have hjt : j + 1 ≤ t := by omega
  by_cases hj : j = 1
  · by_cases hl : l ≤ t
    · exact ⟨h.downOneZero t hj (by omega) htn',
        h.downOneZero_two_chords hj (by omega) htn' hl⟩
    · exact ⟨h.downUpDown t hjt (by omega), h.downUpDown_two_chords hjt (by omega)⟩
  have hj2 : 2 ≤ j := by omega
  by_cases hk : k ≤ j ∨ t ≤ k
  · exact ⟨h.upDown t hjt htn, h.upDown_two_chords hj2 hjt htn hk⟩
  have hkt : k < t := by omega
  have hvk : j + 1 ≤ k := by omega
  by_cases hl : t < l
  · exact ⟨h.downUpDown t hjt hl, h.downUpDown_two_chords hjt hl⟩
  by_cases hkv : k = j + 1
  · exact ⟨h.downUpZero t (by omega) htn' hkv,
      h.downUpZero_two_chords hj2 (by omega) htn' hkv⟩
  · exact ⟨h.down t htn,
      h.down_two_chords_of_internal htn hj2 hkt hvk (by omega) hkv⟩

end Configuration

/-- Interpret the routing lemma in a graph whose cycle vertices have been
numbered `0,...,n`. -/
theorem exists_path_two_chords_of_numbering {V : Type u} {G : SimpleGraph V}
    {n j k l : ℕ} (h : Configuration n j k l) (f : ℕ → V)
    (hf : ∀ a ≤ n, ∀ b ≤ n, f a = f b → a = b)
    (hstep : ∀ i < n, G.Adj (f i) (f (i + 1)))
    (hclose : G.Adj (f n) (f 0))
    (hnj : G.Adj (f n) (f j)) (h1k : G.Adj (f 1) (f k))
    (hvl : G.Adj (f (j + 1)) (f l)) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ n) :
    ∃ P : G.Walk (f t) (f 0), P.IsPath ∧
      (∀ w ∈ P.support, ∃ i ≤ n, f i = w) ∧
      ∃ e g : Sym2 V, e ≠ g ∧ P.IsChord e ∧ P.IsChord g := by
  obtain ⟨R, hR⟩ := h.exists_numericRoute t ht htn
  let v : Fin (n + 1) → V := fun i => f i.val
  have hv : Function.Injective v := by
    intro a b he
    exact Fin.ext (hf a.val (by omega) b.val (by omega) he)
  have hA (a b : Fin (n + 1)) (hab : IndexAdj n j k l a.val b.val) :
      G.Adj (v a) (v b) := by
    change G.Adj (f a.val) (f b.val)
    rcases hab with hab | hba | ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hb⟩ |
      ⟨hb, ha⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩ | ⟨ha, hb⟩ | ⟨hb, ha⟩
    · simpa only [hab] using hstep a.val (by omega)
    · simpa only [hba] using (hstep b.val (by omega)).symm
    · simpa only [ha, hb] using hclose
    · simpa only [ha, hb] using hclose.symm
    · simpa only [ha, hb] using hnj
    · simpa only [ha, hb] using hnj.symm
    · simpa only [ha, hb] using h1k
    · simpa only [ha, hb] using h1k.symm
    · simpa only [ha, hb] using hvl
    · simpa only [ha, hb] using hvl.symm
  obtain ⟨P, hP, hPs, hPc⟩ := R.exists_walk hR htn v hv hA
  refine ⟨P, hP, ?_, hPc⟩
  intro w hw
  obtain ⟨i, hi⟩ := hPs w hw
  exact ⟨i.val, by omega, hi⟩

/-- Consecutive indices on the opened cycle cannot be the ends of a cycle chord. -/
theorem chord_indices_separated {V : Type u} {G : SimpleGraph V} {z : V}
    (C : G.Walk z z) (hC : C.IsCycle) {a b : ℕ}
    (ha : a ≤ C.dropLast.length) (hb : b ≤ C.dropLast.length)
    (hc : C.IsChord s(C.dropLast.getVert a, C.dropLast.getVert b)) :
    a ≠ b ∧ a + 1 ≠ b ∧ b + 1 ≠ a := by
  have hlen := C.length_dropLast_add_one hC.not_nil
  have hal : a < C.length := by omega
  have hbl : b < C.length := by omega
  have hadj := (Walk.isChord_sym2Mk.mp hc).1
  refine ⟨?_, ?_, ?_⟩
  · intro he
    exact hadj.ne (congrArg C.dropLast.getVert he)
  · intro he
    apply hc.2.1
    rw [C.mk_mem_edges_iff_exists]
    refine ⟨a, hal, ?_⟩
    rw [he, ← Walk.getVert_dropLast hal, ← Walk.getVert_dropLast hbl]
  · intro he
    apply hc.2.1
    rw [C.mk_mem_edges_iff_exists]
    refine ⟨b, hbl, ?_⟩
    rw [he, ← Walk.getVert_dropLast hal, ← Walk.getVert_dropLast hbl]
    exact Sym2.eq_swap

/-- The three-chord routing lemma in Mathlib's walk vocabulary. -/
theorem exists_path_two_chords_of_cycle {V : Type u} {G : SimpleGraph V} {z : V}
    (C : G.Walk z z) (hC : C.IsCycle) {j k l : ℕ}
    (hj : 1 ≤ j) (hjn : j + 1 < C.dropLast.length)
    (hk : k ≤ C.dropLast.length) (hl : l ≤ C.dropLast.length)
    (hnj : C.IsChord s(C.penultimate, C.dropLast.getVert j))
    (h1k : C.IsChord s(C.snd, C.dropLast.getVert k))
    (hvl : C.IsChord s(C.dropLast.getVert (j + 1), C.dropLast.getVert l))
    (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ C.dropLast.length) :
    ∃ P : G.Walk (C.dropLast.getVert t) z, P.IsPath ∧
      (∀ w ∈ P.support, w ∈ C.support) ∧
      ∃ e f : Sym2 V, e ≠ f ∧ P.IsChord e ∧ P.IsChord f := by
  let p := C.dropLast
  have hlen := C.length_dropLast_add_one hC.not_nil
  have hpLen : p.length + 1 = C.length := hlen
  have h1 : p.getVert 1 = C.snd := Walk.getVert_dropLast (by omega)
  have h1k' : C.IsChord s(p.getVert 1, p.getVert k) := by
    simpa only [h1] using h1k
  obtain ⟨hkne, hkgap, hkgap'⟩ :=
    chord_indices_separated C hC (a := 1) (by omega) hk h1k'
  obtain ⟨hlne, hlgap, hlgap'⟩ :=
    chord_indices_separated C hC (a := j + 1) (by omega) hl hvl
  have hcfg : Configuration p.length j k l :=
    ⟨by omega, hj, by omega, by omega, hk, hl, by omega, by omega, by omega⟩
  have hinj : ∀ a ≤ p.length, ∀ b ≤ p.length, p.getVert a = p.getVert b → a = b := by
    intro a ha b hb he
    exact hC.isPath_dropLast.getVert_injOn ha hb he
  have hclose : G.Adj (p.getVert p.length) (p.getVert 0) := by
    simpa only [Walk.getVert_length, Walk.getVert_zero] using C.adj_penultimate hC.not_nil
  have hnj' : G.Adj (p.getVert p.length) (p.getVert j) := by
    simpa only [Walk.getVert_length] using (Walk.isChord_sym2Mk.mp hnj).1
  have h1kAdj : G.Adj (p.getVert 1) (p.getVert k) := (Walk.isChord_sym2Mk.mp h1k').1
  obtain ⟨P, hP, hPs, hPc⟩ := exists_path_two_chords_of_numbering hcfg p.getVert hinj
    (fun _ hi => p.adj_getVert_succ hi) hclose hnj' h1kAdj
    (Walk.isChord_sym2Mk.mp hvl).1 t ht htn
  have hzero : p.getVert 0 = z := p.getVert_zero
  let Q := P.copy rfl hzero
  have hsup : Q.support = P.support := Walk.support_copy _ _ _
  have hedge : Q.edges = P.edges := Walk.edges_copy _ _ _
  refine ⟨Q, (Walk.isPath_copy _ _ _).mpr hP, ?_, ?_⟩
  · intro w hw
    obtain ⟨i, hi, hiw⟩ := hPs w (hsup ▸ hw)
    rw [← hiw, Walk.getVert_dropLast (by omega)]
    exact C.getVert_mem_support i
  · obtain ⟨e, f, hef, he, hf⟩ := hPc
    refine ⟨e, f, hef, ?_, ?_⟩
    · simpa only [Walk.IsChord, hsup, hedge] using he
    · simpa only [Walk.IsChord, hsup, hedge] using hf

end Erdos1091.Voss.Routing

namespace Erdos1091.Voss.AttachmentLasso

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {S : Set V}

/-- Every non-branch vertex of a maximal lasso cycle can be joined to the
branch by a path on that cycle having two distinct ambient chords. -/
theorem exists_path_two_chords_to_branch (L : AttachmentLasso G S)
    (hdegree : ∀ v, v ∉ S → 3 ≤ G.degree v)
    (hmaxPath : ∀ Q : AttachmentPath G S, Q.walk.length + 1 ≤ L.length)
    (hnoEar : ∀ E : Ear G S, E.walk.length ≠ L.length)
    (hmaxCycle : ∀ K : AttachmentLasso G S, K.length = L.length →
      K.cycle.length ≤ L.cycle.length)
    {w : V} (hw : w ∈ L.cycle.support) (hwne : w ≠ L.stem.finish) :
    ∃ P : G.Walk w L.stem.finish, P.IsPath ∧
      (∀ v ∈ P.support, v ∈ L.cycle.support) ∧
      ∃ e f : Sym2 V, e ≠ f ∧ P.IsChord e ∧ P.IsChord f := by
  obtain ⟨j, k, l, hj, hjn, hk, hl, hnj, h1k, hvl⟩ :=
    L.exists_three_chord_configuration hdegree hmaxPath hnoEar hmaxCycle
  have hwP : w ∈ L.cycle.dropLast.support := (Traversal.dropLast L).support_iff w |>.mpr hw
  obtain ⟨t, htget, htn⟩ := Walk.mem_support_iff_exists_getVert.mp hwP
  have ht : 1 ≤ t := by
    by_contra h
    have ht0 : t = 0 := by omega
    exact hwne (by simpa only [ht0, Walk.getVert_zero] using htget.symm)
  obtain ⟨P, hP, hPs, e, f, hef, he, hf⟩ :=
    Routing.exists_path_two_chords_of_cycle L.cycle L.isCycle hj hjn hk hl hnj h1k hvl t ht htn
  let Q := P.copy htget rfl
  have hsup : Q.support = P.support := Walk.support_copy _ _ _
  have hedge : Q.edges = P.edges := Walk.edges_copy _ _ _
  refine ⟨Q, (Walk.isPath_copy _ _ _).mpr hP, ?_, e, f, hef, ?_, ?_⟩
  · intro v hv
    exact hPs v (hsup ▸ hv)
  · simpa only [Walk.IsChord, hsup, hedge] using he
  · simpa only [Walk.IsChord, hsup, hedge] using hf

end Erdos1091.Voss.AttachmentLasso
