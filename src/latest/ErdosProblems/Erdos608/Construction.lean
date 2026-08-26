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
import ErdosProblems.Erdos608.Statement

set_option linter.mathlibStandardSet false

/-
Erdős 608 — the witness construction, a rational specialization of the
Füredi–Maleki template (lemma-ladder items L1,
L2, L3b of runs/phase2/erdos-608/CONSTRUCTION.md).

`FM m` is a non-balanced blowup of the path A–B–C–D with a clique on D:
parts of size |A| = 4m, |B| = 7m, |C| = 7m, |D| = 10m (so n = 28m); edges are
all A×B, B×C, C×D pairs plus all pairs inside D.  A, B, C are independent
sets; no A×C, A×D, B×D edges.

Provided here:
* L1 : `V`, `FM`, `card_V` (`Fintype.card (V m) = 28m`).
* L2 : per-part degree lemmas, `sum_degrees`, `card_edgeFinset`, and
  `edgeSet_ncard` (`(FM m).edgeSet.ncard = 197m² − 5m`).
* L3b: `onC5_dd`, `onC5_cd`, `onC5_bc` — every D×D, C×D, B×C edge lies on a
  pentagon (for `1 ≤ m`).
-/

namespace Erdos608

/-! ## L1: the vertex type and the graph -/

/-- Vertex type of the Füredi–Maleki graph: the four blowup classes
A (`4m`), B (`7m`), C (`7m`), D (`10m`) as a nested sum. -/
abbrev V (m : ℕ) := Fin (4*m) ⊕ Fin (7*m) ⊕ Fin (7*m) ⊕ Fin (10*m)

/-- Position of a vertex along the pattern path a–b–c–d (A ↦ 0, …, D ↦ 3). -/
def tag {m : ℕ} : V m → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

@[simp] lemma tag_A {m : ℕ} (a : Fin (4*m)) : tag (Sum.inl a : V m) = 0 := rfl
@[simp] lemma tag_B {m : ℕ} (b : Fin (7*m)) : tag (Sum.inr (Sum.inl b) : V m) = 1 := rfl
@[simp] lemma tag_C {m : ℕ} (c : Fin (7*m)) :
    tag (Sum.inr (Sum.inr (Sum.inl c)) : V m) = 2 := rfl
@[simp] lemma tag_D {m : ℕ} (d : Fin (10*m)) :
    tag (Sum.inr (Sum.inr (Sum.inr d)) : V m) = 3 := rfl

/-- The witness graph — a rational specialization of the Füredi–Maleki
template: two distinct vertices are adjacent iff their
part tags are consecutive on the path (A–B, B–C, C–D) or both lie in D.
Since distinct parts have distinct tags, the `x ≠ y` conjunct is redundant on
the cross-part branches and encodes "adjacent iff distinct" inside D. -/
def FM (m : ℕ) : SimpleGraph (V m) where
  Adj x y := (tag y = tag x + 1 ∨ tag x = tag y + 1 ∨ (tag x = 3 ∧ tag y = 3)) ∧ x ≠ y
  symm := by
    constructor
    rintro x y ⟨ht, hne⟩
    exact ⟨by tauto, hne.symm⟩
  loopless := by
    constructor
    rintro x ⟨-, hne⟩
    exact hne rfl

/-- Definitional unfolding of `(FM m).Adj`. -/
lemma FM_adj {m : ℕ} {x y : V m} :
    (FM m).Adj x y ↔
      (tag y = tag x + 1 ∨ tag x = tag y + 1 ∨ (tag x = 3 ∧ tag y = 3)) ∧ x ≠ y :=
  Iff.rfl

instance FM.adjDecidable (m : ℕ) : DecidableRel ((FM m).Adj) := fun x y =>
  decidable_of_iff _ (FM_adj (m := m) (x := x) (y := y)).symm

lemma card_V (m : ℕ) : Fintype.card (V m) = 28*m := by
  simp only [V, Fintype.card_sum, Fintype.card_fin]
  omega

/-! ## Adjacency and disequality helpers (raw-constructor form) -/

lemma ne_DD {m : ℕ} {d d' : Fin (10*m)} (h : d ≠ d') :
    (Sum.inr (Sum.inr (Sum.inr d)) : V m) ≠ Sum.inr (Sum.inr (Sum.inr d')) := by
  simp [h]

lemma adj_AB {m : ℕ} (a : Fin (4*m)) (b : Fin (7*m)) :
    (FM m).Adj (Sum.inl a) (Sum.inr (Sum.inl b)) :=
  ⟨Or.inl rfl, by simp⟩

lemma adj_BC {m : ℕ} (b : Fin (7*m)) (c : Fin (7*m)) :
    (FM m).Adj (Sum.inr (Sum.inl b)) (Sum.inr (Sum.inr (Sum.inl c))) :=
  ⟨Or.inl rfl, by simp⟩

lemma adj_CD {m : ℕ} (c : Fin (7*m)) (d : Fin (10*m)) :
    (FM m).Adj (Sum.inr (Sum.inr (Sum.inl c))) (Sum.inr (Sum.inr (Sum.inr d))) :=
  ⟨Or.inl rfl, by simp⟩

lemma adj_DD {m : ℕ} {d d' : Fin (10*m)} (h : d ≠ d') :
    (FM m).Adj (Sum.inr (Sum.inr (Sum.inr d))) (Sum.inr (Sum.inr (Sum.inr d'))) :=
  ⟨Or.inr (Or.inr ⟨rfl, rfl⟩), ne_DD h⟩

/-! ## L2: edge count via the degree sum -/

/-- Embedding of part A into the vertex type. -/
def eA (m : ℕ) : Fin (4*m) ↪ V m :=
  ⟨fun a => Sum.inl a, fun _ _ h => by simpa using h⟩

/-- Embedding of part B into the vertex type. -/
def eB (m : ℕ) : Fin (7*m) ↪ V m :=
  ⟨fun b => Sum.inr (Sum.inl b), fun _ _ h => by simpa using h⟩

/-- Embedding of part C into the vertex type. -/
def eC (m : ℕ) : Fin (7*m) ↪ V m :=
  ⟨fun c => Sum.inr (Sum.inr (Sum.inl c)), fun _ _ h => by simpa using h⟩

/-- Embedding of part D into the vertex type. -/
def eD (m : ℕ) : Fin (10*m) ↪ V m :=
  ⟨fun d => Sum.inr (Sum.inr (Sum.inr d)), fun _ _ h => by simpa using h⟩

@[simp] lemma eA_apply {m : ℕ} (a : Fin (4*m)) : eA m a = Sum.inl a := rfl
@[simp] lemma eB_apply {m : ℕ} (b : Fin (7*m)) : eB m b = Sum.inr (Sum.inl b) := rfl
@[simp] lemma eC_apply {m : ℕ} (c : Fin (7*m)) :
    eC m c = Sum.inr (Sum.inr (Sum.inl c)) := rfl
@[simp] lemma eD_apply {m : ℕ} (d : Fin (10*m)) :
    eD m d = Sum.inr (Sum.inr (Sum.inr d)) := rfl

lemma neighborFinset_A (m : ℕ) (a : Fin (4*m)) :
    (FM m).neighborFinset (Sum.inl a) = Finset.univ.map (eB m) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj]

lemma neighborFinset_B (m : ℕ) (b : Fin (7*m)) :
    (FM m).neighborFinset (Sum.inr (Sum.inl b)) =
      Finset.univ.map (eA m) ∪ Finset.univ.map (eC m) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj]

lemma neighborFinset_C (m : ℕ) (c : Fin (7*m)) :
    (FM m).neighborFinset (Sum.inr (Sum.inr (Sum.inl c))) =
      Finset.univ.map (eB m) ∪ Finset.univ.map (eD m) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj]

lemma neighborFinset_D (m : ℕ) (d : Fin (10*m)) :
    (FM m).neighborFinset (Sum.inr (Sum.inr (Sum.inr d))) =
      Finset.univ.map (eC m) ∪
        (Finset.univ.map (eD m)).erase (Sum.inr (Sum.inr (Sum.inr d))) := by
  ext y
  rcases y with a' | b' | c' | d' <;>
    simp [SimpleGraph.mem_neighborFinset, FM_adj, ne_comm]

lemma disjoint_eA_eC (m : ℕ) :
    Disjoint (Finset.univ.map (eA m)) (Finset.univ.map (eC m)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨c, -, hc⟩ := Finset.mem_map.mp hy
  simp at hc

lemma disjoint_eB_eD (m : ℕ) :
    Disjoint (Finset.univ.map (eB m)) (Finset.univ.map (eD m)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨d, -, hd⟩ := Finset.mem_map.mp hy
  simp at hd

lemma disjoint_eC_eD (m : ℕ) :
    Disjoint (Finset.univ.map (eC m)) (Finset.univ.map (eD m)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨d, -, hd⟩ := Finset.mem_map.mp hy
  simp at hd

lemma degree_A (m : ℕ) (a : Fin (4*m)) : (FM m).degree (Sum.inl a) = 7*m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_A,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

lemma degree_B (m : ℕ) (b : Fin (7*m)) :
    (FM m).degree (Sum.inr (Sum.inl b)) = 11*m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_B,
    Finset.card_union_of_disjoint (disjoint_eA_eC m), Finset.card_map, Finset.card_map,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  omega

lemma degree_C (m : ℕ) (c : Fin (7*m)) :
    (FM m).degree (Sum.inr (Sum.inr (Sum.inl c))) = 17*m := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_C,
    Finset.card_union_of_disjoint (disjoint_eB_eD m), Finset.card_map, Finset.card_map,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  omega

lemma degree_D (m : ℕ) (d : Fin (10*m)) :
    (FM m).degree (Sum.inr (Sum.inr (Sum.inr d))) = 7*m + (10*m - 1) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_D,
    Finset.card_union_of_disjoint
      ((disjoint_eC_eD m).mono_right (Finset.erase_subset _ _)),
    Finset.card_map, Finset.card_erase_of_mem (by simp), Finset.card_map,
    Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]

lemma sum_degrees (m : ℕ) :
    ∑ v : V m, (FM m).degree v = 394 * m ^ 2 - 10 * m := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [degree_A, degree_B, degree_C, degree_D, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rcases m with - | k
  · simp
  · have h1 : 7 * (k + 1) + (10 * (k + 1) - 1) = 17 * k + 16 := by omega
    rw [h1]
    symm
    apply Nat.sub_eq_of_eq_add
    ring

lemma card_edgeFinset (m : ℕ) :
    (FM m).edgeFinset.card = 197 * m ^ 2 - 5 * m := by
  have h := (FM m).sum_degrees_eq_twice_card_edges
  rw [sum_degrees] at h
  have h1 : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
  generalize m ^ 2 = t at h h1 ⊢
  omega

/-- **L2.** The Füredi–Maleki graph on `28m` vertices has `197m² − 5m` edges
(so `4e > n²` for `m ≥ 6`). -/
lemma edgeSet_ncard (m : ℕ) : (FM m).edgeSet.ncard = 197 * m ^ 2 - 5 * m := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, card_edgeFinset]

/-! ## L3b: pentagon witnesses -/

/-- In `Fin (10*m)` with `1 ≤ m` there are three distinct elements avoiding
any two given ones (|D| = 10m ≥ 10 ≥ 5). -/
lemma exists_three (m : ℕ) (hm : 1 ≤ m) (x y : Fin (10*m)) :
    ∃ p q r : Fin (10*m),
      p ≠ x ∧ p ≠ y ∧ q ≠ x ∧ q ≠ y ∧ r ≠ x ∧ r ≠ y ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r := by
  have hxy : ({x, y} : Finset (Fin (10*m))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have hcompl : 8 ≤ ({x, y}ᶜ : Finset (Fin (10*m))).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp
    (show 0 < ({x, y}ᶜ : Finset (Fin (10*m))).card by omega)
  obtain ⟨q, hq⟩ := Finset.card_pos.mp
    (show 0 < (({x, y}ᶜ : Finset (Fin (10*m))).erase p).card by
      rw [Finset.card_erase_of_mem hp]; omega)
  obtain ⟨r, hr⟩ := Finset.card_pos.mp
    (show 0 < ((({x, y}ᶜ : Finset (Fin (10*m))).erase p).erase q).card by
      rw [Finset.card_erase_of_mem hq, Finset.card_erase_of_mem hp]; omega)
  simp only [Finset.mem_erase, Finset.mem_compl, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hp hq hr
  exact ⟨p, q, r, hp.1, hp.2, hq.2.1, hq.2.2, hr.2.2.1, hr.2.2.2,
    hq.1.symm, hr.2.1.symm, hr.1.symm⟩

/-- **L3b, D×D.** Every edge inside the clique D lies on a pentagon:
five distinct D-vertices form a `C₅`. -/
lemma onC5_dd (m : ℕ) (hm : 1 ≤ m) :
    ∀ x y : Fin (10*m), x ≠ y →
      Erdos608.OnC5 (FM m)
        s(Sum.inr (Sum.inr (Sum.inr x)), Sum.inr (Sum.inr (Sum.inr y))) := by
  intro x y hxy
  obtain ⟨p, q, r, hpx, hpy, hqx, hqy, hrx, hry, hpq, hpr, hqr⟩ :=
    exists_three m hm x y
  exact ⟨Sum.inr (Sum.inr (Sum.inr x)), Sum.inr (Sum.inr (Sum.inr y)),
    Sum.inr (Sum.inr (Sum.inr p)), Sum.inr (Sum.inr (Sum.inr q)),
    Sum.inr (Sum.inr (Sum.inr r)),
    ne_DD hxy, ne_DD hpx.symm, ne_DD hqx.symm, ne_DD hrx.symm,
    ne_DD hpy.symm, ne_DD hqy.symm, ne_DD hry.symm,
    ne_DD hpq, ne_DD hpr, ne_DD hqr,
    adj_DD hxy, adj_DD hpy.symm, adj_DD hpq, adj_DD hqr, adj_DD hrx,
    Or.inl rfl⟩

/-- **L3b, C×D.** Every C×D edge lies on a pentagon: `c, d₁, d₂, d₃, d₄` with
`d₁ = y` and `d₂ d₃ d₄` three further distinct D-vertices. -/
lemma onC5_cd (m : ℕ) (hm : 1 ≤ m) :
    ∀ (x : Fin (7*m)) (y : Fin (10*m)),
      Erdos608.OnC5 (FM m)
        s(Sum.inr (Sum.inr (Sum.inl x)), Sum.inr (Sum.inr (Sum.inr y))) := by
  intro x y
  obtain ⟨p, q, r, hpy, -, hqy, -, hry, -, hpq, hpr, hqr⟩ := exists_three m hm y y
  exact ⟨Sum.inr (Sum.inr (Sum.inl x)), Sum.inr (Sum.inr (Sum.inr y)),
    Sum.inr (Sum.inr (Sum.inr p)), Sum.inr (Sum.inr (Sum.inr q)),
    Sum.inr (Sum.inr (Sum.inr r)),
    by simp, by simp, by simp, by simp,
    ne_DD hpy.symm, ne_DD hqy.symm, ne_DD hry.symm,
    ne_DD hpq, ne_DD hpr, ne_DD hqr,
    adj_CD x y, adj_DD hpy.symm, adj_DD hpq, adj_DD hqr, (adj_CD x r).symm,
    Or.inl rfl⟩

/-- **L3b, B×C.** Every B×C edge lies on a pentagon: `b, c₁, d₁, d₂, c₂` with
`c₂ ≠ c₁` a second C-vertex and `d₁ ≠ d₂` two D-vertices. -/
lemma onC5_bc (m : ℕ) (hm : 1 ≤ m) :
    ∀ (x y : Fin (7*m)),
      Erdos608.OnC5 (FM m)
        s(Sum.inr (Sum.inl x), Sum.inr (Sum.inr (Sum.inl y))) := by
  intro x y
  obtain ⟨c₂, hc⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card (Fin (7*m)) by rw [Fintype.card_fin]; omega) y
  obtain ⟨d₁, d₂, hd⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card (Fin (10*m)) by rw [Fintype.card_fin]; omega)
  exact ⟨Sum.inr (Sum.inl x), Sum.inr (Sum.inr (Sum.inl y)),
    Sum.inr (Sum.inr (Sum.inr d₁)), Sum.inr (Sum.inr (Sum.inr d₂)),
    Sum.inr (Sum.inr (Sum.inl c₂)),
    by simp, by simp, by simp, by simp,
    by simp, by simp,
    by simp [Ne.symm hc],
    ne_DD hd,
    by simp, by simp,
    adj_BC x y, adj_CD y d₁, adj_DD hd, (adj_CD c₂ d₂).symm, (adj_BC x c₂).symm,
    Or.inl rfl⟩

end Erdos608
