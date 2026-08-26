/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Tactic

/-!
# Partial colorings and fans for Vizing's theorem

This preserves the partial-coloring, Kempe-interchange, and maximal-fan
lemmas from the Erdős 622 development. These are ingredients, not yet the
complete Vizing theorem. The fan-rotation and final augmentation arguments
are supplied separately in the Erdős 19 development.

We deliberately formulate partial colourings on all unordered pairs.  Only
their values on edges are observed.  This makes recolouring operations
literal function updates and avoids transports between the edge subtypes of
successive deleted-edge graphs.
-/

open Finset

namespace Erdos19
namespace Vizing

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V]

/-- A partial edge colouring.  `none` means that the edge is not coloured. -/
abbrev PartialColoring (V : Type u) (K : Type*) := Sym2 V → Option K

/-- Properness of a partial edge colouring, stated at a common endpoint. -/
def IsProper (G : SimpleGraph V) {K : Type*} (C : PartialColoring V K) : Prop :=
  ∀ ⦃u v w : V⦄ ⦃a : K⦄, G.Adj u v → G.Adj u w →
    C s(u, v) = some a → C s(u, w) = some a → v = w

/-- A colour is missing at a vertex when no incident edge has that colour. -/
def Missing (G : SimpleGraph V) {K : Type*} (C : PartialColoring V K)
    (v : V) (a : K) : Prop :=
  ∀ w, G.Adj v w → C s(v, w) ≠ some a

/-- The set of coloured edges, as a finset of unordered pairs. -/
def coloredEdges (G : SimpleGraph V) {K : Type*} (C : PartialColoring V K) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ (C e).isSome

@[simp] lemma mem_coloredEdges (G : SimpleGraph V) {K : Type*}
    (C : PartialColoring V K) (e : Sym2 V) :
    e ∈ coloredEdges G C ↔ e ∈ G.edgeSet ∧ (C e).isSome := by
  simp [coloredEdges]

lemma missing_iff_not_exists (G : SimpleGraph V) {K : Type*}
    (C : PartialColoring V K) (v : V) (a : K) :
    Missing G C v a ↔ ¬ ∃ w, G.Adj v w ∧ C s(v, w) = some a := by
  simp only [Missing, not_exists, not_and]

/-- With one more colour than the degree bound, every vertex misses a colour. -/
lemma exists_missing (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D)
    {C : PartialColoring V (Fin (D + 1))} (hC : IsProper G C) (u : V) :
    ∃ a : Fin (D + 1), Missing G C u a := by
  by_contra h
  simp only [not_exists] at h
  have hpresent : ∀ a : Fin (D + 1),
      ∃ w, G.Adj u w ∧ C s(u, w) = some a := by
    intro a
    exact Classical.not_not.mp ((missing_iff_not_exists G C u a).not.mp (h a))
  choose f hf using hpresent
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    by_contra habval
    have hab' : a ≠ b := by
      intro heq
      exact habval (congrArg Fin.val heq)
    have hsame : C s(u, f a) = some b := by simpa [hab] using (hf b).2
    have habsome : (some a : Option (Fin (D + 1))) = some b :=
      (hf a).2.symm.trans hsame
    exact hab' (Option.some.inj habsome)
  have hcard : D + 1 ≤ G.degree u := by
    let F : Fin (D + 1) → G.neighborFinset u := fun a ↦
      ⟨f a, (G.mem_neighborFinset u (f a)).2 (hf a).1⟩
    have hFinj : Function.Injective F := fun a b heq ↦ by
      apply hfinj
      exact congrArg Subtype.val heq
    have := Fintype.card_le_of_injective F hFinj
    simpa only [Fintype.card_fin, Fintype.card_coe, SimpleGraph.degree] using this
  exact (Nat.not_succ_le_self D) (by
    simpa only [Nat.succ_eq_add_one] using hcard.trans (hdegree u))

/-- The subgraph formed by the two colour classes `a` and `b`. -/
def bichromGraph (G : SimpleGraph V) {K : Type*} (C : PartialColoring V K)
    (a b : K) : SimpleGraph V :=
  SimpleGraph.fromRel fun v w ↦
    G.Adj v w ∧ (C s(v, w) = some a ∨ C s(v, w) = some b)

@[simp] lemma bichromGraph_adj (G : SimpleGraph V) {K : Type*}
    (C : PartialColoring V K) (a b : K) (v w : V) :
    (bichromGraph G C a b).Adj v w ↔
      G.Adj v w ∧ (C s(v, w) = some a ∨ C s(v, w) = some b) := by
  simp only [bichromGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, (h | h)⟩
    · exact h
    · exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

/-- Every two-colour graph of a proper partial colouring has maximum degree two. -/
lemma bichromGraph_degree_le_two (G : SimpleGraph V) {K : Type*}
    (C : PartialColoring V K) (hC : IsProper G C) (a b : K) (v : V) :
    (bichromGraph G C a b).degree v ≤ 2 := by
  let f : (bichromGraph G C a b).neighborFinset v → Fin 2 := fun w ↦
    if C s(v, w.1) = some a then 0 else 1
  have hf : Function.Injective f := by
    intro w z hwz
    apply Subtype.ext
    have hw := (bichromGraph_adj G C a b v w.1).1
      ((bichromGraph G C a b).mem_neighborFinset v w.1 |>.1 w.2)
    have hz := (bichromGraph_adj G C a b v z.1).1
      ((bichromGraph G C a b).mem_neighborFinset v z.1 |>.1 z.2)
    by_cases hwa : C s(v, w.1) = some a
    · have hza : C s(v, z.1) = some a := by
        by_contra hn
        have hw0 : f w = 0 := by simp [f, hwa]
        have hz1 : f z = 1 := by simp [f, hn]
        omega
      exact hC hw.1 hz.1 hwa hza
    · have hwb : C s(v, w.1) = some b := hw.2.resolve_left hwa
      have hza : ¬ C s(v, z.1) = some a := by
        by_contra hz'
        have hw1 : f w = 1 := by simp [f, hwa]
        have hz0 : f z = 0 := by simp [f, hz']
        omega
      have hzb : C s(v, z.1) = some b := hz.2.resolve_left hza
      exact hC hw.1 hz.1 hwb hzb
  simpa only [SimpleGraph.degree, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- If one of the two colours is missing, the corresponding vertex is an
endpoint (or an isolated vertex) of the two-colour graph. -/
lemma bichromGraph_degree_le_one_of_missing (G : SimpleGraph V) {K : Type*}
    (C : PartialColoring V K) (hC : IsProper G C) {a b : K} {v : V}
    (ha : Missing G C v a) :
    (bichromGraph G C a b).degree v ≤ 1 := by
  by_contra hdeg
  have htwo : 2 ≤ (bichromGraph G C a b).degree v := by omega
  obtain ⟨w, hw, z, hz, hwz⟩ :=
    Finset.one_lt_card.1 (by simpa only [SimpleGraph.degree, Nat.lt_iff_add_one_le] using htwo)
  have hwB := (bichromGraph_adj G C a b v w).1
    ((bichromGraph G C a b).mem_neighborFinset v w |>.1 hw)
  have hzB := (bichromGraph_adj G C a b v z).1
    ((bichromGraph G C a b).mem_neighborFinset v z |>.1 hz)
  have hwc : C s(v, w) = some b := hwB.2.resolve_left (ha w hwB.1)
  have hzc : C s(v, z) = some b := hzB.2.resolve_left (ha z hzB.1)
  exact hwz (hC hwB.1 hzB.1 hwc hzc)

/-- A connected finite graph of maximum degree at most two cannot have three
distinct vertices of degree at most one. -/
lemma not_three_endpoints {H : SimpleGraph V} (hconn : H.Connected)
    (hmax : ∀ v, H.degree v ≤ 2) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : H.degree x ≤ 1) (hy : H.degree y ≤ 1) (hz : H.degree z ≤ 1) : False := by
  let S : Finset V := {x, y, z}
  have hScard : S.card = 3 := by simp [S, hxy, hxz, hyz]
  have hpoint : ∀ v ∈ (univ : Finset V),
      H.degree v + (if v ∈ S then 1 else 0) ≤ 2 := by
    intro v _
    by_cases hv : v ∈ S
    · simp only [S, mem_insert, mem_singleton] at hv
      rcases hv with (rfl | rfl | rfl)
      · rw [if_pos (by simp [S])]
        omega
      · rw [if_pos (by simp [S])]
        omega
      · rw [if_pos (by simp [S])]
        omega
    · simp [hv, hmax v]
  have hsum := Finset.sum_le_sum hpoint
  have hindicator : (∑ v : V, if v ∈ S then 1 else 0) = S.card := by simp
  have hconst : (∑ _v : V, 2) = 2 * Fintype.card V := by simp [Nat.mul_comm]
  rw [Finset.sum_add_distrib, hindicator, hconst, hScard] at hsum
  have hupper : (∑ v, H.degree v) + 3 ≤ 2 * Fintype.card V := hsum
  have hlower : Fintype.card V ≤ H.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hhandshake := H.sum_degrees_eq_twice_card_edges
  omega

/-- A component of a proper two-colour graph cannot contain three distinct
vertices at which the indicated endpoint colours are missing. -/
lemma bichrom_component_not_three_missing (G : SimpleGraph V) {K : Type*}
    (C : PartialColoring V K) (hC : IsProper G C) {a b : K}
    (Q : (bichromGraph G C a b).ConnectedComponent)
    {x y z : V} (hxQ : x ∈ Q.supp) (hyQ : y ∈ Q.supp) (hzQ : z ∈ Q.supp)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : Missing G C x a) (hy : Missing G C y b)
    (hz : Missing G C z b) : False := by
  let B := bichromGraph G C a b
  let xx : Q := ⟨x, hxQ⟩
  let yy : Q := ⟨y, hyQ⟩
  let zz : Q := ⟨z, hzQ⟩
  have hdegree (v : Q) : Q.toSimpleGraph.degree v = B.degree v.1 := by
    apply B.degree_induce_of_neighborSet_subset
    intro w hw
    exact Q.mem_supp_of_adj_mem_supp v.2 hw
  have hBcomm : bichromGraph G C a b = bichromGraph G C b a := by
    ext v w
    simp only [bichromGraph_adj]
    tauto
  apply not_three_endpoints Q.connected_toSimpleGraph
      (fun v ↦ (hdegree v).trans_le
        (bichromGraph_degree_le_two G C hC a b v.1))
      (x := xx) (y := yy) (z := zz)
      (by simpa [xx, yy] using hxy) (by simpa [xx, zz] using hxz)
      (by simpa [yy, zz] using hyz)
  · rw [hdegree]
    exact bichromGraph_degree_le_one_of_missing G C hC hx
  · rw [hdegree]
    change (bichromGraph G C a b).degree y ≤ 1
    have hd := bichromGraph_degree_le_one_of_missing G C hC (a := b) (b := a) hy
    exact (congrArg (fun H : SimpleGraph V ↦ H.degree y) hBcomm).trans_le hd
  · rw [hdegree]
    change (bichromGraph G C a b).degree z ≤ 1
    have hd := bichromGraph_degree_le_one_of_missing G C hC (a := b) (b := a) hz
    exact (congrArg (fun H : SimpleGraph V ↦ H.degree z) hBcomm).trans_le hd

/-- Whether an unordered pair touches a set of vertices. -/
def Touches (S : Set V) (e : Sym2 V) : Prop := ∃ v, v ∈ S ∧ v ∈ e

@[simp] lemma touches_s (S : Set V) (u v : V) :
    Touches S s(u, v) ↔ u ∈ S ∨ v ∈ S := by
  constructor
  · rintro ⟨w, hwS, hw⟩
    rcases Sym2.mem_iff.mp hw with (rfl | rfl)
    · exact Or.inl hwS
    · exact Or.inr hwS
  · rintro (hu | hv)
    · exact ⟨u, hu, Sym2.mem_mk_left u v⟩
    · exact ⟨v, hv, Sym2.mem_mk_right u v⟩

/-- Interchange two colours in an optional colour. -/
def swapOption {K : Type*} [DecidableEq K] (a b : K) (o : Option K) : Option K :=
  o.map (Equiv.swap a b)

lemma swapOption_injective {K : Type*} [DecidableEq K] (a b : K) :
    Function.Injective (swapOption a b) := by
  exact Option.map_injective (Equiv.swap a b).injective

@[simp] lemma swapOption_none {K : Type*} [DecidableEq K] (a b : K) :
    swapOption a b none = none := rfl

@[simp] lemma swapOption_some_left {K : Type*} [DecidableEq K] (a b : K) :
    swapOption a b (some a) = some b := by simp [swapOption]

@[simp] lemma swapOption_some_right {K : Type*} [DecidableEq K] (a b : K) :
    swapOption a b (some b) = some a := by simp [swapOption]

lemma swapOption_fixed {K : Type*} [DecidableEq K] {a b : K} {o : Option K}
    (ha : o ≠ some a) (hb : o ≠ some b) : swapOption a b o = o := by
  rcases o with (_ | k)
  · rfl
  · simp only [swapOption, Option.map_some, Option.some.injEq]
    exact Equiv.swap_apply_of_ne_of_ne (by simpa using ha) (by simpa using hb)

/-- Swap two colours on every edge touching one chosen two-colour component.
Edges of other colours are fixed by `swapOption`; consequently using
"touches" rather than "has both endpoints in" gives a particularly simple
local properness proof. -/
def kempeSwap {K : Type*} [DecidableEq K] (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph (⊤ : SimpleGraph V) C a b).ConnectedComponent) :
    PartialColoring V K := fun e ↦
  if Touches Q.supp e then swapOption a b (C e) else C e

/-- The graph parameter in the component matters.  This is the version used
below; it is separate from `kempeSwap` so the component has the graph `G` in
its type. -/
def kempeSwapOn (G : SimpleGraph V) {K : Type*} [DecidableEq K] (C : PartialColoring V K)
    (a b : K) (Q : (bichromGraph G C a b).ConnectedComponent) :
    PartialColoring V K := fun e ↦
  if Touches Q.supp e then swapOption a b (C e) else C e

lemma kempeSwapOn_incident_of_mem (G : SimpleGraph V) {K : Type*} [DecidableEq K]
    (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) {v w : V}
    (hv : v ∈ Q.supp) :
    kempeSwapOn G C a b Q s(v, w) = swapOption a b (C s(v, w)) := by
  simp [kempeSwapOn, hv]

lemma kempeSwapOn_incident_of_not_mem (G : SimpleGraph V) {K : Type*}
    [DecidableEq K] (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) {v w : V}
    (hv : v ∉ Q.supp) (hvw : G.Adj v w) :
    kempeSwapOn G C a b Q s(v, w) = C s(v, w) := by
  rw [kempeSwapOn]
  split_ifs with ht
  · rw [touches_s] at ht
    have hw : w ∈ Q.supp := ht.resolve_left hv
    apply swapOption_fixed
    · intro hc
      have hB : (bichromGraph G C a b).Adj w v :=
        (bichromGraph_adj G C a b w v).2
          ⟨hvw.symm, Or.inl (by simpa [Sym2.eq_swap] using hc)⟩
      exact hv (Q.mem_supp_of_adj_mem_supp hw hB)
    · intro hc
      have hB : (bichromGraph G C a b).Adj w v :=
        (bichromGraph_adj G C a b w v).2
          ⟨hvw.symm, Or.inr (by simpa [Sym2.eq_swap] using hc)⟩
      exact hv (Q.mem_supp_of_adj_mem_supp hw hB)
  · rfl

lemma kempeSwapOn_proper (G : SimpleGraph V) {K : Type*} [DecidableEq K]
    (C : PartialColoring V K) (hC : IsProper G C) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) :
    IsProper G (kempeSwapOn G C a b Q) := by
  intro u v w k huv huw hvcolor hwcolor
  by_cases hu : u ∈ Q.supp
  · rw [kempeSwapOn_incident_of_mem G C a b Q hu] at hvcolor hwcolor
    have hold : C s(u, v) = C s(u, w) :=
      swapOption_injective a b (hvcolor.trans hwcolor.symm)
    rcases hval : C s(u, v) with (_ | l)
    · simp [hval] at hvcolor
    · exact hC huv huw hval (hold ▸ hval)
  · rw [kempeSwapOn_incident_of_not_mem G C a b Q hu huv] at hvcolor
    rw [kempeSwapOn_incident_of_not_mem G C a b Q hu huw] at hwcolor
    exact hC huv huw hvcolor hwcolor

lemma coloredEdges_kempeSwapOn (G : SimpleGraph V) {K : Type*} [DecidableEq K]
    (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) :
    coloredEdges G (kempeSwapOn G C a b Q) = coloredEdges G C := by
  ext e
  simp only [mem_coloredEdges, and_congr_right_iff]
  intro _
  rw [kempeSwapOn]
  split_ifs
  · rcases C e with (_ | k) <;> simp [swapOption]
  · rfl

lemma missing_kempeSwapOn_of_mem (G : SimpleGraph V) {K : Type*}
    [DecidableEq K] (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) {v : V}
    (hv : v ∈ Q.supp) (ha : Missing G C v a) :
    Missing G (kempeSwapOn G C a b Q) v b := by
  intro w hvw
  rw [kempeSwapOn_incident_of_mem G C a b Q hv]
  intro h
  have : swapOption a b (C s(v, w)) = swapOption a b (some a) := by
    simpa using h
  exact ha w hvw (swapOption_injective a b this)

lemma missing_kempeSwapOn_of_not_mem (G : SimpleGraph V) {K : Type*}
    [DecidableEq K] (C : PartialColoring V K) (a b : K)
    (Q : (bichromGraph G C a b).ConnectedComponent) {v : V} {k : K}
    (hv : v ∉ Q.supp) (hk : Missing G C v k) :
    Missing G (kempeSwapOn G C a b Q) v k := by
  intro w hvw
  rw [kempeSwapOn_incident_of_not_mem G C a b Q hv hvw]
  exact hk w hvw

/-- A Vizing fan of length `n + 1`, centred at `x` and beginning at `y`.
For every successive pair, the colour on the later spoke is missing at the
earlier outer vertex. -/
structure Fan (G : SimpleGraph V) {K : Type*} (C : PartialColoring V K)
    (x y : V) (n : ℕ) where
  vert : Fin (n + 1) → V
  injective : Function.Injective vert
  first : vert 0 = y
  adj : ∀ i, G.Adj x (vert i)
  step : ∀ i : Fin n, ∃ a : K,
    C s(x, vert i.succ) = some a ∧ Missing G C (vert i.castSucc) a

namespace Fan

variable {G : SimpleGraph V} {K : Type*} {C : PartialColoring V K} {x y : V}

/-- The one-vertex fan. -/
def singleton (hxy : G.Adj x y) : Fan G C x y 0 where
  vert _ := y
  injective := fun i j _ ↦ Fin.eq_zero i |>.trans (Fin.eq_zero j).symm
  first := rfl
  adj _ := hxy
  step i := Fin.elim0 i

lemma center_ne (F : Fan G C x y n) (i : Fin (n + 1)) : x ≠ F.vert i :=
  (F.adj i).ne

lemma edge_injective (F : Fan G C x y n) :
    Function.Injective (fun i ↦ s(x, F.vert i)) := by
  intro i j hij
  apply F.injective
  rw [Sym2.eq_iff] at hij
  rcases hij with (h | h)
  · exact h.2
  · exact (F.center_ne j h.1).elim

/-- Append one spoke whose colour is missing at the old last vertex. -/
def snoc (F : Fan G C x y n) (z : V) (hz : z ∉ Set.range F.vert)
    (hxz : G.Adj x z) (a : K) (hcolor : C s(x, z) = some a)
    (hmissing : Missing G C (F.vert (Fin.last n)) a) :
    Fan G C x y (n + 1) where
  vert := Fin.lastCases z F.vert
  injective := by
    intro i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;>
      refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · intro _
      rfl
    · intro h
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact (hz ⟨j, h.symm⟩).elim
    · intro h
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at h
      exact (hz ⟨i, h⟩).elim
    · intro h
      simp only [Fin.lastCases_castSucc] at h
      exact congrArg Fin.castSucc (F.injective h)
  first := by
    change Fin.lastCases z F.vert (Fin.castSucc (0 : Fin (n + 1))) = y
    simpa only [Fin.lastCases_castSucc] using F.first
  adj := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.lastCases_last] using hxz
    · simpa only [Fin.lastCases_castSucc] using F.adj j
  step := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · refine ⟨a, ?_, ?_⟩
      · simpa only [Fin.succ_last, Fin.lastCases_last] using hcolor
      · simpa only [Fin.lastCases_castSucc] using hmissing
    · obtain ⟨b, hb, hmiss⟩ := F.step j
      refine ⟨b, ?_, ?_⟩
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hb
      · simpa only [Fin.lastCases_castSucc] using hmiss

end Fan

/-- There is a fan maximal under appending new spokes. -/
lemma exists_maximal_fan (G : SimpleGraph V) {K : Type*}
    (C : PartialColoring V K) {x y : V} (hxy : G.Adj x y) :
    ∃ n, ∃ F : Fan G C x y n,
      ∀ z, G.Adj x z → z ∉ Set.range F.vert →
        ∀ a, C s(x, z) = some a → ¬Missing G C (F.vert (Fin.last n)) a := by
  let sizes : Finset ℕ := (range (Fintype.card V + 1)).filter fun n ↦
    Nonempty (Fan G C x y n)
  have hsizes : sizes.Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_filter]
    exact ⟨mem_range.2 (Nat.zero_lt_succ _), ⟨Fan.singleton (C := C) hxy⟩⟩
  let n := sizes.max' hsizes
  have hnmem : n ∈ sizes := max'_mem sizes hsizes
  have hnfan : Nonempty (Fan G C x y n) := (mem_filter.1 hnmem).2
  let F := hnfan.some
  refine ⟨n, F, ?_⟩
  intro z hxz hz a hcolor hmissing
  let F' := F.snoc z hz hxz a hcolor hmissing
  have hinjcard : n + 2 ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective F'.vert F'.injective
  have hsuccmem : n + 1 ∈ sizes := by
    rw [mem_filter]
    exact ⟨mem_range.2 (by omega), ⟨F'⟩⟩
  have hle : n + 1 ≤ n := by
    simpa only [n] using le_max' sizes (n + 1) hsuccmem
  omega

#print axioms kempeSwapOn_proper
#print axioms bichrom_component_not_three_missing
#print axioms exists_maximal_fan

end
end Vizing
end Erdos19
