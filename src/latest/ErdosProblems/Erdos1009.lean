/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1009.
https://www.erdosproblems.com/forum/thread/1009

Informal authors:
- E. Győri

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1009.md
-/
import ErdosProblems.Erdos1009.External.Erdos207.Prefix
import ErdosProblems.Erdos127.CutComposition
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-!
# Erdős Problem 1009

For every `c > 0`, an `n`-vertex graph with at least
`⌊n² / 4⌋ + k` edges, where `k < c n`, has all but a constant (depending
only on `c`) of `k` pairwise edge-disjoint triangles.

The detailed mathematical proof, explicit constants, source discussion,
and a lemma-by-lemma formalization map are in `tex/1009.tex`.
-/

open Finset
open scoped Sym2

namespace Erdos1009

noncomputable section

abbrev TriangleOn (V : Type*) [DecidableEq V] := Erdos207.TripleOn V
abbrev TriangleFamilyOn (V : Type*) [DecidableEq V] := Erdos207.TripleSystemOn V

/-- The three vertices of `T` span a triangle of `G`. -/
def IsGraphTriangle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : TriangleOn V) : Prop :=
  ∀ ⦃u⦄, u ∈ T.1 → ∀ ⦃v⦄, v ∈ T.1 → u ≠ v → G.Adj u v

/-- A genuine family of pairwise edge-disjoint triangles in `G`. -/
def IsTrianglePacking {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : TriangleFamilyOn V) : Prop :=
  Erdos207.IsPackingOn P ∧ ∀ T ∈ P, IsGraphTriangle G T

@[simp] lemma isGraphTriangle_mono {V : Type*} [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) {T : TriangleOn V}
    (hT : IsGraphTriangle G T) : IsGraphTriangle H T := by
  intro u hu v hv huv
  exact hGH (hT hu hv huv)

lemma IsTrianglePacking.mono {V : Type*} [DecidableEq V]
    {G H : SimpleGraph V} (hGH : G ≤ H) {P : TriangleFamilyOn V}
    (hP : IsTrianglePacking G P) : IsTrianglePacking H P := by
  exact ⟨hP.1, fun T hTP ↦ isGraphTriangle_mono hGH (hP.2 T hTP)⟩

@[simp] lemma isTrianglePacking_empty {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : IsTrianglePacking G (∅ : TriangleFamilyOn V) := by
  constructor
  · intro u v huv T hT
    simp at hT
  · simp

/-- All finite triangle packings of a graph. -/
def trianglePackings {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Finset (TriangleFamilyOn V) :=
  by
    classical
    exact Finset.univ.filter (IsTrianglePacking G)

@[simp] lemma mem_trianglePackings {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : TriangleFamilyOn V) :
    P ∈ trianglePackings G ↔ IsTrianglePacking G P := by
  simp [trianglePackings]

lemma trianglePackings_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : (trianglePackings G).Nonempty := by
  exact ⟨∅, by simp⟩

/-- A maximum-cardinality triangle packing, chosen from the finite set of
all packings. -/
def maximumTrianglePacking {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : TriangleFamilyOn V :=
  (Finset.exists_max_image (trianglePackings G) Finset.card
    (trianglePackings_nonempty G)).choose

lemma maximumTrianglePacking_spec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    maximumTrianglePacking G ∈ trianglePackings G ∧
      ∀ P ∈ trianglePackings G, P.card ≤ (maximumTrianglePacking G).card := by
  exact (Finset.exists_max_image (trianglePackings G) Finset.card
    (trianglePackings_nonempty G)).choose_spec

lemma maximumTrianglePacking_isPacking {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : IsTrianglePacking G (maximumTrianglePacking G) := by
  exact (mem_trianglePackings G _).mp (maximumTrianglePacking_spec G).1

/-- The graph consisting precisely of the three edges of every member of a
triangle family. -/
abbrev packingGraph {V : Type*} [DecidableEq V]
    (P : TriangleFamilyOn V) : SimpleGraph V := Erdos207.coveredGraph P

lemma packingGraph_le {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {P : TriangleFamilyOn V} (hP : IsTrianglePacking G P) : packingGraph P ≤ G := by
  intro u v huv
  rw [Erdos207.coveredGraph_adj] at huv
  obtain ⟨T, hTP, huT, hvT, huv⟩ := huv
  exact hP.2 T hTP huT hvT huv

lemma card_packingGraph_edgeFinset {V : Type*} [Fintype V] [DecidableEq V]
    {P : TriangleFamilyOn V} (hP : Erdos207.IsPackingOn P) :
    (packingGraph P).edgeFinset.card = 3 * P.card := by
  have hdec := hP.isTriangleDecomposition
  rw [hdec.edgeFinset_eq_biUnion,
    Finset.card_biUnion hdec.pairwiseDisjoint_tripleEdgeFinset]
  simp [Erdos207.card_tripleEdgeFinset, mul_comm]

/-- The residual graph after deleting the edges used by `P`. -/
def packingResidual {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : TriangleFamilyOn V) : SimpleGraph V :=
  G \ (packingGraph P : SimpleGraph V)

instance packingResidual.instDecidableRel {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : TriangleFamilyOn V) :
    DecidableRel (packingResidual G P).Adj := by
  dsimp [packingResidual, packingGraph]
  infer_instance

lemma packingResidual_le {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : TriangleFamilyOn V) : packingResidual G P ≤ G := by
  exact sdiff_le

lemma packingGraph_disjoint_residual {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : TriangleFamilyOn V) :
    Disjoint (packingGraph P) (packingResidual G P) := by
  exact disjoint_sdiff_self_right

lemma packingGraph_sup_residual {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {P : TriangleFamilyOn V}
    (hPG : packingGraph P ≤ G) :
    packingGraph P ⊔ packingResidual G P = G := by
  exact sup_sdiff_cancel_right hPG

/-- Maximality makes the residual graph triangle-free. -/
lemma maximum_residual_cliqueFree_three {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    (packingResidual G (maximumTrianglePacking G)).CliqueFree 3 := by
  classical
  let P := maximumTrianglePacking G
  let H := packingResidual G P
  intro s hsClique
  have hP : IsTrianglePacking G P := maximumTrianglePacking_isPacking G
  let T : TriangleOn V := ⟨s, hsClique.card_eq⟩
  have hTtriH : IsGraphTriangle H T := by
    intro u hu v hv huv
    exact hsClique.isClique hu hv huv
  have hTtriG : IsGraphTriangle G T :=
    isGraphTriangle_mono (packingResidual_le G P) hTtriH
  have hTnot : T ∉ P := by
    intro hTP
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by
      rw [hsClique.card_eq]
      decide : 1 < s.card)
    have huvPack : (packingGraph P).Adj u v := by
      rw [Erdos207.coveredGraph_adj]
      exact ⟨T, hTP, hu, hv, huv⟩
    have huvH : H.Adj u v := hTtriH hu hv huv
    exact (packingGraph_disjoint_residual G P).le_bot ⟨huvPack, huvH⟩
  let P' : TriangleFamilyOn V := insert T P
  have hP'packing : Erdos207.IsPackingOn P' := by
    intro u v huv U hUP' huU hvU W hWP' huW hvW
    simp only [P', Finset.mem_insert] at hUP' hWP'
    rcases hUP' with rfl | hUP <;> rcases hWP' with rfl | hWP
    · rfl
    · exfalso
      have huvH : H.Adj u v := hTtriH huU hvU huv
      have huvPack : (packingGraph P).Adj u v := by
        rw [Erdos207.coveredGraph_adj]
        exact ⟨W, hWP, huW, hvW, huv⟩
      exact (packingGraph_disjoint_residual G P).le_bot ⟨huvPack, huvH⟩
    · exfalso
      have huvH : H.Adj u v := hTtriH huW hvW huv
      have huvPack : (packingGraph P).Adj u v := by
        rw [Erdos207.coveredGraph_adj]
        exact ⟨U, hUP, huU, hvU, huv⟩
      exact (packingGraph_disjoint_residual G P).le_bot ⟨huvPack, huvH⟩
    · exact hP.1 u v huv U hUP huU hvU W hWP huW hvW
  have hP'tri : ∀ U ∈ P', IsGraphTriangle G U := by
    intro U hUP'
    simp only [P', Finset.mem_insert] at hUP'
    rcases hUP' with rfl | hUP
    · exact hTtriG
    · exact hP.2 U hUP
  have hP'mem : P' ∈ trianglePackings G := by
    rw [mem_trianglePackings]
    exact ⟨hP'packing, hP'tri⟩
  have hmax := (maximumTrianglePacking_spec G).2 P' hP'mem
  have hcard : P'.card = P.card + 1 := by simp [P', hTnot]
  rw [hcard] at hmax
  change P.card + 1 ≤ P.card at hmax
  omega

/-- Exact edge accounting after deleting a packing. -/
lemma card_residual_add_three_mul {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : TriangleFamilyOn V) (hP : IsTrianglePacking G P) :
    (packingResidual G P).edgeFinset.card + 3 * P.card = G.edgeFinset.card := by
  have hsup := packingGraph_sup_residual (packingGraph_le hP)
  have hdisj := packingGraph_disjoint_residual G P
  have hedge : (packingGraph P ⊔ packingResidual G P).edgeFinset =
      (packingGraph P).edgeFinset ∪ (packingResidual G P).edgeFinset := by
    exact SimpleGraph.edgeFinset_sup
  have hfinDisj : Disjoint (packingGraph P).edgeFinset
      (packingResidual G P).edgeFinset := SimpleGraph.disjoint_edgeFinset.mpr hdisj
  have hcard := Finset.card_union_of_disjoint hfinDisj
  have hcard_eq : (packingGraph P ⊔ packingResidual G P).edgeFinset.card =
      G.edgeFinset.card := by
    calc
      (packingGraph P ⊔ packingResidual G P).edgeFinset.card =
          (packingGraph P ⊔ packingResidual G P).edgeSet.ncard := by
            exact (Set.ncard_eq_toFinset_card' _).symm
      _ = G.edgeSet.ncard := congrArg (fun K : SimpleGraph V ↦ K.edgeSet.ncard) hsup
      _ = G.edgeFinset.card := Set.ncard_eq_toFinset_card' _
  rw [← hedge, hcard_eq, card_packingGraph_edgeFinset hP.1] at hcard
  omega

/-! ## Exact edge restriction and Mantel's theorem -/

lemma edgeSet_from_edgeFinset {V : Type*} [DecidableEq V]
    (s : Finset (Sym2 V)) (hloop : ∀ e ∈ s, ¬e.IsDiag) :
    (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet = (s : Set (Sym2 V)) := by
  ext e
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨fun h ↦ h.1, fun he ↦ ⟨he, hloop e he⟩⟩

/-- Restrict a finite graph to any prescribed smaller number of edges. -/
lemma exists_spanning_subgraph_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) (hm : m ≤ G.edgeSet.ncard) :
    ∃ H : SimpleGraph V, H ≤ G ∧ H.edgeSet.ncard = m := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hm' : m ≤ G.edgeFinset.card := by
    exact hm.trans_eq (Set.ncard_eq_toFinset_card' G.edgeSet)
  obtain ⟨s, hsG, hscard⟩ := Finset.exists_subset_card_eq hm'
  let H := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
  have hsloop : ∀ e ∈ s, ¬e.IsDiag := by
    intro e hes hediag
    have heG : e ∈ G.edgeSet := by
      simpa [SimpleGraph.mem_edgeFinset] using hsG hes
    exact G.not_isDiag_of_mem_edgeSet heG hediag
  have hHedges : H.edgeSet = (s : Set (Sym2 V)) := edgeSet_from_edgeFinset s hsloop
  refine ⟨H, ?_, ?_⟩
  · rw [← SimpleGraph.edgeSet_subset_edgeSet, hHedges]
    intro e he
    simpa [SimpleGraph.mem_edgeFinset] using hsG he
  · rw [hHedges, Set.ncard_coe_finset, hscard]

/-- Mantel's theorem in the exact natural-number form used below. -/
lemma card_edgeFinset_le_quarter_of_cliqueFree_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} [DecidableRel H.Adj] (hH : H.CliqueFree 3) :
    H.edgeFinset.card ≤ Fintype.card V ^ 2 / 4 := by
  let n := Fintype.card V
  have heq : (n ^ 2 - (n % 2) ^ 2) / 4 + (n % 2).choose 2 = n ^ 2 / 4 := by
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hj]
      have hs : (j + j) ^ 2 = 4 * (j * j) := by ring
      have hm : (j + j) % 2 = 0 := by omega
      rw [hs, hm]
      simp
    · rw [hj]
      have hs : (2 * j + 1) ^ 2 = 4 * (j * j + j) + 1 := by ring
      have hm : (2 * j + 1) % 2 = 1 := by omega
      rw [hs, hm]
      simp
      omega
  rw [← heq]
  simpa only [Nat.mul_one, Nat.reduceSub, Nat.reduceMul] using
    hH.card_edgeFinset_le (r := 2)

/-! ## A quantitative stability form of Mantel's theorem -/

private lemma mul_le_add_sq_div_four (a b : ℕ) :
    a * b ≤ (a + b) ^ 2 / 4 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
  rcases le_total a b with hab | hba
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hab
    nlinarith [sq_nonneg r]
  · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hba
    nlinarith [sq_nonneg r]

/-- If a triangle-free graph is `d` edges below Mantel's bound, then some
bipartition has at most `d` internal edges.  This is the exact elementary
stability estimate used in the proof of Problem 1009. -/
lemma exists_cut_internalEdges_le_defect
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ)
    (hH : H.CliqueFree 3)
    (hcard : H.edgeFinset.card + d = Fintype.card V ^ 2 / 4) :
    ∃ S : Finset V,
      (H.insideEdgeFinset S).card + (H.insideEdgeFinset Sᶜ).card ≤ d := by
  classical
  obtain ⟨v, hv⟩ := H.exists_maximal_degree_vertex
  let S := H.neighborFinset v
  let B := Sᶜ
  let K := H.between (S : Set V) (B : Set V)
  let L := H.insideGraph B
  have hSB : Disjoint (S : Set V) (B : Set V) := by
    rw [Set.disjoint_left]
    intro x hxS hxB
    simpa [B, hxS] using hxB
  have hSind : H.IsIndepSet (S : Set V) := by
    simpa [S] using H.isIndepSet_neighborSet_of_triangleFree hH v
  have hinsideS : (H.insideEdgeFinset S).card = 0 := by
    apply Finset.card_eq_zero.mpr
    by_contra hne
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_insideEdgeFinset_mk] at he
        exact hSind he.2.1 he.2.2 (H.ne_of_adj he.1) he.1
  have hdegSplit (x : V) (hx : x ∈ B) :
      K.degree x + L.degree x = H.degree x := by
    have hxS : x ∉ S := by simpa [B] using hx
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext y
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      constructor
      · intro hy
        rcases hy with hy | hy
        · have hy' : H.Adj x y ∧
              ((x ∈ S ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ S)) := by
            simpa only [K, SimpleGraph.between_adj, Finset.mem_coe] using hy
          exact hy'.1
        · have hy' : H.Adj x y ∧ x ∈ B ∧ y ∈ B := by
            simpa only [L, SimpleGraph.insideGraph_adj] using hy
          exact hy'.1
      · intro hxy
        by_cases hyS : y ∈ S
        · left
          change (H.between (S : Set V) (B : Set V)).Adj x y
          rw [SimpleGraph.between_adj]
          exact ⟨hxy, Or.inr ⟨hx, hyS⟩⟩
        · right
          change (H.insideGraph B).Adj x y
          rw [SimpleGraph.insideGraph_adj]
          exact ⟨hxy, hx, by simpa [B] using hyS⟩
    · rw [Finset.disjoint_left]
      intro y hyK hyL
      rw [SimpleGraph.mem_neighborFinset] at hyK hyL
      have hyK' : H.Adj x y ∧
          ((x ∈ S ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ S)) := by
        simpa only [K, SimpleGraph.between_adj, Finset.mem_coe] using hyK
      have hyL' : H.Adj x y ∧ x ∈ B ∧ y ∈ B := by
        simpa only [L, SimpleGraph.insideGraph_adj] using hyL
      rcases hyK'.2 with hbad | hyS
      · exact hxS hbad.1
      · have hyNotS : y ∉ S := by simpa [B] using hyL'.2.2
        exact hyNotS hyS.2
  have hKsum : ∑ x ∈ B, K.degree x = K.edgeFinset.card := by
    exact SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges'
      (SimpleGraph.between_isBipartiteWith hSB)
  have hLoutside (x : V) (hx : x ∉ B) : L.degree x = 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
    ext y
    simp [L, SimpleGraph.insideGraph_adj, hx]
  have hLsum : ∑ x ∈ B, L.degree x = 2 * L.edgeFinset.card := by
    rw [← L.sum_degrees_eq_twice_card_edges]
    exact Finset.sum_subset (by simp) (by
      intro x _ hx
      simpa using hLoutside x hx)
  have hsumSplit :
      K.edgeFinset.card + 2 * L.edgeFinset.card = ∑ x ∈ B, H.degree x := by
    rw [← hKsum, ← hLsum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hdegSplit
  have hsumBound : ∑ x ∈ B, H.degree x ≤ B.card * S.card := by
    calc
      ∑ x ∈ B, H.degree x ≤ ∑ _x ∈ B, H.maxDegree :=
        Finset.sum_le_sum fun x _ ↦ H.degree_le_maxDegree x
      _ = B.card * S.card := by simp [S, ← hv]
  have hKB :
      K.edgeFinset.card = (H.cutEdgeFinset S).card := by
    congr 1
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [SimpleGraph.mem_edgeFinset, K, SimpleGraph.between_adj,
          Finset.mem_coe, B, Finset.mem_compl,
          SimpleGraph.mem_cutEdgeFinset_mk, SimpleGraph.mem_edgeSet]
        tauto
  have hLB :
      L.edgeFinset.card = (H.insideEdgeFinset B).card := by
    simpa [L] using congrArg Finset.card
      (SimpleGraph.edgeFinset_insideGraph_eq_insideEdgeFinset H B)
  have hpart := H.card_edgeFinset_eq_inside_add_cut_add_inside_compl S
  have hBcompl : B = Sᶜ := rfl
  have hprod : S.card * B.card ≤ Fintype.card V ^ 2 / 4 := by
    calc
      S.card * B.card ≤ (S.card + B.card) ^ 2 / 4 :=
        mul_le_add_sq_div_four _ _
      _ = Fintype.card V ^ 2 / 4 := by
        simp [B]
  refine ⟨S, ?_⟩
  rw [hinsideS, zero_add]
  have hcrossTwice :
      (H.cutEdgeFinset S).card + 2 * (H.insideEdgeFinset B).card ≤
        S.card * B.card := by
    rw [← hKB, ← hLB]
    calc
      K.edgeFinset.card + 2 * L.edgeFinset.card = ∑ x ∈ B, H.degree x := hsumSplit
      _ ≤ B.card * S.card := hsumBound
      _ = S.card * B.card := mul_comm _ _
  have hcrossTwice' :
      (H.cutEdgeFinset S).card + 2 * (H.insideEdgeFinset Sᶜ).card ≤
        S.card * (Sᶜ).card := by
    simpa [B] using hcrossTwice
  have hprod' : S.card * (Sᶜ).card ≤ Fintype.card V ^ 2 / 4 := by
    simpa [B] using hprod
  omega

/-! ## Maximum cuts -/

private def toggle {V : Type*} [DecidableEq V] (S : Finset V) (v : V) : Finset V :=
  if v ∈ S then S.erase v else insert v S

@[simp] private lemma mem_toggle {V : Type*} [DecidableEq V]
    (S : Finset V) (v w : V) : w ∈ toggle S v ↔ (w ∈ S ↔ w ≠ v) := by
  by_cases hv : v ∈ S <;> by_cases hw : w = v <;> simp [toggle, hv, hw]

/-- A cut with the largest possible number of crossing edges. -/
def maximumCut {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  (Finset.exists_max_image (Finset.univ : Finset (Finset V))
    (fun S ↦ (G.cutEdgeFinset S).card) Finset.univ_nonempty).choose

lemma maximumCut_spec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ S : Finset V,
      (G.cutEdgeFinset S).card ≤ (G.cutEdgeFinset (maximumCut G)).card := by
  intro S
  exact (Finset.exists_max_image (Finset.univ : Finset (Finset V))
    (fun T ↦ (G.cutEdgeFinset T).card) Finset.univ_nonempty).choose_spec.2 S (by simp)

private lemma cut_toggle_deleteIncidenceSet {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    (G.between (S : Set V) (S : Set V)ᶜ).deleteIncidenceSet v =
      (G.between (toggle S v : Set V) (toggle S v : Set V)ᶜ).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, SimpleGraph.between_adj,
    Finset.mem_coe, Set.mem_compl_iff]
  constructor <;> rintro ⟨hxy, hx, hy⟩ <;> refine ⟨?_, hx, hy⟩
  · refine ⟨hxy.1, ?_⟩
    simpa [hx, hy] using hxy.2
  · refine ⟨hxy.1, ?_⟩
    simpa [hx, hy] using hxy.2

private lemma degree_cut_add_degree_toggle {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) :
    (G.between (S : Set V) (S : Set V)ᶜ).degree v +
      (G.between (toggle S v : Set V) (toggle S v : Set V)ᶜ).degree v =
      G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    ← Finset.card_union_of_disjoint]
  · congr 1
    ext w
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset,
      SimpleGraph.between_adj, Finset.mem_coe, Set.mem_compl_iff, mem_toggle]
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S <;> simp_all
    all_goals
      intro hadj heq
      subst w
      exact G.loopless.irrefl v hadj
  · rw [Finset.disjoint_left]
    intro w hw hw'
    rw [SimpleGraph.mem_neighborFinset] at hw hw'
    simp only [SimpleGraph.between_adj, Finset.mem_coe, Set.mem_compl_iff,
      mem_toggle] at hw hw'
    by_cases hv : v ∈ S <;> by_cases hws : w ∈ S <;> simp_all

/-- At a maximum cut, a vertex has at least as many cross-neighbors as
same-side neighbors. -/
lemma maximumCut_internalDegree_le_crossDegree {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    G.degree v - (G.between (maximumCut G : Set V)
        (maximumCut G : Set V)ᶜ).degree v ≤
      (G.between (maximumCut G : Set V) (maximumCut G : Set V)ᶜ).degree v := by
  classical
  let S := maximumCut G
  let K := G.between (S : Set V) (S : Set V)ᶜ
  let K' := G.between (toggle S v : Set V) (toggle S v : Set V)ᶜ
  have hdelete : K.deleteIncidenceSet v = K'.deleteIncidenceSet v :=
    by simpa [K, K'] using cut_toggle_deleteIncidenceSet G S v
  have hedge : K'.edgeFinset.card ≤ K.edgeFinset.card := by
    simpa [K, K', SimpleGraph.edgeFinset_between_compl_eq_cutEdgeFinset] using
      maximumCut_spec G (toggle S v)
  have hKdeg : K.degree v ≤ K.edgeFinset.card := K.degree_le_card_edgeFinset v
  have hK'deg : K'.degree v ≤ K'.edgeFinset.card := K'.degree_le_card_edgeFinset v
  have hdecomp : (K.deleteIncidenceSet v).edgeFinset.card + K.degree v =
      K.edgeFinset.card := by
    rw [K.card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel hKdeg
  have hdecomp' : (K'.deleteIncidenceSet v).edgeFinset.card + K'.degree v =
      K'.edgeFinset.card := by
    rw [K'.card_edgeFinset_deleteIncidenceSet]
    exact Nat.sub_add_cancel hK'deg
  have hdelcard : (K.deleteIncidenceSet v).edgeFinset.card =
      (K'.deleteIncidenceSet v).edgeFinset.card := by
    calc
      (K.deleteIncidenceSet v).edgeFinset.card =
          (K.deleteIncidenceSet v).edgeSet.ncard :=
        (Set.ncard_eq_toFinset_card' _).symm
      _ = (K'.deleteIncidenceSet v).edgeSet.ncard :=
        congrArg (fun J : SimpleGraph V ↦ J.edgeSet.ncard) hdelete
      _ = (K'.deleteIncidenceSet v).edgeFinset.card :=
        Set.ncard_eq_toFinset_card' _
  have hdeg' : K'.degree v ≤ K.degree v := by omega
  have hsum : K.degree v + K'.degree v = G.degree v :=
    by simpa [K, K'] using degree_cut_add_degree_toggle G S v
  have hresult : G.degree v - K.degree v ≤ K.degree v := by omega
  simpa [K, S] using hresult

/-- A maximum cut minimizes the number of internal edges. -/
lemma maximumCut_internalEdges_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (G.insideEdgeFinset (maximumCut G)).card +
        (G.insideEdgeFinset (maximumCut G)ᶜ).card ≤
      (G.insideEdgeFinset S).card + (G.insideEdgeFinset Sᶜ).card := by
  have hmax := maximumCut_spec G S
  have hpartMax := G.card_edgeFinset_eq_inside_add_cut_add_inside_compl (maximumCut G)
  have hpartS := G.card_edgeFinset_eq_inside_add_cut_add_inside_compl S
  omega

lemma maximumCut_insideDegree_le_otherSide {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (G.insideGraph (maximumCut G)).degree v ≤ (maximumCut G)ᶜ.card ∧
      (G.insideGraph (maximumCut G)ᶜ).degree v ≤ (maximumCut G).card := by
  classical
  let A := maximumCut G
  let B := Aᶜ
  let K := G.between (A : Set V) (A : Set V)ᶜ
  have hlocal : G.degree v - K.degree v ≤ K.degree v := by
    simpa [K, A] using maximumCut_internalDegree_le_crossDegree G v
  have hKA (x : V) (hx : x ∈ A) :
      K.degree x + (G.insideGraph A).degree x = G.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext y
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      constructor
      · intro hy
        rcases hy with hy | hy
        · have hy' : G.Adj x y ∧
              ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := by
            simpa only [K, SimpleGraph.between_adj, Finset.mem_coe,
              Set.mem_compl_iff] using hy
          exact hy'.1
        · have hy' : G.Adj x y ∧ x ∈ A ∧ y ∈ A := by
            simpa only [SimpleGraph.insideGraph_adj] using hy
          exact hy'.1
      · intro hxy
        by_cases hyA : y ∈ A
        · right
          rw [SimpleGraph.insideGraph_adj]
          exact ⟨hxy, hx, hyA⟩
        · left
          change (G.between (A : Set V) (A : Set V)ᶜ).Adj x y
          rw [SimpleGraph.between_adj]
          exact ⟨hxy, Or.inl ⟨hx, hyA⟩⟩
    · rw [Finset.disjoint_left]
      intro y hyK hyI
      rw [SimpleGraph.mem_neighborFinset] at hyK hyI
      have hyK' : G.Adj x y ∧
          ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := by
        simpa only [K, SimpleGraph.between_adj, Finset.mem_coe,
          Set.mem_compl_iff] using hyK
      have hyI' : G.Adj x y ∧ x ∈ A ∧ y ∈ A := by
        simpa only [SimpleGraph.insideGraph_adj] using hyI
      rcases hyK'.2 with h | h
      · exact h.2 hyI'.2.2
      · exact h.1 hx
  have hKB (x : V) (hx : x ∈ B) :
      K.degree x + (G.insideGraph B).degree x = G.degree x := by
    have hxA : x ∉ A := by simpa [B] using hx
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext y
      simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset]
      constructor
      · intro hy
        rcases hy with hy | hy
        · have hy' : G.Adj x y ∧
              ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := by
            simpa only [K, SimpleGraph.between_adj, Finset.mem_coe,
              Set.mem_compl_iff] using hy
          exact hy'.1
        · have hy' : G.Adj x y ∧ x ∈ B ∧ y ∈ B := by
            simpa only [SimpleGraph.insideGraph_adj] using hy
          exact hy'.1
      · intro hxy
        by_cases hyA : y ∈ A
        · left
          change (G.between (A : Set V) (A : Set V)ᶜ).Adj x y
          rw [SimpleGraph.between_adj]
          exact ⟨hxy, Or.inr ⟨hxA, hyA⟩⟩
        · right
          rw [SimpleGraph.insideGraph_adj]
          exact ⟨hxy, hx, by simpa [B] using hyA⟩
    · rw [Finset.disjoint_left]
      intro y hyK hyI
      rw [SimpleGraph.mem_neighborFinset] at hyK hyI
      have hyK' : G.Adj x y ∧
          ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := by
        simpa only [K, SimpleGraph.between_adj, Finset.mem_coe,
          Set.mem_compl_iff] using hyK
      have hyI' : G.Adj x y ∧ x ∈ B ∧ y ∈ B := by
        simpa only [SimpleGraph.insideGraph_adj] using hyI
      rcases hyK'.2 with h | h
      · exact hxA h.1
      · have hyNotA : y ∉ A := by simpa [B] using hyI'.2.2
        exact hyNotA h.2
  have hKdegreeA (x : V) (hx : x ∈ A) : K.degree x ≤ B.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hy' : G.Adj x y ∧
        ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := by
      simpa only [K, SimpleGraph.between_adj, Finset.mem_coe,
        Set.mem_compl_iff] using hy
    rcases hy'.2 with h | h
    · simpa [B] using h.2
    · exact (h.1 hx).elim
  have hKdegreeB (x : V) (hx : x ∈ B) : K.degree x ≤ A.card := by
    have hxA : x ∉ A := by simpa [B] using hx
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    have hy' : G.Adj x y ∧
        ((x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A)) := by
      simpa only [K, SimpleGraph.between_adj, Finset.mem_coe,
        Set.mem_compl_iff] using hy
    rcases hy'.2 with h | h
    · exact (hxA h.1).elim
    · exact h.2
  constructor
  · by_cases hvA : v ∈ A
    · have hs := hKA v hvA
      exact (by omega : (G.insideGraph A).degree v ≤ K.degree v) |>.trans
        (hKdegreeA v hvA)
    · have hz : (G.insideGraph A).degree v = 0 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
        ext w
        simp [SimpleGraph.insideGraph_adj, hvA]
      simp [A, B, hz]
  · by_cases hvB : v ∈ B
    · have hs := hKB v hvB
      exact (by omega : (G.insideGraph B).degree v ≤ K.degree v) |>.trans
        (hKdegreeB v hvB)
    · have hz : (G.insideGraph B).degree v = 0 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
        ext w
        simp [SimpleGraph.insideGraph_adj, hvB]
      simpa [A, B, hz]

lemma insideEdges_sup_le {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (S : Finset V) :
    ((G ⊔ H).insideEdgeFinset S).card ≤
      (G.insideEdgeFinset S).card + (H.insideEdgeFinset S).card := by
  classical
  have hsub : (G ⊔ H).insideEdgeFinset S ⊆
      G.insideEdgeFinset S ∪ H.insideEdgeFinset S := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        rw [SimpleGraph.mem_insideEdgeFinset_mk] at he
        rw [Finset.mem_union]
        rw [SimpleGraph.sup_adj] at he
        rcases he.1 with huv | huv
        · left
          exact (SimpleGraph.mem_insideEdgeFinset_mk G S u v).mpr ⟨huv, he.2⟩
        · right
          exact (SimpleGraph.mem_insideEdgeFinset_mk H S u v).mpr ⟨huv, he.2⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-! ## Finite greedy coloring tools -/

/-- Greedy coloring in the form needed for partial edge-coloring.  The
hypothesis says that every nonempty subfamily has an element with fewer than
`l` conflicts inside that subfamily. -/
lemma greedyColorFinset
    {α : Type*} [DecidableEq α] (R : α → α → Prop) [DecidableRel R]
    (hRsymm : Std.Symm R) (hRirrefl : Std.Irrefl R)
    (E : Finset α) (l : ℕ) (hl : 0 < l)
    (hdeg : ∀ F ⊆ E, F.Nonempty →
      ∃ x ∈ F, ((F.erase x).filter (R x)).card < l) :
    ∃ color : α → Fin l,
      ∀ ⦃x⦄, x ∈ E → ∀ ⦃y⦄, y ∈ E → R x y → color x ≠ color y := by
  classical
  have aux : ∀ F : Finset α, F ⊆ E →
      ∃ color : α → Fin l,
        ∀ ⦃x⦄, x ∈ F → ∀ ⦃y⦄, y ∈ F → R x y → color x ≠ color y := by
    intro F
    refine Finset.strongInductionOn F ?_
    intro F ih hFE
    by_cases hF : F.Nonempty
    · obtain ⟨x, hxF, hxdeg⟩ := hdeg F hFE hF
      have herase : F.erase x ⊂ F := Finset.erase_ssubset hxF
      obtain ⟨color, hcolor⟩ := ih (F.erase x) herase
        ((Finset.erase_subset _ _).trans hFE)
      let forbidden := ((F.erase x).filter (R x)).image color
      have hforbidden : forbidden.card < l := Finset.card_image_le.trans_lt hxdeg
      have hz : ∃ z : Fin l, z ∉ forbidden := by
        by_contra hn
        push Not at hn
        have hsub : (Finset.univ : Finset (Fin l)) ⊆ forbidden := by
          intro z _
          exact hn z
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_univ, Fintype.card_fin] at hc
        omega
      obtain ⟨z, hz⟩ := hz
      let color' := Function.update color x z
      refine ⟨color', ?_⟩
      intro a ha b hb hab
      have habne : a ≠ b := fun heq ↦ hRirrefl.irrefl b (heq ▸ hab)
      by_cases hax : a = x
      · subst a
        have hbx : b ≠ x := Ne.symm habne
        have hbErase : b ∈ F.erase x := Finset.mem_erase.mpr ⟨hbx, hb⟩
        have hbFilter : b ∈ (F.erase x).filter (R x) := by
          exact Finset.mem_filter.mpr ⟨hbErase, hab⟩
        have hnot : color b ≠ z := by
          intro heq
          exact hz (Finset.mem_image.mpr ⟨b, hbFilter, heq⟩)
        simpa [color', hbx] using hnot.symm
      · by_cases hbx : b = x
        · subst b
          have haErase : a ∈ F.erase x := Finset.mem_erase.mpr ⟨hax, ha⟩
          have haFilter : a ∈ (F.erase x).filter (R x) := by
            exact Finset.mem_filter.mpr ⟨haErase, hRsymm.symm _ _ hab⟩
          have hnot : color a ≠ z := by
            intro heq
            exact hz (Finset.mem_image.mpr ⟨a, haFilter, heq⟩)
          simpa [color', hax] using hnot
        · have haErase : a ∈ F.erase x := Finset.mem_erase.mpr ⟨hax, ha⟩
          have hbErase : b ∈ F.erase x := Finset.mem_erase.mpr ⟨hbx, hb⟩
          simpa [color', hax, hbx] using hcolor haErase hbErase hab
    · exact ⟨fun _ ↦ ⟨0, hl⟩, by
        intro x hx
        exact (hF ⟨x, hx⟩).elim⟩
  exact aux E (by simp)

/-- An arbitrary subfinset with cardinality `min n s.card`. -/
noncomputable def trimFinset {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) : Finset α :=
  if h : n ≤ s.card then (Finset.exists_subset_card_eq h).choose else s

lemma trimFinset_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) : trimFinset s n ⊆ s := by
  classical
  unfold trimFinset
  split_ifs with h
  · exact (Finset.exists_subset_card_eq h).choose_spec.1
  · exact Finset.Subset.rfl

lemma card_trimFinset {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) : (trimFinset s n).card = min n s.card := by
  classical
  unfold trimFinset
  split_ifs with h
  · rw [(Finset.exists_subset_card_eq h).choose_spec.2, min_eq_left h]
  · rw [min_eq_right (Nat.le_of_not_ge h)]

lemma card_sdiff_trimFinset_le {α : Type*} [DecidableEq α]
    (s : Finset α) (l h : ℕ) (hhl : h ≤ l) (hs : s.card ≤ l) :
    (s \ trimFinset s (l - h)).card ≤ h := by
  rw [Finset.card_sdiff_of_subset (trimFinset_subset s _), card_trimFinset]
  omega

/-! ## Partial edge-coloring of a sparse graph -/

/-- Two distinct unordered pairs conflict when they share a vertex. -/
def EdgeConflict {V : Type*} (e f : Sym2 V) : Prop :=
  e ≠ f ∧ ∃ v, v ∈ e ∧ v ∈ f

instance EdgeConflict.instDecidableRel {V : Type*} [DecidableEq V] :
    DecidableRel (@EdgeConflict V) := Classical.decRel _

instance EdgeConflict.instSymm {V : Type*} : Std.Symm (@EdgeConflict V) where
  symm e f hef := ⟨hef.1.symm, by
    obtain ⟨v, hve, hvf⟩ := hef.2
    exact ⟨v, hvf, hve⟩⟩

instance EdgeConflict.instIrrefl {V : Type*} : Std.Irrefl (@EdgeConflict V) where
  irrefl e he := he.1 rfl

private lemma card_conflicts_lt_incidence_sum {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) {x y : V} (hxy : x ≠ y) (heF : s(x, y) ∈ F) :
    ((F.erase s(x, y)).filter (EdgeConflict s(x, y))).card <
      (F.filter (x ∈ ·)).card + (F.filter (y ∈ ·)).card := by
  let C := (F.erase s(x, y)).filter (EdgeConflict s(x, y))
  let I := F.filter (x ∈ ·) ∪ F.filter (y ∈ ·)
  have hCI : C ⊆ I := by
    intro e heC
    simp only [C, Finset.mem_filter] at heC
    obtain ⟨v, hvxy, hve⟩ := heC.2.2
    rw [Sym2.mem_iff] at hvxy
    have heF' : e ∈ F := Finset.mem_of_mem_erase heC.1
    rcases hvxy with rfl | rfl
    · simp [I, heF', hve]
    · simp [I, heF', hve]
  have heI : s(x, y) ∈ I := by simp [I, heF]
  have heCnot : s(x, y) ∉ C := by simp [C]
  have hstrict : C ⊂ I := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hCI, ?_⟩
    intro heq
    exact heCnot (heq ▸ heI)
  exact (Finset.card_lt_card hstrict).trans_le (Finset.card_union_le _ _)

/-- Vertices whose internal degree is at least one quarter of the available
number of colors. -/
def highVertices {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (l : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ l ≤ 4 * J.degree v

/-- The cross edges at a high vertex. -/
def crossStar {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (U : Finset V) (u : V) :
    Finset (Sym2 V) :=
  (J.cutEdgeFinset U).filter (u ∈ ·)

/-- Retain every low--low edge and, at each high vertex, at most `l - |U|`
of its high--low edges. -/
noncomputable def retainedEdges {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (l : ℕ) : Finset (Sym2 V) :=
  let U := highVertices J l
  J.insideEdgeFinset Uᶜ ∪ U.biUnion fun u ↦
    trimFinset (crossStar J U u) (l - U.card)

lemma retainedEdges_subset {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (l : ℕ) :
    retainedEdges J l ⊆ J.edgeFinset := by
  classical
  let U := highVertices J l
  intro e he
  rw [retainedEdges, Finset.mem_union] at he
  rcases he with he | he
  · exact (Finset.inter_subset_left : J.insideEdgeFinset Uᶜ ⊆ J.edgeFinset) he
  · rw [Finset.mem_biUnion] at he
    obtain ⟨u, huU, heu⟩ := he
    have heu' := trimFinset_subset (crossStar J U u) (l - U.card) heu
    have heuCut : e ∈ J.cutEdgeFinset U :=
      (Finset.filter_subset _ _ : crossStar J U u ⊆ J.cutEdgeFinset U) heu'
    exact (Finset.filter_subset _ _ : J.cutEdgeFinset U ⊆ J.edgeFinset) heuCut

lemma highVertices_card_mul_le {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (l : ℕ) :
    (highVertices J l).card * l ≤ 8 * J.edgeFinset.card := by
  classical
  let U := highVertices J l
  calc
    U.card * l = ∑ _v ∈ U, l := by simp
    _ ≤ ∑ v ∈ U, 4 * J.degree v := by
      apply Finset.sum_le_sum
      intro v hv
      simpa [U, highVertices] using hv
    _ ≤ ∑ v, 4 * J.degree v := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun _ _ _ ↦ by omega)
    _ = 8 * J.edgeFinset.card := by
      rw [← Finset.mul_sum, J.sum_degrees_eq_twice_card_edges]
      ring

lemma highVertices_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (l : ℕ) (hl : 0 < l)
    (hsparse : 32 * J.edgeFinset.card ≤ l ^ 2) :
    (highVertices J l).card ≤ l := by
  have hsum := highVertices_card_mul_le J l
  nlinarith

private lemma card_inside_high_le_sq {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (U : Finset V) :
    (J.insideEdgeFinset U).card ≤ U.card ^ 2 := by
  classical
  let K := J.insideGraph U
  have houtside (v : V) (hv : v ∉ U) : K.degree v = 0 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero]
    ext w
    simp [K, SimpleGraph.insideGraph_adj, hv]
  have hsumU : ∑ v ∈ U, K.degree v = 2 * K.edgeFinset.card := by
    rw [← K.sum_degrees_eq_twice_card_edges]
    exact Finset.sum_subset (by simp) (by
      intro v _ hv
      simpa using houtside v hv)
  have hdegree (v : V) : K.degree v ≤ U.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    have hw' : J.Adj v w ∧ v ∈ U ∧ w ∈ U := by
      simpa only [K, SimpleGraph.insideGraph_adj] using hw
    exact hw'.2.2
  have hbound : ∑ v ∈ U, K.degree v ≤ U.card * U.card := by
    calc
      ∑ v ∈ U, K.degree v ≤ ∑ _v ∈ U, U.card :=
        Finset.sum_le_sum fun v _ ↦ hdegree v
      _ = U.card * U.card := by simp
  have hedge : K.edgeFinset.card = (J.insideEdgeFinset U).card := by
    simpa [K] using congrArg Finset.card
      (SimpleGraph.edgeFinset_insideGraph_eq_insideEdgeFinset J U)
  rw [hsumU, hedge] at hbound
  nlinarith

lemma card_discarded_retained_mul_sq_le {V : Type*} [Fintype V]
    [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (l : ℕ) (hl : 0 < l) (hmax : ∀ v, J.degree v ≤ l)
    (hsparse : 32 * J.edgeFinset.card ≤ l ^ 2) :
    (J.edgeFinset \ retainedEdges J l).card * l ^ 2 ≤
      128 * J.edgeFinset.card ^ 2 := by
  classical
  let U := highVertices J l
  let h := U.card
  let keptStar (u : V) := trimFinset (crossStar J U u) (l - h)
  have hhl : h ≤ l := by
    simpa [h, U] using highVertices_card_le J l hl hsparse
  have hstarCard (u : V) : (crossStar J U u).card ≤ l := by
    have hsub : crossStar J U u ⊆ J.incidenceFinset u := by
      intro e he
      rw [crossStar, Finset.mem_filter] at he
      rw [J.incidenceFinset_eq_filter, Finset.mem_filter]
      exact ⟨(Finset.filter_subset _ _ : J.cutEdgeFinset U ⊆ J.edgeFinset) he.1,
        he.2⟩
    exact (Finset.card_le_card hsub).trans (by
      rw [J.card_incidenceFinset_eq_degree]
      exact hmax u)
  have hstarLoss (u : V) :
      (crossStar J U u \ keptStar u).card ≤ h := by
    simpa [keptStar] using
      card_sdiff_trimFinset_le (crossStar J U u) l h hhl (hstarCard u)
  have hdiscard :
      J.edgeFinset \ retainedEdges J l ⊆
        J.insideEdgeFinset U ∪ U.biUnion fun u ↦ crossStar J U u \ keptStar u := by
    intro e he
    rw [Finset.mem_sdiff] at he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxyAdj : J.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he.1
        have hxy : x ≠ y := J.ne_of_adj hxyAdj
        rw [Finset.mem_union]
        by_cases hx : x ∈ U <;> by_cases hy : y ∈ U
        · left
          exact (SimpleGraph.mem_insideEdgeFinset_mk J U x y).mpr ⟨hxyAdj, hx, hy⟩
        · right
          rw [Finset.mem_biUnion]
          refine ⟨x, hx, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
          · rw [crossStar, Finset.mem_filter,
              SimpleGraph.mem_cutEdgeFinset_mk]
            exact ⟨⟨hxyAdj, by tauto⟩, by simp⟩
          · intro hkeep
            apply he.2
            change s(x, y) ∈ J.insideEdgeFinset Uᶜ ∪
              U.biUnion fun u ↦ trimFinset (crossStar J U u) (l - U.card)
            rw [Finset.mem_union]
            right
            rw [Finset.mem_biUnion]
            simpa [h, keptStar] using ⟨x, hx, hkeep⟩
        · right
          rw [Finset.mem_biUnion]
          refine ⟨y, hy, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
          · rw [crossStar, Finset.mem_filter,
              SimpleGraph.mem_cutEdgeFinset_mk]
            exact ⟨⟨hxyAdj, by tauto⟩, by simp⟩
          · intro hkeep
            apply he.2
            change s(x, y) ∈ J.insideEdgeFinset Uᶜ ∪
              U.biUnion fun u ↦ trimFinset (crossStar J U u) (l - U.card)
            rw [Finset.mem_union]
            right
            rw [Finset.mem_biUnion]
            simpa [h, keptStar] using ⟨y, hy, hkeep⟩
        · exfalso
          apply he.2
          change s(x, y) ∈ J.insideEdgeFinset Uᶜ ∪
            U.biUnion fun u ↦ trimFinset (crossStar J U u) (l - U.card)
          rw [Finset.mem_union]
          left
          rw [SimpleGraph.mem_insideEdgeFinset_mk]
          exact ⟨hxyAdj, by simpa using hx, by simpa using hy⟩
  have hdiscardCard :
      (J.edgeFinset \ retainedEdges J l).card ≤ 2 * h ^ 2 := by
    calc
      (J.edgeFinset \ retainedEdges J l).card ≤
          (J.insideEdgeFinset U ∪
            U.biUnion fun u ↦ crossStar J U u \ keptStar u).card :=
        Finset.card_le_card hdiscard
      _ ≤ (J.insideEdgeFinset U).card +
          (U.biUnion fun u ↦ crossStar J U u \ keptStar u).card :=
        Finset.card_union_le _ _
      _ ≤ h ^ 2 + ∑ u ∈ U, (crossStar J U u \ keptStar u).card := by
        gcongr
        · simpa [h] using card_inside_high_le_sq J U
        · exact Finset.card_biUnion_le
      _ ≤ h ^ 2 + ∑ _u ∈ U, h := by
        gcongr with u hu
        exact hstarLoss u
      _ = 2 * h ^ 2 := by simp [h, pow_two, two_mul]
  have hhigh : h * l ≤ 8 * J.edgeFinset.card := by
    simpa [h, U] using highVertices_card_mul_le J l
  calc
    (J.edgeFinset \ retainedEdges J l).card * l ^ 2 ≤
        (2 * h ^ 2) * l ^ 2 := Nat.mul_le_mul_right _ hdiscardCard
    _ = 2 * (h * l) ^ 2 := by ring
    _ ≤ 2 * (8 * J.edgeFinset.card) ^ 2 := by
      exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hhigh 2)
    _ = 128 * J.edgeFinset.card ^ 2 := by ring

private lemma eq_of_mem_cutEdge_of_mem_high {V : Type*} [Fintype V]
    [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (U : Finset V) {e : Sym2 V} {x u : V}
    (heCut : e ∈ J.cutEdgeFinset U) (hxe : x ∈ e) (hxU : x ∈ U)
    (hue : u ∈ e) (huU : u ∈ U) : x = u := by
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [SimpleGraph.mem_cutEdgeFinset_mk] at heCut
      simp only [Sym2.mem_iff] at hxe hue
      rcases hxe with rfl | rfl <;> rcases hue with rfl | rfl
      · rfl
      · exfalso
        exact heCut.2 (propext ⟨fun _ ↦ huU, fun _ ↦ hxU⟩)
      · exfalso
        exact heCut.2 (propext ⟨fun _ ↦ hxU, fun _ ↦ huU⟩)
      · rfl

private lemma card_retained_incidence_high_le {V : Type*} [Fintype V]
    [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (l : ℕ) {x : V} (hx : x ∈ highVertices J l) :
    ((retainedEdges J l).filter (x ∈ ·)).card ≤
      l - (highVertices J l).card := by
  classical
  let U := highVertices J l
  let T := trimFinset (crossStar J U x) (l - U.card)
  have hsub : (retainedEdges J l).filter (x ∈ ·) ⊆ T := by
    intro e he
    rw [Finset.mem_filter] at he
    have hxe := he.2
    rw [retainedEdges, Finset.mem_union] at he
    rcases he.1 with heLow | heStars
    · induction e using Sym2.inductionOn with
      | _ a b =>
          rw [SimpleGraph.mem_insideEdgeFinset_mk] at heLow
          simp only [Sym2.mem_iff] at hxe
          rcases hxe with rfl | rfl
          · have hnot : x ∉ U := by simpa using heLow.2.1
            exact (hnot (by simpa [U] using hx)).elim
          · have hnot : x ∉ U := by simpa using heLow.2.2
            exact (hnot (by simpa [U] using hx)).elim
    · rw [Finset.mem_biUnion] at heStars
      obtain ⟨u, huU, heu⟩ := heStars
      have heuStar := trimFinset_subset (crossStar J U u) (l - U.card) heu
      rw [crossStar, Finset.mem_filter] at heuStar
      have hxu : x = u := eq_of_mem_cutEdge_of_mem_high J U
        heuStar.1 hxe (by simpa [U] using hx) heuStar.2 huU
      subst u
      exact heu
  calc
    ((retainedEdges J l).filter (x ∈ ·)).card ≤ T.card := Finset.card_le_card hsub
    _ = min (l - U.card) (crossStar J U x).card := card_trimFinset _ _
    _ ≤ l - U.card := min_le_left _ _

private lemma card_incidence_le_degree {V : Type*} [Fintype V]
    [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (F : Finset (Sym2 V)) (hF : F ⊆ J.edgeFinset) (v : V) :
    (F.filter (v ∈ ·)).card ≤ J.degree v := by
  have hsub : F.filter (v ∈ ·) ⊆ J.incidenceFinset v := by
    intro e he
    rw [Finset.mem_filter] at he
    rw [J.incidenceFinset_eq_filter, Finset.mem_filter]
    exact ⟨hF he.1, he.2⟩
  simpa using Finset.card_le_card hsub

private lemma card_crossOnly_incidence_low_le {V : Type*} [Fintype V]
    [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]
    (U : Finset V) (F : Finset (Sym2 V)) (hF : F ⊆ J.edgeFinset)
    (hcross : ∀ e ∈ F, e ∉ J.insideEdgeFinset Uᶜ)
    {y : V} (hy : y ∉ U) :
    (F.filter (y ∈ ·)).card ≤ U.card := by
  classical
  let stars : Finset (Sym2 V) := U.biUnion fun u ↦ {s(u, y)}
  have hsub : F.filter (y ∈ ·) ⊆ stars := by
    intro e he
    rw [Finset.mem_filter] at he
    induction e using Sym2.inductionOn with
    | _ a b =>
        have habAdj : J.Adj a b := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hF he.1
        have hnotLow := hcross s(a, b) he.1
        have hnotBoth : ¬(a ∉ U ∧ b ∉ U) := by
          intro hab
          apply hnotLow
          rw [SimpleGraph.mem_insideEdgeFinset_mk]
          exact ⟨habAdj, by simpa using hab.1, by simpa using hab.2⟩
        simp only [Sym2.mem_iff] at he
        change s(a, b) ∈ U.biUnion fun u ↦ {s(u, y)}
        rw [Finset.mem_biUnion]
        rcases he.2 with rfl | rfl
        · have hbU : b ∈ U := by tauto
          exact ⟨b, hbU, by simp⟩
        · have haU : a ∈ U := by tauto
          exact ⟨a, haU, by simp [Sym2.eq_swap]⟩
  calc
    (F.filter (y ∈ ·)).card ≤ stars.card := Finset.card_le_card hsub
    _ ≤ ∑ _u ∈ U, ({s(_u, y)} : Finset (Sym2 V)).card :=
      Finset.card_biUnion_le
    _ = U.card := by simp

/-- All retained internal edges have a proper edge-coloring by the opposite
part.  Together with the preceding loss lemma, this is the quantitative
partial edge-coloring assertion used by Győri's packing argument. -/
lemma exists_retained_edgeColoring {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (l : ℕ) (hl : 0 < l)
    (hUcard : (highVertices J l).card ≤ l) :
    ∃ color : Sym2 V → Fin l,
      ∀ ⦃e⦄, e ∈ retainedEdges J l → ∀ ⦃f⦄, f ∈ retainedEdges J l →
        EdgeConflict e f → color e ≠ color f := by
  classical
  let U := highVertices J l
  have hUl : U.card ≤ l := by simpa [U] using hUcard
  apply greedyColorFinset EdgeConflict inferInstance inferInstance
    (retainedEdges J l) l hl
  intro F hF hFne
  have hFJ : F ⊆ J.edgeFinset := hF.trans (retainedEdges_subset J l)
  by_cases hlow : ∃ e ∈ F, e ∈ J.insideEdgeFinset Uᶜ
  · obtain ⟨e, heF, heLow⟩ := hlow
    refine ⟨e, heF, ?_⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxyAdj : J.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hFJ heF
        have hxy : x ≠ y := J.ne_of_adj hxyAdj
        rw [SimpleGraph.mem_insideEdgeFinset_mk] at heLow
        have hxU : x ∉ U := by simpa using heLow.2.1
        have hyU : y ∉ U := by simpa using heLow.2.2
        have hxdeg : 4 * J.degree x < l := by
          simpa [U, highVertices] using hxU
        have hydeg : 4 * J.degree y < l := by
          simpa [U, highVertices] using hyU
        have hxinc := card_incidence_le_degree J F hFJ x
        have hyinc := card_incidence_le_degree J F hFJ y
        have hconf := card_conflicts_lt_incidence_sum F hxy heF
        omega
  · push Not at hlow
    obtain ⟨e, heF⟩ := hFne
    refine ⟨e, heF, ?_⟩
    have heRet := hF heF
    have heCut : e ∈ J.cutEdgeFinset U := by
      rw [retainedEdges, Finset.mem_union] at heRet
      rcases heRet with heLow | heStars
      · exact (hlow e heF heLow).elim
      · rw [Finset.mem_biUnion] at heStars
        obtain ⟨u, huU, heu⟩ := heStars
        exact (Finset.filter_subset _ _ : crossStar J U u ⊆ J.cutEdgeFinset U)
          (trimFinset_subset _ _ heu)
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_cutEdgeFinset_mk] at heCut
        have hxy : x ≠ y := J.ne_of_adj heCut.1
        have hcross : ∀ f ∈ F, f ∉ J.insideEdgeFinset Uᶜ := hlow
        by_cases hxU : x ∈ U
        · have hyU : y ∉ U := by
            intro hy
            exact heCut.2 (propext ⟨fun _ ↦ hy, fun _ ↦ hxU⟩)
          have hsubInc : F.filter (x ∈ ·) ⊆
              (retainedEdges J l).filter (x ∈ ·) := by
            intro z hz
            rw [Finset.mem_filter] at hz ⊢
            exact ⟨hF hz.1, hz.2⟩
          have hxRet : ((retainedEdges J l).filter (x ∈ ·)).card ≤
              l - U.card := by
            simpa [U] using card_retained_incidence_high_le J l
              (by simpa [U] using hxU)
          have hxinc : (F.filter (x ∈ ·)).card ≤ l - U.card :=
            (Finset.card_le_card hsubInc).trans hxRet
          have hyinc : (F.filter (y ∈ ·)).card ≤ U.card :=
            card_crossOnly_incidence_low_le J U F hFJ hcross hyU
          have hconf := card_conflicts_lt_incidence_sum F hxy heF
          omega
        · have hyU : y ∈ U := by
            by_contra hy
            exact heCut.2 (propext ⟨fun h ↦ (hxU h).elim, fun h ↦ (hy h).elim⟩)
          have hxinc : (F.filter (x ∈ ·)).card ≤ U.card :=
            card_crossOnly_incidence_low_le J U F hFJ hcross hxU
          have hsubInc : F.filter (y ∈ ·) ⊆
              (retainedEdges J l).filter (y ∈ ·) := by
            intro z hz
            rw [Finset.mem_filter] at hz ⊢
            exact ⟨hF hz.1, hz.2⟩
          have hyRet : ((retainedEdges J l).filter (y ∈ ·)).card ≤
              l - U.card := by
            simpa [U] using card_retained_incidence_high_le J l
              (by simpa [U] using hyU)
          have hyinc : (F.filter (y ∈ ·)).card ≤ l - U.card :=
            (Finset.card_le_card hsubInc).trans hyRet
          have hconf := card_conflicts_lt_incidence_sum F hxy heF
          omega

/-! ## Averaging two cyclic relabelings -/

private lemma exists_average_bipartiteAbove_mul_card_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (r : α → β → Prop) [∀ a b, Decidable (r a b)]
    (s : Finset α) (t : Finset β) (hs : s.Nonempty) (m : ℕ)
    (hm : ∀ b ∈ t, (s.bipartiteBelow r b).card ≤ m) :
    ∃ a ∈ s, (t.bipartiteAbove r a).card * s.card ≤ t.card * m := by
  classical
  by_contra hn
  push Not at hn
  have hstrict :
      ∑ a ∈ s, t.card * m <
        ∑ a ∈ s, (t.bipartiteAbove r a).card * s.card := by
    exact Finset.sum_lt_sum_of_nonempty hs (fun a ha ↦ hn a ha)
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := s) (t := t) r
  have hsum : ∑ b ∈ t, (s.bipartiteBelow r b).card ≤ ∑ _b ∈ t, m := by
    exact Finset.sum_le_sum hm
  have hstrict' :
      ∑ a ∈ s, t.card * m <
        (∑ b ∈ t, (s.bipartiteBelow r b).card) * s.card := by
    calc
      ∑ a ∈ s, t.card * m <
          ∑ a ∈ s, (t.bipartiteAbove r a).card * s.card := hstrict
      _ = (∑ a ∈ s, (t.bipartiteAbove r a).card) * s.card :=
        (Finset.sum_mul _ _ _).symm
      _ = (∑ b ∈ t, (s.bipartiteBelow r b).card) * s.card := by
        rw [hdouble]
  have hright :
      (∑ b ∈ t, (s.bipartiteBelow r b).card) * s.card ≤
        (∑ _b ∈ t, m) * s.card := Nat.mul_le_mul_right _ hsum
  have hconstS : ∑ _a ∈ s, t.card * m = s.card * (t.card * m) := by
    simp only [Finset.sum_const_nat, nsmul_eq_mul]
  have hconstT : ∑ _b ∈ t, m = t.card * m := by
    simp only [Finset.sum_const_nat, nsmul_eq_mul]
  rw [hconstS] at hstrict'
  rw [hconstT] at hright
  nlinarith

private lemma card_filter_mem_le_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (s : Finset α) (t : Finset β) :
    (s.filter fun x ↦ f x ∈ t).card ≤ t.card := by
  let emb : α ↪ β := ⟨f, hf⟩
  rw [← Finset.card_map emb]
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  simpa [emb] using (Finset.mem_filter.mp hx).2

/-- A collision between the triangle based on `p.1` and the triangle based
on `p.2`, after independently shifting the two color palettes. -/
def ShiftCollision {V : Type*} {a b : ℕ} [NeZero a] [NeZero b]
    (enumA : Fin a ↪ V) (enumB : Fin b ↪ V)
    (colorA : Sym2 V → Fin b) (colorB : Sym2 V → Fin a)
    (shift : Fin a × Fin b) (p : Sym2 V × Sym2 V) : Prop :=
  enumB (shift.2 + colorA p.1) ∈ p.2 ∧
    enumA (shift.1 + colorB p.2) ∈ p.1

instance ShiftCollision.instDecidable {V : Type*} [DecidableEq V]
    {a b : ℕ} [NeZero a] [NeZero b]
    (enumA : Fin a ↪ V) (enumB : Fin b ↪ V)
    (colorA : Sym2 V → Fin b) (colorB : Sym2 V → Fin a)
    (shift : Fin a × Fin b) (p : Sym2 V × Sym2 V) :
    Decidable (ShiftCollision enumA enumB colorA colorB shift p) :=
  Classical.propDecidable _

private lemma card_collision_shifts_le_four
    {V : Type*} [DecidableEq V] {a b : ℕ} [NeZero a] [NeZero b]
    (enumA : Fin a ↪ V) (enumB : Fin b ↪ V)
    (colorA : Sym2 V → Fin b) (colorB : Sym2 V → Fin a)
    (p : Sym2 V × Sym2 V) (hpA : ¬p.1.IsDiag) (hpB : ¬p.2.IsDiag) :
    (((Finset.univ : Finset (Fin a)) ×ˢ (Finset.univ : Finset (Fin b))).filter
      fun shift ↦ ShiftCollision enumA enumB colorA colorB shift p).card ≤ 4 := by
  classical
  let goodA := (Finset.univ : Finset (Fin a)).filter fun t ↦
    enumA (t + colorB p.2) ∈ p.1
  let goodB := (Finset.univ : Finset (Fin b)).filter fun t ↦
    enumB (t + colorA p.1) ∈ p.2
  have hfunA : Function.Injective (fun t : Fin a ↦ enumA (t + colorB p.2)) := by
    intro x y hxy
    apply add_right_cancel (b := colorB p.2)
    exact enumA.injective hxy
  have hfunB : Function.Injective (fun t : Fin b ↦ enumB (t + colorA p.1)) := by
    intro x y hxy
    apply add_right_cancel (b := colorA p.1)
    exact enumB.injective hxy
  have hgoodA : goodA.card ≤ 2 := by
    calc
      goodA.card ≤ p.1.toFinset.card := by
        simpa [goodA] using card_filter_mem_le_of_injective
          (fun t : Fin a ↦ enumA (t + colorB p.2)) hfunA Finset.univ p.1.toFinset
      _ = 2 := Sym2.card_toFinset_of_not_isDiag _ hpA
  have hgoodB : goodB.card ≤ 2 := by
    calc
      goodB.card ≤ p.2.toFinset.card := by
        simpa [goodB] using card_filter_mem_le_of_injective
          (fun t : Fin b ↦ enumB (t + colorA p.1)) hfunB Finset.univ p.2.toFinset
      _ = 2 := Sym2.card_toFinset_of_not_isDiag _ hpB
  have hsub :
      (((Finset.univ : Finset (Fin a)) ×ˢ (Finset.univ : Finset (Fin b))).filter
        fun shift ↦ ShiftCollision enumA enumB colorA colorB shift p) ⊆
        goodA ×ˢ goodB := by
    intro shift hs
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_product]
    exact ⟨by simpa [goodA] using hs.2.2, by simpa [goodB] using hs.2.1⟩
  calc
    _ ≤ (goodA ×ˢ goodB).card := Finset.card_le_card hsub
    _ = goodA.card * goodB.card := Finset.card_product _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul hgoodA hgoodB
    _ = 4 := by decide

lemma exists_shifts_collision_bound
    {V : Type*} [DecidableEq V] {a b : ℕ} [NeZero a] [NeZero b]
    (enumA : Fin a ↪ V) (enumB : Fin b ↪ V)
    (EA EB : Finset (Sym2 V))
    (hEA : ∀ e ∈ EA, ¬e.IsDiag) (hEB : ∀ e ∈ EB, ¬e.IsDiag)
    (colorA : Sym2 V → Fin b) (colorB : Sym2 V → Fin a) :
    ∃ shift : Fin a × Fin b,
      (((EA ×ˢ EB).filter fun p ↦
          ShiftCollision enumA enumB colorA colorB shift p).card) * (a * b) ≤
        4 * EA.card * EB.card := by
  classical
  let shifts := (Finset.univ : Finset (Fin a)) ×ˢ (Finset.univ : Finset (Fin b))
  let pairs := EA ×ˢ EB
  let r (shift : Fin a × Fin b) (p : Sym2 V × Sym2 V) :=
    ShiftCollision enumA enumB colorA colorB shift p
  have hshifts : shifts.Nonempty := by
    rw [Finset.nonempty_product]
    exact ⟨Finset.univ_nonempty, Finset.univ_nonempty⟩
  obtain ⟨shift, hshiftMem, hbound⟩ :=
    exists_average_bipartiteAbove_mul_card_le r shifts pairs hshifts 4 (by
      intro p hp
      rw [Finset.mem_product] at hp
      simpa [r, shifts, Finset.bipartiteBelow] using
        card_collision_shifts_le_four enumA enumB colorA colorB p
          (hEA p.1 hp.1) (hEB p.2 hp.2))
  refine ⟨shift, ?_⟩
  simpa [r, shifts, pairs, Finset.bipartiteAbove, mul_assoc, mul_comm, mul_left_comm]
    using hbound

/-! ## Turning colored internal edges into triangles -/

/-- A fixed enumeration of a finset. -/
noncomputable def enumerateFinset {V : Type*} [DecidableEq V]
    (S : Finset V) : Fin S.card ↪ V :=
  S.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)

@[simp] lemma enumerateFinset_mem {V : Type*} [DecidableEq V]
    (S : Finset V) (i : Fin S.card) : enumerateFinset S i ∈ S := by
  exact (S.equivFin.symm i).property

lemma enumerateFinset_surjective {V : Type*} [DecidableEq V]
    (S : Finset V) {v : V} (hv : v ∈ S) :
    ∃ i : Fin S.card, enumerateFinset S i = v := by
  refine ⟨S.equivFin ⟨v, hv⟩, ?_⟩
  simp [enumerateFinset]

/-- Add a third vertex to a non-loop unordered edge. -/
def edgeTriangle {V : Type*} [DecidableEq V] (e : Sym2 V) (w : V)
    (he : ¬e.IsDiag) (hw : w ∉ e) : TriangleOn V :=
  ⟨insert w e.toFinset, by
    rw [Finset.card_insert_of_notMem (by simpa using hw),
      Sym2.card_toFinset_of_not_isDiag e he]
    ⟩

@[simp] lemma mem_edgeTriangle {V : Type*} [DecidableEq V]
    (e : Sym2 V) (w v : V) (he : ¬e.IsDiag) (hw : w ∉ e) :
    v ∈ (edgeTriangle e w he hw).1 ↔ v = w ∨ v ∈ e := by
  simp [edgeTriangle]

/-- The witness obtained by cyclically shifting a color and then enumerating
the opposite side. -/
noncomputable def shiftedWitness {V : Type*} [DecidableEq V]
    (B : Finset V) [NeZero B.card] (color : Sym2 V → Fin B.card)
    (shift : Fin B.card) (e : Sym2 V) : V :=
  enumerateFinset B (shift + color e)

@[simp] lemma shiftedWitness_mem {V : Type*} [DecidableEq V]
    (B : Finset V) [NeZero B.card] (color : Sym2 V → Fin B.card)
    (shift : Fin B.card) (e : Sym2 V) :
    shiftedWitness B color shift e ∈ B := enumerateFinset_mem _ _

/-- Triangle based on an edge internal to `A`, with its shifted color viewed
as a vertex of the disjoint opposite side `B`. -/
noncomputable def orientedTriangle {V : Type*} [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (Sym2 V)) (hnondiag : ∀ e ∈ E, ¬e.IsDiag)
    (hinternal : ∀ e ∈ E, ∀ v ∈ e, v ∈ A)
    [NeZero B.card] (color : Sym2 V → Fin B.card) (shift : Fin B.card)
    (e : {e // e ∈ E}) : TriangleOn V := by
  let w := shiftedWitness B color shift e.1
  have hwB : w ∈ B := shiftedWitness_mem B color shift e.1
  have hw : w ∉ e.1 := by
    intro hwe
    exact (Finset.disjoint_left.mp hAB) (hinternal e.1 e.2 w hwe) hwB
  exact edgeTriangle e.1 w (hnondiag e.1 e.2) hw

noncomputable def orientedFamily {V : Type*} [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (Sym2 V)) (hnondiag : ∀ e ∈ E, ¬e.IsDiag)
    (hinternal : ∀ e ∈ E, ∀ v ∈ e, v ∈ A)
    [NeZero B.card] (color : Sym2 V → Fin B.card) (shift : Fin B.card) :
    TriangleFamilyOn V :=
  E.attach.image (orientedTriangle A B hAB E hnondiag hinternal color shift)

lemma card_orientedFamily {V : Type*} [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (Sym2 V)) (hnondiag : ∀ e ∈ E, ¬e.IsDiag)
    (hinternal : ∀ e ∈ E, ∀ v ∈ e, v ∈ A)
    [NeZero B.card] (color : Sym2 V → Fin B.card) (shift : Fin B.card) :
    (orientedFamily A B hAB E hnondiag hinternal color shift).card = E.card := by
  classical
  rw [orientedFamily, Finset.card_image_of_injective, Finset.card_attach]
  intro e f hef
  apply Subtype.ext
  ext v
  have hrecover (g : {e // e ∈ E}) :
      v ∈ g.1 ↔ v ∈ (orientedTriangle A B hAB E hnondiag hinternal color shift g).1 ∧
        v ∈ A := by
    let w := shiftedWitness B color shift g.1
    have hwB : w ∈ B := shiftedWitness_mem B color shift g.1
    have hwNotA : w ∉ A := by
      intro hwA
      exact (Finset.disjoint_left.mp hAB) hwA hwB
    have hw : w ∉ g.1 := by
      intro hwg
      exact hwNotA (hinternal g.1 g.2 w hwg)
    simp only [orientedTriangle, mem_edgeTriangle]
    constructor
    · intro hvg
      exact ⟨Or.inr hvg, hinternal g.1 g.2 v hvg⟩
    · rintro ⟨hvtri, hvA⟩
      rcases hvtri with rfl | hvg
      · exact (hwNotA hvA).elim
      · exact hvg
  rw [hrecover e, hrecover f, hef]

@[simp] lemma mem_orientedTriangle {V : Type*} [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (Sym2 V)) (hnondiag : ∀ e ∈ E, ¬e.IsDiag)
    (hinternal : ∀ e ∈ E, ∀ v ∈ e, v ∈ A)
    [NeZero B.card] (color : Sym2 V → Fin B.card) (shift : Fin B.card)
    (e : {e // e ∈ E}) (v : V) :
    v ∈ (orientedTriangle A B hAB E hnondiag hinternal color shift e).1 ↔
      v = shiftedWitness B color shift e.1 ∨ v ∈ e.1 := by
  unfold orientedTriangle
  simp only [mem_edgeTriangle]

lemma orientedFamily_isPackingOn {V : Type*} [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (Sym2 V)) (hnondiag : ∀ e ∈ E, ¬e.IsDiag)
    (hinternal : ∀ e ∈ E, ∀ v ∈ e, v ∈ A)
    [NeZero B.card] (color : Sym2 V → Fin B.card) (shift : Fin B.card)
    (hcolor : ∀ ⦃e⦄, e ∈ E → ∀ ⦃f⦄, f ∈ E →
      EdgeConflict e f → color e ≠ color f) :
    Erdos207.IsPackingOn
      (orientedFamily A B hAB E hnondiag hinternal color shift) := by
  classical
  intro u v huv T hT huT hvT W hW huW hvW
  rw [orientedFamily, Finset.mem_image] at hT hW
  obtain ⟨e, heAttach, rfl⟩ := hT
  obtain ⟨f, hfAttach, rfl⟩ := hW
  have heE : e.1 ∈ E := e.2
  have hfE : f.1 ∈ E := f.2
  let we := shiftedWitness B color shift e.1
  let wf := shiftedWitness B color shift f.1
  have hweB : we ∈ B := shiftedWitness_mem B color shift e.1
  have hwfB : wf ∈ B := shiftedWitness_mem B color shift f.1
  have hweA : we ∉ A := fun h ↦ (Finset.disjoint_left.mp hAB) h hweB
  have hwfA : wf ∉ A := fun h ↦ (Finset.disjoint_left.mp hAB) h hwfB
  have huTe : u = we ∨ u ∈ e.1 := by
    simpa [we] using huT
  have hvTe : v = we ∨ v ∈ e.1 := by
    simpa [we] using hvT
  have huWf : u = wf ∨ u ∈ f.1 := by
    simpa [wf] using huW
  have hvWf : v = wf ∨ v ∈ f.1 := by
    simpa [wf] using hvW
  have source_eq : e.1 = f.1 := by
    by_cases huA : u ∈ A
    · have hue : u ∈ e.1 := huTe.resolve_left fun huw ↦ hweA (huw ▸ huA)
      have huf : u ∈ f.1 := huWf.resolve_left fun huw ↦ hwfA (huw ▸ huA)
      by_cases hvA : v ∈ A
      · have hve : v ∈ e.1 := hvTe.resolve_left fun hvw ↦ hweA (hvw ▸ hvA)
        have hvf : v ∈ f.1 := hvWf.resolve_left fun hvw ↦ hwfA (hvw ▸ hvA)
        exact Sym2.eq_of_ne_mem huv hue hve huf hvf
      · have hvwe : v = we := hvTe.resolve_right fun hve ↦
          hvA (hinternal e.1 heE v hve)
        have hvwf : v = wf := hvWf.resolve_right fun hvf ↦
          hvA (hinternal f.1 hfE v hvf)
        by_contra hef
        have hconf : EdgeConflict e.1 f.1 := ⟨hef, ⟨u, hue, huf⟩⟩
        have hcolNe := hcolor heE hfE hconf
        have hwEq : we = wf := hvwe.symm.trans hvwf
        have hadd : shift + color e.1 = shift + color f.1 :=
          (enumerateFinset B).injective (by simpa [we, wf, shiftedWitness] using hwEq)
        exact hcolNe (add_left_cancel hadd)
    · have huwe : u = we := huTe.resolve_right fun hue ↦
        huA (hinternal e.1 heE u hue)
      have huwf : u = wf := huWf.resolve_right fun huf ↦
        huA (hinternal f.1 hfE u huf)
      by_cases hvA : v ∈ A
      · have hve : v ∈ e.1 := hvTe.resolve_left fun hvw ↦ hweA (hvw ▸ hvA)
        have hvf : v ∈ f.1 := hvWf.resolve_left fun hvw ↦ hwfA (hvw ▸ hvA)
        by_contra hef
        have hconf : EdgeConflict e.1 f.1 := ⟨hef, ⟨v, hve, hvf⟩⟩
        have hcolNe := hcolor heE hfE hconf
        have hwEq : we = wf := huwe.symm.trans huwf
        have hadd : shift + color e.1 = shift + color f.1 :=
          (enumerateFinset B).injective (by simpa [we, wf, shiftedWitness] using hwEq)
        exact hcolNe (add_left_cancel hadd)
      · have hvwe : v = we := hvTe.resolve_right fun hve ↦
          hvA (hinternal e.1 heE v hve)
        exact (huv (huwe.trans hvwe.symm)).elim
  apply Subtype.ext at source_eq
  subst f
  rfl

private lemma cross_oriented_triangles_no_common_edge
    {V : Type*} [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B)
    (EA EB : Finset (Sym2 V))
    (hEA : ∀ e ∈ EA, ¬e.IsDiag) (hEB : ∀ e ∈ EB, ¬e.IsDiag)
    (hintA : ∀ e ∈ EA, ∀ v ∈ e, v ∈ A)
    (hintB : ∀ e ∈ EB, ∀ v ∈ e, v ∈ B)
    [NeZero A.card] [NeZero B.card]
    (colorA : Sym2 V → Fin B.card) (colorB : Sym2 V → Fin A.card)
    (shift : Fin A.card × Fin B.card)
    (e : {e // e ∈ EA}) (f : {e // e ∈ EB})
    (hnocoll : ¬ShiftCollision (enumerateFinset A) (enumerateFinset B)
      colorA colorB shift (e.1, f.1))
    {u v : V} (huv : u ≠ v)
    (huAtri : u ∈ (orientedTriangle A B hAB EA hEA hintA colorA shift.2 e).1)
    (hvAtri : v ∈ (orientedTriangle A B hAB EA hEA hintA colorA shift.2 e).1)
    (huBtri : u ∈ (orientedTriangle B A hAB.symm EB hEB hintB colorB shift.1 f).1)
    (hvBtri : v ∈ (orientedTriangle B A hAB.symm EB hEB hintB colorB shift.1 f).1) :
    False := by
  let we := shiftedWitness B colorA shift.2 e.1
  let wf := shiftedWitness A colorB shift.1 f.1
  have hweB : we ∈ B := shiftedWitness_mem B colorA shift.2 e.1
  have hwfA : wf ∈ A := shiftedWitness_mem A colorB shift.1 f.1
  have hweNotA : we ∉ A := fun h ↦ (Finset.disjoint_left.mp hAB) h hweB
  have hwfNotB : wf ∉ B := fun h ↦ (Finset.disjoint_left.mp hAB) hwfA h
  have huAe : u = we ∨ u ∈ e.1 := by simpa [we] using huAtri
  have hvAe : v = we ∨ v ∈ e.1 := by simpa [we] using hvAtri
  have huBf : u = wf ∨ u ∈ f.1 := by simpa [wf] using huBtri
  have hvBf : v = wf ∨ v ∈ f.1 := by simpa [wf] using hvBtri
  apply hnocoll
  rw [ShiftCollision]
  by_cases huA : u ∈ A
  · have hue : u ∈ e.1 := huAe.resolve_left fun huw ↦ hweNotA (huw ▸ huA)
    have huwf : u = wf := huBf.resolve_right fun huf ↦
      (Finset.disjoint_left.mp hAB) huA (hintB f.1 f.2 u huf)
    by_cases hvA : v ∈ A
    · have hvwf : v = wf := hvBf.resolve_right fun hvf ↦
        (Finset.disjoint_left.mp hAB) hvA (hintB f.1 f.2 v hvf)
      exact (huv (huwf.trans hvwf.symm)).elim
    · have hvwe : v = we := hvAe.resolve_right fun hve ↦
        hvA (hintA e.1 e.2 v hve)
      have hvf : v ∈ f.1 := hvBf.resolve_left fun hvwf ↦
        hvA (hvwf ▸ hwfA)
      exact ⟨by simpa [we, shiftedWitness, hvwe] using hvf,
        by simpa [wf, shiftedWitness, huwf] using hue⟩
  · have huwe : u = we := huAe.resolve_right fun hue ↦
      huA (hintA e.1 e.2 u hue)
    have huf : u ∈ f.1 := huBf.resolve_left fun huwf ↦
      have huB : u ∈ B := by simpa [huwe] using hweB
      hwfNotB (by simpa [huwf] using huB)
    by_cases hvA : v ∈ A
    · have hve : v ∈ e.1 := hvAe.resolve_left fun hvwe ↦
        hweNotA (hvwe ▸ hvA)
      have hvwf : v = wf := hvBf.resolve_right fun hvf ↦
        (Finset.disjoint_left.mp hAB) hvA (hintB f.1 f.2 v hvf)
      exact ⟨by simpa [we, shiftedWitness, huwe] using huf,
        by simpa [wf, shiftedWitness, hvwf] using hve⟩
    · have hvwe : v = we := hvAe.resolve_right fun hve ↦
        hvA (hintA e.1 e.2 v hve)
      exact (huv (huwe.trans hvwe.symm)).elim

lemma orientedFamily_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (Sym2 V)) (hnondiag : ∀ e ∈ E, ¬e.IsDiag)
    (hinternal : ∀ e ∈ E, ∀ v ∈ e, v ∈ A)
    (hEK : E ⊆ K.edgeFinset)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, K.Adj a b)
    [NeZero B.card] (color : Sym2 V → Fin B.card) (shift : Fin B.card) :
    ∀ T ∈ orientedFamily A B hAB E hnondiag hinternal color shift,
      IsGraphTriangle K T := by
  classical
  intro T hT
  rw [orientedFamily, Finset.mem_image] at hT
  obtain ⟨e, heAttach, rfl⟩ := hT
  intro u hu v hv huv
  let w := shiftedWitness B color shift e.1
  have hwB : w ∈ B := shiftedWitness_mem B color shift e.1
  have hu' : u = w ∨ u ∈ e.1 := by simpa [w] using hu
  have hv' : v = w ∨ v ∈ e.1 := by simpa [w] using hv
  rcases hu' with rfl | hue <;> rcases hv' with rfl | hve
  · exact (huv rfl).elim
  · exact (hcross v (hinternal e.1 e.2 v hve) w hwB).symm
  · exact hcross u (hinternal e.1 e.2 u hue) w hwB
  · have heq : e.1 = s(u, v) := (Sym2.mem_and_mem_iff huv).mp ⟨hue, hve⟩
    have hedge : s(u, v) ∈ K.edgeFinset := by simpa [← heq] using hEK e.2
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge

/-- Combine the two oriented colorings, deleting only the second-side edges
that collide with a first-side triangle. -/
lemma exists_combinedPacking {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (A B : Finset V) (hAB : Disjoint A B)
    (EA EB : Finset (Sym2 V))
    (hEA : ∀ e ∈ EA, ¬e.IsDiag) (hEB : ∀ e ∈ EB, ¬e.IsDiag)
    (hintA : ∀ e ∈ EA, ∀ v ∈ e, v ∈ A)
    (hintB : ∀ e ∈ EB, ∀ v ∈ e, v ∈ B)
    (hEAK : EA ⊆ K.edgeFinset) (hEBK : EB ⊆ K.edgeFinset)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, K.Adj a b)
    [NeZero A.card] [NeZero B.card]
    (colorA : Sym2 V → Fin B.card) (colorB : Sym2 V → Fin A.card)
    (hcolorA : ∀ ⦃e⦄, e ∈ EA → ∀ ⦃f⦄, f ∈ EA →
      EdgeConflict e f → colorA e ≠ colorA f)
    (hcolorB : ∀ ⦃e⦄, e ∈ EB → ∀ ⦃f⦄, f ∈ EB →
      EdgeConflict e f → colorB e ≠ colorB f)
    (shift : Fin A.card × Fin B.card) :
    ∃ P : TriangleFamilyOn V, IsTrianglePacking K P ∧
      EA.card + EB.card ≤ P.card +
        ((EA ×ˢ EB).filter fun p ↦ ShiftCollision
          (enumerateFinset A) (enumerateFinset B) colorA colorB shift p).card := by
  classical
  let collision (p : Sym2 V × Sym2 V) := ShiftCollision
    (enumerateFinset A) (enumerateFinset B) colorA colorB shift p
  let badPairs := (EA ×ˢ EB).filter collision
  let badB := EB.filter fun f ↦ ∃ e ∈ EA, collision (e, f)
  let EB' := EB \ badB
  have hbadBsub : badB ⊆ EB := Finset.filter_subset _ _
  have hEB'sub : EB' ⊆ EB := Finset.sdiff_subset
  have hEB'card : EB'.card + badB.card = EB.card := by
    change (EB \ badB).card + badB.card = EB.card
    rw [Finset.card_sdiff_of_subset hbadBsub]
    have := Finset.card_le_card hbadBsub
    omega
  have hbadCard : badB.card ≤ badPairs.card := by
    calc
      badB.card ≤ (badPairs.image Prod.snd).card := by
        apply Finset.card_le_card
        intro f hf
        have hf' : f ∈ EB ∧ ∃ e ∈ EA, collision (e, f) := by
          simpa only [badB, Finset.mem_filter] using hf
        obtain ⟨e, heEA, hecoll⟩ := hf'.2
        rw [Finset.mem_image]
        exact ⟨(e, f), by simp [badPairs, collision, heEA, hf'.1, hecoll], rfl⟩
      _ ≤ badPairs.card := Finset.card_image_le
  have hEB' (e : Sym2 V) (he : e ∈ EB') : ¬e.IsDiag := hEB e (hEB'sub he)
  have hintB' (e : Sym2 V) (he : e ∈ EB') (v : V) (hv : v ∈ e) : v ∈ B :=
    hintB e (hEB'sub he) v hv
  have hEB'K : EB' ⊆ K.edgeFinset := hEB'sub.trans hEBK
  have hcolorB' : ∀ ⦃e⦄, e ∈ EB' → ∀ ⦃f⦄, f ∈ EB' →
      EdgeConflict e f → colorB e ≠ colorB f := by
    intro e he f hf hef
    exact hcolorB (hEB'sub he) (hEB'sub hf) hef
  have hnocol (e : Sym2 V) (he : e ∈ EA) (f : Sym2 V) (hf : f ∈ EB') :
      ¬collision (e, f) := by
    intro hcoll
    have hfBad : f ∈ badB := by
      change f ∈ EB.filter fun f ↦ ∃ e ∈ EA, collision (e, f)
      rw [Finset.mem_filter]
      exact ⟨hEB'sub hf, ⟨e, he, hcoll⟩⟩
    exact (Finset.mem_sdiff.mp hf).2 hfBad
  let PA := orientedFamily A B hAB EA hEA hintA colorA shift.2
  let PB := orientedFamily B A hAB.symm EB' hEB' hintB' colorB shift.1
  have hpackA : Erdos207.IsPackingOn PA := by
    simpa [PA] using orientedFamily_isPackingOn A B hAB EA hEA hintA colorA shift.2 hcolorA
  have hpackB : Erdos207.IsPackingOn PB := by
    simpa [PB] using orientedFamily_isPackingOn B A hAB.symm EB' hEB' hintB'
      colorB shift.1 hcolorB'
  have hcrossNoEdge : ∀ TA ∈ PA, ∀ TB ∈ PB, ∀ {u v : V}, u ≠ v →
      u ∈ TA.1 → v ∈ TA.1 → u ∈ TB.1 → v ∈ TB.1 → False := by
    intro TA hTA TB hTB u v huv huTA hvTA huTB hvTB
    change TA ∈ orientedFamily A B hAB EA hEA hintA colorA shift.2 at hTA
    change TB ∈ orientedFamily B A hAB.symm EB' hEB' hintB' colorB shift.1 at hTB
    rw [orientedFamily, Finset.mem_image] at hTA hTB
    obtain ⟨e, heAttach, rfl⟩ := hTA
    obtain ⟨f, hfAttach, rfl⟩ := hTB
    exact cross_oriented_triangles_no_common_edge A B hAB EA EB' hEA hEB'
      hintA hintB' colorA colorB shift e f
      (by simpa [collision] using hnocol e.1 e.2 f.1 f.2)
      huv huTA hvTA huTB hvTB
  have hPdisj : Disjoint PA PB := by
    rw [Finset.disjoint_left]
    intro T hTA hTB
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by
      rw [T.2]
      decide : 1 < T.1.card)
    exact hcrossNoEdge T hTA T hTB huv hu hv hu hv
  let P : TriangleFamilyOn V := PA ∪ PB
  have hPpack : Erdos207.IsPackingOn P := by
    intro u v huv T hTP huT hvT W hWP huW hvW
    change T ∈ PA ∪ PB at hTP
    change W ∈ PA ∪ PB at hWP
    rw [Finset.mem_union] at hTP hWP
    rcases hTP with hTA | hTB <;> rcases hWP with hWA | hWB
    · exact hpackA u v huv T hTA huT hvT W hWA huW hvW
    · exact (hcrossNoEdge T hTA W hWB huv huT hvT huW hvW).elim
    · exact (hcrossNoEdge W hWA T hTB huv huW hvW huT hvT).elim
    · exact hpackB u v huv T hTB huT hvT W hWB huW hvW
  have hPtri : ∀ T ∈ P, IsGraphTriangle K T := by
    intro T hT
    change T ∈ PA ∪ PB at hT
    rw [Finset.mem_union] at hT
    rcases hT with hTA | hTB
    · exact orientedFamily_triangles K A B hAB EA hEA hintA hEAK hcross
        colorA shift.2 T (by simpa [PA] using hTA)
    · exact orientedFamily_triangles K B A hAB.symm EB' hEB' hintB' hEB'K
        (fun b hb a ha ↦ (hcross a ha b hb).symm) colorB shift.1 T
        (by simpa [PB] using hTB)
  refine ⟨P, ⟨hPpack, hPtri⟩, ?_⟩
  have hPAcard : PA.card = EA.card := by
    simpa [PA] using card_orientedFamily A B hAB EA hEA hintA colorA shift.2
  have hPBcard : PB.card = EB'.card := by
    simpa [PB] using card_orientedFamily B A hAB.symm EB' hEB' hintB' colorB shift.1
  have hPcard : P.card = EA.card + EB'.card := by
    change (PA ∪ PB).card = EA.card + EB'.card
    rw [Finset.card_union_of_disjoint hPdisj, hPAcard, hPBcard]
  simpa [P, badPairs, collision, hPcard] using
    (show EA.card + EB.card ≤ (EA.card + EB'.card) + badPairs.card by omega)

/-- Restrict a packing in a supergraph to triangles of a subgraph.  Because
the original triangles are edge-disjoint, at most one triangle is lost per
deleted edge. -/
lemma restrict_packing_to_subgraph {V : Type*} [Fintype V] [DecidableEq V]
    (G K : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel K.Adj]
    (hGK : G ≤ K) (P : TriangleFamilyOn V) (hP : IsTrianglePacking K P) :
    ∃ Q : TriangleFamilyOn V, IsTrianglePacking G Q ∧
      P.card ≤ Q.card + (K.edgeFinset \ G.edgeFinset).card := by
  classical
  let bad := P.filter fun T ↦ ¬IsGraphTriangle G T
  let Q := P \ bad
  have hbadSub : bad ⊆ P := Finset.filter_subset _ _
  have hQSub : Q ⊆ P := Finset.sdiff_subset
  have hedge (T : {T // T ∈ bad}) :
      ∃ e ∈ K.edgeFinset \ G.edgeFinset, e ∈ T.1.1.sym2 := by
    have hTbad : ¬IsGraphTriangle G T.1 := by
      have hmem : T.1 ∈ P ∧ ¬IsGraphTriangle G T.1 := by
        simpa only [bad, Finset.mem_filter] using T.2
      exact hmem.2
    unfold IsGraphTriangle at hTbad
    push Not at hTbad
    obtain ⟨u, hu, v, hv, huv, huvG⟩ := hTbad
    have hTK : IsGraphTriangle K T.1 := hP.2 T.1 (hbadSub T.2)
    have huvK : K.Adj u v := hTK hu hv huv
    refine ⟨s(u, v), Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using huvK
    · simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using huvG
    · rw [Finset.mem_sym2_iff]
      intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv
  let chosen (T : {T // T ∈ bad}) :
      {e // e ∈ K.edgeFinset \ G.edgeFinset} :=
    ⟨(hedge T).choose, (hedge T).choose_spec.1⟩
  have hchosen_mem (T : {T // T ∈ bad}) :
      (chosen T : Sym2 V) ∈ T.1.1.sym2 :=
    (hedge T).choose_spec.2
  have hchosen_inj : Function.Injective chosen := by
    intro T U hTU
    apply Subtype.ext
    let e : Sym2 V := chosen T
    have hchosenProp : (chosen T : Sym2 V) ∈ K.edgeFinset \ G.edgeFinset :=
      (chosen T).property
    have heK : e ∈ K.edgeFinset := by
      exact (Finset.mem_sdiff.mp hchosenProp).1
    let u := e.out.1
    let v := e.out.2
    have heq : s(u, v) = e := by
      simp only [u, v, Sym2.mk, e.out_eq]
    have hsK : s(u, v) ∈ K.edgeFinset := by simpa [heq] using heK
    have huvK : K.Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hsK
    have huv : u ≠ v := K.ne_of_adj huvK
    have hTmem : ∀ x ∈ e, x ∈ T.1.1 :=
      Finset.mem_sym2_iff.mp (by simpa [e] using hchosen_mem T)
    have hUmem : ∀ x ∈ e, x ∈ U.1.1 := by
      have hmemU : (chosen U : Sym2 V) ∈ U.1.1.sym2 := hchosen_mem U
      have hcoe : (chosen T : Sym2 V) = (chosen U : Sym2 V) :=
        congrArg Subtype.val hTU
      rw [← hcoe] at hmemU
      exact Finset.mem_sym2_iff.mp (by simpa [e] using hmemU)
    exact hP.1 u v huv T.1 (hbadSub T.2)
      (hTmem u (by simpa [u, e] using Sym2.out_fst_mem e))
      (hTmem v (by simpa [v, e] using Sym2.out_snd_mem e))
      U.1 (hbadSub U.2)
      (hUmem u (by simpa [u, e] using Sym2.out_fst_mem e))
      (hUmem v (by simpa [v, e] using Sym2.out_snd_mem e))
  have hbadCard : bad.card ≤ (K.edgeFinset \ G.edgeFinset).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective chosen hchosen_inj
  have hcard : Q.card + bad.card = P.card := by
    change (P \ bad).card + bad.card = P.card
    rw [Finset.card_sdiff_of_subset hbadSub]
    have := Finset.card_le_card hbadSub
    omega
  have hQpack : Erdos207.IsPackingOn Q := by
    intro u v huv T hT huT hvT W hW huW hvW
    exact hP.1 u v huv T (hQSub hT) huT hvT W (hQSub hW) huW hvW
  have hQtri : ∀ T ∈ Q, IsGraphTriangle G T := by
    intro T hT
    have hTP : T ∈ P := hQSub hT
    have hTnotBad : T ∉ bad := (Finset.mem_sdiff.mp hT).2
    by_contra hnot
    exact hTnotBad (by simp [bad, hTP, hnot])
  exact ⟨Q, ⟨hQpack, hQtri⟩, by omega⟩

/-! ## Completing a cut -/

def cutCompletion {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) : SimpleGraph V :=
  G ⊔ (⊤ : SimpleGraph V).between (A : Set V) (A : Set V)ᶜ

instance cutCompletion.instDecidableRel {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    DecidableRel (cutCompletion G A).Adj := by
  dsimp [cutCompletion]
  infer_instance

lemma le_cutCompletion {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) : G ≤ cutCompletion G A := le_sup_left

lemma cutCompletion_cross {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) {a b : V}
    (ha : a ∈ A) (hb : b ∈ Aᶜ) : (cutCompletion G A).Adj a b := by
  rw [cutCompletion, SimpleGraph.sup_adj]
  right
  rw [SimpleGraph.between_adj]
  have hbA : b ∉ A := by simpa using hb
  exact ⟨fun hab ↦ hbA (hab ▸ ha), Or.inl ⟨ha, by simpa using hb⟩⟩

private lemma card_completeCut_edgeFinset {V : Type*} [Fintype V]
    [DecidableEq V] (A : Finset V) :
    ((⊤ : SimpleGraph V).between (A : Set V) (A : Set V)ᶜ).edgeFinset.card =
      A.card * Aᶜ.card := by
  classical
  let C := (⊤ : SimpleGraph V).between (A : Set V) (A : Set V)ᶜ
  have hdisj : Disjoint (A : Set V) ((Aᶜ : Finset V) : Set V) := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    simpa [hxA] using hxB
  have hdeg (b : V) (hb : b ∈ Aᶜ) : C.degree b = A.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext a
    simp only [SimpleGraph.mem_neighborFinset, C, SimpleGraph.between_adj,
      SimpleGraph.top_adj, ne_eq, Finset.mem_coe, Set.mem_compl_iff]
    have hbA : b ∉ A := by simpa using hb
    constructor
    · rintro ⟨hba, hside⟩
      rcases hside with hbad | hgood
      · exact (hbA hbad.1).elim
      · exact hgood.2
    · intro haA
      exact ⟨by
        intro hba
        subst a
        exact hbA haA, Or.inr ⟨by simpa using hb, haA⟩⟩
  have hCBip : C.IsBipartiteWith (A : Set V) ((Aᶜ : Finset V) : Set V) := by
    have hcoe : (((Aᶜ : Finset V) : Set V)) = (A : Set V)ᶜ := by
      ext x
      simp
    have hdisj' : Disjoint (A : Set V) (A : Set V)ᶜ := by
      rw [Set.disjoint_left]
      intro x hxA hxC
      exact hxC hxA
    rw [hcoe]
    simpa only [C] using
      (SimpleGraph.between_isBipartiteWith (G := (⊤ : SimpleGraph V)) hdisj')
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hCBip
  calc
    C.edgeFinset.card = ∑ b ∈ Aᶜ, C.degree b := hsum.symm
    _ = ∑ _b ∈ Aᶜ, A.card := Finset.sum_congr rfl hdeg
    _ = Aᶜ.card * A.card := by simp
    _ = A.card * Aᶜ.card := mul_comm _ _

lemma card_cutCompletion_sdiff_add_cut {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    (cutCompletion G A).edgeFinset.card - G.edgeFinset.card +
        (G.cutEdgeFinset A).card = A.card * Aᶜ.card := by
  classical
  let C := (⊤ : SimpleGraph V).between (A : Set V) (A : Set V)ᶜ
  have hcompEdges : (cutCompletion G A).edgeFinset = G.edgeFinset ∪ C.edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_union]
    change e ∈ (G ⊔ C).edgeSet ↔ e ∈ G.edgeSet ∨ e ∈ C.edgeSet
    rw [SimpleGraph.edgeSet_sup]
    rfl
  have hinter : G.edgeFinset ∩ C.edgeFinset = G.cutEdgeFinset A := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, C, SimpleGraph.between_adj,
          SimpleGraph.top_adj, ne_eq, Finset.mem_coe, Set.mem_compl_iff,
          SimpleGraph.mem_cutEdgeFinset_mk]
        constructor
        · rintro ⟨huv, hne, hside⟩
          exact ⟨huv, by tauto⟩
        · rintro ⟨huv, hside⟩
          exact ⟨huv, G.ne_of_adj huv, by tauto⟩
  have hGsub : G.edgeFinset ⊆ (cutCompletion G A).edgeFinset := by
    intro e he
    rw [hcompEdges]
    exact Finset.mem_union_left _ he
  have hunionCard := Finset.card_union_add_card_inter G.edgeFinset C.edgeFinset
  rw [← hcompEdges, hinter] at hunionCard
  have hGcard := Finset.card_le_card hGsub
  have hCcard := card_completeCut_edgeFinset A
  change C.edgeFinset.card = A.card * Aᶜ.card at hCcard
  omega

/-! ## Numerical estimates for the final assembly -/

private lemma part_card_lower
    (C n k a b I : ℕ) (hC : 0 < C) (hlarge : 16384 * C ≤ n)
    (hk : k < C * n) (hsum : a + b = n)
    (hdefect : a * b + I = n ^ 2 / 4) (hI : I < 4 * k) :
    n ≤ 8 * a := by
  by_contra hna
  have ha : 8 * a < n := by omega
  have hbpos : 0 < b := by
    by_contra hb
    have : b = 0 := by omega
    omega
  have hb : b ≤ n := by omega
  have hab : 8 * (a * b) < n ^ 2 := by
    calc
      8 * (a * b) = (8 * a) * b := by ring
      _ < n * b := Nat.mul_lt_mul_of_pos_right ha hbpos
      _ ≤ n * n := Nat.mul_le_mul_left n hb
      _ = n ^ 2 := by ring
  have hfloor : n ^ 2 ≤ 4 * (n ^ 2 / 4) + 3 := by omega
  have hIsmall : 8 * I + 6 < n ^ 2 := by
    nlinarith
  omega

private lemma total_loss_le
    (C n q sA sB lossA lossB collision eA eB a b : ℕ)
    (hn : 0 < n) (ha : n ≤ 8 * a) (hb : n ≤ 8 * b)
    (hq : sA + sB = q) (heA : eA ≤ sA) (heB : eB ≤ sB)
    (hlossA : lossA * b ^ 2 ≤ 128 * sA ^ 2)
    (hlossB : lossB * a ^ 2 ≤ 128 * sB ^ 2)
    (hcollision : collision * (a * b) ≤ 4 * eA * eB)
    (hqbound : q < 5 * C * n) :
    lossA + lossB + collision ≤ 210000 * C ^ 2 := by
  have hna : n ^ 2 ≤ 64 * a ^ 2 := by nlinarith
  have hnb : n ^ 2 ≤ 64 * b ^ 2 := by nlinarith
  have hnab : n ^ 2 ≤ 64 * (a * b) := by nlinarith
  have hsumSq : sA ^ 2 + sB ^ 2 ≤ q ^ 2 := by nlinarith
  have heSum : eA + eB ≤ q := by omega
  have heProd0 := mul_le_add_sq_div_four eA eB
  have heProd1 : 4 * (eA * eB) ≤ (eA + eB) ^ 2 := by
    simpa [mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < 4)).mp heProd0
  have heProd : 4 * (eA * eB) ≤ q ^ 2 :=
    heProd1.trans (Nat.pow_le_pow_left heSum 2)
  have hlossAn : lossA * n ^ 2 ≤ 8192 * sA ^ 2 := by
    calc
      lossA * n ^ 2 ≤ lossA * (64 * b ^ 2) := Nat.mul_le_mul_left lossA hnb
      _ = 64 * (lossA * b ^ 2) := by ring
      _ ≤ 64 * (128 * sA ^ 2) := Nat.mul_le_mul_left 64 hlossA
      _ = 8192 * sA ^ 2 := by ring
  have hlossBn : lossB * n ^ 2 ≤ 8192 * sB ^ 2 := by
    calc
      lossB * n ^ 2 ≤ lossB * (64 * a ^ 2) := Nat.mul_le_mul_left lossB hna
      _ = 64 * (lossB * a ^ 2) := by ring
      _ ≤ 64 * (128 * sB ^ 2) := Nat.mul_le_mul_left 64 hlossB
      _ = 8192 * sB ^ 2 := by ring
  have hcollisionn : collision * n ^ 2 ≤ 64 * q ^ 2 := by
    calc
      collision * n ^ 2 ≤ collision * (64 * (a * b)) :=
        Nat.mul_le_mul_left collision hnab
      _ = 64 * (collision * (a * b)) := by ring
      _ ≤ 64 * (4 * eA * eB) := Nat.mul_le_mul_left 64 hcollision
      _ = 64 * (4 * (eA * eB)) := by ring
      _ ≤ 64 * q ^ 2 := Nat.mul_le_mul_left 64 heProd
  have htotal : (lossA + lossB + collision) * n ^ 2 ≤ 8256 * q ^ 2 := by
    calc
      (lossA + lossB + collision) * n ^ 2 =
          lossA * n ^ 2 + lossB * n ^ 2 + collision * n ^ 2 := by ring
      _ ≤ 8192 * sA ^ 2 + 8192 * sB ^ 2 + 64 * q ^ 2 :=
        Nat.add_le_add (Nat.add_le_add hlossAn hlossBn) hcollisionn
      _ = 8192 * (sA ^ 2 + sB ^ 2) + 64 * q ^ 2 := by ring
      _ ≤ 8192 * q ^ 2 + 64 * q ^ 2 := by gcongr
      _ = 8256 * q ^ 2 := by ring
  have hqSq : q ^ 2 < (5 * C * n) ^ 2 :=
    Nat.pow_lt_pow_left hqbound (by omega)
  have hstrict : (lossA + lossB + collision) * n ^ 2 <
      (206400 * C ^ 2) * n ^ 2 := by
    calc
      (lossA + lossB + collision) * n ^ 2 ≤ 8256 * q ^ 2 := htotal
      _ < 8256 * (5 * C * n) ^ 2 :=
        (Nat.mul_lt_mul_left (a := 8256) (by omega)).2 hqSq
      _ = (206400 * C ^ 2) * n ^ 2 := by ring
  have hcancel : lossA + lossB + collision < 206400 * C ^ 2 := by
    exact Nat.lt_of_mul_lt_mul_right (by simpa [mul_assoc] using hstrict)
  omega

private lemma edgeFinset_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) : G.edgeFinset ⊆ H.edgeFinset := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ u v =>
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
        hGH (by simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using he)

private lemma insideGraph_edge_vertices {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {e : Sym2 V} (he : e ∈ (G.insideGraph A).edgeFinset) :
    ∀ v ∈ e, v ∈ A := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : (G.insideGraph A).Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      have huv' : G.Adj u v ∧ u ∈ A ∧ v ∈ A := by
        simpa only [SimpleGraph.insideGraph_adj] using huv
      intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact huv'.2.1
      · exact huv'.2.2

private lemma packingGraph_inside_sum_le {V : Type*} [Fintype V]
    [DecidableEq V] (P : TriangleFamilyOn V) (hP : Erdos207.IsPackingOn P)
    (A : Finset V) :
    ((packingGraph P).insideEdgeFinset A).card +
        ((packingGraph P).insideEdgeFinset Aᶜ).card ≤ 3 * P.card := by
  have hpart := (packingGraph P).card_edgeFinset_eq_inside_add_cut_add_inside_compl A
  rw [card_packingGraph_edgeFinset hP] at hpart
  omega

/-! ## The quantitative finite theorem -/

private theorem exists_packing_exact_nat
    (C n k : ℕ) (hC : 0 < C) (hk : k < C * n)
    (G : SimpleGraph (Fin n))
    (hedges : G.edgeSet.ncard = n ^ 2 / 4 + k) :
    ∃ P : TriangleFamilyOn (Fin n), IsTrianglePacking G P ∧
      k ≤ P.card + 210000 * C ^ 2 := by
  classical
  let P₀ := maximumTrianglePacking G
  have hP₀ : IsTrianglePacking G P₀ := maximumTrianglePacking_isPacking G
  by_cases hlarge : 16384 * C ≤ n
  · have hn : 0 < n := by nlinarith
    letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    by_cases hdone : k ≤ P₀.card
    · exact ⟨P₀, hP₀, by omega⟩
    · have hp_lt_k : P₀.card < k := by omega
      let H := packingResidual G P₀
      have haccount := card_residual_add_three_mul G P₀ hP₀
      change H.edgeFinset.card + 3 * P₀.card = G.edgeFinset.card at haccount
      have hGcard : G.edgeFinset.card = n ^ 2 / 4 + k := by
        exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm.trans hedges
      have hHfree : H.CliqueFree 3 := by
        simpa [H, P₀] using maximum_residual_cliqueFree_three G
      have hHmantel : H.edgeFinset.card ≤ n ^ 2 / 4 := by
        simpa using card_edgeFinset_le_quarter_of_cliqueFree_three hHfree
      have hk_three : k ≤ 3 * P₀.card := by
        omega
      let d := 3 * P₀.card - k
      have hHcard : H.edgeFinset.card + d = n ^ 2 / 4 := by
        omega
      obtain ⟨S, hS⟩ := exists_cut_internalEdges_le_defect H d hHfree
        (by simpa using hHcard)
      have hsup : packingGraph P₀ ⊔ H = G := by
        simpa [H] using packingGraph_sup_residual (packingGraph_le hP₀)
      have hinside₁ := insideEdges_sup_le (packingGraph P₀) H S
      have hinside₂ := insideEdges_sup_le (packingGraph P₀) H Sᶜ
      have hinside₁' : (G.insideEdgeFinset S).card ≤
          ((packingGraph P₀).insideEdgeFinset S).card +
            (H.insideEdgeFinset S).card := by
        simpa only [hsup] using hinside₁
      have hinside₂' : (G.insideEdgeFinset Sᶜ).card ≤
          ((packingGraph P₀).insideEdgeFinset Sᶜ).card +
            (H.insideEdgeFinset Sᶜ).card := by
        simpa only [hsup] using hinside₂
      have hpackInside := packingGraph_inside_sum_le P₀ hP₀.1 S
      have hcandidate :
          (G.insideEdgeFinset S).card +
              (G.insideEdgeFinset Sᶜ).card ≤ 6 * P₀.card - k := by
        dsimp [d] at hS
        omega
      let A := maximumCut G
      let B := Aᶜ
      let JA := G.insideGraph A
      let JB := G.insideGraph B
      let sA := JA.edgeFinset.card
      let sB := JB.edgeFinset.card
      let q := sA + sB
      have hqMax := maximumCut_internalEdges_le G S
      have hq_le : q ≤ 6 * P₀.card - k := by
        have hJA : JA.edgeFinset = G.insideEdgeFinset A := by
          exact SimpleGraph.edgeFinset_insideGraph_eq_insideEdgeFinset G A
        have hJB : JB.edgeFinset = G.insideEdgeFinset B := by
          exact SimpleGraph.edgeFinset_insideGraph_eq_insideEdgeFinset G B
        dsimp [q, sA, sB]
        rw [hJA, hJB]
        simpa [A, B] using hqMax.trans hcandidate
      have hq_bound : q < 5 * k := by omega
      have hq_Cn : q < 5 * C * n := by nlinarith
      let r := (G.cutEdgeFinset A).card
      let a := A.card
      let b := B.card
      let K := cutCompletion G A
      let M := K.edgeFinset.card - G.edgeFinset.card
      let I := n ^ 2 / 4 - a * b
      have hab_sum : a + b = n := by simp [a, b, A, B]
      have hab_prod : a * b ≤ n ^ 2 / 4 := by
        simpa [hab_sum] using mul_le_add_sq_div_four a b
      have hIeq : a * b + I = n ^ 2 / 4 := by
        dsimp [I]
        omega
      have hcompletion : M + r = a * b := by
        simpa [M, r, K, a, b, B] using card_cutCompletion_sdiff_add_cut G A
      have hpartition := G.card_edgeFinset_eq_inside_add_cut_add_inside_compl A
      have hedges_qr : q + r = n ^ 2 / 4 + k := by
        have hJA : JA.edgeFinset = G.insideEdgeFinset A :=
          SimpleGraph.edgeFinset_insideGraph_eq_insideEdgeFinset G A
        have hJB : JB.edgeFinset = G.insideEdgeFinset B :=
          SimpleGraph.edgeFinset_insideGraph_eq_insideEdgeFinset G B
        dsimp [q, sA, sB, r]
        rw [hJA, hJB]
        rw [show B = Aᶜ from rfl]
        rw [hGcard] at hpartition
        omega
      have hq_exact : q = k + M + I := by omega
      have hI_small : I < 4 * k := by omega
      have hM_small : M < 4 * k := by omega
      have ha_lower : n ≤ 8 * a :=
        part_card_lower C n k a b I hC hlarge hk hab_sum hIeq hI_small
      have hb_lower : n ≤ 8 * b :=
        part_card_lower C n k b a I hC hlarge hk (by omega)
          (by simpa [mul_comm] using hIeq) hI_small
      have ha_pos : 0 < a := by omega
      have hb_pos : 0 < b := by omega
      letI : NeZero A.card := ⟨by simpa [a] using ha_pos.ne'⟩
      letI : NeZero B.card := ⟨by simpa [b] using hb_pos.ne'⟩
      have hmaxA : ∀ v, JA.degree v ≤ b := by
        intro v
        simpa [JA, a, b, A, B] using
          (maximumCut_insideDegree_le_otherSide G v).1
      have hmaxB : ∀ v, JB.degree v ≤ a := by
        intro v
        simpa [JA, JB, a, b, A, B] using
          (maximumCut_insideDegree_le_otherSide G v).2
      have hsAq : sA ≤ q := by omega
      have hsBq : sB ≤ q := by omega
      have hnC : 10240 * C * n ≤ n ^ 2 := by
        calc
          10240 * C * n ≤ 16384 * C * n := by gcongr <;> omega
          _ ≤ n * n := Nat.mul_le_mul_right n hlarge
          _ = n ^ 2 := by ring
      have hna : n ^ 2 ≤ 64 * a ^ 2 := by
        calc
          n ^ 2 ≤ (8 * a) ^ 2 := Nat.pow_le_pow_left ha_lower 2
          _ = 64 * a ^ 2 := by ring
      have hnb : n ^ 2 ≤ 64 * b ^ 2 := by
        calc
          n ^ 2 ≤ (8 * b) ^ 2 := Nat.pow_le_pow_left hb_lower 2
          _ = 64 * b ^ 2 := by ring
      have hCb : 160 * C * n ≤ b ^ 2 := by
        apply Nat.le_of_mul_le_mul_left (c := 64) _ (by omega)
        calc
          64 * (160 * C * n) = 10240 * C * n := by ring
          _ ≤ n ^ 2 := hnC
          _ ≤ 64 * b ^ 2 := hnb
      have hCa : 160 * C * n ≤ a ^ 2 := by
        apply Nat.le_of_mul_le_mul_left (c := 64) _ (by omega)
        calc
          64 * (160 * C * n) = 10240 * C * n := by ring
          _ ≤ n ^ 2 := hnC
          _ ≤ 64 * a ^ 2 := hna
      have hsparseA : 32 * JA.edgeFinset.card ≤ b ^ 2 := by
        change 32 * sA ≤ b ^ 2
        exact (calc
            32 * sA ≤ 32 * q := Nat.mul_le_mul_left 32 hsAq
            _ < 32 * (5 * C * n) :=
              (Nat.mul_lt_mul_left (a := 32) (by omega)).2 hq_Cn
            _ = 160 * C * n := by ring
            _ ≤ b ^ 2 := hCb).le
      have hsparseB : 32 * JB.edgeFinset.card ≤ a ^ 2 := by
        change 32 * sB ≤ a ^ 2
        exact (calc
            32 * sB ≤ 32 * q := Nat.mul_le_mul_left 32 hsBq
            _ < 32 * (5 * C * n) :=
              (Nat.mul_lt_mul_left (a := 32) (by omega)).2 hq_Cn
            _ = 160 * C * n := by ring
            _ ≤ a ^ 2 := hCa).le
      have hhighA : (highVertices JA b).card ≤ b :=
        highVertices_card_le JA b hb_pos hsparseA
      have hhighB : (highVertices JB a).card ≤ a :=
        highVertices_card_le JB a ha_pos hsparseB
      obtain ⟨colorA, hcolorA⟩ := exists_retained_edgeColoring JA b hb_pos hhighA
      obtain ⟨colorB, hcolorB⟩ := exists_retained_edgeColoring JB a ha_pos hhighB
      let EA := retainedEdges JA b
      let EB := retainedEdges JB a
      let lossA := (JA.edgeFinset \ EA).card
      let lossB := (JB.edgeFinset \ EB).card
      have hlossA : lossA * b ^ 2 ≤ 128 * sA ^ 2 := by
        simpa [lossA, EA, sA] using
          card_discarded_retained_mul_sq_le JA b hb_pos hmaxA hsparseA
      have hlossB : lossB * a ^ 2 ≤ 128 * sB ^ 2 := by
        simpa [lossB, EB, sB] using
          card_discarded_retained_mul_sq_le JB a ha_pos hmaxB hsparseB
      have hEAsub : EA ⊆ JA.edgeFinset := by
        simpa [EA] using retainedEdges_subset JA b
      have hEBsub : EB ⊆ JB.edgeFinset := by
        simpa [EB] using retainedEdges_subset JB a
      have hEAcard : EA.card + lossA = sA := by
        rw [add_comm]
        simpa [lossA, sA] using Finset.card_sdiff_add_card_eq_card hEAsub
      have hEBcard : EB.card + lossB = sB := by
        rw [add_comm]
        simpa [lossB, sB] using Finset.card_sdiff_add_card_eq_card hEBsub
      have hEA : ∀ e ∈ EA, ¬e.IsDiag := by
        intro e he
        exact JA.not_isDiag_of_mem_edgeSet
          (by simpa [SimpleGraph.mem_edgeFinset] using hEAsub he)
      have hEB : ∀ e ∈ EB, ¬e.IsDiag := by
        intro e he
        exact JB.not_isDiag_of_mem_edgeSet
          (by simpa [SimpleGraph.mem_edgeFinset] using hEBsub he)
      have hintA : ∀ e ∈ EA, ∀ v ∈ e, v ∈ A := by
        intro e he
        exact insideGraph_edge_vertices G A (hEAsub he)
      have hintB : ∀ e ∈ EB, ∀ v ∈ e, v ∈ B := by
        intro e he
        exact insideGraph_edge_vertices G B (hEBsub he)
      have hJAG : JA ≤ G := by
        intro u v huv
        have huv' : G.Adj u v ∧ u ∈ A ∧ v ∈ A := by
          simpa only [JA, SimpleGraph.insideGraph_adj] using huv
        exact huv'.1
      have hJBG : JB ≤ G := by
        intro u v huv
        have huv' : G.Adj u v ∧ u ∈ B ∧ v ∈ B := by
          simpa only [JB, SimpleGraph.insideGraph_adj] using huv
        exact huv'.1
      have hEAK : EA ⊆ K.edgeFinset :=
        hEAsub.trans (edgeFinset_mono (hJAG.trans (by simpa [K] using le_cutCompletion G A)))
      have hEBK : EB ⊆ K.edgeFinset :=
        hEBsub.trans (edgeFinset_mono (hJBG.trans (by simpa [K] using le_cutCompletion G A)))
      obtain ⟨shift, hcollision⟩ := exists_shifts_collision_bound
        (enumerateFinset A) (enumerateFinset B) EA EB hEA hEB colorA colorB
      let collision := ((EA ×ˢ EB).filter fun p ↦ ShiftCollision
        (enumerateFinset A) (enumerateFinset B) colorA colorB shift p).card
      have hcollision' : collision * (a * b) ≤ 4 * EA.card * EB.card := by
        simpa [collision, a, b] using hcollision
      have hloss_total : lossA + lossB + collision ≤ 210000 * C ^ 2 :=
        total_loss_le C n q sA sB lossA lossB collision EA.card EB.card a b
          hn ha_lower hb_lower rfl (by omega) (by omega) hlossA hlossB
          hcollision' hq_Cn
      have hcross : ∀ x ∈ A, ∀ y ∈ B, K.Adj x y := by
        intro x hx y hy
        have hy' : y ∈ Aᶜ := by simpa [B] using hy
        simpa [K] using cutCompletion_cross G A hx hy'
      obtain ⟨Pplus, hPplus, hPplusCard⟩ := exists_combinedPacking
        K A B (by
          rw [Finset.disjoint_left]
          intro x hxA hxB
          simpa [B, hxA] using hxB) EA EB hEA hEB hintA hintB hEAK hEBK hcross
        colorA colorB (by simpa [EA] using hcolorA)
          (by simpa [EB] using hcolorB) shift
      have hGK : G ≤ K := by simpa [K] using le_cutCompletion G A
      obtain ⟨Q, hQ, hrestrict⟩ :=
        restrict_packing_to_subgraph G K hGK Pplus hPplus
      have hGedgeSub : G.edgeFinset ⊆ K.edgeFinset := edgeFinset_mono hGK
      have hmissing : (K.edgeFinset \ G.edgeFinset).card = M := by
        rw [Finset.card_sdiff_of_subset hGedgeSub]
      rw [hmissing] at hrestrict
      refine ⟨Q, hQ, ?_⟩
      omega
  · refine ⟨P₀, hP₀, ?_⟩
    have hnsmall : n < 16384 * C := by omega
    nlinarith

/-- Literal formal statement of Problem 1009.  Natural division by four is
the floor in the problem, and `k ≤ P.card + f` is the subtraction-free form
of `P.card ≥ k - f`. -/
def Erdos1009Statement : Prop :=
  ∀ c : ℝ, 0 < c → ∃ f : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.edgeSet.ncard ≥ n ^ 2 / 4 + k →
    (k : ℝ) < c * n →
    ∃ P : TriangleFamilyOn (Fin n), IsTrianglePacking G P ∧ k ≤ P.card + f

/-- Erdős Problem 1009, resolved affirmatively.  The proof above gives the
explicit (non-optimal) choice `f = 210000 * C²` for any natural `C > c`. -/
theorem erdos1009 : Erdos1009Statement := by
  classical
  intro c hc
  obtain ⟨C, hC⟩ := exists_nat_gt c
  have hCReal : 0 < (C : ℝ) := hc.trans hC
  have hCNat : 0 < C := by exact_mod_cast hCReal
  refine ⟨210000 * C ^ 2, ?_⟩
  intro n k G hedges hk
  obtain ⟨H, hHG, hHedges⟩ :=
    exists_spanning_subgraph_card G (n ^ 2 / 4 + k) hedges
  have hkReal : (k : ℝ) < (C : ℝ) * (n : ℝ) := by
    exact hk.trans_le (mul_le_mul_of_nonneg_right hC.le (by positivity))
  have hkNat : k < C * n := by exact_mod_cast hkReal
  obtain ⟨P, hP, hPcard⟩ :=
    exists_packing_exact_nat C n k hCNat hkNat H hHedges
  exact ⟨P, IsTrianglePacking.mono hHG hP, hPcard⟩

#print axioms erdos1009

end

end Erdos1009
