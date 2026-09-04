import ErdosProblems.Erdos76.WeightedCounting
import ErdosProblems.Erdos76.FractionalComplementarity
import Mathlib.Data.Nat.Choose.Cast

/-!
# The explicit fractional bound

The proof combines the weighted two-colour counting inequality with finite
packing/covering duality and complementary slackness.
-/

open Finset
open scoped BigOperators

namespace Erdos76.NewProof

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- A fixed enumeration prevents irrelevant decidability choices for a
complement graph from entering the counting identities. -/
noncomputable def canonicalEdges (G : SimpleGraph V) : Finset (Sym2 V) :=
  @SimpleGraph.edgeFinset V G (Fintype.ofFinite G.edgeSet)

lemma edgeFinset_eq_canonical (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset = canonicalEdges G := by
  ext e
  simp only [canonicalEdges, SimpleGraph.mem_edgeFinset]

lemma triangle_edge_card {G : SimpleGraph V} (t : Finset V) (ht : G.IsNClique 3 t) :
    (G.edgeFinset.filter (fun e ↦ e ∈ t.sym2)).card = 3 := by
  rw [show (G.edgeFinset.filter fun e ↦ e ∈ t.sym2) =
      {e ∈ G.edgeFinset | e.toFinset ⊆ t} by
    ext e
    simp [Finset.mem_sym2_iff, subset_iff]]
  rw [G.card_filter_edgeFinset_toFinset_subset t]
  have htop : G.induce (↑t : Set V) = ⊤ := G.induce_eq_top.mpr ht.isClique
  calc
    #(G.induce (↑t : Set V)).edgeFinset = Nat.card (G.induce (↑t : Set V)).edgeSet := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = Nat.card (⊤ : SimpleGraph t).edgeSet :=
      congrArg (fun H : SimpleGraph t ↦ Nat.card H.edgeSet) htop
    _ = #((⊤ : SimpleGraph t).edgeFinset) := by
      rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    _ = (Fintype.card t).choose 2 := SimpleGraph.card_edgeFinset_top_eq_card_choose_two
    _ = 3 := by simp [ht.card_eq]

noncomputable def triangleEdgeIndices (G : SimpleGraph V) (t : LPDuality.TriangleIndex G) :
    Finset (LPDuality.EdgeIndex G) := univ.filter (fun e ↦ e.val ∈ t.val.sym2)

lemma sum_triangleEdgeIndices (G : SimpleGraph V) (t : LPDuality.TriangleIndex G)
    (z : Sym2 V → ℝ) :
    (∑ e ∈ triangleEdgeIndices G t, z e.val) =
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.val.sym2), z e := by
  simp only [triangleEdgeIndices, sum_filter]
  exact (sum_subtype G.edgeFinset (fun e ↦ SimpleGraph.mem_edgeFinset)
    (fun e ↦ if e ∈ t.val.sym2 then z e else 0)).symm

lemma card_triangleEdgeIndices (G : SimpleGraph V) (t : LPDuality.TriangleIndex G) :
    (triangleEdgeIndices G t).card = 3 := by
  have h := sum_triangleEdgeIndices G t (fun _ ↦ 1)
  simp only [sum_const, nsmul_eq_mul, mul_one, triangle_edge_card t.val t.property] at h
  exact_mod_cast h

lemma load_triangleEdgeIndices (G : SimpleGraph V) (e : LPDuality.EdgeIndex G)
    (w : Finset V → ℝ) :
    (∑ t : LPDuality.TriangleIndex G, if e ∈ triangleEdgeIndices G t then w t.val else 0) =
      fractionalEdgeLoad G w e.val := by
  simp only [triangleEdgeIndices, mem_filter, mem_univ, true_and, fractionalEdgeLoad, sum_filter]
  exact (sum_subtype (G.cliqueFinset 3) (fun t ↦ SimpleGraph.mem_cliqueFinset_iff)
    (fun t ↦ if e.val ∈ t.sym2 then w t else 0)).symm

theorem graph_support_forced_bound (G : SimpleGraph V) (w : Finset V → ℝ) (z : Sym2 V → ℝ)
    (hw : IsFractionalPacking G w) (hz : LPDuality.IsFractionalEdgeCover G z)
    (heq : fractionalSize G w = ∑ e ∈ G.edgeFinset, z e)
    (F : Sym2 V → Prop) (hF : ∀ e ∈ G.edgeFinset, F e → 1 ≤ z e) :
    ((G.edgeFinset.filter (fun e ↦ 0 < z e)).card : ℝ) +
      2 * (G.edgeFinset.filter F).card ≤ 3 * fractionalSize G w := by
  let x : LPDuality.TriangleIndex G → ℝ := fun t ↦ w t.val
  let y : LPDuality.EdgeIndex G → ℝ := fun e ↦ z e.val
  have htotal : (∑ t, x t) = fractionalSize G w :=
    (sum_subtype (G.cliqueFinset 3) (fun t ↦ SimpleGraph.mem_cliqueFinset_iff) w).symm
  have hyTotal : (∑ e, y e) = ∑ e ∈ G.edgeFinset, z e :=
    (sum_subtype G.edgeFinset (fun e ↦ SimpleGraph.mem_edgeFinset) z).symm
  have h := FractionalComplementarity.support_forced_bound (triangleEdgeIndices G)
    (card_triangleEdgeIndices G) x y
    (fun t ↦ hw.1 t.val (SimpleGraph.mem_cliqueFinset_iff.mpr t.property))
    (fun e ↦ hz.1 e.val (SimpleGraph.mem_edgeFinset.mpr e.property))
    (fun e ↦ (load_triangleEdgeIndices G e w).trans_le
      (hw.2 e.val (SimpleGraph.mem_edgeFinset.mpr e.property)))
    (fun t ↦ (hz.2 t.val (SimpleGraph.mem_cliqueFinset_iff.mpr t.property)).trans_eq
      (sum_triangleEdgeIndices G t z).symm)
    (htotal.trans (heq.trans hyTotal.symm))
    (fun e ↦ F e.val) (fun e h ↦ hF e.val (SimpleGraph.mem_edgeFinset.mpr e.property) h)
  rw [htotal] at h
  have hsum : (∑ e : LPDuality.EdgeIndex G,
      ((if 0 < y e then (1 : ℝ) else 0) + 2 * (if F e.val then 1 else 0))) =
      ((G.edgeFinset.filter (fun e ↦ 0 < z e)).card : ℝ) +
        2 * (G.edgeFinset.filter F).card := by
    rw [← sum_subtype G.edgeFinset (fun e ↦ SimpleGraph.mem_edgeFinset)
      (fun e ↦ (if 0 < z e then (1 : ℝ) else 0) + 2 * (if F e then 1 else 0))]
    rw [sum_add_distrib, ← mul_sum]
    simp
  rwa [hsum] at h

lemma triangle_edges_eq {G : SimpleGraph V} {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    G.edgeFinset.filter (fun e ↦ e ∈ ({a, b, c} : Finset V).sym2) =
      {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      mk_mem_sym2_iff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hxy, (rfl | rfl | rfl), (rfl | rfl | rfl)⟩ <;>
        simp_all [Sym2.eq_swap]
    · rintro (h | h | h)
      · have h' := Sym2.eq_iff.mp h
        rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hab, hab.symm]
      · have h' := Sym2.eq_iff.mp h
        rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hac, hac.symm]
      · have h' := Sym2.eq_iff.mp h
        rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hbc, hbc.symm]

lemma triangle_cover_inequality {G : SimpleGraph V} {z : Sym2 V → ℝ}
    (hz : LPDuality.IsFractionalEdgeCover G z) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    1 ≤ z s(a, b) + z s(a, c) + z s(b, c) := by
  have ht := SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩
  have h := hz.2 {a, b, c} (SimpleGraph.mem_cliqueFinset_iff.mpr ht)
  rw [triangle_edges_eq hab hac hbc] at h
  have habac : s(a, b) ≠ s(a, c) := fun h ↦ hbc.ne (Sym2.congr_right.mp h)
  have habbc : s(a, b) ≠ s(b, c) := by
    simp only [ne_eq, Sym2.eq_iff]
    aesop
  have hacbc : s(a, c) ≠ s(b, c) := fun h ↦ hab.ne (Sym2.congr_left.mp h)
  simpa [habac, habbc, hacbc, add_assoc] using h

def zeroGraph (G : SimpleGraph V) (z : Sym2 V → ℝ) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ z s(a, b) = 0
  symm := ⟨fun a b h ↦ ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun _ h ↦ G.irrefl h.1⟩

lemma zeroGraph_edgeFinset (G : SimpleGraph V) (z : Sym2 V → ℝ) :
    (zeroGraph G z).edgeFinset = G.edgeFinset.filter (fun e ↦ z e = 0) := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    rfl

lemma zeroGraph_noTriangle {G : SimpleGraph V} {z : Sym2 V → ℝ}
    (hz : LPDuality.IsFractionalEdgeCover G z) : WeightedCounting.NoTriangle (zeroGraph G z) := by
  intro a b c hab hbc hac
  have h := triangle_cover_inequality hz hab.1 hac.1 hbc.1
  rw [hab.2, hac.2, hbc.2] at h
  norm_num at h

lemma forced_cover_ge_one {G H : SimpleGraph V} {z q : Sym2 V → ℝ}
    (hz : LPDuality.IsFractionalEdgeCover G z) {a b : V}
    (hab : G.Adj a b)
    (hD : WeightedCounting.DoubleCommon (zeroGraph G z) (zeroGraph H q) a b) :
    1 ≤ z s(a, b) := by
  obtain ⟨c, hac, hbc⟩ := hD.1
  have h := triangle_cover_inequality hz hab hac.1 hbc.1
  simpa [hac.2, hbc.2] using h

lemma positive_edge_count {G : SimpleGraph V} {z : Sym2 V → ℝ}
    (hz : ∀ e ∈ G.edgeFinset, 0 ≤ z e) :
    ((G.edgeFinset.filter (fun e ↦ 0 < z e)).card : ℝ) =
      G.edgeFinset.card - (zeroGraph G z).edgeFinset.card := by
  rw [zeroGraph_edgeFinset]
  have hpart : (G.edgeFinset.filter (fun e ↦ z e = 0)).card +
      (G.edgeFinset.filter (fun e ↦ 0 < z e)).card = G.edgeFinset.card := by
    have heq : G.edgeFinset.filter (fun e ↦ 0 < z e) =
        G.edgeFinset.filter (fun e ↦ ¬z e = 0) := by
      ext e
      simp only [mem_filter]
      constructor
      · rintro ⟨he, hp⟩; exact ⟨he, hp.ne'⟩
      · rintro ⟨he, hp⟩; exact ⟨he, lt_of_le_of_ne (hz e he) (Ne.symm hp)⟩
    rw [heq]
    exact card_filter_add_card_filter_not _
  have hpart' : ((G.edgeFinset.filter (fun e ↦ z e = 0)).card : ℝ) +
      (G.edgeFinset.filter (fun e ↦ 0 < z e)).card = G.edgeFinset.card := by exact_mod_cast hpart
  linarith

lemma edge_partition_card (G D : SimpleGraph V) :
    (G.edgeFinset.filter (fun e ↦ e ∈ D.edgeFinset)).card +
      (Gᶜ.edgeFinset.filter (fun e ↦ e ∈ D.edgeFinset)).card = D.edgeFinset.card := by
  have hR : G.edgeFinset.filter (fun e ↦ e ∈ D.edgeFinset) =
      D.edgeFinset.filter (fun e ↦ e ∈ G.edgeFinset) := by
    ext e; simp [and_comm]
  have hB : Gᶜ.edgeFinset.filter (fun e ↦ e ∈ D.edgeFinset) =
      D.edgeFinset.filter (fun e ↦ ¬e ∈ G.edgeFinset) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj]
      exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨h.1.ne, h.2⟩, h.1⟩⟩
  rw [hR, hB]
  exact card_filter_add_card_filter_not _

lemma total_edge_card (G : SimpleGraph V) :
    (G.edgeFinset.card : ℝ) + Gᶜ.edgeFinset.card =
      (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1) / 2 := by
  classical
  let : DecidableRel (⊤ : SimpleGraph V).Adj := Classical.decRel _
  let : DecidableRel Gᶜ.Adj := Classical.decRel _
  have h := edge_partition_card G ⊤
  have hfilter : ∀ H : SimpleGraph V,
      H.edgeFinset.filter (fun e ↦ e ∈ (⊤ : SimpleGraph V).edgeFinset) = H.edgeFinset := by
    intro H
    exact filter_eq_self.mpr (fun e he ↦ SimpleGraph.edgeFinset_mono le_top he)
  simp only [edgeFinset_eq_canonical] at h hfilter
  rw [hfilter, hfilter] at h
  have htop : (canonicalEdges (⊤ : SimpleGraph V)).card = (Fintype.card V).choose 2 := by
    simpa only [edgeFinset_eq_canonical] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V))
  rw [htop] at h
  have hc : (G.edgeFinset.card : ℝ) + Gᶜ.edgeFinset.card = ((Fintype.card V).choose 2 : ℝ) :=
    by
      simp only [edgeFinset_eq_canonical]
      exact_mod_cast h
  simp only [edgeFinset_eq_canonical] at hc ⊢
  rw [hc, Nat.cast_choose_two]

/-- Explicit fractional monochromatic triangle packing, with an error linear
in the number of vertices. -/
theorem explicit_fractional_bound (G : SimpleGraph V) :
    ∃ wR wB : Finset V → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
        (Fintype.card V : ℝ) ^ 2 / 12 - (Fintype.card V : ℝ) / 2 ≤
          fractionalSize G wR + fractionalSize Gᶜ wB := by
  classical
  let : DecidableRel Gᶜ.Adj := Classical.decRel _
  obtain ⟨wR, zR, hwR, hzR₀, hzR₁, heqR⟩ :=
    LPDuality.exists_fractional_triangle_packing_edge_cover G
  obtain ⟨wB, zB, hwB, hzB₀, hzB₁, heqB⟩ :=
    LPDuality.exists_fractional_triangle_packing_edge_cover Gᶜ
  have hzR : LPDuality.IsFractionalEdgeCover G zR := ⟨hzR₀, hzR₁⟩
  have hzB : LPDuality.IsFractionalEdgeCover Gᶜ zB := ⟨hzB₀, hzB₁⟩
  let R := zeroGraph G zR
  let B := zeroGraph Gᶜ zB
  let D := WeightedCounting.doubleCommonGraph R B
  have hforcedR : ∀ e ∈ G.edgeFinset, e ∈ D.edgeFinset → 1 ≤ zR e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he hD
      have hab : G.Adj a b := (SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp he)
      have hd : WeightedCounting.DoubleCommon R B a b :=
        ((SimpleGraph.mem_edgeSet D).mp (SimpleGraph.mem_edgeFinset.mp hD)).2
      exact forced_cover_ge_one hzR hab hd
  have hforcedB : ∀ e ∈ Gᶜ.edgeFinset, e ∈ D.edgeFinset → 1 ≤ zB e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro he hD
      have hab : Gᶜ.Adj a b := (SimpleGraph.mem_edgeSet Gᶜ).mp (SimpleGraph.mem_edgeFinset.mp he)
      have hd : WeightedCounting.DoubleCommon R B a b :=
        ((SimpleGraph.mem_edgeSet D).mp (SimpleGraph.mem_edgeFinset.mp hD)).2
      exact forced_cover_ge_one hzB hab (WeightedCounting.doubleCommon_swap.mp hd)
  have hcountR := graph_support_forced_bound G wR zR hwR hzR heqR
    (fun e ↦ e ∈ D.edgeFinset) hforcedR
  have hcountB := graph_support_forced_bound Gᶜ wB zB hwB hzB heqB
    (fun e ↦ e ∈ D.edgeFinset) hforcedB
  rw [positive_edge_count hzR₀] at hcountR
  rw [positive_edge_count hzB₀] at hcountB
  have hpart : ((G.edgeFinset.filter (fun e ↦ e ∈ D.edgeFinset)).card : ℝ) +
      (Gᶜ.edgeFinset.filter (fun e ↦ e ∈ D.edgeFinset)).card = D.edgeFinset.card :=
    by
      have h := edge_partition_card G D
      simp only [edgeFinset_eq_canonical] at h ⊢
      exact_mod_cast h
  have htotal := total_edge_card G
  have hzero := WeightedCounting.edge_count_bound R B
    (zeroGraph_noTriangle hzR) (zeroGraph_noTriangle hzB)
  refine ⟨wR, wB, hwR, hwB, ?_⟩
  change (R.edgeFinset.card : ℝ) + B.edgeFinset.card - 2 * D.edgeFinset.card ≤ _ at hzero
  change (G.edgeFinset.card : ℝ) - R.edgeFinset.card + _ ≤ _ at hcountR
  change (Gᶜ.edgeFinset.card : ℝ) - B.edgeFinset.card + _ ≤ _ at hcountB
  simp only [edgeFinset_eq_canonical] at hcountR hcountB hzero hpart htotal
  nlinarith

/-- The explicit linear error implies the uniform asymptotic fractional
statement consumed by Haxell–Rödl transference. -/
theorem asymptotic_fractional : AsymptoticFractional := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / (2 * δ))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro G
  obtain ⟨wR, wB, hwR, hwB, hsize⟩ := explicit_fractional_bound G
  simp only [Fintype.card_fin] at hsize
  have hlarge : 3 / (2 * δ) < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hmul : (3 : ℝ) < (n : ℝ) * (2 * δ) :=
    (div_lt_iff₀ (by positivity : 0 < 2 * δ)).mp hlarge
  have herror := mul_le_mul_of_nonneg_right hmul.le (Nat.cast_nonneg n)
  refine ⟨wR, wB, hwR, hwB, ?_⟩
  simp only [fractionalCoveredSize]
  nlinarith

end Erdos76.NewProof
