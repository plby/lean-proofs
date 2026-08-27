/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SparseReserveResidualLinkBounds
import ErdosProblems.Erdos207.ReserveEdgeSampling
import ErdosProblems.Erdos207.IterationLinkTypicality

/-!
# Concentration of available links inside the crossing reserve

For a fixed outside center, sampling crossing edges independently samples
the spoke corresponding to each inside link neighbor independently.  The
finite edge-set representation below transfers the binomial estimates from
`ReserveEdgeSampling` to available-link degree and codegree counts.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Reserve coordinates corresponding to available link neighbors of `x`.
-/
def ambientLinkSpokeEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V) (x : V) :
    Finset (Sym2 V) :=
  (ambientLinkNeighborsIn center A U x).image fun y ↦ s(center, y)

/-- Reserve coordinates corresponding to common available link neighbors
of `x` and `y`. -/
def ambientLinkCommonSpokeEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V) (x y : V) :
    Finset (Sym2 V) :=
  (ambientLinkCommonNeighborsIn center A U x y).image fun z ↦ s(center, z)

lemma ambientLinkSpokeEdges_subset_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {U : Finset V}
    {center x : V} (htri : ConsistsOfTriangles G A) (hc : center ∉ U) :
    ambientLinkSpokeEdges center A U x ⊆ crossingEdges G U := by
  intro e he
  obtain ⟨y, hy, rfl⟩ := mem_image.mp he
  have hydata := mem_ambientLinkNeighborsIn_iff.mp hy
  rw [mem_crossingEdges_iff]
  refine ⟨?_, isCrossingEdge_mk_iff.mpr (Or.inr ⟨hydata.1, hc⟩)⟩
  change G.Adj center y
  exact (ambientLinkRelation_graph_adjacencies htri hydata.2).2.1

lemma ambientLinkCommonSpokeEdges_subset_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V} {U : Finset V}
    {center x y : V} (htri : ConsistsOfTriangles G A) (hc : center ∉ U) :
    ambientLinkCommonSpokeEdges center A U x y ⊆ crossingEdges G U := by
  intro e he
  obtain ⟨z, hz, rfl⟩ := mem_image.mp he
  have hzdata := mem_ambientLinkCommonNeighborsIn_iff.mp hz
  rw [mem_crossingEdges_iff]
  refine ⟨?_, isCrossingEdge_mk_iff.mpr (Or.inr ⟨hzdata.1, hc⟩)⟩
  change G.Adj center z
  exact (ambientLinkRelation_graph_adjacencies htri hzdata.2.1).2.1

lemma ambientLinkSpokeEdges_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V) (x : V)
    (hc : center ∉ U) :
    (ambientLinkSpokeEdges center A U x).card =
      (ambientLinkNeighborsIn center A U x).card := by
  rw [ambientLinkSpokeEdges, card_image_iff.mpr]
  intro y hy z hz hyz
  have hyU := (mem_ambientLinkNeighborsIn_iff.mp hy).1
  have hzU := (mem_ambientLinkNeighborsIn_iff.mp hz).1
  exact Sym2.congr_right.mp hyz

lemma ambientLinkCommonSpokeEdges_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V) (x y : V)
    (hc : center ∉ U) :
    (ambientLinkCommonSpokeEdges center A U x y).card =
      (ambientLinkCommonNeighborsIn center A U x y).card := by
  rw [ambientLinkCommonSpokeEdges, card_image_iff.mpr]
  intro z hz w hw hzw
  have hzU := (mem_ambientLinkCommonNeighborsIn_iff.mp hz).1
  have hwU := (mem_ambientLinkCommonNeighborsIn_iff.mp hw).1
  exact Sym2.congr_right.mp hzw

/-- Filtering available neighbors by sampled spokes is exactly intersection
of their spoke-coordinate set with the sampled reserve. -/
lemma image_sampledAmbientLinkNeighbors_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V)
    (sampled : Finset (Sym2 V)) (x : V) :
    (ambientLinkNeighborsIn center A (spokeVerticesIn U sampled center) x).image
        (fun y ↦ s(center, y)) =
      ambientLinkSpokeEdges center A U x ∩ sampled := by
  ext e
  simp only [mem_image, mem_inter, ambientLinkSpokeEdges]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hydata := mem_ambientLinkNeighborsIn_iff.mp hy
    have hyspoke := mem_spokeVerticesIn_iff.mp hydata.1
    exact ⟨⟨y, mem_ambientLinkNeighborsIn_iff.mpr
      ⟨hyspoke.1, hydata.2⟩, rfl⟩, hyspoke.2⟩
  · rintro ⟨⟨y, hy, rfl⟩, hsampled⟩
    have hydata := mem_ambientLinkNeighborsIn_iff.mp hy
    exact ⟨y, mem_ambientLinkNeighborsIn_iff.mpr
      ⟨mem_spokeVerticesIn_iff.mpr ⟨hydata.1, hsampled⟩,
        hydata.2⟩, rfl⟩

lemma image_sampledAmbientLinkCommonNeighbors_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V)
    (sampled : Finset (Sym2 V)) (x y : V) :
    (ambientLinkCommonNeighborsIn center A
        (spokeVerticesIn U sampled center) x y).image
          (fun z ↦ s(center, z)) =
      ambientLinkCommonSpokeEdges center A U x y ∩ sampled := by
  ext e
  simp only [mem_image, mem_inter, ambientLinkCommonSpokeEdges]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzdata := mem_ambientLinkCommonNeighborsIn_iff.mp hz
    have hzspoke := mem_spokeVerticesIn_iff.mp hzdata.1
    exact ⟨⟨z, mem_ambientLinkCommonNeighborsIn_iff.mpr
      ⟨hzspoke.1, hzdata.2.1, hzdata.2.2⟩, rfl⟩, hzspoke.2⟩
  · rintro ⟨⟨z, hz, rfl⟩, hsampled⟩
    have hzdata := mem_ambientLinkCommonNeighborsIn_iff.mp hz
    exact ⟨z, mem_ambientLinkCommonNeighborsIn_iff.mpr
      ⟨mem_spokeVerticesIn_iff.mpr ⟨hzdata.1, hsampled⟩,
        hzdata.2.1, hzdata.2.2⟩, rfl⟩

lemma sampledAmbientLinkNeighbors_card_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V)
    (sampled : Finset (Sym2 V)) (x : V) (hc : center ∉ U) :
    (ambientLinkNeighborsIn center A
        (spokeVerticesIn U sampled center) x).card =
      (ambientLinkSpokeEdges center A U x ∩ sampled).card := by
  rw [← image_sampledAmbientLinkNeighbors_eq_inter]
  rw [card_image_iff.mpr]
  intro y hy z hz hyz
  exact Sym2.congr_right.mp hyz

lemma sampledAmbientLinkCommonNeighbors_card_eq_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (center : V) (A : TripleSystemOn V) (U : Finset V)
    (sampled : Finset (Sym2 V)) (x y : V) (hc : center ∉ U) :
    (ambientLinkCommonNeighborsIn center A
        (spokeVerticesIn U sampled center) x y).card =
      (ambientLinkCommonSpokeEdges center A U x y ∩ sampled).card := by
  rw [← image_sampledAmbientLinkCommonNeighbors_eq_inter]
  rw [card_image_iff.mpr]
  intro z hz w hw hzw
  exact Sym2.congr_right.mp hzw

/-- Binomial lower-tail bound for one sampled available-link degree. -/
theorem reserveEdgeLaw_probability_sampledLinkDegree_lt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V)
    (htri : ConsistsOfTriangles G A) (center x : V) (hc : center ∉ U)
    (r : ℝ≥0) (hr : r ≤ 1) (m : ℕ) :
    (reserveEdgeLaw G U r hr).probability (fun bits ↦
        (ambientLinkNeighborsIn center A
          (spokeVerticesIn U (reserveEdges G U bits) center) x).card < m) ≤
      (Nat.choose (ambientLinkSpokeEdges center A U x).card
          ((ambientLinkSpokeEdges center A U x).card - (m - 1)) : ℝ≥0) *
        (1 - r) ^
          ((ambientLinkSpokeEdges center A U x).card - (m - 1)) := by
  let L := reserveEdgeLaw G U r hr
  let S := ambientLinkSpokeEdges center A U x
  have hmono : L.probability (fun bits ↦
        (ambientLinkNeighborsIn center A
          (spokeVerticesIn U (reserveEdges G U bits) center) x).card < m) ≤
      L.probability (fun bits ↦
        (S ∩ reserveEdges G U bits).card ≤ m - 1) := by
    apply L.probability_mono
    intro bits hbad
    rw [sampledAmbientLinkNeighbors_card_eq_inter
      center A U (reserveEdges G U bits) x hc] at hbad
    have hbad' : (S ∩ reserveEdges G U bits).card < m := by
      simpa only [S] using hbad
    omega
  exact hmono.trans (by
    simpa only [L, S] using
      reserveEdgeLaw_probability_card_inter_le_le G U r hr S
        (ambientLinkSpokeEdges_subset_crossingEdges htri hc) (m - 1))

/-- Binomial upper-tail bound for one sampled available-link degree. -/
theorem reserveEdgeLaw_probability_sampledLinkDegree_gt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V)
    (htri : ConsistsOfTriangles G A) (center x : V) (hc : center ∉ U)
    (r : ℝ≥0) (hr : r ≤ 1) (D : ℕ) :
    (reserveEdgeLaw G U r hr).probability (fun bits ↦
        D < (ambientLinkNeighborsIn center A
          (spokeVerticesIn U (reserveEdges G U bits) center) x).card) ≤
      (Nat.choose (ambientLinkSpokeEdges center A U x).card (D + 1) : ℝ≥0) *
        r ^ (D + 1) := by
  let S := ambientLinkSpokeEdges center A U x
  have hraw := reserveEdgeLaw_probability_card_inter_ge_le
    G U r hr S (ambientLinkSpokeEdges_subset_crossingEdges htri hc) (D + 1)
  have hevent : (fun bits ↦
      D < (ambientLinkNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x).card) =
      (fun bits ↦ D + 1 ≤ (S ∩ reserveEdges G U bits).card) := by
    funext bits
    apply propext
    rw [sampledAmbientLinkNeighbors_card_eq_inter
      center A U (reserveEdges G U bits) x hc]
    simp only [S]
    omega
  rw [hevent]
  simpa only [S] using hraw

/-- Binomial upper-tail bound for one sampled available-link codegree. -/
theorem reserveEdgeLaw_probability_sampledLinkCodegree_gt_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V)
    (htri : ConsistsOfTriangles G A) (center x y : V) (hc : center ∉ U)
    (r : ℝ≥0) (hr : r ≤ 1) (C : ℕ) :
    (reserveEdgeLaw G U r hr).probability (fun bits ↦
        C < (ambientLinkCommonNeighborsIn center A
          (spokeVerticesIn U (reserveEdges G U bits) center) x y).card) ≤
      (Nat.choose (ambientLinkCommonSpokeEdges center A U x y).card
          (C + 1) : ℝ≥0) * r ^ (C + 1) := by
  let S := ambientLinkCommonSpokeEdges center A U x y
  have hraw := reserveEdgeLaw_probability_card_inter_ge_le
    G U r hr S (ambientLinkCommonSpokeEdges_subset_crossingEdges htri hc)
      (C + 1)
  have hevent : (fun bits ↦
      C < (ambientLinkCommonNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x y).card) =
      (fun bits ↦ C + 1 ≤ (S ∩ reserveEdges G U bits).card) := by
    funext bits
    apply propext
    rw [sampledAmbientLinkCommonNeighbors_card_eq_inter
      center A U (reserveEdges G U bits) x y hc]
    simp only [S]
    omega
  rw [hevent]
  simpa only [S] using hraw

def reserveSampledLinkLowerTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (U : Finset V) (center x : V)
    (r : ℝ≥0) (m : ℕ) : ℝ≥0 :=
  (Nat.choose (ambientLinkSpokeEdges center A U x).card
      ((ambientLinkSpokeEdges center A U x).card - (m - 1)) : ℝ≥0) *
    (1 - r) ^ ((ambientLinkSpokeEdges center A U x).card - (m - 1))

def reserveSampledLinkUpperTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (U : Finset V) (center x : V)
    (r : ℝ≥0) (D : ℕ) : ℝ≥0 :=
  (Nat.choose (ambientLinkSpokeEdges center A U x).card (D + 1) : ℝ≥0) *
    r ^ (D + 1)

def reserveSampledLinkCodegreeTail
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (U : Finset V) (center x y : V)
    (r : ℝ≥0) (C : ℕ) : ℝ≥0 :=
  (Nat.choose (ambientLinkCommonSpokeEdges center A U x y).card
      (C + 1) : ℝ≥0) * r ^ (C + 1)

/-- Explicit finite union bound for all sampled-link degree and codegree
requirements at all outside centers. -/
def reserveSampledLinkFailureTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (U : Finset V) (r : ℝ≥0)
    (m D C : ℕ) : ℝ≥0 :=
  ∑ center ∈ (univ.filter fun c : V ↦ c ∉ U),
    ((∑ x ∈ U, reserveSampledLinkLowerTail A U center x r m) +
      (∑ x ∈ U, reserveSampledLinkUpperTail A U center x r D) +
      ∑ x ∈ U, ∑ y ∈ U,
        reserveSampledLinkCodegreeTail A U center x y r C)

/-- Simultaneous reserve-link estimates used by a sparse-reserve master
stage. -/
def ReserveSampledLinkBoundsGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V)
    (m D C : ℕ) (bits : Sym2 V → Bool) : Prop :=
  ∀ center, center ∉ U →
    (∀ x ∈ U, G.Adj center x →
      m ≤ (ambientLinkNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x).card ∧
      (ambientLinkNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x).card ≤ D) ∧
    ∀ x ∈ U, G.Adj center x → ∀ y ∈ U, G.Adj center y → x ≠ y →
      (ambientLinkCommonNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x y).card ≤ C

/-- At reserve density one, iteration typicality gives all graph-relevant
sampled-link bounds deterministically.  The adjacency hypotheses in
`ReserveSampledLinkBoundsGood` are essential here: links that do not
correspond to residual graph edges need not have positive degree. -/
theorem IsIterationTypical.reserveSampledLinkBoundsGood_of_fullReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 3 ≤ h) (bits : Sym2 V → Bool)
    (hfull : reserveEdges G (W.U i.succ) bits =
      crossingEdges G (W.U i.succ))
    (m D C : ℕ)
    (hlower : (m + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (D : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (C : ℝ≥0)) :
    ReserveSampledLinkBoundsGood G A (W.U i.succ) m D C bits := by
  intro center hc
  constructor
  · intro x hx hcxG
    have houter := hGsupp hcxG
    have hbounds := htyp.ambientLinkDegree_bounds i hstage hcxG.ne
      houter.1 houter.2 hc hcxG (by omega) m D hlower hupper
    have hsubset : ambientLinkSpokeEdges center A (W.U i.succ) x ⊆
        reserveEdges G (W.U i.succ) bits := by
      rw [hfull]
      exact ambientLinkSpokeEdges_subset_crossingEdges htri hc
    have hcard :
        (ambientLinkNeighborsIn center A
          (spokeVerticesIn (W.U i.succ)
            (reserveEdges G (W.U i.succ) bits) center) x).card =
          (ambientLinkNeighborsIn center A (W.U i.succ) x).card := by
      rw [sampledAmbientLinkNeighbors_card_eq_inter center A
        (W.U i.succ) (reserveEdges G (W.U i.succ) bits) x hc,
        inter_eq_left.mpr hsubset,
        ambientLinkSpokeEdges_card center A (W.U i.succ) x hc]
    simpa only [hcard] using hbounds
  · intro x hx hcxG y hy hcyG hxy
    have hxouter := hGsupp hcxG
    have hyouter := hGsupp hcyG
    have hbound := htyp.ambientLinkCodegree_upper i hstage hcxG.ne
      hcyG.ne hxy hxouter.1 hxouter.2 hyouter.2 hcxG hcyG hh C hcodegree
    have hsubset : ambientLinkCommonSpokeEdges center A
        (W.U i.succ) x y ⊆ reserveEdges G (W.U i.succ) bits := by
      rw [hfull]
      exact ambientLinkCommonSpokeEdges_subset_crossingEdges htri hc
    have hcard :
        (ambientLinkCommonNeighborsIn center A
          (spokeVerticesIn (W.U i.succ)
            (reserveEdges G (W.U i.succ) bits) center) x y).card =
          (ambientLinkCommonNeighborsIn center A (W.U i.succ) x y).card := by
      rw [sampledAmbientLinkCommonNeighbors_card_eq_inter center A
        (W.U i.succ) (reserveEdges G (W.U i.succ) bits) x y hc,
        inter_eq_left.mpr hsubset,
        ambientLinkCommonSpokeEdges_card center A (W.U i.succ) x y hc]
    simpa only [hcard] using hbound

lemma FiniteLaw.probability_or_or_le
    {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω)
    (P Q R : Ω → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred R] :
    L.probability (fun ω ↦ P ω ∨ Q ω ∨ R ω) ≤
      L.probability P + L.probability Q + L.probability R := by
  calc
    L.probability (fun ω ↦ P ω ∨ Q ω ∨ R ω) ≤
        L.probability P + L.probability (fun ω ↦ Q ω ∨ R ω) :=
      L.probability_or_le P (fun ω ↦ Q ω ∨ R ω)
    _ ≤ L.probability P + (L.probability Q + L.probability R) :=
      add_le_add le_rfl (L.probability_or_le Q R)
    _ = L.probability P + L.probability Q + L.probability R := by
      rw [add_assoc]

/-- The independent crossing reserve satisfies every sampled-link estimate
except with at most the displayed finite union-bound tail. -/
theorem reserveEdgeLaw_probability_not_sampledLinkBoundsGood_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (U : Finset V)
    (htri : ConsistsOfTriangles G A)
    (r : ℝ≥0) (hr : r ≤ 1) (m D C : ℕ) :
    (reserveEdgeLaw G U r hr).probability
        (fun bits ↦ ¬ ReserveSampledLinkBoundsGood G A U m D C bits) ≤
      reserveSampledLinkFailureTail V A U r m D C := by
  classical
  let L := reserveEdgeLaw G U r hr
  let Centers := univ.filter fun c : V ↦ c ∉ U
  let LowerBad : V → V → (Sym2 V → Bool) → Prop :=
    fun center x bits ↦
      G.Adj center x ∧ (ambientLinkNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x).card < m
  let UpperBad : V → V → (Sym2 V → Bool) → Prop :=
    fun center x bits ↦ G.Adj center x ∧ D <
      (ambientLinkNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x).card
  let CodegreeBad : V → V → V → (Sym2 V → Bool) → Prop :=
    fun center x y bits ↦ G.Adj center x ∧ G.Adj center y ∧ x ≠ y ∧ C <
      (ambientLinkCommonNeighborsIn center A
        (spokeVerticesIn U (reserveEdges G U bits) center) x y).card
  let BadAt : V → (Sym2 V → Bool) → Prop := fun center bits ↦
    (∃ x ∈ U, LowerBad center x bits) ∨
      (∃ x ∈ U, UpperBad center x bits) ∨
      (∃ x ∈ U, ∃ y ∈ U, CodegreeBad center x y bits)
  have hevent : (fun bits ↦
      ¬ ReserveSampledLinkBoundsGood G A U m D C bits) =
      (fun bits ↦ ∃ center ∈ Centers, BadAt center bits) := by
    funext bits
    apply propext
    simp only [ReserveSampledLinkBoundsGood, Centers, mem_filter, mem_univ,
      true_and, BadAt, LowerBad, UpperBad, CodegreeBad]
    constructor
    · intro hbad
      by_contra hnone
      apply hbad
      intro center hc
      have hat : ¬ BadAt center bits := by
        intro hb
        exact hnone ⟨center, hc, hb⟩
      simp only [BadAt, not_or, not_exists] at hat
      refine ⟨fun x hx hcx ↦ ⟨?_, ?_⟩,
        fun x hx hcx y hy hcy hxy ↦ ?_⟩
      · exact Nat.le_of_not_gt (fun hlt ↦ hat.1 x ⟨hx, hcx, hlt⟩)
      · exact Nat.le_of_not_gt (fun hlt ↦ hat.2.1 x ⟨hx, hcx, hlt⟩)
      · exact Nat.le_of_not_gt (fun hlt ↦
          hat.2.2 x ⟨hx, ⟨y, hy, hcx, hcy, hxy, hlt⟩⟩)
    · rintro ⟨center, hc, hbad⟩ hgood
      have hg := hgood center hc
      rcases hbad with hlower | hupper | hcodegree
      · obtain ⟨x, hx, hbad⟩ := hlower
        exact (not_lt_of_ge (hg.1 x hx hbad.1).1) hbad.2
      · obtain ⟨x, hx, hbad⟩ := hupper
        exact (not_lt_of_ge (hg.1 x hx hbad.1).2) hbad.2
      · obtain ⟨x, hx, y, hy, hbad⟩ := hcodegree
        exact (not_lt_of_ge
          (hg.2 x hx hbad.1 y hy hbad.2.1 hbad.2.2.1)) hbad.2.2.2
  rw [hevent]
  calc
    L.probability (fun bits ↦ ∃ center ∈ Centers, BadAt center bits) ≤
        ∑ center ∈ Centers, L.probability (BadAt center) :=
      L.probability_exists_le Centers BadAt
    _ ≤ ∑ center ∈ Centers,
        ((∑ x ∈ U, reserveSampledLinkLowerTail A U center x r m) +
          (∑ x ∈ U, reserveSampledLinkUpperTail A U center x r D) +
          ∑ x ∈ U, ∑ y ∈ U,
            reserveSampledLinkCodegreeTail A U center x y r C) := by
      apply sum_le_sum
      intro center hcCenter
      have hc : center ∉ U := (mem_filter.mp hcCenter).2
      calc
        L.probability (BadAt center) ≤
            L.probability (fun bits ↦ ∃ x ∈ U, LowerBad center x bits) +
              L.probability (fun bits ↦ ∃ x ∈ U, UpperBad center x bits) +
              L.probability (fun bits ↦
                ∃ x ∈ U, ∃ y ∈ U, CodegreeBad center x y bits) := by
          simpa only [BadAt] using L.probability_or_or_le
            (fun bits ↦ ∃ x ∈ U, LowerBad center x bits)
            (fun bits ↦ ∃ x ∈ U, UpperBad center x bits)
            (fun bits ↦ ∃ x ∈ U, ∃ y ∈ U,
              CodegreeBad center x y bits)
        _ ≤ (∑ x ∈ U, reserveSampledLinkLowerTail A U center x r m) +
              (∑ x ∈ U, reserveSampledLinkUpperTail A U center x r D) +
              ∑ x ∈ U, ∑ y ∈ U,
                reserveSampledLinkCodegreeTail A U center x y r C := by
          apply add_le_add
          · apply add_le_add
            · refine (L.probability_exists_le U
                (fun x bits ↦ LowerBad center x bits)).trans ?_
              apply sum_le_sum
              intro x _hx
              calc
                L.probability (LowerBad center x) ≤
                    L.probability (fun bits ↦
                      (ambientLinkNeighborsIn center A
                        (spokeVerticesIn U (reserveEdges G U bits) center)
                        x).card < m) := by
                  apply L.probability_mono
                  exact fun _ h ↦ h.2
                _ ≤ reserveSampledLinkLowerTail A U center x r m := by
                  simpa only [L, reserveSampledLinkLowerTail] using
                    reserveEdgeLaw_probability_sampledLinkDegree_lt_le
                      G A U htri center x hc r hr m
            · refine (L.probability_exists_le U
                (fun x bits ↦ UpperBad center x bits)).trans ?_
              apply sum_le_sum
              intro x _hx
              calc
                L.probability (UpperBad center x) ≤
                    L.probability (fun bits ↦ D <
                      (ambientLinkNeighborsIn center A
                        (spokeVerticesIn U (reserveEdges G U bits) center)
                        x).card) := by
                  apply L.probability_mono
                  exact fun _ h ↦ h.2
                _ ≤ reserveSampledLinkUpperTail A U center x r D := by
                  simpa only [L, reserveSampledLinkUpperTail] using
                    reserveEdgeLaw_probability_sampledLinkDegree_gt_le
                      G A U htri center x hc r hr D
          · refine (L.probability_exists_le U
                (fun x bits ↦ ∃ y ∈ U,
                  CodegreeBad center x y bits)).trans ?_
            apply sum_le_sum
            intro x _hx
            refine (L.probability_exists_le U
                (fun y bits ↦ CodegreeBad center x y bits)).trans ?_
            apply sum_le_sum
            intro y _hy
            calc
              L.probability (CodegreeBad center x y) ≤
                  L.probability (fun bits ↦ C <
                    (ambientLinkCommonNeighborsIn center A
                      (spokeVerticesIn U (reserveEdges G U bits) center)
                      x y).card) := by
                apply L.probability_mono
                exact fun _ h ↦ h.2.2.2
              _ ≤ reserveSampledLinkCodegreeTail A U center x y r C := by
                simpa only [L, reserveSampledLinkCodegreeTail] using
                  reserveEdgeLaw_probability_sampledLinkCodegree_gt_le
                    G A U htri center x y hc r hr C
    _ = reserveSampledLinkFailureTail V A U r m D C := by
      rfl

end

end Erdos207
