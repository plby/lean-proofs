/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib
import PrimeNumberTheoremAnd.Consequences
import Submission.SzemerediTrotter

/-!
# Erdős Problem 808

Erdős Problem 808 asked for a very strong graph-restricted sum--product
estimate.  Alon, Ruzsa, and Solymosi disproved it.  This file formalizes the
literal negation of the conjecture by an explicit prime-block construction.
It also formalizes their complementary Szemerédi--Trotter lower bound for
arbitrary finite sets of distinct real labels.

The graph is represented on a finite vertex type together with an embedding
of that type in the ambient number system.  This is equivalent to putting a
simple graph on the finite image of the embedding, but avoids repeatedly
transporting a graph across a subtype equivalence.
-/

open Classical Filter
open scoped BigOperators Real

noncomputable section

namespace Erdos808

/-- The values of a symmetric operation along the unordered edges of `G`. -/
def edgeValues {V R : Type*} [Fintype V] [DecidableEq R]
    (op : V → V → R) (hop : ∀ u v, op u v = op v u)
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  G.edgeFinset.image (Sym2.lift ⟨op, hop⟩)

/-- Restricted sums along the edges of a finite graph. -/
def edgeSums {V R : Type*} [Fintype V] [DecidableEq R] [AddCommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  edgeValues (fun u v ↦ a u + a v) (fun u v ↦ add_comm (a u) (a v)) G

/-- Restricted products along the edges of a finite graph. -/
def edgeProducts {V R : Type*} [Fintype V] [DecidableEq R] [CommMagma R]
    (a : V → R) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset R :=
  edgeValues (fun u v ↦ a u * a v) (fun u v ↦ mul_comm (a u) (a v)) G

lemma mem_edgeValues_iff {V R : Type*} [Fintype V] [DecidableEq R]
    (op : V → V → R) (hop : ∀ u v, op u v = op v u)
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : R) :
    r ∈ edgeValues op hop G ↔
      ∃ u v, G.Adj u v ∧ r = op u v := by
  constructor
  · intro hr
    obtain ⟨e, he, her⟩ := Finset.mem_image.mp hr
    induction e using Sym2.inductionOn with
    | _ u v =>
        refine ⟨u, v, ?_, ?_⟩
        · simpa using he
        · simpa [Sym2.lift_mk] using her.symm
  · rintro ⟨u, v, huv, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨s(u, v), ?_, by simp [Sym2.lift_mk]⟩
    simpa

/-- The literal strong conjecture in Problem 808.  Exponentiation is real
exponentiation (`Real.rpow`), as required because `c` and `ε` are real. -/
def StrongErdos808 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] (a : V ↪ ℕ)
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
      (Fintype.card V : ℝ) ^ (1 + c) ≤ (G.edgeFinset.card : ℝ) →
      (Fintype.card V : ℝ) ^ (1 + c - ε) ≤
        max ((edgeSums a G).card : ℝ) ((edgeProducts a G).card : ℝ)

/-! ## The complementary Alon--Ruzsa--Solymosi lower bound -/

abbrev ARSPoint := EuclideanSpace ℝ (Fin 2)

abbrev ARSLine :=
  {ell : AffineSubspace ℝ ARSPoint // IsAffineLine ell}

/-- Cartesian coordinates in the Euclidean plane. -/
def arsPoint (x y : ℝ) : ARSPoint := WithLp.toLp 2 ![x, y]

@[simp] lemma arsPoint_apply_zero (x y : ℝ) : arsPoint x y 0 = x := rfl

@[simp] lemma arsPoint_apply_one (x y : ℝ) : arsPoint x y 1 = y := rfl

/-- The affine line `y = c * (x - b)`. -/
noncomputable def arsLineSpace (b c : ℝ) : AffineSubspace ℝ ARSPoint :=
  AffineSubspace.mk' (arsPoint 0 (-b * c))
    (Submodule.span ℝ {arsPoint 1 c})

/-- The line `y = c * (x - b)`, packaged as an affine line. -/
noncomputable def arsLine (b c : ℝ) : ARSLine := by
  refine ⟨arsLineSpace b c, ?_⟩
  constructor
  · refine ⟨arsPoint 0 (-b * c), ?_⟩
    simp [arsLineSpace, AffineSubspace.mem_mk']
  · rw [arsLineSpace, AffineSubspace.direction_mk']
    apply finrank_span_singleton
    intro h
    have h0 := congrArg (fun z : ARSPoint => z 0) h
    simp [arsPoint] at h0

lemma arsPoint_sum_product_mem_line (x b c : ℝ) :
    arsPoint (x + b) (x * c) ∈ arsLineSpace b c := by
  rw [arsLineSpace, AffineSubspace.mem_mk', Submodule.mem_span_singleton]
  refine ⟨x + b, ?_⟩
  ext i
  fin_cases i
  · simp [arsPoint]
  · simp [arsPoint]
    ring

lemma arsLine_injective_of_ne_zero {b c b' c' : ℝ}
    (_hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : arsLine b c = arsLine b' c') : b = b' ∧ c = c' := by
  have hell : arsLineSpace b c = arsLineSpace b' c' :=
    congrArg Subtype.val h
  have hdir : Submodule.span ℝ {arsPoint 1 c} =
      Submodule.span ℝ {arsPoint 1 c'} := by
    have hd := congrArg AffineSubspace.direction hell
    simpa [arsLineSpace] using hd
  have hv : arsPoint 1 c ∈ Submodule.span ℝ {arsPoint 1 c'} := by
    rw [← hdir]
    exact Submodule.subset_span (by simp)
  rw [Submodule.mem_span_singleton] at hv
  obtain ⟨t, ht⟩ := hv
  have ht0 := congrArg (fun z : ARSPoint => z 0) ht
  have ht1 := congrArg (fun z : ARSPoint => z 1) ht
  simp [arsPoint] at ht0 ht1
  have hcc : c = c' := by rw [← ht1, ht0, one_mul]
  have hbmem : arsPoint 0 (-b * c) ∈ arsLineSpace b' c' := by
    rw [← hell]
    simp [arsLineSpace, AffineSubspace.mem_mk']
  rw [arsLineSpace, AffineSubspace.mem_mk',
    Submodule.mem_span_singleton] at hbmem
  obtain ⟨u, hu⟩ := hbmem
  have hu0 := congrArg (fun z : ARSPoint => z 0) hu
  have hu1 := congrArg (fun z : ARSPoint => z 1) hu
  simp [arsPoint] at hu0 hu1
  constructor
  · rw [hcc, hu0, zero_mul] at hu1
    exact mul_right_cancel₀ hc' (by linarith)
  · exact hcc

/-- The Cartesian product of the restricted sum and product sets, embedded
in the Euclidean plane. -/
noncomputable def sumProductPointSet {V : Type*} [Fintype V]
    (a : V → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ARSPoint :=
  ((edgeSums a G).product (edgeProducts a G)).image
    (fun xy => arsPoint xy.1 xy.2)

lemma arsPoint_pair_injective : Function.Injective
    (fun xy : ℝ × ℝ => arsPoint xy.1 xy.2) := by
  intro xy zw h
  apply Prod.ext
  · exact congrArg (fun p : ARSPoint => p 0) h
  · exact congrArg (fun p : ARSPoint => p 1) h

lemma sumProductPointSet_card {V : Type*} [Fintype V]
    (a : V → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (sumProductPointSet a G).card =
      (edgeSums a G).card * (edgeProducts a G).card := by
  rw [sumProductPointSet,
    Finset.card_image_of_injective _ arsPoint_pair_injective]
  exact Finset.card_product _ _

/-- An unordered pair of distinct labels is determined by its sum and
product. -/
lemma sumProductInvariant_injective {V : Type*} (a : V ↪ ℝ) :
    Function.Injective (fun e : Sym2 V =>
      (Sym2.lift ⟨fun u v => a u + a v, fun _ _ => add_comm _ _⟩ e,
       Sym2.lift ⟨fun u v => a u * a v, fun _ _ => mul_comm _ _⟩ e)) := by
  intro e f h
  induction e using Sym2.inductionOn with
  | _ u v =>
      induction f using Sym2.inductionOn with
      | _ x y =>
          simp only [Sym2.lift_mk] at h
          have hsum := congrArg Prod.fst h
          have hprod := congrArg Prod.snd h
          change a u + a v = a x + a y at hsum
          change a u * a v = a x * a y at hprod
          have hz : (a u - a x) * (a u - a y) = 0 := by
            calc
              (a u - a x) * (a u - a y) =
                  (a u) ^ 2 - a u * (a x + a y) + a x * a y := by ring
              _ = (a u) ^ 2 - a u * (a u + a v) + a u * a v := by
                rw [← hsum, ← hprod]
              _ = 0 := by ring
          rcases mul_eq_zero.mp hz with hux | huy
          · have hux' : u = x := a.injective (sub_eq_zero.mp hux)
            subst x
            have hvy : a v = a y := by linarith [hsum]
            have hvy' : v = y := a.injective hvy
            subst y
            rfl
          · have huy' : u = y := a.injective (sub_eq_zero.mp huy)
            subst y
            have hvx : a v = a x := by linarith [hsum]
            have hvx' : v = x := a.injective hvx
            subst x
            exact Sym2.eq_swap

noncomputable def edgeSumProductInvariant {V : Type*}
    (a : V → ℝ) (e : Sym2 V) : ℝ × ℝ :=
  (Sym2.lift ⟨fun u v => a u + a v, fun _ _ => add_comm _ _⟩ e,
   Sym2.lift ⟨fun u v => a u * a v, fun _ _ => mul_comm _ _⟩ e)

lemma edge_card_le_sum_mul_product_card {V : Type*} [Fintype V]
    (a : V ↪ ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ (edgeSums a G).card * (edgeProducts a G).card := by
  let E : Finset (ℝ × ℝ) := G.edgeFinset.image (edgeSumProductInvariant a)
  have hEcard : E.card = G.edgeFinset.card := by
    change (G.edgeFinset.image (edgeSumProductInvariant a)).card = _
    rw [Finset.card_image_of_injective]
    exact sumProductInvariant_injective a
  have hsub : E ⊆ (edgeSums a G).product (edgeProducts a G) := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨e, he, rfl⟩
    · apply Finset.mem_image.mpr
      exact ⟨e, he, rfl⟩
  rw [← Finset.card_product]
  rw [← hEcard]
  exact Finset.card_le_card hsub

/-- The `n²` lines indexed by ordered pairs of labels. -/
noncomputable def arsLineSet {V : Type*} [Fintype V]
    (a : V → ℝ) : Finset ARSLine :=
  ((Finset.univ : Finset V).product Finset.univ).image
    (fun bc => arsLine (a bc.1) (a bc.2))

lemma arsLine_pair_injective {V : Type*} [Fintype V]
    (a : V ↪ ℝ) (ha0 : ∀ v, a v ≠ 0) : Function.Injective
      (fun bc : V × V => arsLine (a bc.1) (a bc.2)) := by
  intro bc de h
  obtain ⟨hb, hc⟩ := arsLine_injective_of_ne_zero
    (ha0 bc.2) (ha0 de.2) h
  exact Prod.ext (a.injective hb) (a.injective hc)

lemma arsLineSet_card {V : Type*} [Fintype V]
    (a : V ↪ ℝ) (ha0 : ∀ v, a v ≠ 0) :
    (arsLineSet a).card = (Fintype.card V) ^ 2 := by
  rw [arsLineSet, Finset.card_image_of_injective _
    (arsLine_pair_injective a ha0)]
  simp [pow_two]

/-- Ordered length-two walks, with the two endpoints allowed to agree. -/
abbrev NeighborTriple {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  Σ x : V, ↥(G.neighborFinset x) × ↥(G.neighborFinset x)

lemma NeighborTriple_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (NeighborTriple G) = ∑ x, (G.degree x) ^ 2 := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Fintype.card_prod]
  simp only [Fintype.card_coe]
  rw [SimpleGraph.card_neighborFinset_eq_degree]
  simp [pow_two]

def triplePoint {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (a : V → ℝ)
    (t : NeighborTriple G) : ARSPoint :=
  arsPoint (a t.1 + a t.2.1.1) (a t.1 * a t.2.2.1)

noncomputable def tripleLine {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (a : V → ℝ)
    (t : NeighborTriple G) : ARSLine :=
  arsLine (a t.2.1.1) (a t.2.2.1)

lemma triplePoint_mem {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (a : V → ℝ)
    (t : NeighborTriple G) : triplePoint a t ∈ sumProductPointSet a G := by
  apply Finset.mem_image.mpr
  refine ⟨(a t.1 + a t.2.1.1, a t.1 * a t.2.2.1), ?_, rfl⟩
  apply Finset.mem_product.mpr
  constructor
  · change a t.1 + a t.2.1.1 ∈ edgeSums a G
    rw [edgeSums, mem_edgeValues_iff]
    refine ⟨t.1, t.2.1.1, ?_, rfl⟩
    exact (G.mem_neighborFinset _ _).mp t.2.1.2
  · change a t.1 * a t.2.2.1 ∈ edgeProducts a G
    rw [edgeProducts, mem_edgeValues_iff]
    refine ⟨t.1, t.2.2.1, ?_, rfl⟩
    exact (G.mem_neighborFinset _ _).mp t.2.2.2

lemma tripleLine_mem {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (a : V → ℝ)
    (t : NeighborTriple G) : tripleLine a t ∈ arsLineSet a := by
  apply Finset.mem_image.mpr
  exact ⟨(t.2.1.1, t.2.2.1), by simp, rfl⟩

lemma triplePoint_incident {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (a : V → ℝ)
    (t : NeighborTriple G) :
    triplePoint a t ∈ (tripleLine a t : AffineSubspace ℝ ARSPoint) := by
  exact arsPoint_sum_product_mem_line _ _ _

/-- The finite type counted by `LineIncidences`. -/
abbrev IncidenceType (P : Finset ARSPoint) (L : Finset ARSLine) :=
  ↥((P.product L).filter
    (fun pl => pl.1 ∈ (pl.2 : AffineSubspace ℝ ARSPoint)))

lemma IncidenceType_card (P : Finset ARSPoint) (L : Finset ARSLine) :
    Fintype.card (IncidenceType P L) = LineIncidences P L := by
  simp [IncidenceType, LineIncidences]

noncomputable def neighborTripleIncidence {V : Type*} [Fintype V]
    (a : V → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    NeighborTriple G → IncidenceType (sumProductPointSet a G) (arsLineSet a) :=
  fun t => ⟨(triplePoint a t, tripleLine a t),
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨triplePoint_mem a t, tripleLine_mem a t⟩,
      triplePoint_incident a t⟩⟩

def tripleVertices {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (t : NeighborTriple G) :
    V × V × V := (t.1, t.2.1.1, t.2.2.1)

lemma tripleVertices_injective {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    Function.Injective (@tripleVertices V _ G _) := by
  rintro ⟨x, b, c⟩ ⟨x', b', c'⟩ h
  simp only [tripleVertices, Prod.mk.injEq] at h
  obtain ⟨hx, hb, hc⟩ := h
  subst x'
  have hbb : b = b' := Subtype.ext hb
  have hcc : c = c' := Subtype.ext hc
  subst b'
  subst c'
  rfl

lemma neighborTripleIncidence_injective {V : Type*} [Fintype V]
    (a : V ↪ ℝ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ha0 : ∀ v, a v ≠ 0) :
    Function.Injective (neighborTripleIncidence a G) := by
  intro t u h
  have hpoint : triplePoint a t = triplePoint a u :=
    congrArg (fun z => z.1.1) h
  have hline : tripleLine a t = tripleLine a u :=
    congrArg (fun z => z.1.2) h
  obtain ⟨hbLabel, hcLabel⟩ := arsLine_injective_of_ne_zero
    (ha0 t.2.2.1) (ha0 u.2.2.1) hline
  have hb : t.2.1.1 = u.2.1.1 := a.injective hbLabel
  have hc : t.2.2.1 = u.2.2.1 := a.injective hcLabel
  have hfirst := congrArg (fun p : ARSPoint => p 0) hpoint
  simp only [triplePoint, arsPoint_apply_zero] at hfirst
  have hxLabel : a t.1 = a u.1 := by rw [hb] at hfirst; linarith
  have hx : t.1 = u.1 := a.injective hxLabel
  apply tripleVertices_injective
  exact Prod.ext hx (Prod.ext hb hc)

lemma neighborTriple_card_le_incidences {V : Type*} [Fintype V]
    (a : V ↪ ℝ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ha0 : ∀ v, a v ≠ 0) :
    Fintype.card (NeighborTriple G) ≤
      LineIncidences (sumProductPointSet a G) (arsLineSet a) := by
  rw [← IncidenceType_card]
  exact Fintype.card_le_of_injective _
    (neighborTripleIncidence_injective a G ha0)


lemma four_edges_sq_le_card_mul_incidences {V : Type*} [Fintype V]
    (a : V ↪ ℝ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ha0 : ∀ v, a v ≠ 0) :
    4 * G.edgeFinset.card ^ 2 ≤ Fintype.card V *
      LineIncidences (sumProductPointSet a G) (arsLineSet a) := by
  have hcs : (∑ x, G.degree x) ^ 2 ≤
      Fintype.card V * ∑ x, (G.degree x) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset V)) (f := fun x => G.degree x))
  have hwalk : ∑ x, (G.degree x) ^ 2 =
      Fintype.card (NeighborTriple G) := (NeighborTriple_card G).symm
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hwalk] at hcs
  calc
    4 * G.edgeFinset.card ^ 2 = (2 * G.edgeFinset.card) ^ 2 := by ring
    _ ≤ Fintype.card V * Fintype.card (NeighborTriple G) := hcs
    _ ≤ Fintype.card V *
        LineIncidences (sumProductPointSet a G) (arsLineSet a) :=
      Nat.mul_le_mul_left _ (neighborTriple_card_le_incidences a G ha0)

/-- The raw inequality obtained by applying Szemerédi--Trotter to the point
and line sets above. -/
lemma ars_raw_bound_nonzero (C : ℝ) (_hC : 0 ≤ C)
    (hST : ∀ (P : Finset ARSPoint) (L : Finset ARSLine),
      (LineIncidences P L : ℝ) ≤
        C * ((((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)) +
          (P.card : ℝ) + (L.card : ℝ)))
    {V : Type*} [Fintype V] (a : V ↪ ℝ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ha0 : ∀ v, a v ≠ 0) :
    4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
      (Fintype.card V : ℝ) * C *
        (((((edgeSums a G).card : ℝ) *
              ((edgeProducts a G).card : ℝ) *
              (Fintype.card V : ℝ) ^ 2) ^ ((2 : ℝ) / 3)) +
          ((edgeSums a G).card : ℝ) *
            ((edgeProducts a G).card : ℝ) +
          (Fintype.card V : ℝ) ^ 2) := by
  let P := sumProductPointSet a G
  let L := arsLineSet a
  have hlowerNat := four_edges_sq_le_card_mul_incidences a G ha0
  have hlower : 4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
      (Fintype.card V : ℝ) * (LineIncidences P L : ℝ) := by
    exact_mod_cast hlowerNat
  have hupper := hST P L
  have hn : 0 ≤ (Fintype.card V : ℝ) := by positivity
  calc
    4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
        (Fintype.card V : ℝ) * (LineIncidences P L : ℝ) := hlower
    _ ≤ (Fintype.card V : ℝ) *
        (C * ((((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)) +
          (P.card : ℝ) + (L.card : ℝ))) :=
      mul_le_mul_of_nonneg_left hupper hn
    _ = (Fintype.card V : ℝ) * C *
        (((((edgeSums a G).card : ℝ) *
              ((edgeProducts a G).card : ℝ) *
              (Fintype.card V : ℝ) ^ 2) ^ ((2 : ℝ) / 3)) +
          ((edgeSums a G).card : ℝ) *
            ((edgeProducts a G).card : ℝ) +
          (Fintype.card V : ℝ) ^ 2) := by
      rw [show P.card = (edgeSums a G).card *
          (edgeProducts a G).card by
        exact sumProductPointSet_card a G,
        show L.card = (Fintype.card V) ^ 2 by
          exact arsLineSet_card a ha0]
      push_cast
      ring

lemma ars_max_bound_nonzero (C : ℝ) (hC : 0 ≤ C)
    (hST : ∀ (P : Finset ARSPoint) (L : Finset ARSLine),
      (LineIncidences P L : ℝ) ≤
        C * ((((P.card : ℝ) * (L.card : ℝ)) ^ ((2 : ℝ) / 3)) +
          (P.card : ℝ) + (L.card : ℝ)))
    {V : Type*} [Fintype V] (a : V ↪ ℝ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ha0 : ∀ v, a v ≠ 0) :
    let M := max ((edgeSums a G).card : ℝ)
      ((edgeProducts a G).card : ℝ)
    4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
      (Fintype.card V : ℝ) * C *
        (((M ^ 2 * (Fintype.card V : ℝ) ^ 2) ^ ((2 : ℝ) / 3)) +
          M ^ 2 + (Fintype.card V : ℝ) ^ 2) := by
  dsimp
  let S : ℝ := (edgeSums a G).card
  let Q : ℝ := (edgeProducts a G).card
  let n : ℝ := Fintype.card V
  let M : ℝ := max S Q
  have hraw := ars_raw_bound_nonzero C hC hST a G ha0
  have hS : S ≤ M := le_max_left _ _
  have hQ : Q ≤ M := le_max_right _ _
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hM0 : 0 ≤ M := hS0.trans hS
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hSQ : S * Q ≤ M ^ 2 := by nlinarith
  have hbase : S * Q * n ^ 2 ≤ M ^ 2 * n ^ 2 := by
    exact mul_le_mul_of_nonneg_right hSQ (sq_nonneg n)
  have hmain : (S * Q * n ^ 2) ^ ((2 : ℝ) / 3) ≤
      (M ^ 2 * n ^ 2) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  change 4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
      n * C * ((M ^ 2 * n ^ 2) ^ ((2 : ℝ) / 3) + M ^ 2 + n ^ 2)
  change 4 * (G.edgeFinset.card : ℝ) ^ 2 ≤
      n * C * ((S * Q * n ^ 2) ^ ((2 : ℝ) / 3) + S * Q + n ^ 2) at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (by linarith) (mul_nonneg hn0 hC))

lemma sq_rpow_eq_rpow_two_mul {x z : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ z = x ^ (2 * z) := by
  symm
  simpa using Real.rpow_natCast_mul hx 2 z

lemma sq_rpow_half {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
  rw [sq_rpow_eq_rpow_two_mul hx]
  norm_num

lemma sq_rpow_three_quarters {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ ((3 : ℝ) / 4) = x ^ ((3 : ℝ) / 2) := by
  rw [sq_rpow_eq_rpow_two_mul hx]
  congr 1
  norm_num

lemma sq_rpow_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    (x ^ 2) ^ ((2 : ℝ) / 3) = x ^ ((4 : ℝ) / 3) := by
  rw [sq_rpow_eq_rpow_two_mul hx]
  congr 1
  norm_num

lemma sq_mul_sq_rpow_two_thirds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x ^ 2 * y ^ 2) ^ ((2 : ℝ) / 3) =
      x ^ ((4 : ℝ) / 3) * y ^ ((4 : ℝ) / 3) := by
  rw [Real.mul_rpow (sq_nonneg x) (sq_nonneg y),
    sq_rpow_two_thirds hx, sq_rpow_two_thirds hy]

lemma edge_rpow_half_le_max {V : Type*} [Fintype V]
    (a : V ↪ ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ^ ((1 : ℝ) / 2) ≤
      max ((edgeSums a G).card : ℝ) ((edgeProducts a G).card : ℝ) := by
  let m : ℝ := G.edgeFinset.card
  let S : ℝ := (edgeSums a G).card
  let Q : ℝ := (edgeProducts a G).card
  let M : ℝ := max S Q
  have hmSQNat := edge_card_le_sum_mul_product_card a G
  have hmSQ : m ≤ S * Q := by
    dsimp [m, S, Q]
    exact_mod_cast hmSQNat
  have hS : S ≤ M := le_max_left _ _
  have hQ : Q ≤ M := le_max_right _ _
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hM0 : 0 ≤ M := hS0.trans hS
  have hmM : m ≤ M ^ 2 := by
    calc
      m ≤ S * Q := hmSQ
      _ ≤ M ^ 2 := by nlinarith
  change m ^ ((1 : ℝ) / 2) ≤ M
  calc
    m ^ ((1 : ℝ) / 2) ≤ (M ^ 2) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by dsimp [m]; positivity) hmM (by norm_num)
    _ = M := sq_rpow_half hM0

lemma edge_rpow_half_le_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) ^ ((1 : ℝ) / 2) ≤ Fintype.card V := by
  have hmNat : G.edgeFinset.card ≤ (Fintype.card V) ^ 2 :=
    G.card_edgeFinset_le_card_choose_two.trans
      (Nat.choose_le_pow (Fintype.card V) 2)
  have hm : (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast hmNat
  calc
    (G.edgeFinset.card : ℝ) ^ ((1 : ℝ) / 2) ≤
        ((Fintype.card V : ℝ) ^ 2) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hm (by norm_num)
    _ = Fintype.card V := sq_rpow_half (by positivity)

lemma main_term_rpow_three_quarters {C M n : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hn : 0 ≤ n) :
    (3 * C * M ^ ((4 : ℝ) / 3) * n ^ ((7 : ℝ) / 3)) ^
        ((3 : ℝ) / 4) =
      (3 * C) ^ ((3 : ℝ) / 4) * M * n ^ ((7 : ℝ) / 4) := by
  rw [Real.mul_rpow (mul_nonneg (mul_nonneg (by norm_num) hC)
      (Real.rpow_nonneg hM _)) (Real.rpow_nonneg hn _),
    Real.mul_rpow (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hM _)]
  rw [← Real.rpow_mul hM, ← Real.rpow_mul hn]
  norm_num

lemma second_term_rpow_half {C M n : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hn : 0 ≤ n) :
    (3 * C * n * M ^ 2) ^ ((1 : ℝ) / 2) =
      (3 * C) ^ ((1 : ℝ) / 2) * n ^ ((1 : ℝ) / 2) * M := by
  rw [Real.mul_rpow (mul_nonneg (mul_nonneg (by norm_num) hC) hn)
      (sq_nonneg M),
    Real.mul_rpow (mul_nonneg (by norm_num) hC) hn,
    sq_rpow_half hM]

lemma third_term_rpow_half {C n : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ n) :
    (3 * C * n ^ 3) ^ ((1 : ℝ) / 2) =
      (3 * C) ^ ((1 : ℝ) / 2) * n ^ ((3 : ℝ) / 2) := by
  rw [Real.mul_rpow (mul_nonneg (by positivity) hC) (by positivity)]
  rw [show n ^ (3 : ℕ) = n ^ (3 : ℝ) by
    exact (Real.rpow_natCast n 3).symm]
  rw [← Real.rpow_mul hn]
  norm_num

lemma rpow_three_halves_eq_mul_half {x : ℝ} (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * x ^ ((1 : ℝ) / 2) := by
  calc
    x ^ ((3 : ℝ) / 2) = x ^ ((1 : ℝ) + (1 : ℝ) / 2) := by
      congr 1
      norm_num
    _ = x ^ (1 : ℝ) * x ^ ((1 : ℝ) / 2) := Real.rpow_add hx _ _
    _ = x * x ^ ((1 : ℝ) / 2) := by rw [Real.rpow_one]

lemma rpow_half_mul_self {x : ℝ} (hx : 0 < x) :
    x ^ ((1 : ℝ) / 2) * x = x ^ ((3 : ℝ) / 2) := by
  rw [mul_comm, ← rpow_three_halves_eq_mul_half hx]

/-- The Alon--Ruzsa--Solymosi lower bound for distinct nonzero real labels. -/
theorem erdos808_quantitative_nonzero :
    ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] (a : V ↪ ℝ)
        (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ v, a v ≠ 0) →
        (G.edgeFinset.card : ℝ) ^ ((3 : ℝ) / 2) ≤
          K * (Fintype.card V : ℝ) ^ ((7 : ℝ) / 4) *
            max ((edgeSums a G).card : ℝ)
              ((edgeProducts a G).card : ℝ) := by
  obtain ⟨C, hC, hST⟩ := SzemerediTrotter
  let K : ℝ := 1 + (3 * C) ^ ((3 : ℝ) / 4) +
    (3 * C) ^ ((1 : ℝ) / 2)
  have h3C : 0 ≤ 3 * C := by positivity
  have hmainCoeff : (3 * C) ^ ((3 : ℝ) / 4) ≤ K := by
    dsimp [K]
    have hhalf0 : 0 ≤ (3 * C) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg h3C _
    linarith
  have hhalfCoeff : (3 * C) ^ ((1 : ℝ) / 2) ≤ K := by
    dsimp [K]
    have hmain0 : 0 ≤ (3 * C) ^ ((3 : ℝ) / 4) :=
      Real.rpow_nonneg h3C _
    linarith
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro V _instV a G _instG ha0
  let m : ℝ := G.edgeFinset.card
  let n : ℝ := Fintype.card V
  let M : ℝ := max ((edgeSums a G).card : ℝ)
    ((edgeProducts a G).card : ℝ)
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact (by positivity : (0 : ℝ) ≤ (edgeSums a G).card).trans
      (le_max_left _ _)
  by_cases hmzero : m = 0
  · change m ^ ((3 : ℝ) / 2) ≤ K * n ^ ((7 : ℝ) / 4) * M
    simp [hmzero]
    positivity
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hmzero)
  have hmNat : 0 < G.edgeFinset.card := by
    dsimp [m] at hmpos
    exact_mod_cast hmpos
  have hmNatLe : G.edgeFinset.card ≤ (Fintype.card V) ^ 2 :=
    G.card_edgeFinset_le_card_choose_two.trans
      (Nat.choose_le_pow (Fintype.card V) 2)
  have hnNat : 1 ≤ Fintype.card V := by
    by_contra hn
    have hnzero : Fintype.card V = 0 := by omega
    have hmedgezero : G.edgeFinset.card = 0 := by
      have : G.edgeFinset.card ≤ 0 := by simpa [hnzero] using hmNatLe
      omega
    rw [hmedgezero] at hmNat
    exact (Nat.lt_irrefl 0) hmNat
  have hnOne : 1 ≤ n := by dsimp [n]; exact_mod_cast hnNat
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hnOne
  have hbound0 := ars_max_bound_nonzero C hC.le hST a G ha0
  change 4 * m ^ 2 ≤ n * C *
      ((M ^ 2 * n ^ 2) ^ ((2 : ℝ) / 3) + M ^ 2 + n ^ 2) at hbound0
  rw [sq_mul_sq_rpow_two_thirds hM0 hn0] at hbound0
  let T : ℝ := M ^ ((4 : ℝ) / 3) * n ^ ((4 : ℝ) / 3)
  let A : ℝ := n * C * T
  let B : ℝ := n * C * M ^ 2
  let D : ℝ := n * C * n ^ 2
  have hsum : 4 * m ^ 2 ≤ A + B + D := by
    dsimp [A, B, D, T]
    nlinarith
  by_cases hmain : 4 * m ^ 2 ≤ 3 * A
  · have hnmerge : n * n ^ ((4 : ℝ) / 3) = n ^ ((7 : ℝ) / 3) := by
      calc
        n * n ^ ((4 : ℝ) / 3) =
            n ^ (1 : ℝ) * n ^ ((4 : ℝ) / 3) := by rw [Real.rpow_one]
        _ = n ^ ((1 : ℝ) + (4 : ℝ) / 3) :=
          (Real.rpow_add hnpos _ _).symm
        _ = n ^ ((7 : ℝ) / 3) := by
          congr 1
          norm_num
    have hbase : m ^ 2 ≤
        3 * C * M ^ ((4 : ℝ) / 3) * n ^ ((7 : ℝ) / 3) := by
      calc
        m ^ 2 ≤ 4 * m ^ 2 := by nlinarith [sq_nonneg m]
        _ ≤ 3 * A := hmain

        _ = 3 * C * M ^ ((4 : ℝ) / 3) * n ^ ((7 : ℝ) / 3) := by
          dsimp [A, T]
          calc
            3 * (n * C * (M ^ ((4 : ℝ) / 3) * n ^ ((4 : ℝ) / 3))) =
                3 * C * M ^ ((4 : ℝ) / 3) *
                  (n * n ^ ((4 : ℝ) / 3)) := by ring
            _ = 3 * C * M ^ ((4 : ℝ) / 3) * n ^ ((7 : ℝ) / 3) := by
              rw [hnmerge]
    have hr := Real.rpow_le_rpow (sq_nonneg m) hbase
      (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rw [sq_rpow_three_quarters hm0,
      main_term_rpow_three_quarters hC.le hM0 hn0] at hr
    change m ^ ((3 : ℝ) / 2) ≤ K * n ^ ((7 : ℝ) / 4) * M
    calc
      m ^ ((3 : ℝ) / 2) ≤
          (3 * C) ^ ((3 : ℝ) / 4) * M * n ^ ((7 : ℝ) / 4) := hr
      _ ≤ K * M * n ^ ((7 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmainCoeff hM0)
          (Real.rpow_nonneg hn0 _)
      _ = K * n ^ ((7 : ℝ) / 4) * M := by ring
  by_cases hsecond : 4 * m ^ 2 ≤ 3 * B
  · have hbase : m ^ 2 ≤ 3 * C * n * M ^ 2 := by
      calc
        m ^ 2 ≤ 4 * m ^ 2 := by nlinarith [sq_nonneg m]
        _ ≤ 3 * B := hsecond
        _ = 3 * C * n * M ^ 2 := by dsimp [B]; ring
    have hr := Real.rpow_le_rpow (sq_nonneg m) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [sq_rpow_half hm0, second_term_rpow_half hC.le hM0 hn0] at hr
    have hmhalf : m ^ ((1 : ℝ) / 2) ≤ n := by
      simpa only [m, n] using edge_rpow_half_le_card G
    have hnPow : n ^ ((3 : ℝ) / 2) ≤ n ^ ((7 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
    change m ^ ((3 : ℝ) / 2) ≤ K * n ^ ((7 : ℝ) / 4) * M
    calc
      m ^ ((3 : ℝ) / 2) = m * m ^ ((1 : ℝ) / 2) :=
        rpow_three_halves_eq_mul_half hmpos
      _ ≤ ((3 * C) ^ ((1 : ℝ) / 2) *
          n ^ ((1 : ℝ) / 2) * M) * n :=
        mul_le_mul hr hmhalf (Real.rpow_nonneg hm0 _)
          (by positivity)
      _ = (3 * C) ^ ((1 : ℝ) / 2) * M * n ^ ((3 : ℝ) / 2) := by
        calc
          (3 * C) ^ ((1 : ℝ) / 2) * n ^ ((1 : ℝ) / 2) * M * n =
              (3 * C) ^ ((1 : ℝ) / 2) * M *
                (n ^ ((1 : ℝ) / 2) * n) := by ring
          _ = (3 * C) ^ ((1 : ℝ) / 2) * M * n ^ ((3 : ℝ) / 2) := by
            rw [rpow_half_mul_self hnpos]
      _ ≤ K * M * n ^ ((7 : ℝ) / 4) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right hhalfCoeff hM0) hnPow
          (Real.rpow_nonneg hn0 _) (mul_nonneg hK.le hM0)
      _ = K * n ^ ((7 : ℝ) / 4) * M := by ring
  · have hthird : 4 * m ^ 2 ≤ 3 * D := by
      by_contra hthird
      have hmain' : 3 * A < 4 * m ^ 2 := lt_of_not_ge hmain
      have hsecond' : 3 * B < 4 * m ^ 2 := lt_of_not_ge hsecond
      have hthird' : 3 * D < 4 * m ^ 2 := lt_of_not_ge hthird
      linarith
    have hbase : m ^ 2 ≤ 3 * C * n ^ 3 := by
      calc
        m ^ 2 ≤ 4 * m ^ 2 := by nlinarith [sq_nonneg m]
        _ ≤ 3 * D := hthird
        _ = 3 * C * n ^ 3 := by dsimp [D]; ring
    have hr := Real.rpow_le_rpow (sq_nonneg m) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [sq_rpow_half hm0, third_term_rpow_half hC.le hn0] at hr
    have hmhalf : m ^ ((1 : ℝ) / 2) ≤ M := by
      simpa only [m, M] using edge_rpow_half_le_max a G
    have hnPow : n ^ ((3 : ℝ) / 2) ≤ n ^ ((7 : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
    change m ^ ((3 : ℝ) / 2) ≤ K * n ^ ((7 : ℝ) / 4) * M
    calc
      m ^ ((3 : ℝ) / 2) = m * m ^ ((1 : ℝ) / 2) :=
        rpow_three_halves_eq_mul_half hmpos
      _ ≤ ((3 * C) ^ ((1 : ℝ) / 2) *
          n ^ ((3 : ℝ) / 2)) * M :=
        mul_le_mul hr hmhalf (Real.rpow_nonneg hm0 _) (by positivity)
      _ ≤ (K * n ^ ((7 : ℝ) / 4)) * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hhalfCoeff hnPow
            (Real.rpow_nonneg hn0 _) hK.le) hM0
      _ = K * n ^ ((7 : ℝ) / 4) * M := by ring

lemma edgeSums_induce_subset {V : Type*} [Fintype V]
    (a : V → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) :
    edgeSums (fun x : s => a x) (G.induce s) ⊆ edgeSums a G := by
  intro r hr
  rw [edgeSums, mem_edgeValues_iff] at hr
  obtain ⟨u, v, huv, rfl⟩ := hr
  rw [edgeSums, mem_edgeValues_iff]
  exact ⟨u.1, v.1, huv, rfl⟩

lemma edgeProducts_induce_subset {V : Type*} [Fintype V]
    (a : V → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) :
    edgeProducts (fun x : s => a x) (G.induce s) ⊆ edgeProducts a G := by
  intro r hr
  rw [edgeProducts, mem_edgeValues_iff] at hr
  obtain ⟨u, v, huv, rfl⟩ := hr
  rw [edgeProducts, mem_edgeValues_iff]
  exact ⟨u.1, v.1, huv, rfl⟩

lemma card_induced_max_le {V : Type*} [Fintype V]
    (a : V → ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V) :
    max ((edgeSums (fun x : s => a x) (G.induce s)).card : ℝ)
        ((edgeProducts (fun x : s => a x) (G.induce s)).card : ℝ) ≤
      max ((edgeSums a G).card : ℝ) ((edgeProducts a G).card : ℝ) := by
  apply max_le
  · have hsNat := Finset.card_le_card (edgeSums_induce_subset a G s)
    have hs : ((edgeSums (fun x : s => a x) (G.induce s)).card : ℝ) ≤
        (edgeSums a G).card := by exact_mod_cast hsNat
    exact hs.trans (le_max_left _ _)
  · have hpNat := Finset.card_le_card (edgeProducts_induce_subset a G s)
    have hp : ((edgeProducts (fun x : s => a x) (G.induce s)).card : ℝ) ≤
        (edgeProducts a G).card := by exact_mod_cast hpNat
    exact hp.trans (le_max_right _ _)

/-- **Alon--Ruzsa--Solymosi's quantitative theorem.**  For every finite set
of distinct real labels and every graph on it,
`max(|A +_G A|, |A * _G A|) ≫ m^(3/2) n^(-7/4)`.

The multiplication form avoids division at `n = 0` and is exactly equivalent
to the usual asymptotic statement for nonempty vertex sets. -/
theorem erdos808_quantitative_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (V : Type) [Fintype V] (a : V ↪ ℝ)
        (G : SimpleGraph V) [DecidableRel G.Adj],
        (G.edgeFinset.card : ℝ) ^ ((3 : ℝ) / 2) ≤
          K * (Fintype.card V : ℝ) ^ ((7 : ℝ) / 4) *
            max ((edgeSums a G).card : ℝ)
              ((edgeProducts a G).card : ℝ) := by
  obtain ⟨K, hK, hnonzero⟩ := erdos808_quantitative_nonzero
  let R : ℝ := (2 : ℝ) ^ ((3 : ℝ) / 2)
  let K₀ : ℝ := 2 + R * K
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact Real.one_le_rpow (by norm_num) (by norm_num)
  have hKtwo : (2 : ℝ) ≤ K₀ := by
    dsimp [K₀]
    have : 0 ≤ R * K := mul_nonneg hR0 hK.le
    linarith
  have hKR : R * K ≤ K₀ := by
    dsimp [K₀]
    linarith
  have hKle : K ≤ K₀ := by
    have : K ≤ R * K := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hR1 hK.le
    exact this.trans hKR
  have hK₀ : 0 < K₀ := lt_of_lt_of_le (by norm_num) hKtwo
  refine ⟨K₀, hK₀, ?_⟩
  intro V _instV a G _instG
  let m : ℝ := G.edgeFinset.card
  let n : ℝ := Fintype.card V
  let M : ℝ := max ((edgeSums a G).card : ℝ)
    ((edgeProducts a G).card : ℝ)
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact (by positivity : (0 : ℝ) ≤ (edgeSums a G).card).trans
      (le_max_left _ _)
  by_cases hsparse : m < 2 * n
  · by_cases hmzero : m = 0
    · change m ^ ((3 : ℝ) / 2) ≤ K₀ * n ^ ((7 : ℝ) / 4) * M
      simp [hmzero]
      positivity
    have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hmzero)
    have hmNat : 0 < G.edgeFinset.card := by
      dsimp [m] at hmpos
      exact_mod_cast hmpos
    have hmNatLe : G.edgeFinset.card ≤ (Fintype.card V) ^ 2 :=
      G.card_edgeFinset_le_card_choose_two.trans
        (Nat.choose_le_pow (Fintype.card V) 2)
    have hnNat : 1 ≤ Fintype.card V := by
      by_contra hn
      have hnzero : Fintype.card V = 0 := by omega
      have hmedgezero : G.edgeFinset.card = 0 := by
        have : G.edgeFinset.card ≤ 0 := by simpa [hnzero] using hmNatLe
        omega
      rw [hmedgezero] at hmNat
      exact (Nat.lt_irrefl 0) hmNat
    have hnOne : 1 ≤ n := by dsimp [n]; exact_mod_cast hnNat
    have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hnOne
    have hmhalf : m ^ ((1 : ℝ) / 2) ≤ M := by
      simpa only [m, M] using edge_rpow_half_le_max a G
    have hnPow : n ≤ n ^ ((7 : ℝ) / 4) := by
      calc
        n = n ^ (1 : ℝ) := (Real.rpow_one n).symm
        _ ≤ n ^ ((7 : ℝ) / 4) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
    change m ^ ((3 : ℝ) / 2) ≤ K₀ * n ^ ((7 : ℝ) / 4) * M
    calc
      m ^ ((3 : ℝ) / 2) = m * m ^ ((1 : ℝ) / 2) :=
        rpow_three_halves_eq_mul_half hmpos
      _ ≤ (2 * n) * M :=
        mul_le_mul hsparse.le hmhalf (Real.rpow_nonneg hm0 _) (by positivity)
      _ ≤ (K₀ * n ^ ((7 : ℝ) / 4)) * M := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hKtwo hnPow hn0 hK₀.le) hM0
      _ = K₀ * n ^ ((7 : ℝ) / 4) * M := by ring
  have hdense : 2 * n ≤ m := le_of_not_gt hsparse
  by_cases hz : ∃ z, a z = 0
  · obtain ⟨z, hz⟩ := hz
    let s : Set V := {z}ᶜ
    let W := ↥s
    let a' : W ↪ ℝ :=
      ⟨fun w => a w, fun _ _ h => Subtype.ext (a.injective h)⟩
    let G' : SimpleGraph W := G.induce s
    have ha'0 : ∀ w, a' w ≠ 0 := by
      intro w hw
      have hwlabel : a (w : V) = a z := by
        dsimp [a'] at hw
        rw [hz]
        exact hw
      have hwz : (w : V) = z := a.injective hwlabel
      have hwne : (w : V) ≠ z := by
        have hs := w.2
        change (w : V) ∈ ({z} : Set V)ᶜ at hs
        intro hwz'
        exact hs (by simp [hwz'])
      exact hwne hwz
    have hinduced := hnonzero W a' G' ha'0
    have hedgeCard : G'.edgeFinset.card =
        G.edgeFinset.card - G.degree z := by
      dsimp [G', s]
      rw [G.card_edgeFinset_induce_compl_singleton z,
        G.card_edgeFinset_deleteIncidenceSet z]
    have hdenseNat : 2 * Fintype.card V ≤ G.edgeFinset.card := by
      dsimp [m, n] at hdense
      exact_mod_cast hdense
    have hdegree : G.degree z ≤ Fintype.card V :=
      (G.degree_lt_card_verts z).le
    have htwiceNat : G.edgeFinset.card ≤ 2 * G'.edgeFinset.card := by
      rw [hedgeCard]
      omega
    have htwice : m ≤ 2 * (G'.edgeFinset.card : ℝ) := by
      dsimp [m]
      exact_mod_cast htwiceNat
    have hWcardNat : Fintype.card W ≤ Fintype.card V := by
      exact Fintype.card_subtype_le _
    have hWcard : (Fintype.card W : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast hWcardNat
    have hWpow : (Fintype.card W : ℝ) ^ ((7 : ℝ) / 4) ≤
        n ^ ((7 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hWcard (by norm_num)
    have hmax :
        max ((edgeSums a' G').card : ℝ)
            ((edgeProducts a' G').card : ℝ) ≤ M := by
      have hsSub : edgeSums a' G' ⊆ edgeSums a G := by
        intro r hr
        rw [edgeSums, mem_edgeValues_iff] at hr ⊢
        obtain ⟨u, v, huv, rfl⟩ := hr
        exact ⟨u.1, v.1, huv, rfl⟩
      have hpSub : edgeProducts a' G' ⊆ edgeProducts a G := by
        intro r hr
        rw [edgeProducts, mem_edgeValues_iff] at hr ⊢
        obtain ⟨u, v, huv, rfl⟩ := hr
        exact ⟨u.1, v.1, huv, rfl⟩
      have hsNat := Finset.card_le_card hsSub
      have hpNat := Finset.card_le_card hpSub
      apply max_le
      · apply (show ((edgeSums a' G').card : ℝ) ≤
            (edgeSums a G).card by exact_mod_cast hsNat).trans
        exact le_max_left _ _
      · apply (show ((edgeProducts a' G').card : ℝ) ≤
            (edgeProducts a G).card by exact_mod_cast hpNat).trans
        exact le_max_right _ _
    have hraise := Real.rpow_le_rpow hm0 htwice
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hfactor : (2 * (G'.edgeFinset.card : ℝ)) ^ ((3 : ℝ) / 2) =
        R * (G'.edgeFinset.card : ℝ) ^ ((3 : ℝ) / 2) := by
      dsimp [R]
      rw [Real.mul_rpow (by norm_num) (by positivity)]
    rw [hfactor] at hraise
    have hinner :
        K * (Fintype.card W : ℝ) ^ ((7 : ℝ) / 4) *
            max ((edgeSums a' G').card : ℝ)
              ((edgeProducts a' G').card : ℝ) ≤
          K * n ^ ((7 : ℝ) / 4) * M := by
      calc
        K * (Fintype.card W : ℝ) ^ ((7 : ℝ) / 4) *
            max ((edgeSums a' G').card : ℝ)
              ((edgeProducts a' G').card : ℝ) ≤
            K * n ^ ((7 : ℝ) / 4) *
              max ((edgeSums a' G').card : ℝ)
                ((edgeProducts a' G').card : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hWpow hK.le) (by positivity)
        _ ≤ K * n ^ ((7 : ℝ) / 4) * M :=
          mul_le_mul_of_nonneg_left hmax
            (mul_nonneg hK.le (Real.rpow_nonneg hn0 _))
    change m ^ ((3 : ℝ) / 2) ≤ K₀ * n ^ ((7 : ℝ) / 4) * M
    calc
      m ^ ((3 : ℝ) / 2) ≤
          R * (G'.edgeFinset.card : ℝ) ^ ((3 : ℝ) / 2) := hraise
      _ ≤ R * (K * (Fintype.card W : ℝ) ^ ((7 : ℝ) / 4) *
          max ((edgeSums a' G').card : ℝ)
            ((edgeProducts a' G').card : ℝ)) :=
        mul_le_mul_of_nonneg_left hinduced hR0
      _ ≤ R * (K * n ^ ((7 : ℝ) / 4) * M) :=
        mul_le_mul_of_nonneg_left hinner hR0
      _ = (R * K) * n ^ ((7 : ℝ) / 4) * M := by ring
      _ ≤ K₀ * n ^ ((7 : ℝ) / 4) * M :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKR (Real.rpow_nonneg hn0 _)) hM0
  · have ha0 : ∀ v, a v ≠ 0 := by
      intro v hv
      exact hz ⟨v, hv⟩
    have h := hnonzero V a G ha0
    change m ^ ((3 : ℝ) / 2) ≤ K₀ * n ^ ((7 : ℝ) / 4) * M
    change m ^ ((3 : ℝ) / 2) ≤ K * n ^ ((7 : ℝ) / 4) * M at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKle (Real.rpow_nonneg hn0 _)) hM0)


/-! ## The prime block and the sifted interval -/

/-- The `i`th prime in the block beginning at prime index `q²`. -/
def blockPrime (q : ℕ) (i : Fin q) : ℕ :=
  nth_prime (q ^ 2 + i)

lemma blockPrime_prime (q : ℕ) (i : Fin q) : (blockPrime q i).Prime := by
  exact Nat.prime_nth_prime _

lemma blockPrime_injective (q : ℕ) : Function.Injective (blockPrime q) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel
    (Nat.nth_injective Nat.infinite_setOfPred_prime hij)

lemma sq_le_blockPrime (q : ℕ) (i : Fin q) : q ^ 2 ≤ blockPrime q i := by
  exact (Nat.le_add_right (q ^ 2) (i : ℕ)).trans
    ((Nat.le_add_right _ 2).trans (Nat.add_two_le_nth_prime _))

/-- A deliberately coarse polynomial upper bound for the selected primes.
The wide exponent keeps the later arithmetic completely elementary. -/
lemma blockPrime_le_seventh_eventually :
    ∀ᶠ q : ℕ in atTop, ∀ i : Fin q, blockPrime q i ≤ q ^ 7 := by
  obtain ⟨C, hC, hbound⟩ := nth_prime_asymp.isBigO.exists_pos
  obtain ⟨M : ℕ, hCM⟩ := exists_nat_ge C
  have hbound' := hbound.bound
  rw [eventually_atTop] at hbound'
  obtain ⟨N, hN⟩ := hbound'
  filter_upwards [eventually_ge_atTop (max (max N M) 2)] with q hq
  intro i
  let r : ℕ := q ^ 2 + i
  have hNq : N ≤ q :=
    (le_max_left N M).trans ((le_max_left (max N M) 2).trans hq)
  have hMq : M ≤ q :=
    (le_max_right N M).trans ((le_max_left (max N M) 2).trans hq)
  have hq2 : 2 ≤ q := (le_max_right (max N M) 2).trans hq
  have hNr : N ≤ r := by
    dsimp [r]
    nlinarith
  have hrq3 : r ≤ q ^ 3 := by
    dsimp [r]
    have hi : (i : ℕ) < q := i.isLt
    nlinarith
  have hrpos : (0 : ℝ) ≤ r := by positivity
  have hlog : Real.log (r : ℝ) ≤ r := Real.log_le_self hrpos
  have hb := hN r hNr
  have hpnnonneg : (0 : ℝ) ≤ nth_prime r := by positivity
  have hrlognonneg : (0 : ℝ) ≤ (r : ℝ) * Real.log r := by
    have : (1 : ℕ) ≤ r := by
      dsimp [r]
      nlinarith
    exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast this))
  simp only [Real.norm_eq_abs, abs_of_nonneg hpnnonneg,
    abs_of_nonneg hrlognonneg] at hb
  have hCq : C ≤ (q : ℝ) := hCM.trans (by exact_mod_cast hMq)
  have hb' : (nth_prime r : ℝ) ≤ q ^ 7 := by
    calc
      (nth_prime r : ℝ) ≤ C * (r : ℝ) * Real.log r := by
        simpa [mul_assoc] using hb
      _ ≤ (q : ℝ) * r * r := by gcongr
      _ ≤ (q : ℝ) * q ^ 3 * q ^ 3 := by
        gcongr <;> exact_mod_cast hrq3
      _ = (q : ℝ) ^ 7 := by ring
  exact_mod_cast hb'

/-- Positive integers at most `q¹⁵` which avoid every prime in the block. -/
def goodNumbers (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 15)).filter
    (fun u ↦ ∀ i : Fin q, ¬ blockPrime q i ∣ u)

@[simp] lemma mem_goodNumbers {q u : ℕ} :
    u ∈ goodNumbers q ↔
      1 ≤ u ∧ u ≤ q ^ 15 ∧ ∀ i : Fin q, ¬ blockPrime q i ∣ u := by
  simp [goodNumbers, and_assoc]

lemma goodNumbers_pos {q u : ℕ} (hu : u ∈ goodNumbers q) : 0 < u := by
  exact (mem_goodNumbers.mp hu).1

lemma goodNumbers_le {q u : ℕ} (hu : u ∈ goodNumbers q) : u ≤ q ^ 15 := by
  exact (mem_goodNumbers.mp hu).2.1

/-- Multiples of one selected prime in the ambient interval. -/
def blockMultiples (q : ℕ) (i : Fin q) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 15)).filter (fun u ↦ blockPrime q i ∣ u)

/-- The complement of `goodNumbers` inside the ambient interval. -/
def badNumbers (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 15)).filter
    (fun u ↦ ¬ ∀ i : Fin q, ¬ blockPrime q i ∣ u)

lemma blockMultiples_card_le (q : ℕ) (i : Fin q) :
    (blockMultiples q i).card ≤ q ^ 13 := by
  have heq : blockMultiples q i =
      (Finset.Ioc 0 (q ^ 15)).filter (fun u ↦ blockPrime q i ∣ u) := by
    ext u
    simp only [blockMultiples, Finset.mem_filter, Finset.mem_Icc,
      Finset.mem_Ioc]
    omega
  rw [heq, Nat.Ioc_filter_dvd_card_eq_div]
  apply Nat.div_le_of_le_mul
  calc
    q ^ 15 = q ^ 13 * q ^ 2 := by ring
    _ ≤ q ^ 13 * blockPrime q i :=
      Nat.mul_le_mul_left _ (sq_le_blockPrime q i)
    _ = blockPrime q i * q ^ 13 := by ac_rfl

lemma badNumbers_subset_biUnion (q : ℕ) :
    badNumbers q ⊆
      (Finset.univ : Finset (Fin q)).biUnion (blockMultiples q) := by
  intro u hu
  rw [Finset.mem_biUnion]
  rw [badNumbers, Finset.mem_filter] at hu
  push Not at hu
  obtain ⟨i, hi⟩ := hu.2
  exact ⟨i, Finset.mem_univ _, by
    exact Finset.mem_filter.mpr ⟨hu.1, hi⟩⟩

lemma badNumbers_card_le (q : ℕ) : (badNumbers q).card ≤ q ^ 14 := by
  calc
    (badNumbers q).card ≤
        ((Finset.univ : Finset (Fin q)).biUnion (blockMultiples q)).card :=
      Finset.card_le_card (badNumbers_subset_biUnion q)
    _ ≤ ∑ i : Fin q, (blockMultiples q i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin q, q ^ 13 :=
      Finset.sum_le_sum fun i _ ↦ blockMultiples_card_le q i
    _ = q ^ 14 := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      simpa using (pow_succ' q 13).symm

lemma goodNumbers_card_add_badNumbers_card (q : ℕ) :
    (goodNumbers q).card + (badNumbers q).card = q ^ 15 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.Icc 1 (q ^ 15))
    (p := fun u ↦ ∀ i : Fin q, ¬ blockPrime q i ∣ u)
  have hcard : (Finset.Icc 1 (q ^ 15)).card = q ^ 15 := by
    simp [Nat.card_Icc]
  simpa only [goodNumbers, badNumbers, hcard] using h

lemma goodNumbers_card_lower (q : ℕ) :
    q ^ 15 - q ^ 14 ≤ (goodNumbers q).card := by
  have hsum := goodNumbers_card_add_badNumbers_card q
  have hbad := badNumbers_card_le q
  omega

lemma goodNumbers_card_half {q : ℕ} (hq : 2 ≤ q) :
    q ^ 15 ≤ 2 * (goodNumbers q).card := by
  have hlower := goodNumbers_card_lower q
  have hpowers : 2 * q ^ 14 ≤ q ^ 15 := by
    calc
      2 * q ^ 14 ≤ q * q ^ 14 := Nat.mul_le_mul_right _ hq
      _ = q ^ 15 := by ring
  omega

lemma goodNumbers_card_upper (q : ℕ) :
    (goodNumbers q).card ≤ q ^ 15 := by
  exact (Finset.card_filter_le _ _).trans (by simp [Nat.card_Icc])

/-! ## Vertices and their integer labels -/

/-- Sifted positive integers used as the first vertex coordinate. -/
abbrev Good (q : ℕ) := ↑(goodNumbers q)

/-- Ordered pairs of distinct block indices. -/
abbrev OrientedPair (q : ℕ) :=
  ↑((Finset.univ : Finset (Fin q)).offDiag)

/-- The vertices of the counterexample. -/
abbrev CounterVertex (q : ℕ) := Good q × OrientedPair q

/-- Product of all block primes except the one indexed by `i`. -/
def primeQuotient (q : ℕ) (i : Fin q) : ℕ :=
  ∏ k ∈ (Finset.univ : Finset (Fin q)).erase i, blockPrime q k

/-- Product of all block primes. -/
def primeProduct (q : ℕ) : ℕ :=
  ∏ k : Fin q, blockPrime q k

lemma blockPrime_mul_primeQuotient (q : ℕ) (i : Fin q) :
    blockPrime q i * primeQuotient q i = primeProduct q := by
  exact Finset.mul_prod_erase (Finset.univ : Finset (Fin q))
    (blockPrime q) (Finset.mem_univ i)

lemma primeQuotient_pos (q : ℕ) (i : Fin q) : 0 < primeQuotient q i := by
  exact Finset.prod_pos fun k _ ↦ (blockPrime_prime q k).pos

lemma blockPrime_dvd_primeQuotient {q : ℕ} {i k : Fin q} (hki : k ≠ i) :
    blockPrime q k ∣ primeQuotient q i := by
  exact Finset.dvd_prod_of_mem (blockPrime q) (by simp [hki])

lemma blockPrime_not_dvd_primeQuotient (q : ℕ) (i : Fin q) :
    ¬ blockPrime q i ∣ primeQuotient q i := by
  apply (blockPrime_prime q i).prime.not_dvd_finsetProd
  intro k hk hdvd
  have hik : i = k := (blockPrime_injective q)
    ((Nat.prime_dvd_prime_iff_eq (blockPrime_prime q i)
      (blockPrime_prime q k)).mp hdvd)
  exact (Finset.mem_erase.mp hk).1 hik.symm

/-- The label `u p_j (D / p_i)`, written without natural-number division. -/
def counterLabel (q : ℕ) (x : CounterVertex q) : ℕ :=
  x.1.1 * blockPrime q x.2.1.2 * primeQuotient q x.2.1.1

lemma oriented_ne (q : ℕ) (x : CounterVertex q) : x.2.1.1 ≠ x.2.1.2 := by
  exact (Finset.mem_offDiag.mp x.2.2).2.2

lemma counterLabel_pos (q : ℕ) (x : CounterVertex q) :
    0 < counterLabel q x := by
  exact mul_pos (mul_pos (goodNumbers_pos x.1.2)
    (blockPrime_prime q x.2.1.2).pos) (primeQuotient_pos q x.2.1.1)

lemma index_prime_not_dvd_counterLabel (q : ℕ) (x : CounterVertex q) :
    ¬ blockPrime q x.2.1.1 ∣ counterLabel q x := by
  intro hdvd
  rcases (blockPrime_prime q x.2.1.1).dvd_mul.mp hdvd with hdvd | hdvd
  · rcases (blockPrime_prime q x.2.1.1).dvd_mul.mp hdvd with hu | hp
    · exact (mem_goodNumbers.mp x.1.2).2.2 x.2.1.1 hu
    · exact (oriented_ne q x)
        ((blockPrime_injective q)
          ((Nat.prime_dvd_prime_iff_eq (blockPrime_prime q x.2.1.1)
            (blockPrime_prime q x.2.1.2)).mp hp))
  · exact blockPrime_not_dvd_primeQuotient q x.2.1.1 hdvd

lemma blockPrime_dvd_counterLabel_of_ne (q : ℕ) (x : CounterVertex q)
    (k : Fin q) (hki : k ≠ x.2.1.1) :
    blockPrime q k ∣ counterLabel q x := by
  exact dvd_mul_of_dvd_right (blockPrime_dvd_primeQuotient hki)
    (x.1.1 * blockPrime q x.2.1.2)

lemma counterLabel_injective (q : ℕ) : Function.Injective (counterLabel q) := by
  intro x y hxy
  have hi : x.2.1.1 = y.2.1.1 := by
    by_contra hne
    have hdvd := blockPrime_dvd_counterLabel_of_ne q y x.2.1.1 hne
    rw [← hxy] at hdvd
    exact index_prime_not_dvd_counterLabel q x hdvd
  have hcore :
      x.1.1 * blockPrime q x.2.1.2 =
        y.1.1 * blockPrime q y.2.1.2 := by
    apply Nat.mul_right_cancel (m := primeQuotient q x.2.1.1)
      (primeQuotient_pos q x.2.1.1)
    simpa only [counterLabel, hi] using hxy
  have hjdvd : blockPrime q x.2.1.2 ∣
      y.1.1 * blockPrime q y.2.1.2 := by
    rw [← hcore]
    exact ⟨x.1.1, by ac_rfl⟩
  have hj : x.2.1.2 = y.2.1.2 := by
    rcases (blockPrime_prime q x.2.1.2).dvd_mul.mp hjdvd with hu | hp
    · exact False.elim ((mem_goodNumbers.mp y.1.2).2.2 x.2.1.2 hu)
    · exact (blockPrime_injective q)
        ((Nat.prime_dvd_prime_iff_eq (blockPrime_prime q x.2.1.2)
          (blockPrime_prime q y.2.1.2)).mp hp)
  have hu : x.1.1 = y.1.1 := by
    apply Nat.mul_right_cancel (m := blockPrime q x.2.1.2)
      (blockPrime_prime q x.2.1.2).pos
    simpa only [hj] using hcore
  apply Prod.ext
  · exact Subtype.ext hu
  · apply Subtype.ext
    exact Prod.ext hi hj

/-- The label embedding used in the statement of Problem 808. -/
def counterEmbedding (q : ℕ) : CounterVertex q ↪ ℕ :=
  ⟨counterLabel q, counterLabel_injective q⟩

lemma counterVertex_card (q : ℕ) :
    Fintype.card (CounterVertex q) =
      (goodNumbers q).card * (q * q - q) := by
  simp only [Fintype.card_prod, Fintype.card_coe, Finset.offDiag_card,
    Finset.card_univ, Fintype.card_fin]

lemma counterVertex_card_upper (q : ℕ) :
    Fintype.card (CounterVertex q) ≤ q ^ 17 := by
  rw [counterVertex_card]
  calc
    (goodNumbers q).card * (q * q - q) ≤ q ^ 15 * q ^ 2 := by
      apply Nat.mul_le_mul (goodNumbers_card_upper q)
      simp [pow_two]
    _ = q ^ 17 := by ring

lemma orderedPair_card_half {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 ≤ 2 * (q * q - q) := by
  have hlin : q ≤ 2 * (q - 1) := by omega
  have hfac : q * q - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib]
    simp
  calc
    q ^ 2 = q * q := by ring
    _ ≤ q * (2 * (q - 1)) := Nat.mul_le_mul_left q hlin
    _ = 2 * (q * q - q) := by rw [hfac]; ring

lemma counterVertex_card_quarter {q : ℕ} (hq : 2 ≤ q) :
    q ^ 17 ≤ 4 * Fintype.card (CounterVertex q) := by
  rw [counterVertex_card]
  calc
    q ^ 17 = q ^ 15 * q ^ 2 := by ring
    _ ≤ (2 * (goodNumbers q).card) * (2 * (q * q - q)) :=
      Nat.mul_le_mul (goodNumbers_card_half hq) (orderedPair_card_half hq)
    _ = 4 * ((goodNumbers q).card * (q * q - q)) := by ring

/-! ## The swap graph -/

/-- Two vertices are adjacent when their ordered prime indices are reversed. -/
def counterGraph (q : ℕ) : SimpleGraph (CounterVertex q) where
  Adj x y := x.2.1.1 = y.2.1.2 ∧ x.2.1.2 = y.2.1.1
  symm := ⟨by
      intro x y h
      exact ⟨h.2.symm, h.1.symm⟩⟩
  loopless := ⟨by
      intro x h
      exact oriented_ne q x h.1⟩

instance counterGraph_decidableAdj (q : ℕ) :
    DecidableRel (counterGraph q).Adj := fun _ _ ↦ inferInstance

@[simp] lemma counterGraph_adj {q : ℕ} {x y : CounterVertex q} :
    (counterGraph q).Adj x y ↔
      x.2.1.1 = y.2.1.2 ∧ x.2.1.2 = y.2.1.1 := Iff.rfl

/-- The unique neighbor of `x` with prescribed sifted coordinate `u`. -/
def swapNeighbor (q : ℕ) (x : CounterVertex q) (u : Good q) :
    CounterVertex q :=
  ⟨u, ⟨(x.2.1.2, x.2.1.1), Finset.mem_offDiag.mpr
    ⟨Finset.mem_univ _, Finset.mem_univ _, (oriented_ne q x).symm⟩⟩⟩

lemma swapNeighbor_injective (q : ℕ) (x : CounterVertex q) :
    Function.Injective (swapNeighbor q x) := by
  intro u v huv
  exact congrArg Prod.fst huv

def swapNeighborEmbedding (q : ℕ) (x : CounterVertex q) :
    Good q ↪ CounterVertex q :=
  ⟨swapNeighbor q x, swapNeighbor_injective q x⟩

lemma neighborFinset_counterGraph (q : ℕ) (x : CounterVertex q) :
    (counterGraph q).neighborFinset x =
      (Finset.univ : Finset (Good q)).map (swapNeighborEmbedding q x) := by
  ext y
  constructor
  · intro hy
    have hadj : (counterGraph q).Adj x y := by simpa using hy
    apply Finset.mem_map.mpr
    refine ⟨y.1, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Prod.ext hadj.2 hadj.1
  · intro hy
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_map.mp hy
    apply ((counterGraph q).mem_neighborFinset x _).mpr
    exact ⟨rfl, rfl⟩

lemma counterGraph_degree (q : ℕ) (x : CounterVertex q) :
    (counterGraph q).degree x = (goodNumbers q).card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_counterGraph, Finset.card_map]
  simp

lemma counterGraph_twice_edges (q : ℕ) :
    2 * (counterGraph q).edgeFinset.card =
      Fintype.card (CounterVertex q) * (goodNumbers q).card := by
  rw [← (counterGraph q).sum_degrees_eq_twice_card_edges]
  simp only [counterGraph_degree, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rfl

lemma counterGraph_many_edges {q : ℕ} (hq : 2 ≤ q) :
    q ^ 32 ≤ 16 * (counterGraph q).edgeFinset.card := by
  calc
    q ^ 32 = q ^ 17 * q ^ 15 := by ring
    _ ≤ (4 * Fintype.card (CounterVertex q)) *
        (2 * (goodNumbers q).card) :=
      Nat.mul_le_mul (counterVertex_card_quarter hq) (goodNumbers_card_half hq)
    _ = 8 * (Fintype.card (CounterVertex q) *
        (goodNumbers q).card) := by ring
    _ = 8 * (2 * (counterGraph q).edgeFinset.card) := by
      rw [counterGraph_twice_edges]
    _ = 16 * (counterGraph q).edgeFinset.card := by ring

/-! ## The two restricted image bounds -/

/-- Product of all block primes except `p_i` and `p_j`. -/
def primeRest (q : ℕ) (i j : Fin q) : ℕ :=
  ∏ k ∈ ((Finset.univ : Finset (Fin q)).erase i).erase j,
    blockPrime q k

lemma primeRest_symm (q : ℕ) (i j : Fin q) :
    primeRest q i j = primeRest q j i := by
  unfold primeRest
  apply Finset.prod_congr
  · ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  · intro k _
    rfl

lemma primeQuotient_eq_mul_rest {q : ℕ} {i j : Fin q} (hij : i ≠ j) :
    primeQuotient q i = blockPrime q j * primeRest q i j := by
  symm
  exact Finset.mul_prod_erase
    ((Finset.univ : Finset (Fin q)).erase i) (blockPrime q)
    (by simp [hij.symm])

lemma counterLabel_mul_of_adj {q : ℕ} {x y : CounterVertex q}
    (hxy : (counterGraph q).Adj x y) :
    counterLabel q x * counterLabel q y =
      (x.1.1 * y.1.1) * primeProduct q ^ 2 := by
  have hxi := blockPrime_mul_primeQuotient q x.2.1.1
  have hxj := blockPrime_mul_primeQuotient q x.2.1.2
  rw [counterLabel, counterLabel, ← hxy.1, ← hxy.2]
  calc
    (x.1.1 * blockPrime q x.2.1.2 * primeQuotient q x.2.1.1) *
        (y.1.1 * blockPrime q x.2.1.1 * primeQuotient q x.2.1.2) =
      (x.1.1 * y.1.1) *
        (blockPrime q x.2.1.1 * primeQuotient q x.2.1.1) *
        (blockPrime q x.2.1.2 * primeQuotient q x.2.1.2) := by ring
    _ = (x.1.1 * y.1.1) * primeProduct q ^ 2 := by
      rw [hxi, hxj]
      ring

lemma counterLabel_add_of_adj {q : ℕ} {x y : CounterVertex q}
    (hxy : (counterGraph q).Adj x y) :
    counterLabel q x + counterLabel q y =
      primeRest q x.2.1.1 x.2.1.2 *
        (x.1.1 * blockPrime q x.2.1.2 ^ 2 +
          y.1.1 * blockPrime q x.2.1.1 ^ 2) := by
  have hne := oriented_ne q x
  have hQi := primeQuotient_eq_mul_rest (q := q) hne
  have hQj := primeQuotient_eq_mul_rest (q := q) hne.symm
  rw [counterLabel, counterLabel, ← hxy.1, ← hxy.2, hQi, hQj,
    ← primeRest_symm q x.2.1.1 x.2.1.2]
  ring

/-- A one-dimensional target containing every restricted product. -/
def productTargets (q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (q ^ 30)).image
    (fun t ↦ t * primeProduct q ^ 2)

lemma edgeProducts_subset_productTargets (q : ℕ) :
    edgeProducts (counterEmbedding q) (counterGraph q) ⊆ productTargets q := by
  intro r hr
  rw [edgeProducts, mem_edgeValues_iff] at hr
  obtain ⟨x, y, hxy, rfl⟩ := hr
  change counterLabel q x * counterLabel q y ∈ productTargets q
  rw [counterLabel_mul_of_adj hxy]
  apply Finset.mem_image.mpr
  refine ⟨x.1.1 * y.1.1, ?_, rfl⟩
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (goodNumbers_pos x.1.2)
    (goodNumbers_pos y.1.2), by
      calc
        x.1.1 * y.1.1 ≤ q ^ 15 * q ^ 15 :=
          Nat.mul_le_mul (goodNumbers_le x.1.2) (goodNumbers_le y.1.2)
        _ = q ^ 30 := by ring⟩

lemma productTargets_card_le (q : ℕ) :
    (productTargets q).card ≤ q ^ 30 := by
  calc
    (productTargets q).card ≤ (Finset.Icc 1 (q ^ 30)).card :=
      Finset.card_image_le
    _ ≤ q ^ 30 := by simp [Nat.card_Icc]

lemma counter_edgeProducts_card_le (q : ℕ) :
    (edgeProducts (counterEmbedding q) (counterGraph q)).card ≤ q ^ 30 :=
  (Finset.card_le_card (edgeProducts_subset_productTargets q)).trans
    (productTargets_card_le q)

/-- A target containing every restricted sum, indexed by its two omitted
primes and by its bounded numerator. -/
def sumTargets (q : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin q)).biUnion fun i ↦
    (Finset.univ : Finset (Fin q)).biUnion fun j ↦
      (Finset.Icc 1 (2 * q ^ 29)).image (fun t ↦ primeRest q i j * t)

lemma edgeSums_subset_sumTargets (q : ℕ)
    (hp : ∀ i : Fin q, blockPrime q i ≤ q ^ 7) :
    edgeSums (counterEmbedding q) (counterGraph q) ⊆ sumTargets q := by
  intro r hr
  rw [edgeSums, mem_edgeValues_iff] at hr
  obtain ⟨x, y, hxy, rfl⟩ := hr
  change counterLabel q x + counterLabel q y ∈ sumTargets q
  rw [counterLabel_add_of_adj hxy]
  rw [sumTargets, Finset.mem_biUnion]
  refine ⟨x.2.1.1, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨x.2.1.2, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  let t := x.1.1 * blockPrime q x.2.1.2 ^ 2 +
    y.1.1 * blockPrime q x.2.1.1 ^ 2
  refine ⟨t, ?_, rfl⟩
  apply Finset.mem_Icc.mpr
  constructor
  · dsimp [t]
    have hxpos : 0 < x.1.1 := goodNumbers_pos x.1.2
    have hppos : 0 < blockPrime q x.2.1.2 :=
      (blockPrime_prime q x.2.1.2).pos
    have hpos : 0 < x.1.1 * blockPrime q x.2.1.2 ^ 2 := by
      exact Nat.mul_pos hxpos (pow_pos hppos 2)
    omega
  · dsimp [t]
    calc
      x.1.1 * blockPrime q x.2.1.2 ^ 2 +
          y.1.1 * blockPrime q x.2.1.1 ^ 2 ≤
        q ^ 15 * (q ^ 7) ^ 2 + q ^ 15 * (q ^ 7) ^ 2 :=
          Nat.add_le_add
            (Nat.mul_le_mul (goodNumbers_le x.1.2)
              (pow_le_pow_left' (hp x.2.1.2) 2))
            (Nat.mul_le_mul (goodNumbers_le y.1.2)
              (pow_le_pow_left' (hp x.2.1.1) 2))
      _ = 2 * q ^ 29 := by ring

lemma sumTargets_card_le (q : ℕ) :
    (sumTargets q).card ≤ 2 * q ^ 31 := by
  calc
    (sumTargets q).card ≤
        ∑ _i : Fin q, ∑ _j : Fin q,
          ((Finset.Icc 1 (2 * q ^ 29)).image
            (fun t ↦ primeRest q _i _j * t)).card := by
      exact Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun i _ ↦ Finset.card_biUnion_le)
    _ ≤ ∑ _i : Fin q, ∑ _j : Fin q, 2 * q ^ 29 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le.trans (by simp [Nat.card_Icc])
    _ = 2 * q ^ 31 := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hpow : q ^ 2 * q ^ 29 = q ^ 31 := by
        rw [← pow_add]
      calc
        q * (q * (2 * q ^ 29)) = 2 * (q ^ 2 * q ^ 29) := by ring
        _ = 2 * q ^ 31 := by rw [hpow]

lemma counter_edgeSums_card_le (q : ℕ)
    (hp : ∀ i : Fin q, blockPrime q i ≤ q ^ 7) :
    (edgeSums (counterEmbedding q) (counterGraph q)).card ≤ 2 * q ^ 31 :=
  (Finset.card_le_card (edgeSums_subset_sumTargets q hp)).trans
    (sumTargets_card_le q)

/-! ## Real-power comparisons and the disproof -/

/-- A fixed multiple of a smaller real power of a natural parameter is
eventually at most a larger power. -/
lemma eventually_const_mul_rpow_le_rpow_nat
    {C a b : ℝ} (_hC : 0 ≤ C) (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ a ≤ (q : ℝ) ^ b := by
  have htop : Tendsto (fun q : ℕ ↦ (q : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [htop (eventually_ge_atTop C), eventually_ge_atTop (1 : ℕ)]
    with q hqC hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (zero_lt_one.trans_le hq)
  calc
    C * (q : ℝ) ^ a ≤ (q : ℝ) ^ (b - a) * (q : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hqC (Real.rpow_nonneg hqpos.le _)
    _ = (q : ℝ) ^ b := by
      rw [← Real.rpow_add hqpos]
      congr 1
      ring

lemma pow_rpow_eq_rpow_mul (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (a : ℝ) :
    (x ^ n) ^ a = x ^ ((n : ℝ) * a) := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_mul hx (n : ℝ) a).symm

lemma counterGraph_edge_threshold_eventually :
    ∀ᶠ q : ℕ in atTop,
      (Fintype.card (CounterVertex q) : ℝ) ^ ((63 : ℝ) / 34) ≤
        ((counterGraph q).edgeFinset.card : ℝ) := by
  have habsorb : ∀ᶠ q : ℕ in atTop,
      16 * (q : ℝ) ^ ((63 : ℝ) / 2) ≤ (q : ℝ) ^ (32 : ℝ) :=
    eventually_const_mul_rpow_le_rpow_nat (by norm_num)
      (by norm_num : (63 : ℝ) / 2 < 32)
  filter_upwards [habsorb, eventually_ge_atTop 2] with q hab hq
  let n := Fintype.card (CounterVertex q)
  let m := (counterGraph q).edgeFinset.card
  have hn : (n : ℝ) ≤ (q : ℝ) ^ 17 := by
    exact_mod_cast counterVertex_card_upper q
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hmono : (n : ℝ) ^ ((63 : ℝ) / 34) ≤
      ((q : ℝ) ^ 17) ^ ((63 : ℝ) / 34) :=
    Real.rpow_le_rpow hnnonneg hn (by norm_num)
  have hrexp : ((q : ℝ) ^ 17) ^ ((63 : ℝ) / 34) =
      (q : ℝ) ^ ((63 : ℝ) / 2) := by
    rw [pow_rpow_eq_rpow_mul _ hqnonneg]
    congr 1
    norm_num
  have hedgeNat := counterGraph_many_edges hq
  have hedge : ((q ^ 32 : ℕ) : ℝ) ≤ 16 * (m : ℝ) := by
    exact_mod_cast hedgeNat
  have hpowEq : (q : ℝ) ^ (32 : ℝ) = ((q ^ 32 : ℕ) : ℝ) := by
    norm_num [Real.rpow_natCast]
  have hqm : (q : ℝ) ^ ((63 : ℝ) / 2) ≤ (m : ℝ) := by
    linarith [hab, hedge]
  exact hmono.trans_eq hrexp |>.trans hqm

lemma counterGraph_output_small_eventually :
    ∀ᶠ q : ℕ in atTop,
      max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) <
        (Fintype.card (CounterVertex q) : ℝ) ^ ((125 : ℝ) / 68) := by
  let b : ℝ := 125 / 68
  let scale : ℝ := (4 : ℝ) ^ b
  have hscale : 0 < scale := Real.rpow_pos_of_pos (by norm_num) _
  have habsorb : ∀ᶠ q : ℕ in atTop,
      (3 * scale) * (q : ℝ) ^ (31 : ℝ) ≤
        (q : ℝ) ^ ((125 : ℝ) / 4) :=
    eventually_const_mul_rpow_le_rpow_nat
      (mul_nonneg (by norm_num) hscale.le)
      (by norm_num : (31 : ℝ) < 125 / 4)
  filter_upwards [habsorb, blockPrime_le_seventh_eventually,
    eventually_ge_atTop 2] with q hab hp hq
  let n := Fintype.card (CounterVertex q)
  have hsumNat := counter_edgeSums_card_le q hp
  have hprodNat := counter_edgeProducts_card_le q
  have hprodCoarse : (edgeProducts (counterEmbedding q)
      (counterGraph q)).card ≤ 2 * q ^ 31 := by
    calc
      (edgeProducts (counterEmbedding q) (counterGraph q)).card ≤ q ^ 30 :=
        hprodNat
      _ ≤ 2 * q ^ 31 := by
        have hpows : q ^ 30 ≤ q ^ 31 :=
          pow_le_pow_right' (by omega : 1 ≤ q) (by omega)
        omega
  have hout : max ((edgeSums (counterEmbedding q)
      (counterGraph q)).card : ℝ)
      ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) ≤
      2 * (q : ℝ) ^ (31 : ℝ) := by
    have houtNat : max (edgeSums (counterEmbedding q)
        (counterGraph q)).card
        (edgeProducts (counterEmbedding q) (counterGraph q)).card ≤
        2 * q ^ 31 := max_le hsumNat hprodCoarse
    have houtCast :
        max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) ≤
          ((2 * q ^ 31 : ℕ) : ℝ) := by
      exact_mod_cast houtNat
    calc
      max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) ≤
          ((2 * q ^ 31 : ℕ) : ℝ) := houtCast
      _ = 2 * (q : ℝ) ^ (31 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hnNat := counterVertex_card_quarter hq
  have hn : (q : ℝ) ^ 17 ≤ 4 * (n : ℝ) := by
    exact_mod_cast hnNat
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hbase : (q : ℝ) ^ ((125 : ℝ) / 4) ≤
      scale * (n : ℝ) ^ b := by
    calc
      (q : ℝ) ^ ((125 : ℝ) / 4) =
          ((q : ℝ) ^ 17) ^ b := by
        rw [pow_rpow_eq_rpow_mul _ hqnonneg]
        dsimp [b]
        congr 1
        norm_num
      _ ≤ (4 * (n : ℝ)) ^ b :=
        Real.rpow_le_rpow (by positivity) hn (by dsimp [b]; norm_num)
      _ = scale * (n : ℝ) ^ b := by
        rw [Real.mul_rpow (by norm_num) hnnonneg]
  have hscaled : scale * (3 * (q : ℝ) ^ (31 : ℝ)) ≤
      scale * (n : ℝ) ^ b := by
    calc
      scale * (3 * (q : ℝ) ^ (31 : ℝ)) =
          (3 * scale) * (q : ℝ) ^ (31 : ℝ) := by ring
      _ ≤ (q : ℝ) ^ ((125 : ℝ) / 4) := hab
      _ ≤ scale * (n : ℝ) ^ b := hbase
  have hqpowpos : 0 < (q : ℝ) ^ (31 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < q by omega)) _
  have hstrictScaled :
      scale * (2 * (q : ℝ) ^ (31 : ℝ)) <
        scale * (3 * (q : ℝ) ^ (31 : ℝ)) := by
    exact mul_lt_mul_of_pos_left (by linarith) hscale
  have hstrict : 2 * (q : ℝ) ^ (31 : ℝ) < (n : ℝ) ^ b :=
    lt_of_mul_lt_mul_left (hstrictScaled.trans_le hscaled) hscale.le
  exact hout.trans_lt (by simpa only [b, n] using hstrict)

/-- Alon--Ruzsa--Solymosi's construction refutes the literal strong
graph-restricted sum--product conjecture. -/
theorem erdos808_disproved : ¬ StrongErdos808 := by
  intro hstrong
  obtain ⟨n₀, hstrong⟩ := hstrong ((29 : ℝ) / 34) (by norm_num)
    ((1 : ℝ) / 68) (by norm_num)
  have hcounter : ∀ᶠ q : ℕ in atTop,
      (∀ i : Fin q, blockPrime q i ≤ q ^ 7) ∧
      (Fintype.card (CounterVertex q) : ℝ) ^ ((63 : ℝ) / 34) ≤
        ((counterGraph q).edgeFinset.card : ℝ) ∧
      max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) <
        (Fintype.card (CounterVertex q) : ℝ) ^ ((125 : ℝ) / 68) ∧
      max (4 * n₀) 2 ≤ q := by
    filter_upwards [blockPrime_le_seventh_eventually,
      counterGraph_edge_threshold_eventually,
      counterGraph_output_small_eventually,
      eventually_ge_atTop (max (4 * n₀) 2)] with q hp hedge hout hq
    exact ⟨hp, hedge, hout, hq⟩
  obtain ⟨q, hp, hedge, hout, hq⟩ := hcounter.exists
  have hq2 : 2 ≤ q := (le_max_right (4 * n₀) 2).trans hq
  have hqlarge : 4 * n₀ ≤ q := (le_max_left (4 * n₀) 2).trans hq
  have hqpow : q ≤ q ^ 17 := le_self_pow (by omega) (by norm_num)
  have hnlarge : n₀ ≤ Fintype.card (CounterVertex q) := by
    have hv := counterVertex_card_quarter hq2
    omega
  have hclaimed := hstrong (CounterVertex q) (counterEmbedding q)
    (counterGraph q) hnlarge (by simpa only [show (1 : ℝ) + 29 / 34 = 63 / 34 by norm_num]
      using hedge)
  have hclaimed' :
      (Fintype.card (CounterVertex q) : ℝ) ^ ((125 : ℝ) / 68) ≤
        max ((edgeSums (counterEmbedding q) (counterGraph q)).card : ℝ)
          ((edgeProducts (counterEmbedding q) (counterGraph q)).card : ℝ) := by
    simpa only [show (1 : ℝ) + 29 / 34 - 1 / 68 = 125 / 68 by norm_num]
      using hclaimed
  exact (not_lt_of_ge hclaimed') hout

/-- The repository's conventional name for the resolution of Problem 808. -/
theorem erdos_808 : ¬ StrongErdos808 := erdos808_disproved

#print axioms erdos808_quantitative_bound
#print axioms erdos_808

end Erdos808
