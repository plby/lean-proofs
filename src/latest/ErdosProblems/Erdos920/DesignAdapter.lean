import ErdosProblems.Erdos920.Projective

/-!
# Quantitative projective-design estimates for Erdős 920

This file turns the exact cardinality calculations in `Projective` into the
coarse numerical bounds used by the poor-point part of the container
argument.  The incidence relation is the projective dot-product polarity; in
particular, isotropic points are allowed as loops, exactly as in `Mixing`.
-/

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.DesignAdapter

noncomputable section

open Erdos920.Projective
open Erdos920.Mixing

/-- The point set of `PG(t,q)`. -/
abbrev P (q t : ℕ) [Fact q.Prime] := Point (ZMod q) (t + 1)

/-- Projective orthogonality with its field and dimension parameters fixed. -/
abbrev Incidence (q t : ℕ) [Fact q.Prime] : P q t → P q t → Prop :=
  Orthogonal

/-- The common polarity degree in `PG(t,q)`. -/
def degree (q t : ℕ) : ℕ := ∑ i ∈ Finset.range t, q ^ i

/-- The common off-diagonal polarity codegree in `PG(t,q)`. -/
def codegree (q t : ℕ) : ℕ := ∑ i ∈ Finset.range (t - 1), q ^ i

noncomputable local instance pointFintype (q t : ℕ) [Fact q.Prime] :
    Fintype (P q t) := Fintype.ofFinite _

local instance incidenceDecidable (q t : ℕ) [Fact q.Prime] :
    DecidableRel (Incidence q t) := Classical.decRel _

/-- Exact number of projective points in the `Finset` model. -/
theorem card_points (q t : ℕ) [Fact q.Prime] :
    Fintype.card (P q t) = ∑ i ∈ Finset.range (t + 1), q ^ i := by
  rw [← Nat.card_eq_fintype_card]
  exact natCard_point_zmod q (t + 1)

/-- Exact row size of projective orthogonality. -/
theorem card_filter_orthogonal_zmod (q t : ℕ) [Fact q.Prime]
    (x : P q t) :
    (Finset.univ.filter (Incidence q t x)).card = degree q t := by
  classical
  simpa [degree] using (card_filter_orthogonal (x := x))

/-- Exact common-row size for two distinct projective points. -/
theorem card_filter_commonOrthogonal_zmod (q t : ℕ) [Fact q.Prime]
    {x y : P q t} (hxy : x ≠ y) :
    (Finset.univ.filter fun z ↦ Incidence q t x z ∧ Incidence q t y z).card =
      codegree q t := by
  classical
  simpa [codegree] using (card_filter_commonOrthogonal (x := x) (y := y) hxy)

/-- Symmetry of the projective polarity, in the form expected by `Mixing`. -/
theorem orthogonal_symm_zmod (q t : ℕ) [Fact q.Prime]
    {x y : P q t} (hxy : Incidence q t x y) : Incidence q t y x :=
  (orthogonal_comm x y).mp hxy

/-- The point, degree, and codegree estimates used by the container proof. -/
theorem design_parameter_bounds (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) :
    q ^ t ≤ Fintype.card (P q t) ∧
      Fintype.card (P q t) ≤ 2 * q ^ t ∧
      q ^ (t - 1) ≤ degree q t ∧
      degree q t ≤ 2 * q ^ (t - 1) ∧
      codegree q t ≤ degree q t := by
  have hpoint := point_zmod_bounds q t
  have hdegree : q ^ (t - 1) ≤ degree q t ∧
      degree q t ≤ 2 * q ^ (t - 1) := by
    exact ⟨pow_pred_le_geomSum q t (by omega),
      geomSum_le_two_mul_pow_pred q t (Fact.out : q.Prime).two_le⟩
  have hcode : codegree q t ≤ degree q t := by
    unfold codegree degree
    apply Finset.sum_le_sum_of_subset
    exact Finset.range_mono (by omega)
  have hpoint' : q ^ t ≤ Fintype.card (P q t) ∧
      Fintype.card (P q t) ≤ 2 * q ^ t := by
    simpa only [Nat.card_eq_fintype_card] using hpoint
  exact ⟨hpoint'.1, hpoint'.2, hdegree.1, hdegree.2, hcode⟩

/-- The degree-to-point-count density lower bound, with denominators
cleared. -/
theorem card_points_le_two_mul_q_mul_degree
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) :
    Fintype.card (P q t) ≤ 2 * q * degree q t := by
  have h := design_parameter_bounds q t ht
  have hpow : q ^ t = q ^ (t - 1) * q := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    rw [pow_succ]
  calc
    Fintype.card (P q t) ≤ 2 * q ^ t := h.2.1
    _ = 2 * q * q ^ (t - 1) := by
      rw [hpow]
      ring
    _ ≤ 2 * q * degree q t := Nat.mul_le_mul_left (2 * q) h.2.2.1

/-- Coarse normalized expander mixing for projective orthogonality.  The
right side uses only the leading order `2 q^(t-1)` for the design variance. -/
theorem orthogonal_normalized_deviation_sq_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A B : Finset (P q t)) :
    (((orderedEdges (Incidence q t) A B : ℝ) -
        (degree q t : ℝ) / Fintype.card (P q t) * A.card * B.card) ^ 2 ≤
      2 * (q : ℝ) ^ (t - 1) * A.card * B.card) := by
  classical
  have hpar := design_parameter_bounds q t ht
  have hmix := orderedEdges_normalized_deviation_sq_le
    (Incidence q t) (degree q t) (codegree q t)
    (fun {_ _} h ↦ orthogonal_symm_zmod q t h)
    (card_filter_orthogonal_zmod q t)
    (fun _ _ hxy ↦ card_filter_commonOrthogonal_zmod q t hxy)
    hpar.2.2.2.2 A B
  have hgap : (degree q t : ℝ) - codegree q t ≤
      2 * (q : ℝ) ^ (t - 1) := by
    have hd : (degree q t : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
      exact_mod_cast hpar.2.2.2.1
    have hc : (0 : ℝ) ≤ codegree q t := Nat.cast_nonneg _
    linarith
  calc
    (((orderedEdges (Incidence q t) A B : ℝ) -
        (degree q t : ℝ) / Fintype.card (P q t) * A.card * B.card) ^ 2) ≤
      ((degree q t : ℝ) - codegree q t) * A.card * B.card := hmix
    _ ≤ 2 * (q : ℝ) ^ (t - 1) * A.card * B.card := by
      have hAB : (0 : ℝ) ≤ (A.card : ℝ) * B.card := by positivity
      nlinarith

/-- Absolute-value version of the coarse projective mixing estimate. -/
theorem abs_orthogonal_sub_expected_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A B : Finset (P q t)) :
    |(orderedEdges (Incidence q t) A B : ℝ) -
        (degree q t : ℝ) / Fintype.card (P q t) * A.card * B.card| ≤
      Real.sqrt (2 * (q : ℝ) ^ (t - 1) * A.card * B.card) := by
  apply Real.abs_le_sqrt
  exact orthogonal_normalized_deviation_sq_le q t ht A B

/-- A set of points all having at most a `1/(8q)` fraction of their
`Z`-neighbours has small product with `Z`.  The constant `512` deliberately
absorbs all geometric-series estimates. -/
theorem poor_product_le_real
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card) :
    (A.card : ℝ) * Z.card ≤ 512 * (q : ℝ) ^ (t + 1) := by
  classical
  let d := degree q t
  let c := codegree q t
  have hpar := design_parameter_bounds q t ht
  have hsparseNat :
      8 * q * orderedEdges (Incidence q t) A Z ≤ A.card * Z.card := by
    simpa [Nat.mul_assoc] using
      (mul_orderedEdges_le_card_mul_of_pointwise (Incidence q t) (8 * q) A Z
        (by simpa [restrictedDegree] using hpoor))
  have hsparse :
      8 * (q : ℝ) * orderedEdges Orthogonal A Z ≤
        (A.card : ℝ) * Z.card := by
    exact_mod_cast hsparseNat
  have hNd : (Fintype.card (P q t) : ℝ) ≤
      2 * (q : ℝ) * d := by
    exact_mod_cast card_points_le_two_mul_q_mul_degree q t ht
  have hvar : (d : ℝ) - c ≤ 2 * (q : ℝ) ^ (t - 1) := by
    have hd : (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
      exact_mod_cast hpar.2.2.2.1
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    linarith
  have hm := card_mul_le_of_sparse_orderedEdges
    (Incidence q t) d c (fun {_ _} h ↦ orthogonal_symm_zmod q t h)
    (card_filter_orthogonal_zmod q t)
    (fun _ _ hxy ↦ card_filter_commonOrthogonal_zmod q t hxy)
    hpar.2.2.2.2 A Z (q : ℝ) (2 * (q : ℝ) ^ (t - 1))
    (by exact_mod_cast (Fact.out : q.Prime).pos)
    (by positivity) hNd hvar hsparse
  calc
    (A.card : ℝ) * Z.card ≤
        256 * (q : ℝ) ^ 2 * (2 * (q : ℝ) ^ (t - 1)) := hm
    _ = 512 * (q : ℝ) ^ (t + 1) := by
      rw [show t + 1 = 2 + (t - 1) by omega, pow_add]
      ring

/-- Natural-number form of `poor_product_le_real`. -/
theorem poor_product_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card) :
    A.card * Z.card ≤ 512 * q ^ (t + 1) := by
  exact_mod_cast poor_product_le_real q t ht A Z hpoor

/-- The actual finite set of points which are poor with respect to `Z`. -/
def poorSet (q t : ℕ) [Fact q.Prime] (Z : Finset (P q t)) : Finset (P q t) :=
  Finset.univ.filter fun a ↦
    8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card

@[simp] theorem mem_poorSet_iff
    (q t : ℕ) [Fact q.Prime] (Z : Finset (P q t)) (a : P q t) :
    a ∈ poorSet q t Z ↔
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card := by
  simp [poorSet]

/-- Product estimate stated for the canonical poor set. -/
theorem poorSet_product_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) (Z : Finset (P q t)) :
    (poorSet q t Z).card * Z.card ≤ 512 * q ^ (t + 1) := by
  apply poor_product_le q t ht
  intro a ha
  exact (mem_poorSet_iff q t Z a).mp ha

/-- A mixed-edge consequence of the poor product estimate.  It is important
that only `|B| ≤ |Z|` is assumed: `B` need not be a subset of `Z`.  A second
application of expander mixing costs only a constant factor. -/
theorem poor_edges_le_real
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z B : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card)
    (hBZ : B.card ≤ Z.card) :
    (orderedEdges (Incidence q t) A B : ℝ) ≤
      2048 * (q : ℝ) ^ t := by
  classical
  let d := degree q t
  let c := codegree q t
  let N : ℝ := Fintype.card (P q t)
  let X : ℝ := (A.card : ℝ) * B.card
  have hpar := design_parameter_bounds q t ht
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast (Fact.out : q.Prime).pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos
  have hNlow : (q : ℝ) ^ t ≤ N := by
    dsimp [N]
    exact_mod_cast hpar.1
  have hd : (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
    exact_mod_cast hpar.2.2.2.1
  have hc : (c : ℝ) ≤ d := by
    exact_mod_cast hpar.2.2.2.2
  have hgap : (d : ℝ) - c ≤ 2 * (q : ℝ) ^ (t - 1) := by
    have : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    linarith
  have hgap0 : (0 : ℝ) ≤ (d : ℝ) - c := sub_nonneg.mpr hc
  have hX0 : 0 ≤ X := by
    dsimp [X]
    positivity
  have hX : X ≤ 512 * (q : ℝ) ^ (t + 1) := by
    dsimp [X]
    have hcast : (B.card : ℝ) ≤ Z.card := by exact_mod_cast hBZ
    calc
      (A.card : ℝ) * B.card ≤ (A.card : ℝ) * Z.card :=
        mul_le_mul_of_nonneg_left hcast (Nat.cast_nonneg _)
      _ ≤ 512 * (q : ℝ) ^ (t + 1) :=
        poor_product_le_real q t ht A Z hpoor
  have hpow : (q : ℝ) ^ t = (q : ℝ) ^ (t - 1) * q := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    rw [pow_succ]
  have hdensity : (d : ℝ) / N ≤ 2 / (q : ℝ) := by
    rw [div_le_div_iff₀ hNpos hqpos]
    calc
      (d : ℝ) * q ≤ (2 * (q : ℝ) ^ (t - 1)) * q :=
        mul_le_mul_of_nonneg_right hd hqpos.le
      _ = 2 * (q : ℝ) ^ t := by rw [hpow]; ring
      _ ≤ 2 * N := mul_le_mul_of_nonneg_left hNlow (by norm_num)
  have hdensity0 : 0 ≤ (d : ℝ) / N := by positivity
  have hexpected : (d : ℝ) / N * X ≤ 1024 * (q : ℝ) ^ t := by
    calc
      (d : ℝ) / N * X ≤ (2 / (q : ℝ)) * X :=
        mul_le_mul_of_nonneg_right hdensity hX0
      _ ≤ (2 / (q : ℝ)) *
          (512 * (q : ℝ) ^ (t + 1)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 1024 * (q : ℝ) ^ t := by
        rw [pow_succ]
        field_simp
        <;> ring
  have hvariance :
      ((d : ℝ) - c) * X ≤ 1024 * (q : ℝ) ^ (2 * t) := by
    calc
      ((d : ℝ) - c) * X ≤
          (2 * (q : ℝ) ^ (t - 1)) *
            (512 * (q : ℝ) ^ (t + 1)) :=
        mul_le_mul hgap hX hX0 (by positivity)
      _ = 1024 * (q : ℝ) ^ (2 * t) := by
        rw [show 2 * t = (t - 1) + (t + 1) by omega, pow_add]
        ring
  have hpowsq : ((q : ℝ) ^ t) ^ 2 = (q : ℝ) ^ (2 * t) := by
    rw [← pow_mul]
    congr 1
    omega
  have hsqrt :
      Real.sqrt (((d : ℝ) - c) * X) ≤ 1024 * (q : ℝ) ^ t := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · calc
        ((d : ℝ) - c) * X ≤ 1024 * (q : ℝ) ^ (2 * t) := hvariance
        _ ≤ (1024 * (q : ℝ) ^ t) ^ 2 := by
          rw [mul_pow, hpowsq]
          have hpow0 : (0 : ℝ) ≤ (q : ℝ) ^ (2 * t) := by positivity
          nlinarith
  have hmix := abs_orderedEdges_sub_expected_le
    (Incidence q t) d c (fun {_ _} h ↦ orthogonal_symm_zmod q t h)
    (card_filter_orthogonal_zmod q t)
    (fun _ _ hxy ↦ card_filter_commonOrthogonal_zmod q t hxy)
    hpar.2.2.2.2 A B
  have hmix' :
      |(orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X| ≤
        Real.sqrt (((d : ℝ) - c) * X) := by
    dsimp [N, X]
    convert hmix using 1 <;> ring
  have hupper :
      (orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X ≤
        Real.sqrt (((d : ℝ) - c) * X) := by
    have habs :
        (orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X ≤
          |(orderedEdges (Incidence q t) A B : ℝ) - (d : ℝ) / N * X| :=
      le_abs_self _
    exact habs.trans hmix'
  have hsum :
      (orderedEdges (Incidence q t) A B : ℝ) ≤
        (d : ℝ) / N * X + Real.sqrt (((d : ℝ) - c) * X) := by
    linarith
  calc
    (orderedEdges (Incidence q t) A B : ℝ) ≤
        (d : ℝ) / N * X + Real.sqrt (((d : ℝ) - c) * X) := hsum
    _ ≤ 1024 * (q : ℝ) ^ t + 1024 * (q : ℝ) ^ t :=
      add_le_add hexpected hsqrt
    _ = 2048 * (q : ℝ) ^ t := by ring

/-- Natural-number form of `poor_edges_le_real`. -/
theorem poor_edges_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (A Z B : Finset (P q t))
    (hpoor : ∀ a ∈ A,
      8 * q * (Z.filter (Incidence q t a)).card ≤ Z.card)
    (hBZ : B.card ≤ Z.card) :
    orderedEdges (Incidence q t) A B ≤ 2048 * q ^ t := by
  exact_mod_cast poor_edges_le_real q t ht A Z B hpoor hBZ

/-- Edge estimate for the canonical poor set. -/
theorem poorSet_edges_le
    (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t)
    (Z B : Finset (P q t)) (hBZ : B.card ≤ Z.card) :
    orderedEdges (Incidence q t) (poorSet q t Z) B ≤ 2048 * q ^ t := by
  apply poor_edges_le q t ht (poorSet q t Z) Z B
  · intro a ha
    exact (mem_poorSet_iff q t Z a).mp ha
  · exact hBZ

end

end Erdos920.DesignAdapter
