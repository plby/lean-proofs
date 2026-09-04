import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Analysis.Normed.Module.FiniteDimension
import ErdosProblems.Erdos76.Fractional

/-!
# Finite fractional packing/covering duality

This file derives the finite nonnegative matrix packing/covering duality needed by the
fractional layer of Erdős Problem 76.  The proof is a direct application of Sion's minimax
theorem to the two standard simplices.  It avoids introducing a simplex algorithm or a
polyhedral closedness theorem.
-/

open Set
open scoped Matrix

noncomputable section

namespace Erdos76
namespace LPDuality

variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

/-- Every finite real matrix game has a pair of optimal mixed strategies.  The first player
minimizes and the second player maximizes. -/
theorem matrix_game_saddle (A : Matrix I J ℝ) :
    ∃ p ∈ stdSimplex ℝ J, ∃ q ∈ stdSimplex ℝ I,
      ∀ p' ∈ stdSimplex ℝ J, ∀ q' ∈ stdSimplex ℝ I,
        Matrix.toLinearMap₂' ℝ A q' p ≤ Matrix.toLinearMap₂' ℝ A q p ∧
          Matrix.toLinearMap₂' ℝ A q p ≤ Matrix.toLinearMap₂' ℝ A q p' := by
  classical
  let B : (I → ℝ) →ₗ[ℝ] (J → ℝ) →ₗ[ℝ] ℝ := Matrix.toLinearMap₂' ℝ A
  let f : (J → ℝ) → (I → ℝ) → ℝ := fun p q ↦ B q p
  have hXne : (stdSimplex ℝ J).Nonempty :=
    ⟨Pi.single (Classical.arbitrary J) 1, single_mem_stdSimplex ℝ _⟩
  have hYne : (stdSimplex ℝ I).Nonempty :=
    ⟨Pi.single (Classical.arbitrary I) 1, single_mem_stdSimplex ℝ _⟩
  have hfy : ∀ q ∈ stdSimplex ℝ I,
      LowerSemicontinuousOn (fun p : J → ℝ ↦ f p q) (stdSimplex ℝ J) := by
    intro q _hq
    exact (B q).continuous_of_finiteDimensional.lowerSemicontinuous.lowerSemicontinuousOn _
  have hfy' : ∀ q ∈ stdSimplex ℝ I,
      QuasiconvexOn ℝ (stdSimplex ℝ J) (fun p ↦ f p q) := by
    intro q _hq
    exact (B q).convexOn (convex_stdSimplex ℝ J) |>.quasiconvexOn
  have hfx : ∀ p ∈ stdSimplex ℝ J,
      UpperSemicontinuousOn (fun q : I → ℝ ↦ f p q) (stdSimplex ℝ I) := by
    intro p _hp
    exact (B.flip p).continuous_of_finiteDimensional.upperSemicontinuous.upperSemicontinuousOn _
  have hfx' : ∀ p ∈ stdSimplex ℝ J,
      QuasiconcaveOn ℝ (stdSimplex ℝ I) (fun q ↦ f p q) := by
    intro p _hp
    exact (B.flip p).concaveOn (convex_stdSimplex ℝ I) |>.quasiconcaveOn
  obtain ⟨p, hp, q, hq, hpq⟩ := Sion.exists_isSaddlePointOn
    hXne (convex_stdSimplex ℝ J) (isCompact_stdSimplex ℝ J)
    hfy hfy' (convex_stdSimplex ℝ I) hYne (isCompact_stdSimplex ℝ I)
    hfx hfx'
  refine ⟨p, hp, q, hq, ?_⟩
  intro p' hp' q' hq'
  constructor
  · simpa [f, B] using hpq p hp q' hq'
  · simpa [f, B] using hpq p' hp' q hq

/-- A positive saddle value rescales the two optimal mixed strategies to a feasible fractional
packing and a feasible fractional cover of the same total weight. -/
theorem primal_dual_of_positive_saddle (A : Matrix I J ℝ)
    (p : J → ℝ) (hp : p ∈ stdSimplex ℝ J)
    (q : I → ℝ) (hq : q ∈ stdSimplex ℝ I)
    (hsaddle : ∀ p' ∈ stdSimplex ℝ J, ∀ q' ∈ stdSimplex ℝ I,
      Matrix.toLinearMap₂' ℝ A q' p ≤ Matrix.toLinearMap₂' ℝ A q p ∧
        Matrix.toLinearMap₂' ℝ A q p ≤ Matrix.toLinearMap₂' ℝ A q p')
    (hv : 0 < Matrix.toLinearMap₂' ℝ A q p) :
    ∃ x : J → ℝ, ∃ y : I → ℝ,
      (∀ j, 0 ≤ x j) ∧ (∀ i, (A *ᵥ x) i ≤ 1) ∧
      (∀ i, 0 ≤ y i) ∧ (∀ j, 1 ≤ (y ᵥ* A) j) ∧
      ∑ j, x j = ∑ i, y i := by
  classical
  let v := Matrix.toLinearMap₂' ℝ A q p
  let x : J → ℝ := fun j ↦ p j / v
  let y : I → ℝ := fun i ↦ q i / v
  have hload (i : I) : (A *ᵥ p) i ≤ v := by
    have h := (hsaddle p hp (Pi.single i 1) (single_mem_stdSimplex ℝ i)).1
    simpa [v, Matrix.toLinearMap₂'_apply', single_one_dotProduct] using h
  have hcover (j : J) : v ≤ (q ᵥ* A) j := by
    have h := (hsaddle (Pi.single j 1) (single_mem_stdSimplex ℝ j) q hq).2
    simpa [v, Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec, dotProduct_single_one,
      Matrix.vecMul, Matrix.col_apply'] using h
  refine ⟨x, y, fun j ↦ div_nonneg (hp.1 j) hv.le,
    fun i ↦ ?_, fun i ↦ div_nonneg (hq.1 i) hv.le, fun j ↦ ?_, ?_⟩
  · have hx : x = v⁻¹ • p := by
      ext j
      simp [x, div_eq_mul_inv, mul_comm]
    rw [hx, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    calc
      v⁻¹ * (A *ᵥ p) i ≤ v⁻¹ * v :=
        mul_le_mul_of_nonneg_left (hload i) (inv_nonneg.2 hv.le)
      _ = 1 := inv_mul_cancel₀ hv.ne'
  · have hy : y = v⁻¹ • q := by
      ext i
      simp [y, div_eq_mul_inv, mul_comm]
    rw [hy, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
    calc
      1 = v⁻¹ * v := (inv_mul_cancel₀ hv.ne').symm
      _ ≤ v⁻¹ * (q ᵥ* A) j :=
        mul_le_mul_of_nonneg_left (hcover j) (inv_nonneg.2 hv.le)
  · simp only [x, y, div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hp.2, hq.2]

/-- It is enough for one mixed row strategy to give every column strictly positive payoff in
order to know that the saddle value is positive. -/
theorem saddle_value_pos_of_positive_mixed_row (A : Matrix I J ℝ)
    (p : J → ℝ) (hp : p ∈ stdSimplex ℝ J)
    (q : I → ℝ) (hq : q ∈ stdSimplex ℝ I)
    (hsaddle : ∀ p' ∈ stdSimplex ℝ J, ∀ q' ∈ stdSimplex ℝ I,
      Matrix.toLinearMap₂' ℝ A q' p ≤ Matrix.toLinearMap₂' ℝ A q p ∧
        Matrix.toLinearMap₂' ℝ A q p ≤ Matrix.toLinearMap₂' ℝ A q p')
    (q₀ : I → ℝ) (hq₀ : q₀ ∈ stdSimplex ℝ I)
    (hq₀A : ∀ j, 0 < (q₀ ᵥ* A) j) :
    0 < Matrix.toLinearMap₂' ℝ A q p := by
  classical
  have hp_pos : ∃ j, 0 < p j := by
    by_contra! h
    have hp_zero : ∀ j, p j = 0 := fun j ↦ (h j).antisymm (hp.1 j)
    have : ∑ j, p j = 0 := by simp [hp_zero]
    linarith [hp.2]
  obtain ⟨j, hj⟩ := hp_pos
  have hpositive : 0 < Matrix.toLinearMap₂' ℝ A q₀ p := by
    rw [Matrix.toLinearMap₂'_apply', Matrix.dotProduct_mulVec, dotProduct]
    exact Finset.sum_pos'
      (fun k _ ↦ mul_nonneg (hq₀A k).le (hp.1 k))
      ⟨j, Finset.mem_univ _, mul_pos (hq₀A j) hj⟩
  exact hpositive.trans_le ((hsaddle p hp q₀ hq₀).1)

/-- Strong finite packing/covering duality for a matrix admitting a strictly positive mixed row.
The witnesses have equal total weight. -/
theorem matrix_fractional_matching_cover (A : Matrix I J ℝ)
    (q₀ : I → ℝ) (hq₀ : q₀ ∈ stdSimplex ℝ I)
    (hq₀A : ∀ j, 0 < (q₀ ᵥ* A) j) :
    ∃ x : J → ℝ, ∃ y : I → ℝ,
      (∀ j, 0 ≤ x j) ∧ (∀ i, (A *ᵥ x) i ≤ 1) ∧
      (∀ i, 0 ≤ y i) ∧ (∀ j, 1 ≤ (y ᵥ* A) j) ∧
      ∑ j, x j = ∑ i, y i := by
  obtain ⟨p, hp, q, hq, hsaddle⟩ := matrix_game_saddle A
  exact primal_dual_of_positive_saddle A p hp q hq hsaddle
    (saddle_value_pos_of_positive_mixed_row A p hp q hq hsaddle q₀ hq₀ hq₀A)

/-- If every matrix entry is nonnegative and every column has a positive entry, the barycenter of
the row simplex is a strictly positive mixed row. -/
theorem matrix_fractional_matching_cover_of_column_pos (A : Matrix I J ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hcol : ∀ j, ∃ i, 0 < A i j) :
    ∃ x : J → ℝ, ∃ y : I → ℝ,
      (∀ j, 0 ≤ x j) ∧ (∀ i, (A *ᵥ x) i ≤ 1) ∧
      (∀ i, 0 ≤ y i) ∧ (∀ j, 1 ≤ (y ᵥ* A) j) ∧
      ∑ j, x j = ∑ i, y i := by
  classical
  let q₀ : I → ℝ := (stdSimplex.barycenter : stdSimplex ℝ I).val
  apply matrix_fractional_matching_cover A q₀ (stdSimplex.barycenter : stdSimplex ℝ I).prop
  intro j
  rw [Matrix.vecMul, dotProduct]
  obtain ⟨i, hi⟩ := hcol j
  apply Finset.sum_pos'
  · intro k _hk
    exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (hA k j)
  · refine ⟨i, Finset.mem_univ _, mul_pos ?_ hi⟩
    exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

omit [Nonempty I] [Nonempty J] [DecidableEq I] [DecidableEq J] in
/-- Weak packing/covering duality.  This identifies the equal witnesses above as simultaneous
optima without defining suprema or infima. -/
theorem weak_fractional_matching_cover_duality (A : Matrix I J ℝ)
    (x : J → ℝ) (y : I → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hload : ∀ i, (A *ᵥ x) i ≤ 1)
    (hy : ∀ i, 0 ≤ y i) (hcover : ∀ j, 1 ≤ (y ᵥ* A) j) :
    ∑ j, x j ≤ ∑ i, y i := by
  classical
  calc
    ∑ j, x j ≤ ∑ j, (y ᵥ* A) j * x j := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa using mul_le_mul_of_nonneg_right (hcover j) (hx j)
    _ = y ⬝ᵥ (A *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec]
      rfl
    _ ≤ ∑ i, y i := by
      simp only [dotProduct]
      apply Finset.sum_le_sum
      intro i _hi
      simpa using mul_le_mul_of_nonneg_left (hload i) (hy i)

section TriangleIncidence

variable {α : Type*} [Fintype α] [DecidableEq α]

attribute [local instance] Classical.propDecidable

/-- The finite type of edges of `G`, used as the row index of its triangle-incidence
matrix. -/
abbrev EdgeIndex (G : SimpleGraph α) := {e : Sym2 α // e ∈ G.edgeSet}

/-- The finite type of triangles of `G`, used as the column index of its
triangle-incidence matrix. -/
abbrev TriangleIndex (G : SimpleGraph α) := {t : Finset α // G.IsNClique 3 t}

noncomputable instance triangleIndexFintype (G : SimpleGraph α) : Fintype (TriangleIndex G) :=
  Fintype.ofFinite _

/-- The edge-versus-triangle incidence matrix of a finite simple graph. -/
noncomputable def triangleIncidenceMatrix (G : SimpleGraph α) :
    Matrix (EdgeIndex G) (TriangleIndex G) ℝ := by
  classical
  exact fun e t ↦ if e.val ∈ t.val.sym2 then 1 else 0

/-- Extend a vector indexed by the triangles of `G` by zero to all finite vertex sets. -/
noncomputable def triangleWeight (G : SimpleGraph α)
    (x : TriangleIndex G → ℝ) : Finset α → ℝ := by
  classical
  exact fun t ↦ if ht : G.IsNClique 3 t then x ⟨t, ht⟩ else 0

/-- Extend a vector indexed by the edges of `G` by zero to all unordered pairs. -/
noncomputable def edgeCoverWeight (G : SimpleGraph α)
    (y : EdgeIndex G → ℝ) : Sym2 α → ℝ := by
  classical
  exact fun e ↦ if he : e ∈ G.edgeSet then y ⟨e, he⟩ else 0

@[simp] lemma triangleWeight_index (G : SimpleGraph α) (x : TriangleIndex G → ℝ)
    (t : TriangleIndex G) : triangleWeight G x t.val = x t := by
  classical
  rw [triangleWeight, dif_pos t.property]

@[simp] lemma edgeCoverWeight_index (G : SimpleGraph α) (y : EdgeIndex G → ℝ)
    (e : EdgeIndex G) : edgeCoverWeight G y e.val = y e := by
  classical
  rw [edgeCoverWeight, dif_pos e.property]

lemma triangleIncidence_mulVec_apply (G : SimpleGraph α) (x : TriangleIndex G → ℝ)
    (e : EdgeIndex G) :
    (triangleIncidenceMatrix G *ᵥ x) e =
      fractionalEdgeLoad G (triangleWeight G x) e.val := by
  classical
  rw [Matrix.mulVec, dotProduct, fractionalEdgeLoad]
  calc
    ∑ i, triangleIncidenceMatrix G e i * x i =
        ∑ i : TriangleIndex G,
          (if e.val ∈ i.val.sym2 then 1 else 0) * triangleWeight G x i.val := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [triangleWeight_index]
      rfl
    _ = ∑ t ∈ G.cliqueFinset 3,
          (if e.val ∈ t.sym2 then 1 else 0) * triangleWeight G x t :=
      (Finset.sum_subtype (G.cliqueFinset 3)
        (fun t ↦ SimpleGraph.mem_cliqueFinset_iff)
        (fun t ↦ (if e.val ∈ t.sym2 then 1 else 0) * triangleWeight G x t)).symm
    _ = ∑ t ∈ G.cliqueFinset 3 with e.val ∈ t.sym2, triangleWeight G x t := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _ht
      by_cases het : e.val ∈ t.sym2 <;> simp [het]

lemma triangleIncidence_vecMul_apply (G : SimpleGraph α) (y : EdgeIndex G → ℝ)
    (t : TriangleIndex G) :
    (y ᵥ* triangleIncidenceMatrix G) t =
      ∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.val.sym2), edgeCoverWeight G y e := by
  classical
  rw [Matrix.vecMul, dotProduct]
  calc
    ∑ i, y i * triangleIncidenceMatrix G i t =
        ∑ i : EdgeIndex G,
          edgeCoverWeight G y i.val * (if i.val ∈ t.val.sym2 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [edgeCoverWeight_index]
      rfl
    _ = ∑ e ∈ G.edgeFinset,
          edgeCoverWeight G y e * (if e ∈ t.val.sym2 then 1 else 0) :=
      (Finset.sum_subtype G.edgeFinset
        (fun e ↦ SimpleGraph.mem_edgeFinset)
        (fun e ↦ edgeCoverWeight G y e * (if e ∈ t.val.sym2 then 1 else 0))).symm
    _ = ∑ e ∈ G.edgeFinset with e ∈ t.val.sym2, edgeCoverWeight G y e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases het : e ∈ t.val.sym2 <;> simp [het]

lemma triangleWeight_fractionalSize (G : SimpleGraph α) (x : TriangleIndex G → ℝ) :
    fractionalSize G (triangleWeight G x) = ∑ t, x t := by
  classical
  calc
    fractionalSize G (triangleWeight G x) =
        ∑ t ∈ G.cliqueFinset 3, triangleWeight G x t := rfl
    _ = ∑ t : TriangleIndex G, triangleWeight G x t.val :=
      Finset.sum_subtype (G.cliqueFinset 3)
        (fun t ↦ SimpleGraph.mem_cliqueFinset_iff) (triangleWeight G x)
    _ = ∑ t, x t := Finset.sum_congr rfl (fun t _ ↦ triangleWeight_index G x t)

lemma edgeCoverWeight_sum (G : SimpleGraph α) (y : EdgeIndex G → ℝ) :
    ∑ e ∈ G.edgeFinset, edgeCoverWeight G y e = ∑ e, y e := by
  classical
  calc
    ∑ e ∈ G.edgeFinset, edgeCoverWeight G y e =
        ∑ e : EdgeIndex G, edgeCoverWeight G y e.val :=
      Finset.sum_subtype G.edgeFinset
        (fun e ↦ SimpleGraph.mem_edgeFinset) (edgeCoverWeight G y)
    _ = ∑ e, y e := Finset.sum_congr rfl (fun e _ ↦ edgeCoverWeight_index G y e)

/-- Every triangle column of the incidence matrix contains an entry equal to one. -/
lemma triangleIncidenceMatrix_exists_one (G : SimpleGraph α) (t : TriangleIndex G) :
    ∃ e : EdgeIndex G, triangleIncidenceMatrix G e t = 1 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ht⟩ := Finset.card_eq_three.mp t.property.card_eq
  have ha : a ∈ t.val := by simp [ht]
  have hb : b ∈ t.val := by simp [ht]
  have hadj : G.Adj a b := t.property.isClique ha hb hab
  let e : EdgeIndex G := ⟨s(a, b), (SimpleGraph.mem_edgeSet G).mpr hadj⟩
  refine ⟨e, ?_⟩
  simp [triangleIncidenceMatrix, e, ha, hb]

/-- A finite graph has a feasible fractional triangle packing and a feasible fractional
edge cover of exactly the same total weight.  The packing is expressed using the definitions
from `Erdos76.Fractional`; the cover assigns nonnegative weights to graph edges and gives every
triangle total incident-edge weight at least one. -/
theorem exists_fractional_triangle_packing_edge_cover (G : SimpleGraph α) :
    ∃ w : Finset α → ℝ, ∃ z : Sym2 α → ℝ,
      IsFractionalPacking G w ∧
      (∀ e ∈ G.edgeFinset, 0 ≤ z e) ∧
      (∀ t ∈ G.cliqueFinset 3,
        1 ≤ ∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.sym2), z e) ∧
      fractionalSize G w = ∑ e ∈ G.edgeFinset, z e := by
  classical
  by_cases htri : (G.cliqueFinset 3).Nonempty
  · let : Nonempty (TriangleIndex G) :=
      ⟨⟨htri.choose, SimpleGraph.mem_cliqueFinset_iff.mp htri.choose_spec⟩⟩
    let : Nonempty (EdgeIndex G) := by
      obtain ⟨e, _he⟩ := triangleIncidenceMatrix_exists_one G
        (Classical.arbitrary (TriangleIndex G))
      exact ⟨e⟩
    obtain ⟨x, y, hx, hload, hy, hcover, hxy⟩ :=
      matrix_fractional_matching_cover_of_column_pos (triangleIncidenceMatrix G)
        (by
          intro e t
          by_cases h : e.val ∈ t.val.sym2 <;> simp [triangleIncidenceMatrix, h])
        (by
          intro t
          obtain ⟨e, he⟩ := triangleIncidenceMatrix_exists_one G t
          exact ⟨e, he ▸ zero_lt_one⟩)
    refine ⟨triangleWeight G x, edgeCoverWeight G y, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro t ht
        have ht' : G.IsNClique 3 t := SimpleGraph.mem_cliqueFinset_iff.mp ht
        simpa [triangleWeight, ht'] using hx ⟨t, ht'⟩
      · intro e he
        let e' : EdgeIndex G := ⟨e, SimpleGraph.mem_edgeFinset.mp he⟩
        rw [← triangleIncidence_mulVec_apply G x e']
        exact hload e'
    · intro e he
      let e' : EdgeIndex G := ⟨e, SimpleGraph.mem_edgeFinset.mp he⟩
      rw [show edgeCoverWeight G y e = y e' from edgeCoverWeight_index G y e']
      exact hy e'
    · intro t ht
      let t' : TriangleIndex G := ⟨t, SimpleGraph.mem_cliqueFinset_iff.mp ht⟩
      rw [← triangleIncidence_vecMul_apply G y t']
      exact hcover t'
    · rw [triangleWeight_fractionalSize, edgeCoverWeight_sum]
      exact hxy
  · refine ⟨fun _ ↦ 0, fun _ ↦ 0, isFractionalPacking_zero G, ?_, ?_, ?_⟩
    · simp
    · intro t ht
      exact (htri ⟨t, ht⟩).elim
    · simp

/-- Feasibility for the LP dual to fractional triangle packing: edge weights are nonnegative
and each triangle receives total weight at least one from its three edges. -/
def IsFractionalEdgeCover (G : SimpleGraph α) (z : Sym2 α → ℝ) : Prop :=
  (∀ e ∈ G.edgeFinset, 0 ≤ z e) ∧
    ∀ t ∈ G.cliqueFinset 3,
      1 ≤ ∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.sym2), z e

/-- Specialized weak duality: every feasible fractional triangle packing has weight at most
every feasible fractional edge cover. -/
theorem fractionalSize_le_edgeCover_sum (G : SimpleGraph α)
    (u : Finset α → ℝ) (z : Sym2 α → ℝ)
    (hu : IsFractionalPacking G u) (hz : IsFractionalEdgeCover G z) :
    fractionalSize G u ≤ ∑ e ∈ G.edgeFinset, z e := by
  classical
  let x : TriangleIndex G → ℝ := fun t ↦ u t.val
  let y : EdgeIndex G → ℝ := fun e ↦ z e.val
  have hx : ∀ t, 0 ≤ x t := by
    intro t
    exact hu.1 t.val (SimpleGraph.mem_cliqueFinset_iff.mpr t.property)
  have hload : ∀ e, (triangleIncidenceMatrix G *ᵥ x) e ≤ 1 := by
    intro e
    rw [triangleIncidence_mulVec_apply]
    calc
      fractionalEdgeLoad G (triangleWeight G x) e.val =
          fractionalEdgeLoad G u e.val := by
        simp only [fractionalEdgeLoad]
        apply Finset.sum_congr rfl
        intro t ht
        have ht' : G.IsNClique 3 t :=
          SimpleGraph.mem_cliqueFinset_iff.mp (Finset.mem_filter.mp ht).1
        simp [triangleWeight, x, ht']
      _ ≤ 1 := hu.2 e.val (SimpleGraph.mem_edgeFinset.mpr e.property)
  have hy : ∀ e, 0 ≤ y e := by
    intro e
    exact hz.1 e.val (SimpleGraph.mem_edgeFinset.mpr e.property)
  have hcover : ∀ t, 1 ≤ (y ᵥ* triangleIncidenceMatrix G) t := by
    intro t
    rw [triangleIncidence_vecMul_apply]
    calc
      1 ≤ ∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.val.sym2), z e :=
        hz.2 t.val (SimpleGraph.mem_cliqueFinset_iff.mpr t.property)
      _ = ∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.val.sym2), edgeCoverWeight G y e := by
        apply Finset.sum_congr rfl
        intro e he
        have he' : e ∈ G.edgeSet :=
          SimpleGraph.mem_edgeFinset.mp (Finset.mem_filter.mp he).1
        simp [edgeCoverWeight, y, he']
  calc
    fractionalSize G u = ∑ t, x t :=
      Finset.sum_subtype (G.cliqueFinset 3)
        (fun t ↦ SimpleGraph.mem_cliqueFinset_iff) u
    _ ≤ ∑ e, y e := weak_fractional_matching_cover_duality
      (triangleIncidenceMatrix G) x y hx hload hy hcover
    _ = ∑ e ∈ G.edgeFinset, z e :=
      (Finset.sum_subtype G.edgeFinset
        (fun e ↦ SimpleGraph.mem_edgeFinset) z).symm

/-- Strong graph-specific LP duality, including attainment on both sides: the returned packing
maximizes `fractionalSize`, the returned edge cover minimizes its total edge weight, and the two
optimal values are equal. -/
theorem exists_optimal_fractional_triangle_packing_edge_cover (G : SimpleGraph α) :
    ∃ w : Finset α → ℝ, ∃ z : Sym2 α → ℝ,
      IsFractionalPacking G w ∧ IsFractionalEdgeCover G z ∧
      fractionalSize G w = ∑ e ∈ G.edgeFinset, z e ∧
      (∀ u : Finset α → ℝ, IsFractionalPacking G u →
        fractionalSize G u ≤ fractionalSize G w) ∧
      (∀ q : Sym2 α → ℝ, IsFractionalEdgeCover G q →
        (∑ e ∈ G.edgeFinset, z e) ≤ ∑ e ∈ G.edgeFinset, q e) := by
  obtain ⟨w, z, hw, hznonneg, hzcover, hwz⟩ :=
    exists_fractional_triangle_packing_edge_cover G
  have hz : IsFractionalEdgeCover G z := ⟨hznonneg, hzcover⟩
  refine ⟨w, z, hw, hz, hwz, ?_, ?_⟩
  · intro u hu
    calc
      fractionalSize G u ≤ ∑ e ∈ G.edgeFinset, z e :=
        fractionalSize_le_edgeCover_sum G u z hu hz
      _ = fractionalSize G w := hwz.symm
  · intro q hq
    calc
      (∑ e ∈ G.edgeFinset, z e) = fractionalSize G w := hwz.symm
      _ ≤ ∑ e ∈ G.edgeFinset, q e :=
        fractionalSize_le_edgeCover_sum G w q hw hq

/-- The fractional triangle-packing LP of every finite simple graph attains its maximum. -/
theorem exists_maximal_fractional_triangle_packing (G : SimpleGraph α) :
    ∃ w : Finset α → ℝ, IsFractionalPacking G w ∧
      ∀ u : Finset α → ℝ, IsFractionalPacking G u →
        fractionalSize G u ≤ fractionalSize G w := by
  obtain ⟨w, _z, hw, _hz, _hwz, hwmax, _hzmin⟩ :=
    exists_optimal_fractional_triangle_packing_edge_cover G
  exact ⟨w, hw, hwmax⟩

/-- The sum of the red and blue fractional covered-size objectives attains its maximum.  This is
the expression called `twoColorCoveredSize` in `GruslysLetzter.lean`; it is stated by expansion
here so that the GL development can import this foundational LP module without an import cycle. -/
theorem exists_maximal_twoColor_fractionalCoveredSize (G : SimpleGraph α) :
    ∃ wR wB : Finset α → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
      ∀ uR uB : Finset α → ℝ,
        IsFractionalPacking G uR → IsFractionalPacking Gᶜ uB →
        fractionalCoveredSize G uR + fractionalCoveredSize Gᶜ uB ≤
          fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB := by
  obtain ⟨wR, hwR, hwRmax⟩ := exists_maximal_fractional_triangle_packing G
  obtain ⟨wB, hwB, hwBmax⟩ := exists_maximal_fractional_triangle_packing Gᶜ
  refine ⟨wR, wB, hwR, hwB, ?_⟩
  intro uR uB huR huB
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hwRmax uR huR) (by norm_num)
  · exact mul_le_mul_of_nonneg_left (hwBmax uB huB) (by norm_num)

end TriangleIncidence

end LPDuality
end Erdos76
