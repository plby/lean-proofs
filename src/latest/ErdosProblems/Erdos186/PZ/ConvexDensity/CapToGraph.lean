/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.FiniteCap
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# From a finite direction cap to graph coordinates

This file supplies the deterministic coordinate interface needed after
`FiniteCap`.  It has two complementary parts.

* `representativeToLast` is a genuine orthogonal linear isometry.  For a unit
  vector `v`, it is the Householder reflection which sends `v` to the last
  standard basis vector.
* `capBaseCoordinate`, `capLastCoordinate`, and `capSlope` give the explicit
  coordinate/sign/permutation chart carried by a `DirectionCapIndex`.  Every
  direction in one cap has positive last coordinate in this chart, and its
  base slope differs from the slope of any representative by at most `1/m`
  in every coordinate.

The second description is especially convenient for an upper-boundary graph:
it avoids choosing an orthonormal basis of the representative's perpendicular
space, while retaining the exact `d-1` transverse coordinates.
-/

open Set

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-! ## A genuine orthogonal straightening of one representative -/

/-- The last standard unit vector in dimension `n+1`. -/
def lastBasisVector (n : ℕ) : EuclideanPoint (n + 1) :=
  EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)

@[simp]
theorem norm_lastBasisVector (n : ℕ) : ‖lastBasisVector n‖ = 1 := by
  simp [lastBasisVector]

@[simp]
theorem coordinate_lastBasisVector_last (n : ℕ) :
    coordinate (lastBasisVector n) (Fin.last n) = 1 := by
  simp [lastBasisVector, coordinate]

/-- The Householder reflection in the perpendicular hyperplane to
`v - e_last`.  When `v` is a unit vector this sends `v` to `e_last`. -/
def representativeToLast {n : ℕ} (v : EuclideanPoint (n + 1)) :
    EuclideanPoint (n + 1) ≃ₗᵢ[ℝ] EuclideanPoint (n + 1) :=
  (ℝ ∙ (v - lastBasisVector n)).orthogonal.reflection

theorem representativeToLast_apply {n : ℕ} {v : EuclideanPoint (n + 1)}
    (hv : ‖v‖ = 1) : representativeToLast v v = lastBasisVector n := by
  exact Submodule.reflection_sub (hv.trans (norm_lastBasisVector n).symm)

@[simp]
theorem norm_representativeToLast {n : ℕ} (v x : EuclideanPoint (n + 1)) :
    ‖representativeToLast v x‖ = ‖x‖ :=
  (representativeToLast v).norm_map x

theorem representativeToLast_normalizedDirection {n : ℕ}
    {x : EuclideanPoint (n + 1)} (hx : x ≠ 0) :
    representativeToLast (normalizedDirection x) (normalizedDirection x) =
      lastBasisVector n :=
  representativeToLast_apply (norm_normalizedDirection hx)

/-! ## The explicit sign-corrected dominant-coordinate graph chart -/

/-- The sign multiplier recorded by a cap. -/
def capSign {n m : ℕ} (c : DirectionCapIndex n m) : ℝ :=
  if c.2.1 then 1 else -1

theorem capSign_eq_one_or_neg_one {n m : ℕ} (c : DirectionCapIndex n m) :
    capSign c = 1 ∨ capSign c = -1 := by
  rcases c with ⟨i, b, g⟩
  cases b <;> simp [capSign]

@[simp]
theorem capSign_sq {n m : ℕ} (c : DirectionCapIndex n m) :
    capSign c ^ 2 = 1 := by
  simp [capSign]

/-- The sign-corrected pivot coordinate, regarded as the vertical or last
coordinate of the graph chart. -/
def capLastCoordinate {n m : ℕ} (c : DirectionCapIndex n m)
    (x : EuclideanPoint (n + 1)) : ℝ :=
  capSign c * coordinate x c.1

/-- The sign-corrected non-pivot coordinates.  `c.1.succAbove` enumerates
exactly the `n=d-1` coordinates other than the pivot. -/
def capBaseCoordinate {n m : ℕ} (c : DirectionCapIndex n m)
    (x : EuclideanPoint (n + 1)) : Fin n → ℝ :=
  fun j ↦ capSign c * coordinate x (c.1.succAbove j)

/-- Projective base coordinates in the cap chart. -/
def capSlope {n m : ℕ} (c : DirectionCapIndex n m)
    (x : EuclideanPoint (n + 1)) : Fin n → ℝ :=
  fun j ↦ capBaseCoordinate c x j / capLastCoordinate c x

/-- The explicit pivot-to-last coordinate permutation is a linear isometry.
It is useful when an actual ambient coordinate change, rather than just the
graph chart functions, is required. -/
def pivotToLastIsometry {n : ℕ} (i : Fin (n + 1)) :
    EuclideanPoint (n + 1) ≃ₗᵢ[ℝ] EuclideanPoint (n + 1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i (Fin.last n))

theorem pivotToLastIsometry_last {n : ℕ} (i : Fin (n + 1))
    (x : EuclideanPoint (n + 1)) :
    coordinate (pivotToLastIsometry i x) (Fin.last n) = coordinate x i := by
  classical
  simp [pivotToLastIsometry, coordinate, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

@[simp]
theorem norm_pivotToLastIsometry {n : ℕ} (i : Fin (n + 1))
    (x : EuclideanPoint (n + 1)) :
    ‖pivotToLastIsometry i x‖ = ‖x‖ :=
  (pivotToLastIsometry i).norm_map x

/-- A cap's last coordinate is strictly positive. -/
theorem capLastCoordinate_pos {n m : ℕ} {c : DirectionCapIndex n m}
    {x : EuclideanPoint (n + 1)} (hx : x ∈ directionCap m c) :
    0 < capLastCoordinate c x := by
  rcases c with ⟨i, b, g⟩
  cases b
  · change 0 < -1 * coordinate x i
    have hs : coordinate x i < 0 := hx.2.2.1
    linarith
  · change 0 < 1 * coordinate x i
    have hs : 0 < coordinate x i := hx.2.2.1
    linarith

theorem capLastCoordinate_ne_zero {n m : ℕ} {c : DirectionCapIndex n m}
    {x : EuclideanPoint (n + 1)} (hx : x ∈ directionCap m c) :
    capLastCoordinate c x ≠ 0 :=
  (capLastCoordinate_pos hx).ne'

/-- The signed projective chart is exactly the dominant-coordinate chart:
the common sign cancels from numerator and denominator. -/
theorem capSlope_eq_dominantChart {n m : ℕ} {c : DirectionCapIndex n m}
    {x : EuclideanPoint (n + 1)} (hx : x ∈ directionCap m c) :
    capSlope c x = dominantChart c.1 x := by
  funext j
  rcases c with ⟨i, b, g⟩
  cases b <;>
    simp [capSlope, capBaseCoordinate, capLastCoordinate, capSign, dominantChart]

/-- All directions in one cap have centered base slope at most `1/m` in
every one of the `d-1` base coordinates. -/
theorem capSlope_sub_le_inv {n m : ℕ} (hm : 0 < m)
    {c : DirectionCapIndex n m} {representative x : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hx : x ∈ directionCap m c) (j : Fin n) :
    |capSlope c x j - capSlope c representative j| ≤ (m : ℝ)⁻¹ := by
  rw [capSlope_eq_dominantChart hx,
    capSlope_eq_dominantChart hrepresentative]
  exact directionCap_chart_diameter hm hx hrepresentative j

/-- Every Euclidean coordinate is bounded by the Euclidean norm. -/
theorem abs_coordinate_le_norm {d : ℕ} (x : EuclideanPoint d) (i : Fin d) :
    |coordinate x i| ≤ ‖x‖ := by
  have hi : coordinate x i ^ 2 ≤ ∑ j, coordinate x j ^ 2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (coordinate x j))
      (Finset.mem_univ i)
  rw [← EuclideanSpace.real_norm_sq_eq] at hi
  nlinarith [sq_abs (coordinate x i), abs_nonneg (coordinate x i), norm_nonneg x]

/-- The vertical coordinate of the sign/permutation chart is bounded by the
ambient norm. -/
theorem abs_capLastCoordinate_le_norm {n m : ℕ} (c : DirectionCapIndex n m)
    (x : EuclideanPoint (n + 1)) :
    |capLastCoordinate c x| ≤ ‖x‖ := by
  rcases c with ⟨i, b, g⟩
  cases b <;>
    simpa [capLastCoordinate, capSign, abs_mul] using abs_coordinate_le_norm x i

/-- Base residual after subtracting the representative graph slope. -/
def capBaseResidual {n m : ℕ} (c : DirectionCapIndex n m)
    (representative x : EuclideanPoint (n + 1)) (j : Fin n) : ℝ :=
  capBaseCoordinate c x j -
    capSlope c representative j * capLastCoordinate c x

/-- For a unit vector in the same cap as the representative, every actual
base residual is at most `1/m`.  Thus the centered base projection, not only
its projective slope, is quantitatively small. -/
theorem abs_capBaseResidual_le_inv {n m : ℕ} (hm : 0 < m)
    {c : DirectionCapIndex n m} {representative x : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hx : x ∈ directionCap m c) (hxnorm : ‖x‖ = 1) (j : Fin n) :
    |capBaseResidual c representative x j| ≤ (m : ℝ)⁻¹ := by
  have hlast : capLastCoordinate c x ≠ 0 := capLastCoordinate_ne_zero hx
  have hbase : capBaseCoordinate c x j =
      capSlope c x j * capLastCoordinate c x := by
    simp only [capSlope]
    field_simp
  have hslope := capSlope_sub_le_inv hm hrepresentative hx j
  have hlastBound : |capLastCoordinate c x| ≤ 1 := by
    simpa [hxnorm] using abs_capLastCoordinate_le_norm c x
  rw [capBaseResidual, hbase]
  rw [show capSlope c x j * capLastCoordinate c x -
      capSlope c representative j * capLastCoordinate c x =
      (capSlope c x j - capSlope c representative j) * capLastCoordinate c x by
        ring,
    abs_mul]
  calc
    |capSlope c x j - capSlope c representative j| * |capLastCoordinate c x| ≤
        (m : ℝ)⁻¹ * 1 := by
      gcongr
    _ = (m : ℝ)⁻¹ := mul_one _

/-- Multiplying a vector by a positive scalar does not change its cap
slopes.  This is the link from normalized directions back to points in a
bounded annulus. -/
theorem capSlope_smul {n m : ℕ} (c : DirectionCapIndex n m)
    (t : ℝ) (ht : t ≠ 0) (x : EuclideanPoint (n + 1)) :
    capSlope c (t • x) = capSlope c x := by
  funext j
  simp only [capSlope, capBaseCoordinate, capLastCoordinate, coordinate,
    PiLp.smul_apply, smul_eq_mul]
  rw [show capSign c * (t * WithLp.ofLp x (c.1.succAbove j)) =
      t * (capSign c * WithLp.ofLp x (c.1.succAbove j)) by ring,
    show capSign c * (t * WithLp.ofLp x c.1) =
      t * (capSign c * WithLp.ofLp x c.1) by ring,
    mul_div_mul_left _ _ ht]

/-! ## Pigeonhole output packaged for an upper graph -/

/--
The finite cap theorem with a chosen representative and its graph-chart
consequences exposed.  The points remain in the input annulus; normalized
directions have positive vertical coordinate and lie in a base-slope box of
radius `1/m` about the representative.
-/
theorem exists_large_cap_graph_chart {n m : ℕ} (hm : 0 < m)
    {inner outer : ℝ} (hinner : 0 < inner)
    (X : Finset (EuclideanPoint (n + 1))) (hX : X.Nonempty)
    (hannulus : ∀ x ∈ X, x ∈ boundedAnnulus inner outer) :
    ∃ (c : DirectionCapIndex n m)
      (Y : Finset (EuclideanPoint (n + 1)))
      (representative : EuclideanPoint (n + 1)),
      representative ∈ Y ∧
      Y ⊆ X ∧
      ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * X.card ≤ Y.card ∧
      (∀ y ∈ Y, y ∈ boundedAnnulus inner outer) ∧
      representativeToLast (normalizedDirection representative)
          (normalizedDirection representative) = lastBasisVector n ∧
      (∀ y ∈ Y,
        0 < capLastCoordinate c (normalizedDirection y) ∧
        ∀ j : Fin n,
          |capSlope c (normalizedDirection y) j -
            capSlope c (normalizedDirection representative) j| ≤ (m : ℝ)⁻¹ ∧
          |capBaseResidual c (normalizedDirection representative)
            (normalizedDirection y) j| ≤ (m : ℝ)⁻¹) := by
  obtain ⟨c, Y, hY, hYX, hcard, hann, hcap⟩ :=
    exists_large_direction_cap_mesh_fraction hm hinner X hX hannulus
  obtain ⟨representative, hrepresentative⟩ := hY
  have hrepX : representative ∈ X := hYX hrepresentative
  have hrep0 : representative ≠ 0 :=
    ne_zero_of_mem_boundedAnnulus hinner (hann representative hrepresentative)
  refine ⟨c, Y, representative, hrepresentative, hYX, hcard, hann,
    representativeToLast_normalizedDirection hrep0, ?_⟩
  intro y hy
  have hcapRep := hcap representative hrepresentative
  have hcapY := hcap y hy
  have hy0 : y ≠ 0 :=
    ne_zero_of_mem_boundedAnnulus hinner (hann y hy)
  exact ⟨capLastCoordinate_pos hcapY,
    fun j ↦ ⟨capSlope_sub_le_inv hm hcapRep hcapY j,
      abs_capBaseResidual_le_inv hm hcapRep hcapY (norm_normalizedDirection hy0) j⟩⟩

/-!
## Label-preserving indexed form

The point-valued theorem above uses a finset of points, hence equal points
cannot occur with different labels.  In boundary and incidence applications
the labels are meaningful.  The following theorem performs the finite
pigeonhole directly on an arbitrary source finset `I`; its selected set `J`
is a filter of `I`, never an image under the point map.
-/

/-- Indexed, label-preserving version of `exists_large_cap_graph_chart`.
Repeated values of `x` remain distinct elements of the selected index set. -/
theorem exists_large_indexed_cap_graph_chart
    {ι : Type*} {n m : ℕ} (hm : 0 < m)
    {inner outer : ℝ} (hinner : 0 < inner)
    (I : Finset ι) (hI : I.Nonempty)
    (x : ι → EuclideanPoint (n + 1))
    (hannulus : ∀ i ∈ I, x i ∈ boundedAnnulus inner outer) :
    ∃ (c : DirectionCapIndex n m) (J : Finset ι) (representative : ι),
      representative ∈ J ∧
      J ⊆ I ∧
      ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * I.card ≤ J.card ∧
      (∀ j ∈ J, x j ∈ boundedAnnulus inner outer) ∧
      (∀ j ∈ J,
        normalizedDirection (x j) ∈ directionCap m c) ∧
      representativeToLast (normalizedDirection (x representative))
          (normalizedDirection (x representative)) = lastBasisVector n ∧
      (∀ j ∈ J,
        0 < capLastCoordinate c (normalizedDirection (x j)) ∧
        ∀ k : Fin n,
          |capSlope c (normalizedDirection (x j)) k -
            capSlope c (normalizedDirection (x representative)) k| ≤ (m : ℝ)⁻¹ ∧
          |capBaseResidual c (normalizedDirection (x representative))
            (normalizedDirection (x j)) k| ≤ (m : ℝ)⁻¹) := by
  classical
  let code : ι → DirectionCapIndex n m := fun i ↦
    directionCapCode m hm (normalizedDirection (x i))
  obtain ⟨c, hc⟩ := exists_color_card_le_mul_fiber I code
  let J : Finset ι := I.filter fun i ↦ code i = c
  have hcount : I.card ≤
      (2 * (n + 1) * (2 * m + 1) ^ n) * J.card := by
    simpa only [J, card_directionCapIndex, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hc
  have hconstantPos : 0 < 2 * (n + 1) * (2 * m + 1) ^ n := by positivity
  have hJ : J.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hJempty
    have hIpos : 0 < I.card := Finset.card_pos.mpr hI
    rw [hJempty, Finset.card_empty, mul_zero] at hcount
    omega
  have hcodeReal :
      (I.card : ℝ) / (2 * (n + 1) * (2 * m + 1) ^ n) ≤ (J.card : ℝ) := by
    apply (div_le_iff₀ (by exact_mod_cast hconstantPos)).2
    have hcount' :
        ((I.card : ℝ) ≤
          (2 * (n + 1) * (2 * m + 1) ^ n : ℕ) * J.card) := by
      exact_mod_cast hcount
    simpa [mul_comm] using hcount'
  have hfraction :
      ((((m : ℝ)⁻¹ / 3) ^ n) / (2 * (n + 1))) * I.card ≤ (J.card : ℝ) :=
    (mesh_fraction_le_code_fraction n m hm
      (by positivity : 0 ≤ (I.card : ℝ))).trans hcodeReal
  have hJI : J ⊆ I := Finset.filter_subset _ _
  have hannJ : ∀ j ∈ J, x j ∈ boundedAnnulus inner outer := by
    intro j hj
    exact hannulus j (hJI hj)
  have hcap : ∀ j ∈ J,
      normalizedDirection (x j) ∈ directionCap m c := by
    intro j hj
    have hjI : j ∈ I := hJI hj
    have hx0 : x j ≠ 0 :=
      ne_zero_of_mem_boundedAnnulus hinner (hannulus j hjI)
    have hnormalized0 : normalizedDirection (x j) ≠ 0 :=
      normalizedDirection_ne_zero hx0
    have hj' : j ∈ I.filter fun i ↦ code i = c := by simpa [J] using hj
    have hcode : code j = c := (Finset.mem_filter.mp hj').2
    rw [← hcode]
    exact directionCapCode_spec hm hnormalized0
  obtain ⟨representative, hrepresentative⟩ := hJ
  have hrepI : representative ∈ I := hJI hrepresentative
  have hrep0 : x representative ≠ 0 :=
    ne_zero_of_mem_boundedAnnulus hinner (hannulus representative hrepI)
  refine ⟨c, J, representative, hrepresentative, hJI, hfraction, hannJ, hcap,
    representativeToLast_normalizedDirection hrep0, ?_⟩
  intro j hj
  have hcapRep := hcap representative hrepresentative
  have hcapJ := hcap j hj
  have hxj0 : x j ≠ 0 :=
    ne_zero_of_mem_boundedAnnulus hinner (hannJ j hj)
  exact ⟨capLastCoordinate_pos hcapJ,
    fun k ↦ ⟨capSlope_sub_le_inv hm hcapRep hcapJ k,
      abs_capBaseResidual_le_inv hm hcapRep hcapJ
        (norm_normalizedDirection hxj0) k⟩⟩

end

end Erdos186.PZ.ConvexDensity
