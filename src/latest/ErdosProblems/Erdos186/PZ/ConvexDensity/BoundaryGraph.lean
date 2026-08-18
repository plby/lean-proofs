/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.AxisBoxes

/-!
# Upper boundary graphs of compact convex sets

This file supplies the geometric reduction used in the graph-approximation
part of the Pham--Zakharov density argument.  We split
`EuclideanSpace ℝ (Fin (n + 1))` into its first `n` coordinates and its last
coordinate, take the maximum of every nonempty vertical fibre of a compact
set, and prove the standard boundary and concavity properties of that maximum.

The definitions deliberately use `Fin.castSucc` and `Fin.last`.  This avoids
an abstract, unspecified identification of the two Euclidean spaces and gives simp
lemmas in exactly the coordinate form needed by the later grid argument.
-/

open Set MeasureTheory

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false

noncomputable section

/-! ## Splitting off the last coordinate -/

/-- The first `n` coordinates of a point in dimension `n + 1`. -/
def baseCoordinates {n : ℕ} (z : EuclideanPoint (n + 1)) : EuclideanPoint n :=
  WithLp.toLp 2 (fun i : Fin n ↦ coordinate z i.castSucc)

/-- The last coordinate of a point in dimension `n + 1`. -/
def lastCoordinate {n : ℕ} (z : EuclideanPoint (n + 1)) : ℝ :=
  coordinate z (Fin.last n)

/-- Reassemble a base point and a last coordinate. -/
def appendCoordinate {n : ℕ} (x : EuclideanPoint n) (t : ℝ) :
    EuclideanPoint (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)

@[simp]
theorem coordinate_baseCoordinates {n : ℕ} (z : EuclideanPoint (n + 1))
    (i : Fin n) :
    coordinate (baseCoordinates z) i = coordinate z i.castSucc := by
  rfl

@[simp]
theorem coordinate_appendCoordinate_castSucc {n : ℕ}
    (x : EuclideanPoint n) (t : ℝ) (i : Fin n) :
    coordinate (appendCoordinate x t) i.castSucc = coordinate x i := by
  simp [appendCoordinate, coordinate]

@[simp]
theorem coordinate_appendCoordinate_last {n : ℕ}
    (x : EuclideanPoint n) (t : ℝ) :
    coordinate (appendCoordinate x t) (Fin.last n) = t := by
  simp [appendCoordinate, coordinate]

@[simp]
theorem baseCoordinates_appendCoordinate {n : ℕ}
    (x : EuclideanPoint n) (t : ℝ) :
    baseCoordinates (appendCoordinate x t) = x := by
  ext i
  simp

@[simp]
theorem lastCoordinate_appendCoordinate {n : ℕ}
    (x : EuclideanPoint n) (t : ℝ) :
    lastCoordinate (appendCoordinate x t) = t := by
  exact coordinate_appendCoordinate_last x t

@[simp]
theorem appendCoordinate_baseCoordinates_lastCoordinate {n : ℕ}
    (z : EuclideanPoint (n + 1)) :
    appendCoordinate (baseCoordinates z) (lastCoordinate z) = z := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp [lastCoordinate]

/-- Splitting and reassembling the last coordinate gives an equivalence. -/
def lastCoordinateEquiv (n : ℕ) :
    EuclideanPoint (n + 1) ≃ EuclideanPoint n × ℝ where
  toFun z := (baseCoordinates z, lastCoordinate z)
  invFun p := appendCoordinate p.1 p.2
  left_inv := appendCoordinate_baseCoordinates_lastCoordinate
  right_inv p := by
    ext <;> simp

@[simp]
theorem lastCoordinateEquiv_apply (n : ℕ) (z : EuclideanPoint (n + 1)) :
    lastCoordinateEquiv n z = (baseCoordinates z, lastCoordinate z) :=
  rfl

@[simp]
theorem lastCoordinateEquiv_symm_apply (n : ℕ)
    (p : EuclideanPoint n × ℝ) :
    (lastCoordinateEquiv n).symm p = appendCoordinate p.1 p.2 :=
  rfl

/-- The coordinate split as a continuous linear equivalence.  Internally this
is Mathlib's `Fin n + Fin 1` / product equivalence (`finAddEquivProd`). -/
def lastCoordinateCLE (n : ℕ) :
    EuclideanPoint (n + 1) ≃L[ℝ] EuclideanPoint n × ℝ :=
  (EuclideanSpace.finAddEquivProd (n := n) (m := 1)).trans
    ((ContinuousLinearEquiv.refl ℝ (EuclideanPoint n)).prodCongr
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)))

@[simp]
theorem lastCoordinateCLE_apply (n : ℕ) (z : EuclideanPoint (n + 1)) :
    lastCoordinateCLE n z = (baseCoordinates z, lastCoordinate z) := by
  rfl

@[simp]
theorem lastCoordinateCLE_symm_apply_castSucc {n : ℕ}
    (x : EuclideanPoint n) (t : ℝ) (i : Fin n) :
    coordinate ((lastCoordinateCLE n).symm (x, t)) i.castSucc = coordinate x i := by
  simp [lastCoordinateCLE, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, coordinate]

@[simp]
theorem lastCoordinateCLE_symm_apply_last {n : ℕ}
    (x : EuclideanPoint n) (t : ℝ) :
    coordinate ((lastCoordinateCLE n).symm (x, t)) (Fin.last n) = t := by
  simp [lastCoordinateCLE, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, coordinate]

theorem lastCoordinateCLE_symm_apply {n : ℕ}
    (p : EuclideanPoint n × ℝ) :
    (lastCoordinateCLE n).symm p = appendCoordinate p.1 p.2 := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa [coordinate] using lastCoordinateCLE_symm_apply_last p.1 p.2
  · simpa [coordinate] using lastCoordinateCLE_symm_apply_castSucc p.1 p.2 j

theorem baseCoordinates_add {n : ℕ} (z w : EuclideanPoint (n + 1)) :
    baseCoordinates (z + w) = baseCoordinates z + baseCoordinates w := by
  ext i
  rfl

theorem baseCoordinates_smul {n : ℕ} (a : ℝ)
    (z : EuclideanPoint (n + 1)) :
    baseCoordinates (a • z) = a • baseCoordinates z := by
  ext i
  rfl

theorem lastCoordinate_add {n : ℕ} (z w : EuclideanPoint (n + 1)) :
    lastCoordinate (z + w) = lastCoordinate z + lastCoordinate w := by
  rfl

theorem lastCoordinate_smul {n : ℕ} (a : ℝ)
    (z : EuclideanPoint (n + 1)) :
    lastCoordinate (a • z) = a * lastCoordinate z := by
  rfl

theorem continuous_baseCoordinates {n : ℕ} :
    Continuous (baseCoordinates : EuclideanPoint (n + 1) → EuclideanPoint n) := by
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun (i : Fin n) ↦ PiLp.continuous_apply 2 _ i.castSucc)

theorem continuous_lastCoordinate {n : ℕ} :
    Continuous (lastCoordinate : EuclideanPoint (n + 1) → ℝ) := by
  exact PiLp.continuous_apply 2 _ (Fin.last n)

theorem norm_appendCoordinate_sq {n : ℕ} (x : EuclideanPoint n) (t : ℝ) :
    ‖appendCoordinate x t‖ ^ 2 = ‖x‖ ^ 2 + |t| ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_castSucc]
  simp [appendCoordinate]

@[simp]
theorem norm_appendCoordinate_zero {n : ℕ} (x : EuclideanPoint n) :
    ‖appendCoordinate x 0‖ = ‖x‖ := by
  have hsquare := norm_appendCoordinate_sq x 0
  simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at hsquare
  nlinarith [norm_nonneg (appendCoordinate x 0), norm_nonneg x]

@[simp]
theorem dist_appendCoordinate_same {n : ℕ} (x : EuclideanPoint n) (s t : ℝ) :
    dist (appendCoordinate x s) (appendCoordinate x t) = |s - t| := by
  rw [dist_eq_norm]
  have hsquare : ‖appendCoordinate x s - appendCoordinate x t‖ ^ 2 = |s - t| ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    simp [appendCoordinate]
  nlinarith [norm_nonneg (appendCoordinate x s - appendCoordinate x t), abs_nonneg (s - t)]

/-! ## Compact vertical fibres and their maxima -/

/-- The projection of `P` onto its first `n` coordinates. -/
def projectedBase {n : ℕ} (P : Set (EuclideanPoint (n + 1))) :
    Set (EuclideanPoint n) :=
  baseCoordinates '' P

/-- The part of `P` over the base point `x`. -/
def verticalFiber {n : ℕ} (P : Set (EuclideanPoint (n + 1)))
    (x : EuclideanPoint n) : Set (EuclideanPoint (n + 1)) :=
  P ∩ {z | baseCoordinates z = x}

/-- The set of last-coordinate heights attained by `P` over `x`. -/
def verticalSection {n : ℕ} (P : Set (EuclideanPoint (n + 1)))
    (x : EuclideanPoint n) : Set ℝ :=
  lastCoordinate '' verticalFiber P x

@[simp]
theorem mem_verticalFiber_iff {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    {x : EuclideanPoint n} {z : EuclideanPoint (n + 1)} :
    z ∈ verticalFiber P x ↔ z ∈ P ∧ baseCoordinates z = x :=
  Iff.rfl

@[simp]
theorem mem_verticalSection_iff {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    {x : EuclideanPoint n} {t : ℝ} :
    t ∈ verticalSection P x ↔ appendCoordinate x t ∈ P := by
  constructor
  · rintro ⟨z, ⟨hzP, hzx⟩, rfl⟩
    rw [← hzx, appendCoordinate_baseCoordinates_lastCoordinate]
    exact hzP
  · intro ht
    exact ⟨appendCoordinate x t, ⟨ht, by simp⟩, by simp⟩

theorem mem_projectedBase_iff_verticalFiber_nonempty {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} {x : EuclideanPoint n} :
    x ∈ projectedBase P ↔ (verticalFiber P x).Nonempty := by
  constructor
  · rintro ⟨z, hzP, rfl⟩
    exact ⟨z, hzP, rfl⟩
  · rintro ⟨z, hzP, hzx⟩
    exact ⟨z, hzP, hzx⟩

theorem mem_projectedBase_iff_verticalSection_nonempty {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} {x : EuclideanPoint n} :
    x ∈ projectedBase P ↔ (verticalSection P x).Nonempty := by
  rw [mem_projectedBase_iff_verticalFiber_nonempty]
  constructor
  · exact fun h ↦ h.image lastCoordinate
  · rintro ⟨t, z, hz, rfl⟩
    exact ⟨z, hz⟩

theorem isCompact_verticalFiber {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    (hP : IsCompact P) (x : EuclideanPoint n) :
    IsCompact (verticalFiber P x) := by
  exact hP.inter_right (isClosed_singleton.preimage continuous_baseCoordinates)

theorem isCompact_verticalSection {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    (hP : IsCompact P) (x : EuclideanPoint n) :
    IsCompact (verticalSection P x) :=
  (isCompact_verticalFiber hP x).image continuous_lastCoordinate

private theorem exists_upperBoundaryPoint {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P) :
    ∃ z ∈ verticalFiber P x,
      ∀ w ∈ verticalFiber P x, lastCoordinate w ≤ lastCoordinate z := by
  have hnonempty : (verticalFiber P x).Nonempty :=
    mem_projectedBase_iff_verticalFiber_nonempty.mp hx
  obtain ⟨z, hz, hmax⟩ :=
    (isCompact_verticalFiber hP x).exists_isMaxOn hnonempty
      continuous_lastCoordinate.continuousOn
  exact ⟨z, hz, isMaxOn_iff.mp hmax⟩

/-- The top point of the vertical fibre.  Away from `projectedBase P` it is
defined to be `(x,0)`; all geometric theorems below are restricted to the
projected base. -/
def upperBoundaryPoint {n : ℕ} (P : Set (EuclideanPoint (n + 1)))
    (hP : IsCompact P) (x : EuclideanPoint n) : EuclideanPoint (n + 1) := by
  classical
  exact if hx : x ∈ projectedBase P then
      Classical.choose (exists_upperBoundaryPoint hP hx)
    else
      appendCoordinate x 0

/-- The upper-fibre maximum, as a real-valued function on the base space. -/
def upperBoundaryValue {n : ℕ} (P : Set (EuclideanPoint (n + 1)))
    (hP : IsCompact P) (x : EuclideanPoint n) : ℝ :=
  lastCoordinate (upperBoundaryPoint P hP x)

theorem upperBoundaryPoint_mem_verticalFiber {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P) :
    upperBoundaryPoint P hP x ∈ verticalFiber P x := by
  rw [upperBoundaryPoint, dif_pos hx]
  exact (Classical.choose_spec (exists_upperBoundaryPoint hP hx)).1

theorem upperBoundaryPoint_mem {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P) :
    upperBoundaryPoint P hP x ∈ P :=
  (upperBoundaryPoint_mem_verticalFiber hP hx).1

@[simp]
theorem baseCoordinates_upperBoundaryPoint {n : ℕ}
    (P : Set (EuclideanPoint (n + 1))) (hP : IsCompact P)
    (x : EuclideanPoint n) :
    baseCoordinates (upperBoundaryPoint P hP x) = x := by
  by_cases hx : x ∈ projectedBase P
  · exact (upperBoundaryPoint_mem_verticalFiber hP hx).2
  · simp [upperBoundaryPoint, hx]

@[simp]
theorem appendCoordinate_upperBoundaryValue {n : ℕ}
    (P : Set (EuclideanPoint (n + 1))) (hP : IsCompact P)
    (x : EuclideanPoint n) :
    appendCoordinate x (upperBoundaryValue P hP x) =
      upperBoundaryPoint P hP x := by
  simpa only [upperBoundaryValue, baseCoordinates_upperBoundaryPoint] using
    (appendCoordinate_baseCoordinates_lastCoordinate (upperBoundaryPoint P hP x))

theorem upperBoundaryValue_mem_verticalSection {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P) :
    upperBoundaryValue P hP x ∈ verticalSection P x := by
  rw [mem_verticalSection_iff, appendCoordinate_upperBoundaryValue]
  exact upperBoundaryPoint_mem hP hx

theorem le_upperBoundaryValue {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} {z : EuclideanPoint (n + 1)}
    (hzP : z ∈ P) (hzx : baseCoordinates z = x) :
    lastCoordinate z ≤ upperBoundaryValue P hP x := by
  have hx : x ∈ projectedBase P := ⟨z, hzP, hzx⟩
  rw [upperBoundaryValue, upperBoundaryPoint, dif_pos hx]
  exact (Classical.choose_spec (exists_upperBoundaryPoint hP hx)).2 z ⟨hzP, hzx⟩

theorem height_le_upperBoundaryValue {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} {t : ℝ} (ht : appendCoordinate x t ∈ P) :
    t ≤ upperBoundaryValue P hP x := by
  simpa using le_upperBoundaryValue hP ht (baseCoordinates_appendCoordinate x t)

/-- A point at the maximal height of a fibre is uniquely the boundary point. -/
theorem eq_upperBoundaryPoint_of_mem_of_height_eq {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} {z : EuclideanPoint (n + 1)}
    (_hzP : z ∈ P) (hzx : baseCoordinates z = x)
    (hzheight : lastCoordinate z = upperBoundaryValue P hP x) :
    z = upperBoundaryPoint P hP x := by
  rw [← appendCoordinate_baseCoordinates_lastCoordinate z, hzx, hzheight,
    appendCoordinate_upperBoundaryValue]

/-- Every nonempty compact fibre has a unique point which realizes its
largest last coordinate. -/
theorem existsUnique_upperBoundaryPoint {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P) :
    ∃! z : EuclideanPoint (n + 1),
      z ∈ verticalFiber P x ∧
        ∀ w ∈ verticalFiber P x, lastCoordinate w ≤ lastCoordinate z := by
  refine ⟨upperBoundaryPoint P hP x, ?_, ?_⟩
  · refine ⟨upperBoundaryPoint_mem_verticalFiber hP hx, ?_⟩
    intro w hw
    exact le_upperBoundaryValue hP hw.1 hw.2
  · intro z hz
    have hzu : lastCoordinate z ≤ upperBoundaryValue P hP x :=
      le_upperBoundaryValue hP hz.1.1 hz.1.2
    have huz : upperBoundaryValue P hP x ≤ lastCoordinate z := by
      exact hz.2 (upperBoundaryPoint P hP x)
        (upperBoundaryPoint_mem_verticalFiber hP hx)
    exact eq_upperBoundaryPoint_of_mem_of_height_eq hP hz.1.1 hz.1.2
      (le_antisymm hzu huz)

/-! ## Convexity of the projected base and concavity of the upper graph -/

theorem convex_projectedBase {n : ℕ} {P : Set (EuclideanPoint (n + 1))}
    (hP : Convex ℝ P) : Convex ℝ (projectedBase P) := by
  rintro x ⟨zx, hzxP, rfl⟩ y ⟨zy, hzyP, rfl⟩ a b ha hb hab
  refine ⟨a • zx + b • zy, hP hzxP hzyP ha hb hab, ?_⟩
  simp [baseCoordinates_add, baseCoordinates_smul]

/-- The upper-fibre maximum of a compact convex set is concave on its
projected base. -/
theorem concaveOn_upperBoundaryValue {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hcompact : IsCompact P)
    (hconvex : Convex ℝ P) :
    ConcaveOn ℝ (projectedBase P) (upperBoundaryValue P hcompact) := by
  refine ⟨convex_projectedBase hconvex, ?_⟩
  intro x hx y hy a b ha hb hab
  let zx := upperBoundaryPoint P hcompact x
  let zy := upperBoundaryPoint P hcompact y
  have hzxP : zx ∈ P := upperBoundaryPoint_mem hcompact hx
  have hzyP : zy ∈ P := upperBoundaryPoint_mem hcompact hy
  have hzcomb : a • zx + b • zy ∈ P := hconvex hzxP hzyP ha hb hab
  have hzbase : baseCoordinates (a • zx + b • zy) = a • x + b • y := by
    simp [zx, zy, baseCoordinates_add, baseCoordinates_smul]
  have hmax := le_upperBoundaryValue hcompact hzcomb hzbase
  simpa [zx, zy, upperBoundaryValue, lastCoordinate_add, lastCoordinate_smul,
    smul_eq_mul] using hmax

/-! ## The upper graph is part of the frontier -/

/-- A vertical-fibre maximum of a compact set lies on its topological
frontier.  Convexity is not needed for this fact. -/
theorem upperBoundaryPoint_mem_frontier {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P) :
    upperBoundaryPoint P hP x ∈ frontier P := by
  rw [mem_frontier_iff_notMem_interior (upperBoundaryPoint_mem hP hx)]
  intro hinterior
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hinterior)
  let q := appendCoordinate x (upperBoundaryValue P hP x + ε / 2)
  have hqball : q ∈ Metric.ball (upperBoundaryPoint P hP x) ε := by
    rw [Metric.mem_ball]
    change dist (appendCoordinate x (upperBoundaryValue P hP x + ε / 2))
      (upperBoundaryPoint P hP x) < ε
    rw [← appendCoordinate_upperBoundaryValue P hP x,
      dist_appendCoordinate_same]
    rw [show upperBoundaryValue P hP x + ε / 2 - upperBoundaryValue P hP x =
      ε / 2 by ring, abs_of_pos (half_pos hε)]
    linarith
  have hqP : q ∈ P := hball hqball
  have hqmax : upperBoundaryValue P hP x + ε / 2 ≤
      upperBoundaryValue P hP x := by
    exact height_le_upperBoundaryValue hP hqP
  linarith

/-! ## Range bounds and normalized base regions -/

theorem abs_lastCoordinate_le_norm {n : ℕ} (z : EuclideanPoint (n + 1)) :
    |lastCoordinate z| ≤ ‖z‖ := by
  simpa [lastCoordinate, coordinate, Real.norm_eq_abs] using
    (PiLp.norm_apply_le z (Fin.last n))

/-- An ambient coordinate box gives the corresponding exact bounds on every
vertical section. -/
theorem verticalSection_subset_Icc_of_subset_closedAxisBox {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} {x : EuclideanPoint n}
    {lower upper : Fin (n + 1) → ℝ}
    (hbox : P ⊆ closedAxisBox lower upper) :
    verticalSection P x ⊆
      Set.Icc (lower (Fin.last n)) (upper (Fin.last n)) := by
  intro t ht
  have hz := hbox (mem_verticalSection_iff.mp ht)
  simpa using hz (Fin.last n)

/-- Containment in a centred ball bounds every vertical height in absolute
value. -/
theorem abs_le_of_mem_verticalSection_of_subset_closedBall {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} {x : EuclideanPoint n}
    {t R : ℝ} (hball : P ⊆ Metric.closedBall 0 R)
    (ht : t ∈ verticalSection P x) :
    |t| ≤ R := by
  have hzball := hball (mem_verticalSection_iff.mp ht)
  have hnorm : ‖appendCoordinate x t‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hzball
  have htNorm : |t| ≤ ‖appendCoordinate x t‖ := by
    simpa using abs_lastCoordinate_le_norm (appendCoordinate x t)
  exact htNorm.trans hnorm

theorem upperBoundaryValue_mem_Icc_of_subset_closedAxisBox {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P)
    {lower upper : Fin (n + 1) → ℝ}
    (hbox : P ⊆ closedAxisBox lower upper) :
    upperBoundaryValue P hP x ∈
      Set.Icc (lower (Fin.last n)) (upper (Fin.last n)) :=
  verticalSection_subset_Icc_of_subset_closedAxisBox hbox
    (upperBoundaryValue_mem_verticalSection hP hx)

theorem abs_upperBoundaryValue_le_of_subset_closedBall {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} (hx : x ∈ projectedBase P) {R : ℝ}
    (hball : P ⊆ Metric.closedBall 0 R) :
    |upperBoundaryValue P hP x| ≤ R :=
  abs_le_of_mem_verticalSection_of_subset_closedBall hball
    (upperBoundaryValue_mem_verticalSection hP hx)

/-- A ball contained in `P` guarantees a nonempty vertical section above
every point of the corresponding base ball. -/
theorem closedBall_subset_projectedBase {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} {rho : ℝ}
    (hinner : Metric.closedBall 0 rho ⊆ P) :
    Metric.closedBall (0 : EuclideanPoint n) rho ⊆ projectedBase P := by
  intro x hx
  have hzball : appendCoordinate x 0 ∈
      Metric.closedBall (0 : EuclideanPoint (n + 1)) rho := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  exact ⟨appendCoordinate x 0, hinner hzball, by simp⟩

theorem zero_le_upperBoundaryValue_of_closedBall_subset {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} {rho : ℝ}
    (hinner : Metric.closedBall 0 rho ⊆ P) (hx : ‖x‖ ≤ rho) :
    0 ≤ upperBoundaryValue P hP x := by
  apply height_le_upperBoundaryValue hP
  apply hinner
  simpa [Metric.mem_closedBall, dist_zero_right] using hx

/-- Ball-sandwich range package: over the inner base ball, the roof is
defined, nonnegative, and bounded in absolute value by the outer radius. -/
theorem upperBoundaryValue_bounds_of_ball_sandwich {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} {rho R : ℝ}
    (hinner : Metric.closedBall 0 rho ⊆ P)
    (houter : P ⊆ Metric.closedBall 0 R) (hx : ‖x‖ ≤ rho) :
    0 ≤ upperBoundaryValue P hP x ∧ upperBoundaryValue P hP x ≤ R := by
  have hxbase : x ∈ projectedBase P := closedBall_subset_projectedBase hinner
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hx)
  exact ⟨zero_le_upperBoundaryValue_of_closedBall_subset hP hinner hx,
    (abs_le.mp (abs_upperBoundaryValue_le_of_subset_closedBall hP hxbase houter)).2⟩

/-- The symmetric coordinate box `[-r,r]^d`. -/
def symmetricAxisBox (d : ℕ) (r : ℝ) : Set (EuclideanPoint d) :=
  closedAxisBox (fun _ ↦ -r) (fun _ ↦ r)

@[simp]
theorem mem_symmetricAxisBox_iff {d : ℕ} {r : ℝ} {x : EuclideanPoint d} :
    x ∈ symmetricAxisBox d r ↔ ∀ i, -r ≤ coordinate x i ∧ coordinate x i ≤ r :=
  Iff.rfl

theorem convex_symmetricAxisBox (d : ℕ) (r : ℝ) :
    Convex ℝ (symmetricAxisBox d r) :=
  convex_closedAxisBox (fun _ ↦ -r) (fun _ ↦ r)

/-- A symmetric ambient box contained in `P` projects onto the symmetric base
box with the same coordinate radius. -/
theorem symmetricAxisBox_subset_projectedBase {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} {rho : ℝ} (hrho : 0 ≤ rho)
    (hinner : symmetricAxisBox (n + 1) rho ⊆ P) :
    symmetricAxisBox n rho ⊆ projectedBase P := by
  intro x hx
  refine ⟨appendCoordinate x 0, hinner ?_, by simp⟩
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [hrho]
  · simpa using hx j

/-- Coordinate-box sandwich package.  Over the inner base box, the upper
boundary is attained and lies in the outer vertical interval `[-R,R]`. -/
theorem upperBoundaryValue_mem_Icc_of_axisBox_sandwich {n : ℕ}
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} {rho R : ℝ} (hrho : 0 ≤ rho)
    (hinner : symmetricAxisBox (n + 1) rho ⊆ P)
    (houter : P ⊆ symmetricAxisBox (n + 1) R)
    (hx : x ∈ symmetricAxisBox n rho) :
    upperBoundaryValue P hP x ∈ Set.Icc (-R) R := by
  have hxbase : x ∈ projectedBase P :=
    symmetricAxisBox_subset_projectedBase hrho hinner hx
  simpa [symmetricAxisBox] using
    (upperBoundaryValue_mem_Icc_of_subset_closedAxisBox hP hxbase houter)

/-- Euclidean norm bound for a point in a symmetric coordinate box. -/
theorem norm_le_sqrt_card_mul_of_mem_symmetricAxisBox {n : ℕ}
    {r : ℝ} (hr : 0 ≤ r) {x : EuclideanPoint n}
    (hx : x ∈ symmetricAxisBox n r) :
    ‖x‖ ≤ Real.sqrt (n : ℝ) * r := by
  apply (sq_le_sq₀ (norm_nonneg x)
    (mul_nonneg (Real.sqrt_nonneg _) hr)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin n, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hi := hx i
      change -r ≤ x i ∧ x i ≤ r at hi
      nlinarith [sq_nonneg (x i - r), sq_nonneg (x i + r)]
    _ = (Real.sqrt (n : ℝ) * r) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      simp

/-- The standard axis box inscribed in a Euclidean ball.  Its coordinate
radius is `rho / sqrt n`. -/
theorem inscribedAxisBox_subset_closedBall {n : ℕ} (hn : 0 < n)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    symmetricAxisBox n (rho / Real.sqrt (n : ℝ)) ⊆
      Metric.closedBall (0 : EuclideanPoint n) rho := by
  intro x hx
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hradius : 0 ≤ rho / Real.sqrt (n : ℝ) := div_nonneg hrho hsqrt_pos.le
  have hnorm := norm_le_sqrt_card_mul_of_mem_symmetricAxisBox hradius hx
  have hcancel : Real.sqrt (n : ℝ) * (rho / Real.sqrt (n : ℝ)) = rho := by
    field_simp
  rw [Metric.mem_closedBall, dist_zero_right, ← hcancel]
  exact hnorm

/-- If `P` contains a ball about the origin, all fibres over the standard
inscribed base box are nonempty. -/
theorem inscribedAxisBox_subset_projectedBase {n : ℕ} (hn : 0 < n)
    {P : Set (EuclideanPoint (n + 1))} {rho : ℝ} (hrho : 0 ≤ rho)
    (hinner : Metric.closedBall 0 rho ⊆ P) :
    symmetricAxisBox n (rho / Real.sqrt (n : ℝ)) ⊆ projectedBase P :=
  (inscribedAxisBox_subset_closedBall hn hrho).trans
    (closedBall_subset_projectedBase hinner)

/-- Concavity restricted to the inscribed axis box supplied by an inner
ball.  This is the direct interface expected by the grid approximation. -/
theorem concaveOn_upperBoundaryValue_on_inscribedAxisBox {n : ℕ}
    (hn : 0 < n) {P : Set (EuclideanPoint (n + 1))}
    (hcompact : IsCompact P) (hconvex : Convex ℝ P)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (hinner : Metric.closedBall 0 rho ⊆ P) :
    ConcaveOn ℝ (symmetricAxisBox n (rho / Real.sqrt (n : ℝ)))
      (upperBoundaryValue P hcompact) := by
  exact (concaveOn_upperBoundaryValue hcompact hconvex).subset
    (inscribedAxisBox_subset_projectedBase hn hrho hinner)
    (convex_symmetricAxisBox n (rho / Real.sqrt (n : ℝ)))

/-- Ball-sandwich bounds stated on the axis box used in the grid argument. -/
theorem upperBoundaryValue_bounds_on_inscribedAxisBox {n : ℕ} (hn : 0 < n)
    {P : Set (EuclideanPoint (n + 1))} (hP : IsCompact P)
    {x : EuclideanPoint n} {rho R : ℝ} (hrho : 0 ≤ rho)
    (hinner : Metric.closedBall 0 rho ⊆ P)
    (houter : P ⊆ Metric.closedBall 0 R)
    (hx : x ∈ symmetricAxisBox n (rho / Real.sqrt (n : ℝ))) :
    0 ≤ upperBoundaryValue P hP x ∧ upperBoundaryValue P hP x ≤ R := by
  have hxball := inscribedAxisBox_subset_closedBall hn hrho hx
  have hxnorm : ‖x‖ ≤ rho := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hxball
  exact upperBoundaryValue_bounds_of_ball_sandwich hP hinner houter hxnorm

end

end Erdos186.PZ.ConvexDensity
