import ErdosProblems.Erdos957.HullOrder

/-!
# Cyclic exterior-angle bookkeeping for Erdős 957

This file isolates the non-geometric part of the familiar fact that the
exterior angles of a counterclockwise convex polygon sum to `2 * π`.

The geometry supplies a *lift* of the directions of the `m` cyclic edges,
represented here by a total sequence `angle : ℕ → ℝ` whose relevant segment
is `0, ..., m`.  Thus `angle m` is a second representative of the direction
of edge zero, one full turn beyond `angle 0`.  Consecutive differences are
the exterior turns.  Under those concrete hypotheses, the sum theorem is
just a finite telescoping identity; no topology or choice of principal
arguments remains hidden in the statement.

`CyclicPolygonAngleData` also records the bridge to actual planar vertices:
the edge from vertex `i` to its cyclic successor is a positive multiple of
the unit vector with direction `angle i`.  Constructing this data from a
strictly convex cyclic enumeration is the separate geometric lifting step.
-/

namespace Erdos957TurnSum

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The unit planar vector at real angle `θ`. -/
noncomputable def unitDirection (θ : ℝ) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i => if i = 0 then Real.cos θ else Real.sin θ)

/-- Oriented area (the two-dimensional determinant). -/
noncomputable def det (x y : Plane) : ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ x) 0 *
      (EuclideanSpace.equiv (Fin 2) ℝ y) 1 -
    (EuclideanSpace.equiv (Fin 2) ℝ x) 1 *
      (EuclideanSpace.equiv (Fin 2) ℝ y) 0

lemma det_eq_crossVec (x y : Plane) :
    det x y = Erdos957.crossVec x y := by
  simp [det, Erdos957.crossVec]

lemma inner_unitDirection (a b : ℝ) :
    @inner ℝ Plane _ (unitDirection a) (unitDirection b) =
      Real.cos (b - a) := by
  rw [Real.cos_sub]
  simp [unitDirection, PiLp.inner_apply]

lemma norm_unitDirection (a : ℝ) : ‖unitDirection a‖ = 1 := by
  have hs : ‖unitDirection a‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [unitDirection]
  nlinarith [norm_nonneg (unitDirection a)]

/-- On a counterclockwise angular interval of length at most `π`, the
unoriented Hilbert-space angle between unit directions is the angular
difference. -/
lemma angle_unitDirection {a b : ℝ} (h0 : 0 ≤ b - a)
    (hpi : b - a ≤ Real.pi) :
    InnerProductGeometry.angle (unitDirection a) (unitDirection b) = b - a := by
  rw [InnerProductGeometry.angle, inner_unitDirection, norm_unitDirection,
    norm_unitDirection]
  simp only [one_mul, div_one]
  exact Real.arccos_cos h0 hpi

/-- The interior angle between the reversed incoming direction and the
outgoing direction is complementary to a counterclockwise turn in
`[0, π]`. -/
lemma pi_sub_angle_neg_unitDirection {a b : ℝ} (h0 : 0 ≤ b - a)
    (hpi : b - a ≤ Real.pi) :
    Real.pi - InnerProductGeometry.angle (-unitDirection a) (unitDirection b) =
      b - a := by
  rw [InnerProductGeometry.angle_neg_left,
    angle_unitDirection h0 hpi]
  ring

lemma pi_sub_angle_scaled_directions {a b r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (h0 : 0 ≤ b - a)
    (hpi : b - a ≤ Real.pi) :
    Real.pi - InnerProductGeometry.angle (-(r • unitDirection a))
        (s • unitDirection b) = b - a := by
  rw [show -(r • unitDirection a) = r • (-unitDirection a) by simp,
    InnerProductGeometry.angle_smul_left_of_pos _ _ hr,
    InnerProductGeometry.angle_smul_right_of_pos _ _ hs]
  exact pi_sub_angle_neg_unitDirection h0 hpi

lemma unitDirection_add_two_pi (a : ℝ) :
    unitDirection (a + 2 * Real.pi) = unitDirection a := by
  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
  funext i
  fin_cases i <;> simp [unitDirection, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

/-- Adding the normalized counterclockwise displacement from `z` to `w`
to the principal argument of `z` gives a real representative of the unit
direction of `w`.  This packages the only wrap-around case needed when
turning radial and chord arguments into once-around real lifts. -/
lemma unitDirection_arg_add_ccwAngleDiff (z w : ℂ) :
    unitDirection (Complex.arg z + Erdos957.ccwAngleDiff z w) =
      unitDirection (Complex.arg w) := by
  by_cases hzw : Complex.arg z < Complex.arg w
  · rw [Erdos957.ccwAngleDiff, if_pos hzw]
    congr 1
    ring
  · rw [Erdos957.ccwAngleDiff, if_neg hzw]
    rw [show Complex.arg z +
          (2 * Real.pi + Complex.arg w - Complex.arg z) =
        Complex.arg w + 2 * Real.pi by ring,
      unitDirection_add_two_pi]

/-- Two normalized counterclockwise displacements based at the same ray
may independently cross the principal-argument seam.  Their difference is
nevertheless congruent modulo `2π` to the difference of the two target
arguments. -/
lemma sin_ccwAngleDiff_sub_ccwAngleDiff (z w x : ℂ) :
    Real.sin (Erdos957.ccwAngleDiff z x - Erdos957.ccwAngleDiff z w) =
      Real.sin (Complex.arg x - Complex.arg w) := by
  simp only [Erdos957.ccwAngleDiff]
  split_ifs with hzx hzw
  · congr 1
    ring
  · rw [show (Complex.arg x - Complex.arg z) -
          (2 * Real.pi + Complex.arg w - Complex.arg z) =
        (Complex.arg x - Complex.arg w) - 2 * Real.pi by ring,
      Real.sin_sub_two_pi]
  · rw [show (2 * Real.pi + Complex.arg x - Complex.arg z) -
          (Complex.arg w - Complex.arg z) =
        (Complex.arg x - Complex.arg w) + 2 * Real.pi by ring,
      Real.sin_add_two_pi]
  · congr 1
    ring

/-- Every nonzero planar vector has the expected polar representation in
the standard real-coordinate orientation.  (The equality also holds at
zero because `Complex.arg 0 = 0` and the scale vanishes.) -/
lemma norm_smul_unitDirection_arg (x : Plane) :
    ‖x‖ • unitDirection (Complex.arg (Erdos957.pointComplexEquiv x)) = x := by
  have hnorm : ‖Erdos957.pointComplexEquiv x‖ = ‖x‖ := by
    rw [Complex.norm_def, EuclideanSpace.norm_eq]
    simp [Erdos957.pointComplexEquiv, Complex.normSq_apply]
    congr 1
    ring
  ext i
  fin_cases i
  · rw [← hnorm]
    simp [unitDirection, Erdos957.pointComplexEquiv,
      Complex.norm_mul_cos_arg]
  · rw [← hnorm]
    simp [unitDirection, Erdos957.pointComplexEquiv,
      Complex.norm_mul_sin_arg]

lemma det_unitDirection (a b : ℝ) :
    det (unitDirection a) (unitDirection b) = Real.sin (b - a) := by
  rw [Real.sin_sub]
  simp [det, unitDirection]
  ring

/-- In the principal open interval `(-π, π)`, a positive sine forces
the argument itself to be positive. -/
lemma pos_of_neg_pi_lt_of_sin_pos {x : ℝ}
    (hneg : -Real.pi < x) (hsin : 0 < Real.sin x) : 0 < x := by
  by_contra hx
  have hxle : x ≤ 0 := le_of_not_gt hx
  by_cases hxzero : x = 0
  · simp [hxzero] at hsin
  · have hxlt : x < 0 := lt_of_le_of_ne hxle hxzero
    have := Real.sin_neg_of_neg_of_neg_pi_lt hxlt hneg
    linarith

lemma det_smul_smul (r s : ℝ) (x y : Plane) :
    det (r • x) (s • y) = r * s * det x y := by
  simp [det]
  ring

/-- Counterclockwise cyclic successor on a nonempty finite index type. -/
def cyclicSucc {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.1 + 1) % m, Nat.mod_lt _ hm⟩

/-- A lifted list of `m` cyclic directions.  The value at index `m`
duplicates the initial direction after one full positive revolution. -/
structure DirectionLift (m : ℕ) where
  /-- A total sequence is convenient for finite telescoping; only its values
  at `0, ..., m` are part of the represented lift. -/
  angle : ℕ → ℝ
  monotone : ∀ i : Fin m, angle i ≤ angle (i + 1)
  closes : angle m = angle 0 + 2 * Real.pi

/-- Extend a finite strictly sorted phase list through its closing endpoint.
Only values `0, ..., m` are used: the initial phase is repeated after adding
one full revolution. -/
noncomputable def closedPhaseLift {m : ℕ} (hm : 0 < m)
    (phase : Fin m → ℝ) (n : ℕ) : ℝ :=
  if hn : n < m then phase ⟨n, hn⟩ else phase ⟨0, hm⟩ + 2 * Real.pi

@[simp]
lemma closedPhaseLift_of_lt {m : ℕ} (hm : 0 < m) (phase : Fin m → ℝ)
    {n : ℕ} (hn : n < m) :
    closedPhaseLift hm phase n = phase ⟨n, hn⟩ := by
  simp [closedPhaseLift, hn]

@[simp]
lemma closedPhaseLift_at_card {m : ℕ} (hm : 0 < m) (phase : Fin m → ℝ) :
    closedPhaseLift hm phase m =
      closedPhaseLift hm phase 0 + 2 * Real.pi := by
  simp [closedPhaseLift, hm]

/-- Strict sorting before the seam, plus the standard argument upper bound
against the first phase, makes `closedPhaseLift` strictly increasing through
the closing endpoint. -/
lemma closedPhaseLift_strict {m : ℕ} (hm : 0 < m) (phase : Fin m → ℝ)
    (hmono : StrictMono phase)
    (hupper : ∀ i, phase i < phase ⟨0, hm⟩ + 2 * Real.pi)
    (i : Fin m) :
    closedPhaseLift hm phase i < closedPhaseLift hm phase (i.1 + 1) := by
  by_cases hnext : i.1 + 1 < m
  · rw [closedPhaseLift_of_lt hm phase i.isLt,
      closedPhaseLift_of_lt hm phase hnext]
    apply hmono
    exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.1)
  · have hi : i.1 + 1 = m := by omega
    rw [closedPhaseLift_of_lt hm phase i.isLt, hi,
      closedPhaseLift_at_card]
    simpa [closedPhaseLift, hm] using hupper i

/-- Radial angles and chord angles in the intervals arising from a strictly
convex counterclockwise polygon.  The radial lift makes one revolution.
Each outgoing chord direction lies strictly after the next radial ray and
strictly before the antipodal current radial ray.  Positive sine of each
successive chord-angle difference is the local strict-turn condition.

The lemmas below prove that these local interval facts force the chord-angle
sequence itself to be a monotone once-around lift. -/
structure RadialChordAngleData (m : ℕ) where
  three_le : 3 ≤ m
  radial : ℕ → ℝ
  chord : ℕ → ℝ
  radial_strict : ∀ i : Fin m, radial i < radial (i + 1)
  radial_closes : radial m = radial 0 + 2 * Real.pi
  chord_lower : ∀ i : Fin m, radial (i + 1) < chord i
  chord_upper : ∀ i : Fin m, chord i < radial i + Real.pi
  chord_closes : chord m = chord 0 + 2 * Real.pi
  strict_turn : ∀ i : Fin m, 0 < Real.sin (chord (i + 1) - chord i)

namespace RadialChordAngleData

/-- The next chord direction remains strictly after the corresponding
radial ray, including at the closing seam. -/
lemma radial_succ_lt_chord_succ {m : ℕ} (D : RadialChordAngleData m)
    (i : Fin m) : D.radial (i.1 + 1) < D.chord (i.1 + 1) := by
  by_cases hnext : i.1 + 1 < m
  · let j : Fin m := ⟨i.1 + 1, hnext⟩
    have hj := D.chord_lower j
    have hr := D.radial_strict j
    change D.radial (i.1 + 2) < D.chord (i.1 + 1) at hj
    change D.radial (i.1 + 1) < D.radial (i.1 + 2) at hr
    linarith
  · have hi : i.1 + 1 = m := by omega
    have hzero : (0 : ℕ) < m := by omega
    have hc0 := D.chord_lower (⟨0, hzero⟩ : Fin m)
    have hr0 := D.radial_strict (⟨0, hzero⟩ : Fin m)
    rw [hi, D.radial_closes, D.chord_closes]
    norm_num at hc0 hr0 ⊢
    linarith

/-- The next chord direction remains before the antipodal corresponding
radial ray, including at the closing seam. -/
lemma chord_succ_lt_radial_succ_add_pi {m : ℕ}
    (D : RadialChordAngleData m) (i : Fin m) :
    D.chord (i.1 + 1) < D.radial (i.1 + 1) + Real.pi := by
  by_cases hnext : i.1 + 1 < m
  · exact D.chord_upper (⟨i.1 + 1, hnext⟩ : Fin m)
  · have hi : i.1 + 1 = m := by omega
    have hzero : (0 : ℕ) < m := by omega
    have hc0 := D.chord_upper (⟨0, hzero⟩ : Fin m)
    rw [hi, D.radial_closes, D.chord_closes]
    norm_num at hc0 ⊢
    linarith

lemma neg_pi_lt_chord_turn {m : ℕ} (D : RadialChordAngleData m)
    (i : Fin m) :
    -Real.pi < D.chord (i.1 + 1) - D.chord i := by
  have hnext := D.radial_succ_lt_chord_succ i
  have hupper := D.chord_upper i
  have hradial := D.radial_strict i
  linarith

lemma chord_turn_lt_pi {m : ℕ} (D : RadialChordAngleData m)
    (i : Fin m) :
    D.chord (i.1 + 1) - D.chord i < Real.pi := by
  have hnext := D.chord_succ_lt_radial_succ_add_pi i
  have hlower := D.chord_lower i
  linarith

/-- A positive sine in the principal open interval `(-π, π)` must have a
positive argument. -/
lemma chord_turn_pos {m : ℕ} (D : RadialChordAngleData m) (i : Fin m) :
    0 < D.chord (i.1 + 1) - D.chord i := by
  exact pos_of_neg_pi_lt_of_sin_pos
    (D.neg_pi_lt_chord_turn i) (D.strict_turn i)

/-- The chord directions supplied by the radial interval construction form
the monotone, once-around direction lift required by the total-turn bridge. -/
def toDirectionLift {m : ℕ} (D : RadialChordAngleData m) : DirectionLift m where
  angle := D.chord
  monotone i := sub_nonneg.mp (D.chord_turn_pos i).le
  closes := D.chord_closes

end RadialChordAngleData

namespace DirectionLift

/-- Build the total-sequence presentation from the more geometric finite
list `Fin (m+1) → ℝ`; values beyond the closing endpoint are held constant
and play no role. -/
noncomputable def ofFinAngles {m : ℕ} (angle : Fin (m + 1) → ℝ)
    (hmono : ∀ i : Fin m, angle i.castSucc ≤ angle i.succ)
    (hclose : angle (Fin.last m) = angle 0 + 2 * Real.pi) :
    DirectionLift m where
  angle n := angle ⟨min n m, Nat.lt_succ_iff.mpr (Nat.min_le_right n m)⟩
  monotone i := by
    have h := hmono i
    change angle ⟨i.1, by omega⟩ ≤ angle ⟨i.1 + 1, by omega⟩ at h
    simpa only [Nat.min_eq_left (Nat.le_of_lt i.isLt),
      Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)] using h
  closes := by
    change angle ⟨min m m, by omega⟩ = angle ⟨min 0 m, by omega⟩ + 2 * Real.pi
    have hm : (⟨min m m, by omega⟩ : Fin (m + 1)) = Fin.last m := by
      apply Fin.ext
      simp
    have hz : (⟨min 0 m, by omega⟩ : Fin (m + 1)) = 0 := by
      apply Fin.ext
      simp
    rw [hm, hz]
    exact hclose

/-- The exterior turn between successive lifted edge directions. -/
def turn {m : ℕ} (D : DirectionLift m) (i : Fin m) : ℝ :=
  D.angle (i + 1) - D.angle i

lemma turn_nonneg {m : ℕ} (D : DirectionLift m) (i : Fin m) :
    0 ≤ D.turn i := by
  exact sub_nonneg.mpr (D.monotone i)

/-- The telescoping identity before the closing-up hypothesis is used. -/
lemma sum_turn_eq_sub {m : ℕ} (D : DirectionLift m) :
    ∑ i : Fin m, D.turn i = D.angle m - D.angle 0 := by
  exact (Fin.sum_univ_eq_sum_range
    (fun n => D.angle (n + 1) - D.angle n) m).trans
      (Finset.sum_range_sub D.angle m)

/-- Total exterior turn of a positively lifted cyclic direction list. -/
theorem sum_turn {m : ℕ} (D : DirectionLift m) :
    ∑ i : Fin m, D.turn i = 2 * Real.pi := by
  rw [D.sum_turn_eq_sub, D.closes]
  ring

/-- The unwrapped direction at index `i+1` represents the edge at the
cyclic successor of `i`, including at the wrap from the last index to zero. -/
lemma unitDirection_angle_succ_eq_finRotate {m : ℕ} (D : DirectionLift m)
    (i : Fin m) :
    unitDirection (D.angle (i.1 + 1)) =
      unitDirection (D.angle ((finRotate m i).1)) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ k =>
      by_cases hi : i = Fin.last k
      · subst i
        rw [finRotate_last]
        simp only [Fin.val_last, Fin.val_zero]
        rw [D.closes, unitDirection_add_two_pi]
      · rw [coe_finRotate_of_ne_last hi]

/-- A quantitative form of total turning: a collection of turns which are
all at least `ε` consumes at least `ε` times its cardinality of the available
full turn. -/
theorem threshold_mul_card_le_two_pi {m : ℕ} (D : DirectionLift m)
    (S : Finset (Fin m)) (ε : ℝ)
    (hlarge : ∀ i ∈ S, ε ≤ D.turn i) :
    ε * S.card ≤ 2 * Real.pi := by
  have hS : ∑ i ∈ S, ε ≤ ∑ i ∈ S, D.turn i := by
    exact Finset.sum_le_sum fun i hi => hlarge i hi
  have hsub : ∑ i ∈ S, D.turn i ≤ ∑ i : Fin m, D.turn i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => D.turn_nonneg i)
  calc
    ε * S.card = ∑ _i ∈ S, ε := by simp [nsmul_eq_mul]; ring
    _ ≤ ∑ i ∈ S, D.turn i := hS
    _ ≤ ∑ i : Fin m, D.turn i := hsub
    _ = 2 * Real.pi := D.sum_turn

/-- In particular, at most 360 exterior turns can be at least one degree.
This is the numerical estimate used before the seven-window union bound in
the published proof of Erdős 957. -/
theorem card_turn_ge_one_degree_le {m : ℕ} (D : DirectionLift m)
    (S : Finset (Fin m))
    (hlarge : ∀ i ∈ S, Real.pi / 180 ≤ D.turn i) :
    S.card ≤ 360 := by
  have hmass := D.threshold_mul_card_le_two_pi S (Real.pi / 180) hlarge
  have hreal : (S.card : ℝ) ≤ 360 := by
    nlinarith [Real.pi_pos]
  exact_mod_cast hreal

end DirectionLift

/-- Concrete edge-direction data for a cyclic planar polygon.  This is a
usable interface between convex-polygon geometry and `DirectionLift`:
strict convexity is used upstream to choose `lift`, while the positive-scale
edge identities ensure that the chosen angles really are the edge
directions of `vertex`. -/
structure CyclicPolygonAngleData (m : ℕ) where
  nonempty : 0 < m
  vertex : Fin m → Plane
  lift : DirectionLift m
  edgeScale : Fin m → ℝ
  edgeScale_pos : ∀ i, 0 < edgeScale i
  edge_eq : ∀ i,
    vertex (cyclicSucc nonempty i) - vertex i =
      edgeScale i • unitDirection (lift.angle i)

namespace CyclicPolygonAngleData

/-- Exterior turns extracted from the edge-direction lift. -/
def turn {m : ℕ} (P : CyclicPolygonAngleData m) (i : Fin m) : ℝ :=
  P.lift.turn i

lemma turn_nonneg {m : ℕ} (P : CyclicPolygonAngleData m) (i : Fin m) :
    0 ≤ P.turn i := P.lift.turn_nonneg i

/-- The exterior turns of the represented cyclic polygon sum to one full
turn.  Notice that the proof uses only the direction lift; `edge_eq` is the
certificate tying that lift to the given vertices. -/
theorem sum_turn {m : ℕ} (P : CyclicPolygonAngleData m) :
    ∑ i : Fin m, P.turn i = 2 * Real.pi :=
  P.lift.sum_turn

/-- The edge-direction certificate recovers the expected orientation
formula for every pair of represented edges.  This is the direct bridge
from the analytic angle lift back to the concrete polygon embedding. -/
theorem det_edge_edge {m : ℕ} (P : CyclicPolygonAngleData m)
    (i j : Fin m) :
    det (P.vertex (cyclicSucc P.nonempty i) - P.vertex i)
        (P.vertex (cyclicSucc P.nonempty j) - P.vertex j) =
      P.edgeScale i * P.edgeScale j *
        Real.sin (P.lift.angle j - P.lift.angle i) := by
  rw [P.edge_eq i, P.edge_eq j, det_smul_smul, det_unitDirection]

/-- Angular separation in `[0, π]` implies the corresponding pair of
represented edges has nonnegative counterclockwise orientation. -/
theorem det_edge_edge_nonneg {m : ℕ} (P : CyclicPolygonAngleData m)
    (i j : Fin m)
    (h0 : 0 ≤ P.lift.angle j - P.lift.angle i)
    (hpi : P.lift.angle j - P.lift.angle i ≤ Real.pi) :
    0 ≤ det (P.vertex (cyclicSucc P.nonempty i) - P.vertex i)
        (P.vertex (cyclicSucc P.nonempty j) - P.vertex j) := by
  rw [P.det_edge_edge i j]
  exact mul_nonneg
    (mul_nonneg (P.edgeScale_pos i).le (P.edgeScale_pos j).le)
    (Real.sin_nonneg_of_nonneg_of_le_pi h0 hpi)

end CyclicPolygonAngleData

/-! ## Bridge to the cyclic convex-hull order -/

namespace HullOrderBridge

open Erdos957

/-- The checked angular sorting of hull vertices has a canonical radial
angle lift through one complete revolution.  The last-to-first inequality
is precisely `Complex.arg_lt_arg_add_two_pi`. -/
theorem exists_centerAngle_radialLift (A : Finset Erdos957.Point)
    (hthree : 3 ≤ hullVertexCount A) :
    ∃ C : Erdos957.Point,
      C ∈ interior (convexHull ℝ (A : Set Erdos957.Point)) ∧
      ∃ v : Fin (hullVertexCount A) ↪ Erdos957.Point,
        Set.range v = (hullVertices A : Set Erdos957.Point) ∧
        ∃ radial : ℕ → ℝ,
          (∀ i : Fin (hullVertexCount A),
            radial i = centerAngle C (v i)) ∧
          (∀ i : Fin (hullVertexCount A), radial i < radial (i.1 + 1)) ∧
          radial (hullVertexCount A) = radial 0 + 2 * Real.pi := by
  obtain ⟨C, hC⟩ := convexHull_interior_nonempty_of_three_le_hullVertices A hthree
  obtain ⟨v, hvrange, hvmono⟩ := exists_angleSorted_hullVertexEmbedding A hC
  have hm : 0 < hullVertexCount A := by omega
  let phase : Fin (hullVertexCount A) → ℝ := fun i => centerAngle C (v i)
  let radial : ℕ → ℝ := closedPhaseLift hm phase
  have hphaseMono : StrictMono phase := by
    intro i j hij
    exact hvmono i j hij
  have hphaseUpper : ∀ i,
      phase i < phase ⟨0, hm⟩ + 2 * Real.pi := by
    intro i
    exact Complex.arg_lt_arg_add_two_pi
      (pointComplexEquiv (v i - C))
      (pointComplexEquiv (v ⟨0, hm⟩ - C))
  refine ⟨C, hC, v, hvrange, radial, ?_, ?_, ?_⟩
  · intro i
    simp [radial, phase, i.isLt]
  · intro i
    exact closedPhaseLift_strict hm phase hphaseMono hphaseUpper i
  · exact closedPhaseLift_at_card hm phase

/-- The exterior angle at a vertex of a genuine cyclic hull order, stated in
exactly the `π - angle(predecessor vector, successor vector)` form consumed
by `Erdos957GeometryCore.CyclicHullData`. -/
noncomputable def exteriorTurn {A : Finset Erdos957.Point}
    (P : CyclicHullOrder A) (i : Fin (hullVertexCount A)) : ℝ :=
  Real.pi - InnerProductGeometry.angle
    (P.vertex ((finRotate (hullVertexCount A)).symm i) - P.vertex i)
    (P.vertex (finRotate (hullVertexCount A) i) - P.vertex i)

/-- A cyclic hull order together with an unwrapped, once-around lift of its
edge directions.  The hull-order construction has to supply this record;
all three exterior-turn obligations (`turn_eq`, nonnegativity, and total
sum) are consequences proved below.

No upper bound on each increment is assumed.  It is derived below from the
strict positive local turn already present in `CyclicHullOrder`, together
with monotonicity and the fact that the lift closes after one revolution. -/
structure LiftedCyclicHullOrder {A : Finset Erdos957.Point}
    (P : CyclicHullOrder A) where
  hull_has_three : 3 ≤ hullVertexCount A
  lift : DirectionLift (hullVertexCount A)
  edgeScale : Fin (hullVertexCount A) → ℝ
  edgeScale_pos : ∀ i, 0 < edgeScale i
  edge_eq : ∀ i,
    P.vertex (finRotate (hullVertexCount A) i) - P.vertex i =
      edgeScale i • unitDirection (lift.angle i)

/-- Minimal output expected from an angular-sorting construction.  It need
only choose a monotone once-around real lift whose unit direction agrees
with the principal argument of each concrete outgoing edge.  Positive edge
scales and the actual vector equalities are then canonical. -/
structure UnwrappedCyclicEdgeAngles {A : Finset Erdos957.Point}
    (P : CyclicHullOrder A) where
  hull_has_three : 3 ≤ hullVertexCount A
  lift : DirectionLift (hullVertexCount A)
  represents : ∀ i : Fin (hullVertexCount A),
    unitDirection (lift.angle i) =
      unitDirection (Complex.arg (Erdos957.pointComplexEquiv
        (P.vertex (finRotate (hullVertexCount A) i) - P.vertex i)))

namespace UnwrappedCyclicEdgeAngles

variable {A : Finset Erdos957.Point} {P : CyclicHullOrder A}

/-- The radial-angle/chord-interval construction supplies the minimal
unwrapped edge-angle record once its chosen chord representatives are tied
to the concrete edge arguments. -/
noncomputable def ofRadialChord
    (D : RadialChordAngleData (hullVertexCount A))
    (hrep : ∀ i : Fin (hullVertexCount A),
      unitDirection (D.chord i) =
        unitDirection (Complex.arg (Erdos957.pointComplexEquiv
          (P.vertex (finRotate (hullVertexCount A) i) - P.vertex i)))) :
    UnwrappedCyclicEdgeAngles P where
  hull_has_three := D.three_le
  lift := D.toDirectionLift
  represents := hrep

/-- Upgrade angle representatives to the concrete positive-scale edge
certificate, taking each scale to be the edge norm. -/
noncomputable def toLiftedCyclicHullOrder
    (U : UnwrappedCyclicEdgeAngles P) : LiftedCyclicHullOrder P where
  hull_has_three := U.hull_has_three
  lift := U.lift
  edgeScale i := ‖P.vertex (finRotate (hullVertexCount A) i) - P.vertex i‖
  edgeScale_pos i := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (P.consecutive_ne i).symm
  edge_eq i := by
    rw [U.represents i]
    exact (norm_smul_unitDirection_arg
      (P.vertex (finRotate (hullVertexCount A) i) - P.vertex i)).symm

end UnwrappedCyclicEdgeAngles

namespace LiftedCyclicHullOrder

variable {A : Finset Erdos957.Point} {P : CyclicHullOrder A}

/-- The outgoing edge at the cyclic successor uses the next *unwrapped*
angle, including across the last-to-first seam. -/
theorem successor_edge_eq (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    P.vertex (finRotate (hullVertexCount A)
          (finRotate (hullVertexCount A) i)) -
        P.vertex (finRotate (hullVertexCount A) i) =
      L.edgeScale (finRotate (hullVertexCount A) i) •
        unitDirection (L.lift.angle (i.1 + 1)) := by
  rw [L.edge_eq (finRotate (hullVertexCount A) i)]
  rw [L.lift.unitDirection_angle_succ_eq_finRotate i]

/-- A single nonnegative turn cannot exceed the total turn. -/
theorem lift_turn_le_two_pi (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    L.lift.turn i ≤ 2 * Real.pi := by
  have hmass := L.lift.threshold_mul_card_le_two_pi
    ({i} : Finset (Fin (hullVertexCount A))) (L.lift.turn i) (by simp)
  simpa using hmass

/-- Strict counterclockwise turning of three consecutive hull vertices says
that the sine of the corresponding lifted direction increment is positive. -/
theorem sin_lift_turn_pos (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    0 < Real.sin (L.lift.turn i) := by
  have hdet :
      0 < det
        (P.vertex (finRotate (hullVertexCount A) i) - P.vertex i)
        (P.vertex (finRotate (hullVertexCount A)
            (finRotate (hullVertexCount A) i)) -
          P.vertex (finRotate (hullVertexCount A) i)) := by
    rw [det_eq_crossVec]
    simpa [Erdos957.orientedTurn, Erdos957.crossVec] using P.strict_turn i
  rw [L.edge_eq i, L.successor_edge_eq i, det_smul_smul,
    det_unitDirection] at hdet
  have hp :
      0 < (L.edgeScale i *
          L.edgeScale (finRotate (hullVertexCount A) i)) *
        Real.sin (L.lift.turn i) := by
    simpa [DirectionLift.turn, mul_assoc] using hdet
  rcases (mul_pos_iff.mp hp) with h | h
  · exact h.2
  · exact False.elim ((not_lt_of_ge
      (mul_pos (L.edgeScale_pos i)
        (L.edgeScale_pos (finRotate (hullVertexCount A) i))).le) h.1)

/-- The positive local orientation rules out an increment in the second
half of the full turn.  Thus every lifted exterior turn is at most `π`; this
need not be supplied as an additional field. -/
theorem lift_turn_le_pi (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    L.lift.turn i ≤ Real.pi := by
  by_contra hle
  have hpi : Real.pi < L.lift.turn i := lt_of_not_ge hle
  have htwo := L.lift_turn_le_two_pi i
  have hnonpos : Real.sin (L.lift.turn i - 2 * Real.pi) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
  rw [Real.sin_sub_two_pi] at hnonpos
  exact (not_lt_of_ge hnonpos) (L.sin_lift_turn_pos i)

/-- At the successor vertex, the lifted change of edge direction is exactly
the usual exterior angle.  Positive rescaling of the two edge vectors does
not change their Hilbert-space angle; the incoming edge is the negative of
the preceding unit direction. -/
theorem lift_turn_eq_exterior_at_successor (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    L.lift.turn i =
      Real.pi - InnerProductGeometry.angle
        (P.vertex i - P.vertex (finRotate (hullVertexCount A) i))
        (P.vertex (finRotate (hullVertexCount A)
            (finRotate (hullVertexCount A) i)) -
          P.vertex (finRotate (hullVertexCount A) i)) := by
  have hin :
      P.vertex i - P.vertex (finRotate (hullVertexCount A) i) =
        -(L.edgeScale i • unitDirection (L.lift.angle i)) := by
    rw [← L.edge_eq i]
    abel
  rw [hin, L.successor_edge_eq i]
  exact (pi_sub_angle_scaled_directions
    (L.edgeScale_pos i)
    (L.edgeScale_pos (finRotate (hullVertexCount A) i))
    (L.lift.turn_nonneg i) (L.lift_turn_le_pi i)).symm

/-- Same bridge, expressed using `exteriorTurn` and therefore ready for a
finite reindexing by the cyclic successor. -/
theorem lift_turn_eq_exteriorTurn_finRotate (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    L.lift.turn i = exteriorTurn P (finRotate (hullVertexCount A) i) := by
  rw [exteriorTurn]
  simp only [Equiv.symm_apply_apply]
  exact L.lift_turn_eq_exterior_at_successor i

/-- Exterior angles in a lifted genuine cyclic hull order are nonnegative. -/
theorem exteriorTurn_nonneg (L : LiftedCyclicHullOrder P)
    (i : Fin (hullVertexCount A)) :
    0 ≤ exteriorTurn P i := by
  let j := (finRotate (hullVertexCount A)).symm i
  have hji : finRotate (hullVertexCount A) j = i := by
    exact (finRotate (hullVertexCount A)).apply_symm_apply i
  rw [← hji, ← L.lift_turn_eq_exteriorTurn_finRotate j]
  exact L.lift.turn_nonneg j

/-- Exterior angles in a lifted genuine cyclic hull order sum to `2π`. -/
theorem exteriorTurn_sum (L : LiftedCyclicHullOrder P) :
    ∑ i, exteriorTurn P i = 2 * Real.pi := by
  calc
    ∑ i, exteriorTurn P i =
        ∑ i, exteriorTurn P (finRotate (hullVertexCount A) i) :=
      (Equiv.sum_comp (finRotate (hullVertexCount A)) (exteriorTurn P)).symm
    _ = ∑ i, L.lift.turn i := by
      apply Finset.sum_congr rfl
      intro i _
      exact (L.lift_turn_eq_exteriorTurn_finRotate i).symm
    _ = 2 * Real.pi := L.lift.sum_turn

/-- The three fields needed by the production geometry record, bundled as a
single conjunction to make downstream construction concise. -/
theorem exteriorTurn_spec (L : LiftedCyclicHullOrder P) :
    (∀ i, 0 ≤ exteriorTurn P i) ∧
    (∀ i, exteriorTurn P i = Real.pi - InnerProductGeometry.angle
      (P.vertex ((finRotate (hullVertexCount A)).symm i) - P.vertex i)
      (P.vertex (finRotate (hullVertexCount A) i) - P.vertex i)) ∧
    (∑ i, exteriorTurn P i = 2 * Real.pi) := by
  exact ⟨L.exteriorTurn_nonneg, fun _ => rfl, L.exteriorTurn_sum⟩

end LiftedCyclicHullOrder

end HullOrderBridge

end Erdos957TurnSum
