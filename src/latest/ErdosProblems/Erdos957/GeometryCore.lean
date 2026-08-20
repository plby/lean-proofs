import Mathlib
import ErdosProblems.Erdos957.Angle
import ErdosProblems.Erdos957.Hex
import ErdosProblems.Erdos957.Cases13
import ErdosProblems.Erdos957.Cases24
import ErdosProblems.Erdos957.Case13Bridge
import ErdosProblems.Erdos957.Case24Bridge
import ErdosProblems.Erdos957.Locality
import ErdosProblems.Erdos957.Overcharge
import ErdosProblems.Erdos957.FlatCount
import ErdosProblems.Erdos957.TransferCert
import ErdosProblems.Erdos957.Basic
import ErdosProblems.Erdos957.Hull

/-!
# Honest geometry interface for the charging step of Erdős problem 957

This file connects the checked local coordinate kernels to a global finite
point-set interface.  The interface contains only geometric data: a cyclic
enumeration of strict hull vertices, genuine local Euclidean frames, exterior
turns tied to the cyclic polygon, and genuine farthest-point witnesses.

The principal unresolved theorem is stated downstream in
`GeometryStatement`, after a genuine radial cyclic order and its lifted edge
angles have been constructed.  No field of `CyclicHullData` or
`DiameterWitnessData` is a transfer, an incoming-token bound, or a
final-capacity bound.

`FlatAlignedFrameData` is a separate intermediate geometric record for the
polar edge coordinates consumed by the locality estimate.  Its existence is
not assumed by the downstream transfer statement (nor by any theorem here).
The production `BisectorFrame` module constructs its owned chart from the
actual incident hull edges and the unwrapped edge-angle lift; Case 2 and
Case 4 may instead select their honest unit-edge rigid chart per source.

The lemmas below prove the global facts that do follow from the current
library: degree at most six everywhere, degree at most three at every strict
hull vertex, the `2520` non-flat count, and a complete transfer certificate
when the set of degree-three flat diameter sources is empty.  This pins the
remaining gap down to the four-case transfer construction and its ten-pair
no-overcharge theorem.
-/

open scoped BigOperators RealInnerProductSpace
open InnerProductGeometry
open Set

noncomputable section

namespace Erdos957GeometryCore

abbrev Point := Erdos957.Point

/-- The vertices of a finite point configuration, as a finite type. -/
abbrev Vertex (A : Finset Point) := {p // p ∈ A}

/-- The normalized shortest-distance graph. -/
def unitDistanceGraph (A : Finset Point) : SimpleGraph (Vertex A) where
  Adj p q := dist (p : Point) q = 1
  symm.symm := by
    intro p q hpq
    simpa [dist_comm] using hpq
  loopless.irrefl := by
    intro p hp
    simpa using hp

instance (A : Finset Point) : DecidableRel (unitDistanceGraph A).Adj :=
  Classical.decRel _

/-- Normalized minimum separation. -/
def IsOneSeparated (A : Finset Point) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y

/-- Coordinate-pair copy of a point in the production Euclidean plane. -/
def pointPair (p : Point) : ℝ × ℝ := (p 0, p 1)

lemma pointPair_injective : Function.Injective pointPair := by
  intro p q hpq
  ext i
  fin_cases i
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq

/-- The finite pair-coordinate copy used by `Erdos957Case13Bridge`. -/
def pairConfiguration (A : Finset Point) : Finset (ℝ × ℝ) :=
  A.map ⟨pointPair, pointPair_injective⟩

lemma sqDist_pointPair (p q : Point) :
    Erdos957Cases13.sqDist (pointPair p) (pointPair q) = dist p q ^ 2 := by
  rw [Erdos957Cases24.dist_sq_eq_coordinates]
  simp [Erdos957Cases13.sqDist, pointPair]

lemma pairConfiguration_oneSeparated {A : Finset Point} (hA : IsOneSeparated A) :
    Erdos957Cases13.IsOneSeparated (pairConfiguration A : Set (ℝ × ℝ)) := by
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨p, hpA, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨q, hqA, rfl⟩
  have hpq : p ≠ q := fun h ↦ hxy (congrArg pointPair h)
  change 1 ≤ Erdos957Cases13.sqDist (pointPair p) (pointPair q)
  rw [sqDist_pointPair]
  have hdist := hA p hpA q hqA hpq
  nlinarith [(dist_nonneg : 0 ≤ dist p q)]

/-- The production graph degree agrees with the pair-coordinate degree used
by the checked local transfer bridge. -/
lemma degree_unitDistanceGraph_eq_pairDegree (A : Finset Point) (p : Vertex A) :
    (unitDistanceGraph A).degree p =
      Erdos957Case13Bridge.degree (pairConfiguration A) (pointPair p) := by
  classical
  rw [SimpleGraph.degree]
  apply Finset.card_bij
    (s := (unitDistanceGraph A).neighborFinset p)
    (t := Erdos957Case13Bridge.unitNeighbors (pairConfiguration A) (pointPair p))
    (fun (q : Vertex A) _ ↦ pointPair q)
  · intro q hq
    have hdist : dist (p : Point) (q : Point) = 1 := by
      exact (SimpleGraph.mem_neighborFinset (G := unitDistanceGraph A) (v := p) q).mp hq
    apply Erdos957Case13Bridge.mem_unitNeighbors.mpr
    refine ⟨Finset.mem_map.mpr ⟨q, q.property, rfl⟩, ?_⟩
    rw [sqDist_pointPair, hdist]
    norm_num
  · intro q _ r _ hqr
    exact Subtype.ext (pointPair_injective hqr)
  · intro q hq
    rcases Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).1 with
      ⟨r, hrA, hrq⟩
    have hsquare := (Erdos957Case13Bridge.mem_unitNeighbors.mp hq).2
    change Erdos957Cases13.sqDist (pointPair p) q = 1 at hsquare
    rw [← hrq] at hsquare
    change Erdos957Cases13.sqDist (pointPair p) (pointPair r) = 1 at hsquare
    rw [sqDist_pointPair] at hsquare
    have hdist : dist (p : Point) r = 1 := by
      nlinarith [(dist_nonneg : 0 ≤ dist (p : Point) r)]
    refine ⟨⟨r, hrA⟩, ?_, hrq⟩
    exact (SimpleGraph.mem_neighborFinset (G := unitDistanceGraph A) (v := p)
      ⟨r, hrA⟩).mpr hdist

/-- The kissing-number bound in the exact graph model used by the certificate. -/
theorem degree_unitDistanceGraph_le_six {A : Finset Point}
    (hA : IsOneSeparated A) (p : Vertex A) :
    (unitDistanceGraph A).degree p ≤ 6 := by
  rw [degree_unitDistanceGraph_eq_pairDegree]
  exact Erdos957Case13Bridge.degree_le_six (pairConfiguration_oneSeparated hA) (pointPair p)

/-! ## Cyclic strict-hull data -/

/-- Seven consecutive cyclic shifts, with the source at position `3`. -/
def sevenShift {ι : Type*} (next : Equiv.Perm ι) (j : Fin 7) : Equiv.Perm ι :=
  next ^ j.1 * (next⁻¹) ^ 3

/-- Signed oriented area in production Euclidean coordinates. -/
def cross (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/--
An honest finite cyclic hull interface.

`H` contains vertices of `A`.  The permutation `next` cyclically enumerates
it.  `frame i` is a real-linear Euclidean isometry placing the strict
supporting half-plane at `i` in the open upper half-plane.  The final two
fields tie `turn` to the actual predecessor and successor vectors and state
the standard exterior-turn sum.
-/
structure CyclicHullData (A : Finset Point) where
  H : Finset (Vertex A)
  hull_exact : ∀ p : Vertex A,
    p ∈ H ↔ (p : Point) ∈ (convexHull ℝ (A : Set Point)).extremePoints ℝ
  next : Equiv.Perm {p // p ∈ H}
  next_is_cyclic : ∀ i j, ∃ k < H.card, (next ^ k) i = j
  edge_support : ∀ (i : {p // p ∈ H}) (q : Vertex A),
    0 ≤ cross ((next i).1.1 - i.1.1) ((q : Point) - i.1.1)
  frame : {p // p ∈ H} → Point ≃ₗᵢ[ℝ] Point
  strict_support : ∀ (i : {p // p ∈ H}) (q : Vertex A), q ≠ i.1 →
    0 < frame i ((q : Point) - (i.1 : Point)) 1
  turn : {p // p ∈ H} → ℝ
  turn_nonneg : ∀ i, 0 ≤ turn i
  turn_eq : ∀ i,
    turn i = Real.pi - InnerProductGeometry.angle
      (((next⁻¹) i).1.1 - i.1.1)
      ((next i).1.1 - i.1.1)
  turn_sum : ∑ i, turn i = 2 * Real.pi

namespace CyclicHullData

variable {A : Finset Point} (P : CyclicHullData A)

/-- The canonical bounded forward exponent from one cyclic hull index to
another, chosen from the one-cycle witness. -/
noncomputable def stepTo (i j : {p // p ∈ P.H}) : ℕ :=
  Classical.choose (P.next_is_cyclic i j)

theorem stepTo_lt_card (i j : {p // p ∈ P.H}) :
    P.stepTo i j < P.H.card :=
  (Classical.choose_spec (P.next_is_cyclic i j)).1

theorem next_pow_stepTo (i j : {p // p ∈ P.H}) :
    (P.next ^ P.stepTo i j) i = j :=
  (Classical.choose_spec (P.next_is_cyclic i j)).2

/-- The cyclic successor has no fixed point.  A fixed point would make the
one-cycle hull index type a singleton, contradicting the `2π` turn sum and
the fact that one exterior turn is at most `π`. -/
theorem next_ne_self (i : {p // p ∈ P.H}) : P.next i ≠ i := by
  intro hfix
  have hpow (k : ℕ) : (P.next ^ k) i = i := by
    induction k with
    | zero => simp
    | succ k ih => simp [pow_succ, ih, hfix]
  have hall (j : {p // p ∈ P.H}) : j = i := by
    obtain ⟨k, _hk, hki⟩ := P.next_is_cyclic i j
    exact hki.symm.trans (hpow k)
  have huniv : (Finset.univ : Finset {p // p ∈ P.H}) = {i} := by
    ext j
    simp [hall j]
  have hturnle : P.turn i ≤ Real.pi := by
    rw [P.turn_eq]
    exact sub_le_self _ (InnerProductGeometry.angle_nonneg _ _)
  have hsum := P.turn_sum
  rw [huniv] at hsum
  simp only [Finset.sum_singleton] at hsum
  nlinarith [Real.pi_pos]

theorem prev_ne_self (i : {p // p ∈ P.H}) : P.next⁻¹ i ≠ i := by
  intro hprev
  apply P.next_ne_self i
  simpa using (congrArg P.next hprev).symm

/-- Ambient convex-hull vertices, lifted to the graph vertex subtype. -/
def liftedHullVertices (P : CyclicHullData A) : Finset (Vertex A) :=
  Finset.univ.filter fun p ↦
    (p : Point) ∈ Erdos957.hullVertices A

@[simp]
theorem mem_liftedHullVertices (p : Vertex A) :
    p ∈ P.liftedHullVertices ↔
      (p : Point) ∈ Erdos957.hullVertices A := by
  simp [liftedHullVertices]

/-- The hull finset in the cyclic record is exactly the production lifted
convex-hull finset, not a freely chosen superset. -/
theorem H_eq_liftedHullVertices : P.H = P.liftedHullVertices := by
  classical
  ext p
  rw [P.hull_exact, P.mem_liftedHullVertices,
    Erdos957.mem_hullVertices]

/-- Hull indices whose seven-position window contains a turn of at least one degree. -/
def nonflatIndices : Finset {p // p ∈ P.H} :=
  Erdos957FlatCount.nonflatIndices P.turn (Real.pi / 180) (sevenShift P.next)

/-- A hull index is flat when all seven turns in its window are below one degree. -/
def IsFlat (i : {p // p ∈ P.H}) : Prop :=
  i ∉ P.nonflatIndices

/-- Every turn occurring in a flat seven-position window is strictly below
one degree. -/
theorem turn_sevenShift_lt (i : {p // p ∈ P.H}) (hi : P.IsFlat i)
    (j : Fin 7) :
    P.turn (sevenShift P.next j i) < Real.pi / 180 := by
  by_contra hlarge
  apply hi
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨j, le_of_not_gt hlarge⟩⟩

/-- The source turn itself is one of the seven flat-window turns. -/
theorem turn_lt_of_isFlat (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    P.turn i < Real.pi / 180 := by
  simpa [sevenShift] using P.turn_sevenShift_lt i hi (3 : Fin 7)

/-- Flat hull vertices, returned in the ambient graph's vertex type. -/
def flatVertices : Finset (Vertex A) :=
  by
    classical
    exact (Finset.univ.filter P.IsFlat).map
      ⟨fun i ↦ i.1, fun _ _ h ↦ Subtype.ext h⟩

lemma flatVertices_subset_hull : P.flatVertices ⊆ P.H := by
  intro p hp
  rcases Finset.mem_map.mp hp with ⟨i, _, rfl⟩
  exact i.property

/-- The checked seven-window counting argument gives the exact constant `2520`. -/
theorem card_nonflatIndices_le_2520 : P.nonflatIndices.card ≤ 2520 := by
  exact Erdos957FlatCount.card_nonflatIndices_le_2520
    P.turn (sevenShift P.next) P.turn_nonneg P.turn_sum

/-- Mapping a non-flat hull index back to its ambient vertex preserves the
exceptional-set cardinality exactly. -/
theorem card_hull_sdiff_flatVertices_eq :
    (P.H \ P.flatVertices).card = P.nonflatIndices.card := by
  classical
  apply Finset.card_bij
    (s := P.H \ P.flatVertices) (t := P.nonflatIndices)
    (fun p hp ↦ ⟨p, (Finset.mem_sdiff.mp hp).1⟩)
  · intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpH, hpFlat⟩
    by_contra hnonflat
    apply hpFlat
    apply Finset.mem_map.mpr
    refine ⟨⟨p, hpH⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonflat⟩
  · intro p hp q hq hpq
    exact congrArg Subtype.val hpq
  · intro i hi
    refine ⟨i.1, ?_, ?_⟩
    · apply Finset.mem_sdiff.mpr
      refine ⟨i.property, ?_⟩
      intro hiFlat
      rcases Finset.mem_map.mp hiFlat with ⟨j, hj, hji⟩
      have heq : j = i := Subtype.ext hji
      subst j
      exact (Finset.mem_filter.mp hj).2 hi
    · rfl

/-- Ambient form of the seven-window exceptional-vertex bound. -/
theorem card_hull_sdiff_flatVertices_le_2520 :
    (P.H \ P.flatVertices).card ≤ 2520 := by
  rw [P.card_hull_sdiff_flatVertices_eq]
  exact P.card_nonflatIndices_le_2520

/-! ### Coordinate bridge to the four checked local cases -/

/-- The paper's local coordinates, with the supporting half-plane below the
horizontal axis.  The sign flip converts the upper-half-plane convention of
`strict_support` into the convention used in `Erdos957Cases13` and
`Erdos957Cases24`. -/
def localCoord (i : {p // p ∈ P.H}) (q : Vertex A) : ℝ × ℝ :=
  let z := P.frame i ((q : Point) - (i.1 : Point))
  (z 0, -z 1)

/-- The unreflected chart used for the open-upper-half-plane degree bound. -/
def upperCoord (i : {p // p ∈ P.H}) (q : Vertex A) : ℝ × ℝ :=
  let z := P.frame i ((q : Point) - (i.1 : Point))
  (z 0, z 1)

@[simp]
theorem localCoord_source (i : {p // p ∈ P.H}) : P.localCoord i i.1 = (0, 0) := by
  simp [localCoord]

@[simp]
theorem upperCoord_source (i : {p // p ∈ P.H}) : P.upperCoord i i.1 = (0, 0) := by
  simp [upperCoord]

/-- Every other point of the configuration lies strictly below the local
supporting line. -/
theorem localCoord_snd_neg (i : {p // p ∈ P.H}) (q : Vertex A)
    (hq : q ≠ i.1) : (P.localCoord i q).2 < 0 := by
  simpa [localCoord] using neg_lt_neg (P.strict_support i q hq)

/-- The local coordinate map is injective. -/
theorem localCoord_injective (i : {p // p ∈ P.H}) :
    Function.Injective (P.localCoord i) := by
  intro q r hqr
  have hzero :
      P.frame i ((q : Point) - (i.1 : Point)) 0 =
        P.frame i ((r : Point) - (i.1 : Point)) 0 :=
    congrArg Prod.fst hqr
  have hone :
      P.frame i ((q : Point) - (i.1 : Point)) 1 =
        P.frame i ((r : Point) - (i.1 : Point)) 1 := by
    have h := congrArg Prod.snd hqr
    simp only [localCoord] at h
    linarith
  have hframe :
      P.frame i ((q : Point) - (i.1 : Point)) =
        P.frame i ((r : Point) - (i.1 : Point)) :=
    by
      ext j
      fin_cases j
      · exact hzero
      · exact hone
  have hsub := (P.frame i).injective hframe
  exact Subtype.ext (sub_left_inj.mp hsub)

/-- Squared Euclidean distance is exactly `Cases13.sqDist` after moving to a
source chart. -/
theorem sqDist_localCoord (i : {p // p ∈ P.H}) (q r : Vertex A) :
    Erdos957Cases13.sqDist (P.localCoord i q) (P.localCoord i r) =
      dist (q : Point) (r : Point) ^ 2 := by
  let zq := P.frame i ((q : Point) - (i.1 : Point))
  let zr := P.frame i ((r : Point) - (i.1 : Point))
  calc
    Erdos957Cases13.sqDist (P.localCoord i q) (P.localCoord i r) =
        (zq 0 - zr 0) ^ 2 + (zq 1 - zr 1) ^ 2 := by
      simp [Erdos957Cases13.sqDist, localCoord, zq, zr]
      ring
    _ = dist zq zr ^ 2 := (Erdos957Cases24.dist_sq_eq_coordinates zq zr).symm
    _ = dist (q : Point) (r : Point) ^ 2 := by
      congr 1
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map]
      simp [zq, zr]

theorem sqDist_upperCoord (i : {p // p ∈ P.H}) (q r : Vertex A) :
    Erdos957Cases13.sqDist (P.upperCoord i q) (P.upperCoord i r) =
      dist (q : Point) (r : Point) ^ 2 := by
  rw [← P.sqDist_localCoord i q r]
  simp only [Erdos957Cases13.sqDist, upperCoord, localCoord]
  ring

/-- Strict support plus angular packing gives degree at most three at every
hull vertex, now in the production Euclidean point model. -/
theorem hull_degree_le_three (hA : IsOneSeparated A) (i : {p // p ∈ P.H}) :
    (unitDistanceGraph A).degree i.1 ≤ 3 := by
  classical
  let N := (unitDistanceGraph A).neighborFinset i.1
  let f : Vertex A → ℂ := fun q ↦ Erdos957Cases13.toComplex (P.upperCoord i q)
  let V : Finset ℂ := N.image f
  have hf : Function.Injective f := by
    intro q r hqr
    have hpairs : P.upperCoord i q = P.upperCoord i r := by
      exact Erdos957Case13Bridge.pointComplexEquiv.injective hqr
    have hzero := congrArg Prod.fst hpairs
    have hone := congrArg Prod.snd hpairs
    have hframe :
        P.frame i ((q : Point) - (i.1 : Point)) =
          P.frame i ((r : Point) - (i.1 : Point)) := by
      ext j
      fin_cases j
      · exact hzero
      · exact hone
    have hsub := (P.frame i).injective hframe
    exact Subtype.ext (sub_left_inj.mp hsub)
  have hcard : V.card = N.card := by
    exact Finset.card_image_of_injective N hf
  have hnorm : ∀ z ∈ V, ‖z‖ = 1 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    have hdist :=
      (SimpleGraph.mem_neighborFinset (G := unitDistanceGraph A) (v := i.1) q).mp hq
    have hsqd : Erdos957Cases13.sqDist (P.upperCoord i i.1) (P.upperCoord i q) = 1 := by
      rw [P.sqDist_upperCoord, hdist]
      norm_num
    have hc := (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
      (P.upperCoord i i.1) (P.upperCoord i q)).mp hsqd
    rw [P.upperCoord_source] at hc
    change dist 0 (f q) = 1 at hc
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hc
  have him : ∀ z ∈ V, 0 < z.im := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    have hne : q ≠ i.1 := by
      intro heq
      subst q
      change i.1 ∈ (unitDistanceGraph A).neighborFinset i.1 at hq
      exact (SimpleGraph.notMem_neighborFinset_self
        (G := unitDistanceGraph A) (v := i.1)) hq
    simpa [f, Erdos957Cases13.toComplex, upperCoord] using P.strict_support i q hne
  have hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
    have hqr : q ≠ r := fun heq ↦ hxy (congrArg f heq)
    have hdist := hA q q.property r r.property (fun h ↦ hqr (Subtype.ext h))
    have hsqd : 1 ≤ Erdos957Cases13.sqDist (P.upperCoord i q) (P.upperCoord i r) := by
      rw [P.sqDist_upperCoord]
      nlinarith [(dist_nonneg : 0 ≤ dist (q : Point) (r : Point))]
    have hc := (Erdos957Cases13.one_le_sqDist_iff_one_le_dist
      (P.upperCoord i q) (P.upperCoord i r)).mp hsqd
    simpa [f, dist_eq_norm] using hc
  rw [SimpleGraph.degree, ← hcard]
  exact Erdos957Hex.card_le_three_of_unit_oneSeparated_of_im_pos V hnorm him hsep

/-- The actual finite configuration expressed in the source chart. -/
def localSet (i : {p // p ∈ P.H}) : Set (ℝ × ℝ) :=
  Set.range (P.localCoord i)

/-- Minimum separation transports to the exact predicate used by the
Case-1/Case-3 coordinate module. -/
theorem localSet_oneSeparated (hA : IsOneSeparated A) (i : {p // p ∈ P.H}) :
    Erdos957Cases13.IsOneSeparated (P.localSet i) := by
  intro x hx y hy hxy
  rcases hx with ⟨q, rfl⟩
  rcases hy with ⟨r, rfl⟩
  have hqr : q ≠ r := fun h ↦ hxy (congrArg (P.localCoord i) h)
  rw [P.sqDist_localCoord]
  have hdist := hA q q.property r r.property (fun h ↦ hqr (Subtype.ext h))
  nlinarith [(dist_nonneg : 0 ≤ dist (q : Point) (r : Point))]

/-- The finite local-coordinate copy of the entire configuration. -/
def localConfiguration (i : {p // p ∈ P.H}) : Finset (ℝ × ℝ) :=
  Finset.univ.map ⟨P.localCoord i, P.localCoord_injective i⟩

/-- The finite local-coordinate copy of the exact hull set. -/
def localHull (i : {p // p ∈ P.H}) : Finset (ℝ × ℝ) :=
  P.H.map ⟨P.localCoord i, P.localCoord_injective i⟩

lemma localCoord_mem_localConfiguration (i : {p // p ∈ P.H}) (q : Vertex A) :
    P.localCoord i q ∈ P.localConfiguration i := by
  exact Finset.mem_map.mpr ⟨q, Finset.mem_univ _, rfl⟩

lemma localCoord_mem_localHull (i : {p // p ∈ P.H}) {q : Vertex A}
    (hq : q ∈ P.H) : P.localCoord i q ∈ P.localHull i := by
  exact Finset.mem_map.mpr ⟨q, hq, rfl⟩

@[simp]
lemma origin_mem_localConfiguration (i : {p // p ∈ P.H}) :
    Erdos957Cases13.origin ∈ P.localConfiguration i := by
  change (0, 0) ∈ P.localConfiguration i
  rw [← P.localCoord_source i]
  exact P.localCoord_mem_localConfiguration i i.1

@[simp]
lemma origin_mem_localHull (i : {p // p ∈ P.H}) :
    Erdos957Cases13.origin ∈ P.localHull i := by
  change (0, 0) ∈ P.localHull i
  rw [← P.localCoord_source i]
  exact P.localCoord_mem_localHull i i.property

/-- The finite coordinate copy lies in the closed lower supporting
half-plane, exactly as required by the Case-1/Case-3 bridge. -/
theorem localConfiguration_below_support (i : {p // p ∈ P.H}) :
    ∀ p ∈ P.localConfiguration i, p.2 ≤ 0 := by
  intro p hp
  rcases Finset.mem_map.mp hp with ⟨q, _, rfl⟩
  by_cases hq : q = i.1
  · subst q
    simp
  · exact (P.localCoord_snd_neg i q hq).le

/-- Degree is preserved by the local coordinate embedding. -/
theorem case13_degree_localCoord (i : {p // p ∈ P.H}) (q : Vertex A) :
    Erdos957Case13Bridge.degree (P.localConfiguration i) (P.localCoord i q) =
      (unitDistanceGraph A).degree q := by
  classical
  rw [Erdos957Case13Bridge.degree, SimpleGraph.degree]
  apply Finset.card_bij
    (s := Erdos957Case13Bridge.unitNeighbors (P.localConfiguration i) (P.localCoord i q))
    (t := (unitDistanceGraph A).neighborFinset q)
    (fun p hp ↦ Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1))
  · intro p hp
    let r : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)
    have hrCoord : P.localCoord i r = p :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)).2
    have hsquare := (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).2
    rw [← hrCoord, P.sqDist_localCoord] at hsquare
    have hdist : dist (q : Point) (r : Point) = 1 := by
      nlinarith [(dist_nonneg : 0 ≤ dist (q : Point) (r : Point))]
    exact (SimpleGraph.mem_neighborFinset (G := unitDistanceGraph A) (v := q) r).mpr hdist
  · intro p hp r hr hpr
    let p' : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)
    let r' : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hr).1)
    have hpCoord : P.localCoord i p' = p :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)).2
    have hrCoord : P.localCoord i r' = r :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hr).1)).2
    have hvertex : p' = r' := hpr
    rw [← hpCoord, ← hrCoord, hvertex]
  · intro r hr
    refine ⟨P.localCoord i r, ?_, ?_⟩
    · apply Erdos957Case13Bridge.mem_unitNeighbors.mpr
      refine ⟨P.localCoord_mem_localConfiguration i r, ?_⟩
      rw [P.sqDist_localCoord]
      have hdist :=
        (SimpleGraph.mem_neighborFinset (G := unitDistanceGraph A) (v := q) r).mp hr
      rw [hdist]
      norm_num
    · dsimp
      exact (P.localCoord_injective i)
        (Classical.choose_spec
          (Finset.mem_map.mp (P.localCoord_mem_localConfiguration i r))).2

/-- The same source chart in the `EuclideanSpace ℝ (Fin 2)` model used by
Cases 2 and 4. -/
def localEuclidean (i : {p // p ∈ P.H}) (q : Vertex A) :
    Erdos957Cases24.Point :=
  Erdos957Cases13.toEuclidean (P.localCoord i q)

theorem dist_localEuclidean (i : {p // p ∈ P.H}) (q r : Vertex A) :
    dist (P.localEuclidean i q) (P.localEuclidean i r) =
      dist (q : Point) (r : Point) := by
  have hsquare : dist (P.localEuclidean i q) (P.localEuclidean i r) ^ 2 =
      dist (q : Point) (r : Point) ^ 2 := by
    rw [← P.sqDist_localCoord]
    exact (Erdos957Cases13.sqDist_eq_euclidean_dist_sq
      (P.localCoord i q) (P.localCoord i r)).symm
  nlinarith [
    (dist_nonneg : 0 ≤ dist (P.localEuclidean i q) (P.localEuclidean i r)),
    (dist_nonneg : 0 ≤ dist (q : Point) (r : Point))]

/-! ## Constructible aligned-frame data for locality

The exposing frame stored in `CyclicHullData` is deliberately arbitrary.
The locality argument additionally chooses its horizontal direction to be
the bisector convention of the paper.  The following separate record keeps
that extra *geometric* choice out of the basic cyclic-hull constructor.  Its
fields are polar descriptions of genuine consecutive hull edges and the
numerical angle bounds implied by a flat seven-window; no transfer, token,
collision, or capacity assertion occurs here. -/

/-- Reflect the horizontal coordinate, if necessary, so that the actual
cyclic successor is on the nonnegative-x side.  This preserves the support
half-plane and every rectangle used later. -/
def horizontalSign (i : {p // p ∈ P.H}) : ℝ :=
  if 0 ≤ (P.localCoord i (P.next i).1).1 then 1 else -1

def alignedLocalCoord (i : {p // p ∈ P.H}) (q : Vertex A) : ℝ × ℝ :=
  (P.horizontalSign i * (P.localCoord i q).1, (P.localCoord i q).2)

@[simp]
theorem horizontalSign_sq (i : {p // p ∈ P.H}) :
    P.horizontalSign i ^ 2 = 1 := by
  simp [horizontalSign]

theorem alignedLocalCoord_snd (i : {p // p ∈ P.H}) (q : Vertex A) :
    (P.alignedLocalCoord i q).2 = (P.localCoord i q).2 := rfl

theorem alignedSuccessor_fst_nonneg (i : {p // p ∈ P.H}) :
    0 ≤ (P.alignedLocalCoord i (P.next i).1).1 := by
  by_cases h : 0 ≤ (P.localCoord i (P.next i).1).1
  · simpa [alignedLocalCoord, horizontalSign, h]
  · simp [alignedLocalCoord, horizontalSign, h]
    exact le_of_not_ge h

theorem sqDist_alignedLocalCoord (i : {p // p ∈ P.H}) (q r : Vertex A) :
    Erdos957Cases13.sqDist (P.alignedLocalCoord i q)
      (P.alignedLocalCoord i r) = dist (q : Point) (r : Point) ^ 2 := by
  rw [← P.sqDist_localCoord i q r]
  simp only [Erdos957Cases13.sqDist, alignedLocalCoord]
  have hs := P.horizontalSign_sq i
  nlinarith

theorem alignedLocalCoord_injective (i : {p // p ∈ P.H}) :
    Function.Injective (P.alignedLocalCoord i) := by
  intro q r hqr
  apply P.localCoord_injective i
  apply Prod.ext
  · apply mul_left_cancel₀ (a := P.horizontalSign i)
    · intro hz
      have hs := P.horizontalSign_sq i
      rw [hz] at hs
      norm_num at hs
    · simpa [alignedLocalCoord] using congrArg Prod.fst hqr
  · simpa [alignedLocalCoord] using congrArg Prod.snd hqr

theorem next_pow_succ_ne (i : {p // p ∈ P.H}) (k : ℕ) :
    (P.next ^ (k + 1)) i ≠ (P.next ^ k) i := by
  intro h
  apply P.next_ne_self ((P.next ^ k) i)
  simpa [pow_succ] using h

theorem prev_pow_succ_ne (i : {p // p ∈ P.H}) (k : ℕ) :
    ((P.next⁻¹) ^ (k + 1)) i ≠ ((P.next⁻¹) ^ k) i := by
  intro h
  apply P.prev_ne_self i
  have h' := congrArg (P.next ^ k) h
  simpa [pow_succ] using h'

/-- The `k`-th forward hull vertex in the oriented source coordinates. -/
def rightOrbitCoord (i : {p // p ∈ P.H}) (k : ℕ) : ℝ × ℝ :=
  P.alignedLocalCoord i ((P.next ^ k) i).1

/-- The `k`-th backward hull vertex, reflected across the local vertical
axis so that both sides can use the same right-going locality estimate. -/
def leftOrbitReflectedCoord (i : {p // p ∈ P.H}) (k : ℕ) : ℝ × ℝ :=
  let z := P.alignedLocalCoord i (((P.next⁻¹) ^ k) i).1
  (-z.1, z.2)

@[simp]
theorem rightOrbitCoord_zero (i : {p // p ∈ P.H}) :
    P.rightOrbitCoord i 0 = (0, 0) := by
  simp [rightOrbitCoord, alignedLocalCoord, P.localCoord_source]

@[simp]
theorem leftOrbitReflectedCoord_zero (i : {p // p ∈ P.H}) :
    P.leftOrbitReflectedCoord i 0 = (0, 0) := by
  simp [leftOrbitReflectedCoord, alignedLocalCoord, P.localCoord_source]

/-- Complex displacement of two coordinate pairs. -/
def coordinateVector (p q : ℝ × ℝ) : ℂ :=
  ⟨q.1 - p.1, q.2 - p.2⟩

def polarRadius (p q : ℝ × ℝ) : ℝ := ‖coordinateVector p q‖

def polarAngle (p q : ℝ × ℝ) : ℝ := (coordinateVector p q).arg

/-- Every nondegenerate coordinate edge has its canonical polar
description, with radius its actual Euclidean norm and angle `Complex.arg`. -/
theorem isPolarEdge_polar (p q : ℝ × ℝ) (hpq : p ≠ q) :
    Erdos957Locality.IsPolarEdge p q (polarRadius p q) (polarAngle p q) := by
  let z := coordinateVector p q
  have hz : z ≠ 0 := by
    intro hz0
    apply hpq
    apply Prod.ext
    · have := congrArg Complex.re hz0
      simpa [z, coordinateVector] using (sub_eq_zero.mp this).symm
    · have := congrArg Complex.im hz0
      simpa [z, coordinateVector] using (sub_eq_zero.mp this).symm
  have hnorm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  constructor
  · change z.re = ‖z‖ * Real.cos z.arg
    rw [Complex.cos_arg hz]
    field_simp
  · change z.im = ‖z‖ * Real.sin z.arg
    rw [Complex.sin_arg]
    field_simp

theorem polarRadius_sq (p q : ℝ × ℝ) :
    polarRadius p q ^ 2 = Erdos957Cases13.sqDist p q := by
  rw [Erdos957Cases13.sqDist_eq_complex_dist_sq]
  rw [dist_eq_norm]
  have hz : coordinateVector p q =
      -(Erdos957Cases13.toComplex p - Erdos957Cases13.toComplex q) := by
    apply Complex.ext <;> simp [coordinateVector, Erdos957Cases13.toComplex]
  rw [polarRadius, hz, norm_neg]

theorem rightOrbitCoord_succ_ne (i : {p // p ∈ P.H}) (k : ℕ) :
    P.rightOrbitCoord i (k + 1) ≠ P.rightOrbitCoord i k := by
  intro h
  apply P.next_pow_succ_ne i k
  apply Subtype.ext
  exact P.alignedLocalCoord_injective i h

theorem leftOrbitReflectedCoord_succ_ne (i : {p // p ∈ P.H}) (k : ℕ) :
    P.leftOrbitReflectedCoord i (k + 1) ≠
      P.leftOrbitReflectedCoord i k := by
  intro h
  apply P.prev_pow_succ_ne i k
  apply Subtype.ext
  apply P.alignedLocalCoord_injective i
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    simp only [leftOrbitReflectedCoord] at hx
    linarith
  · simpa [leftOrbitReflectedCoord] using congrArg Prod.snd h

def canonicalRightRadius (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarRadius (P.rightOrbitCoord i k.1) (P.rightOrbitCoord i (k.1 + 1))

def canonicalRightAngle (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarAngle (P.rightOrbitCoord i k.1) (P.rightOrbitCoord i (k.1 + 1))

def canonicalLeftRadius (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarRadius (P.leftOrbitReflectedCoord i k.1)
    (P.leftOrbitReflectedCoord i (k.1 + 1))

def canonicalLeftAngle (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarAngle (P.leftOrbitReflectedCoord i k.1)
    (P.leftOrbitReflectedCoord i (k.1 + 1))

theorem canonicalRightPolar (i : {p // p ∈ P.H}) (k : Fin 4) :
    Erdos957Locality.IsPolarEdge
      (P.rightOrbitCoord i k.1) (P.rightOrbitCoord i (k.1 + 1))
      (P.canonicalRightRadius i k) (P.canonicalRightAngle i k) :=
  isPolarEdge_polar _ _ (P.rightOrbitCoord_succ_ne i k.1).symm

theorem canonicalLeftPolar (i : {p // p ∈ P.H}) (k : Fin 4) :
    Erdos957Locality.IsPolarEdge
      (P.leftOrbitReflectedCoord i k.1)
      (P.leftOrbitReflectedCoord i (k.1 + 1))
      (P.canonicalLeftRadius i k) (P.canonicalLeftAngle i k) :=
  isPolarEdge_polar _ _ (P.leftOrbitReflectedCoord_succ_ne i k.1).symm

/-- Signed area in pair coordinates. -/
def pairCross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- Coordinatewise subtraction in the pair model. -/
def pairSub (u v : ℝ × ℝ) : ℝ × ℝ := (u.1 - v.1, u.2 - v.2)

/--
An honest source-dependent chart for the locality argument.

Unlike `CyclicHullData.frame`, this chart is not an arbitrary exposing
frame: downstream `BisectorFrame` constructs it from the two incident hull
edges.  The support field is the weak half-plane fact actually consumed by
the local case modules; the constructed bisector chart is strict away from
the source.  The last field records its orientation convention exactly.  It
is a coordinate identity, not a locality or collision estimate.
-/
structure AlignedChartData where
  coord : {p // p ∈ P.H} → Vertex A → ℝ × ℝ
  coord_source : ∀ i, coord i i.1 = (0, 0)
  sqDist_coord : ∀ i q r,
    Erdos957Cases13.sqDist (coord i q) (coord i r) =
      dist (q : Point) (r : Point) ^ 2
  coord_snd_nonpos : ∀ i q, (coord i q).2 ≤ 0
  cross_displacements : ∀ i p q r,
    pairCross (pairSub (coord i q) (coord i p))
        (pairSub (coord i r) (coord i p)) =
      -cross ((q : Point) - (p : Point)) ((r : Point) - (p : Point))

namespace AlignedChartData

variable (C : AlignedChartData (P := P))

/-- The `k`-th forward hull vertex in the honest aligned chart. -/
def rightOrbitCoord (i : {p // p ∈ P.H}) (k : ℕ) : ℝ × ℝ :=
  C.coord i ((P.next ^ k) i).1

/-- The `k`-th backward hull vertex, horizontally reflected so that the two
sides use the same right-going analytic kernel. -/
def leftOrbitReflectedCoord (i : {p // p ∈ P.H}) (k : ℕ) : ℝ × ℝ :=
  let z := C.coord i (((P.next⁻¹) ^ k) i).1
  (-z.1, z.2)

@[simp]
theorem rightOrbitCoord_zero (i : {p // p ∈ P.H}) :
    C.rightOrbitCoord P i 0 = (0, 0) := by
  simp [rightOrbitCoord, C.coord_source]

@[simp]
theorem leftOrbitReflectedCoord_zero (i : {p // p ∈ P.H}) :
    C.leftOrbitReflectedCoord P i 0 = (0, 0) := by
  simp [leftOrbitReflectedCoord, C.coord_source]

/-- Exact metric preservation makes every aligned chart injective. -/
theorem coord_injective (i : {p // p ∈ P.H}) :
    Function.Injective (C.coord i) := by
  intro q r hqr
  have hs := C.sqDist_coord i q r
  rw [hqr] at hs
  simp [Erdos957Cases13.sqDist] at hs
  have hd : dist (q : Point) (r : Point) = 0 := by
    nlinarith [(dist_nonneg : 0 ≤ dist (q : Point) (r : Point))]
  exact Subtype.ext (dist_eq_zero.mp hd)

theorem rightOrbitCoord_succ_ne (i : {p // p ∈ P.H}) (k : ℕ) :
    C.rightOrbitCoord P i (k + 1) ≠ C.rightOrbitCoord P i k := by
  intro h
  apply P.next_pow_succ_ne i k
  apply Subtype.ext
  exact coord_injective P C i h

theorem leftOrbitReflectedCoord_succ_ne (i : {p // p ∈ P.H}) (k : ℕ) :
    C.leftOrbitReflectedCoord P i (k + 1) ≠
      C.leftOrbitReflectedCoord P i k := by
  intro h
  apply P.prev_pow_succ_ne i k
  apply Subtype.ext
  apply coord_injective P C i
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    simp only [leftOrbitReflectedCoord] at hx
    linarith
  · simpa [leftOrbitReflectedCoord] using congrArg Prod.snd h

def canonicalRightRadius (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarRadius (C.rightOrbitCoord P i k.1)
    (C.rightOrbitCoord P i (k.1 + 1))

def canonicalRightAngle (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarAngle (C.rightOrbitCoord P i k.1)
    (C.rightOrbitCoord P i (k.1 + 1))

def canonicalLeftRadius (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarRadius (C.leftOrbitReflectedCoord P i k.1)
    (C.leftOrbitReflectedCoord P i (k.1 + 1))

def canonicalLeftAngle (i : {p // p ∈ P.H}) (k : Fin 4) : ℝ :=
  polarAngle (C.leftOrbitReflectedCoord P i k.1)
    (C.leftOrbitReflectedCoord P i (k.1 + 1))

theorem canonicalRightPolar (i : {p // p ∈ P.H}) (k : Fin 4) :
    Erdos957Locality.IsPolarEdge
      (C.rightOrbitCoord P i k.1) (C.rightOrbitCoord P i (k.1 + 1))
      (C.canonicalRightRadius P i k) (C.canonicalRightAngle P i k) :=
  isPolarEdge_polar _ _ (C.rightOrbitCoord_succ_ne P i k.1).symm

theorem canonicalLeftPolar (i : {p // p ∈ P.H}) (k : Fin 4) :
    Erdos957Locality.IsPolarEdge
      (C.leftOrbitReflectedCoord P i k.1)
      (C.leftOrbitReflectedCoord P i (k.1 + 1))
      (C.canonicalLeftRadius P i k) (C.canonicalLeftAngle P i k) :=
  isPolarEdge_polar _ _ (C.leftOrbitReflectedCoord_succ_ne P i k.1).symm

theorem canonicalRightRadius_ge_one (hA : IsOneSeparated A)
    (i : {p // p ∈ P.H}) (k : Fin 4) :
    1 ≤ C.canonicalRightRadius P i k := by
  let q := ((P.next ^ k.1) i).1
  let r := ((P.next ^ (k.1 + 1)) i).1
  have hqr : q ≠ r := by
    intro h
    exact P.next_pow_succ_ne i k.1 (Subtype.ext h).symm
  have hdist := hA q q.property r r.property
    (fun h ↦ hqr (Subtype.ext h))
  have hs := polarRadius_sq (C.rightOrbitCoord P i k.1)
    (C.rightOrbitCoord P i (k.1 + 1))
  have hscoord : Erdos957Cases13.sqDist
      (C.rightOrbitCoord P i k.1)
      (C.rightOrbitCoord P i (k.1 + 1)) =
      dist (q : Point) (r : Point) ^ 2 := by
    simpa [rightOrbitCoord] using C.sqDist_coord i q r
  rw [hscoord] at hs
  have hrnonneg : 0 ≤ C.canonicalRightRadius P i k := norm_nonneg _
  change C.canonicalRightRadius P i k ^ 2 = dist (q : Point) (r : Point) ^ 2 at hs
  nlinarith

theorem canonicalLeftRadius_ge_one (hA : IsOneSeparated A)
    (i : {p // p ∈ P.H}) (k : Fin 4) :
    1 ≤ C.canonicalLeftRadius P i k := by
  let q := (((P.next⁻¹) ^ k.1) i).1
  let r := (((P.next⁻¹) ^ (k.1 + 1)) i).1
  have hqr : q ≠ r := by
    intro h
    exact P.prev_pow_succ_ne i k.1 (Subtype.ext h).symm
  have hdist := hA q q.property r r.property
    (fun h ↦ hqr (Subtype.ext h))
  have hs := polarRadius_sq (C.leftOrbitReflectedCoord P i k.1)
    (C.leftOrbitReflectedCoord P i (k.1 + 1))
  have hscoord : Erdos957Cases13.sqDist
      (C.leftOrbitReflectedCoord P i k.1)
      (C.leftOrbitReflectedCoord P i (k.1 + 1)) =
      dist (q : Point) (r : Point) ^ 2 := by
    change Erdos957Cases13.sqDist
      (-(C.coord i q).1, (C.coord i q).2)
      (-(C.coord i r).1, (C.coord i r).2) = _
    rw [← C.sqDist_coord i q r]
    simp [Erdos957Cases13.sqDist]
    ring
  rw [hscoord] at hs
  have hrnonneg : 0 ≤ C.canonicalLeftRadius P i k := norm_nonneg _
  change C.canonicalLeftRadius P i k ^ 2 = dist (q : Point) (r : Point) ^ 2 at hs
  nlinarith

/-- Finite coordinate image of the whole configuration. -/
def configuration (i : {p // p ∈ P.H}) : Finset (ℝ × ℝ) :=
  Finset.univ.map ⟨C.coord i, coord_injective P C i⟩

/-- Finite coordinate image of the exact cyclic hull. -/
def hullImage (i : {p // p ∈ P.H}) : Finset (ℝ × ℝ) :=
  P.H.map ⟨C.coord i, coord_injective P C i⟩

theorem coord_mem_configuration (i : {p // p ∈ P.H}) (q : Vertex A) :
    C.coord i q ∈ C.configuration P i := by
  exact Finset.mem_map.mpr ⟨q, Finset.mem_univ _, rfl⟩

theorem coord_mem_hullImage (i : {p // p ∈ P.H}) {q : Vertex A}
    (hq : q ∈ P.H) : C.coord i q ∈ C.hullImage P i := by
  exact Finset.mem_map.mpr ⟨q, hq, rfl⟩

@[simp]
theorem origin_mem_configuration (i : {p // p ∈ P.H}) :
    Erdos957Cases13.origin ∈ C.configuration P i := by
  change (0, 0) ∈ C.configuration P i
  rw [← C.coord_source i]
  exact C.coord_mem_configuration P i i.1

@[simp]
theorem origin_mem_hullImage (i : {p // p ∈ P.H}) :
    Erdos957Cases13.origin ∈ C.hullImage P i := by
  change (0, 0) ∈ C.hullImage P i
  rw [← C.coord_source i]
  exact C.coord_mem_hullImage P i i.property

/-- The exact weak supporting-half-plane statement used by the local case
bridges. -/
theorem configuration_below_support (i : {p // p ∈ P.H}) :
    ∀ p ∈ C.configuration P i, p.2 ≤ 0 := by
  intro p hp
  rcases Finset.mem_map.mp hp with ⟨q, _, rfl⟩
  exact C.coord_snd_nonpos i q

/-- Minimum separation transports to an arbitrary honest aligned chart. -/
theorem configuration_oneSeparated (hA : IsOneSeparated A)
    (i : {p // p ∈ P.H}) :
    Erdos957Cases13.IsOneSeparated (C.configuration P i : Set (ℝ × ℝ)) := by
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨q, _, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨r, _, rfl⟩
  have hqr : q ≠ r := fun h ↦ hxy (congrArg (C.coord i) h)
  change 1 ≤ Erdos957Cases13.sqDist (C.coord i q) (C.coord i r)
  rw [C.sqDist_coord]
  have hdist := hA q q.property r r.property (fun h ↦ hqr (Subtype.ext h))
  nlinarith [(dist_nonneg : 0 ≤ dist (q : Point) (r : Point))]

/-- Unit-distance graph degree is invariant under an honest aligned chart. -/
theorem case13_degree_coord (i : {p // p ∈ P.H}) (q : Vertex A) :
    Erdos957Case13Bridge.degree (C.configuration P i) (C.coord i q) =
      (unitDistanceGraph A).degree q := by
  classical
  rw [Erdos957Case13Bridge.degree, SimpleGraph.degree]
  apply Finset.card_bij
    (s := Erdos957Case13Bridge.unitNeighbors (C.configuration P i) (C.coord i q))
    (t := (unitDistanceGraph A).neighborFinset q)
    (fun p hp ↦ Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1))
  · intro p hp
    let r : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)
    have hrCoord : C.coord i r = p :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)).2
    have hsquare := (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).2
    rw [← hrCoord, C.sqDist_coord] at hsquare
    have hdist : dist (q : Point) (r : Point) = 1 := by
      nlinarith [(dist_nonneg : 0 ≤ dist (q : Point) (r : Point))]
    exact (SimpleGraph.mem_neighborFinset (G := unitDistanceGraph A) (v := q) r).mpr hdist
  · intro p hp r hr hpr
    let p' : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)
    let r' : Vertex A := Classical.choose
      (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hr).1)
    have hpCoord : C.coord i p' = p :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hp).1)).2
    have hrCoord : C.coord i r' = r :=
      (Classical.choose_spec
        (Finset.mem_map.mp (Erdos957Case13Bridge.mem_unitNeighbors.mp hr).1)).2
    have hvertex : p' = r' := hpr
    rw [← hpCoord, ← hrCoord, hvertex]
  · intro r hr
    refine ⟨C.coord i r, ?_, ?_⟩
    · apply Erdos957Case13Bridge.mem_unitNeighbors.mpr
      refine ⟨C.coord_mem_configuration P i r, ?_⟩
      rw [C.sqDist_coord]
      have hdist :=
        (SimpleGraph.mem_neighborFinset (G := unitDistanceGraph A) (v := q) r).mp hr
      rw [hdist]
      norm_num
    · dsimp
      exact (coord_injective P C i)
        (Classical.choose_spec
          (Finset.mem_map.mp (C.coord_mem_configuration P i r))).2

end AlignedChartData

/-- Angle-bisector alignment for the first four edges on both sides of a
flat source.  The record owns the genuine chart on which its polar data are
stated; no conclusion about arrivals, collisions, or capacity is a field. -/
structure FlatAlignedFrameData where
  chart : AlignedChartData (P := P)
  rightRadius : {p // p ∈ P.H} → Fin 4 → ℝ
  rightAngle : {p // p ∈ P.H} → Fin 4 → ℝ
  rightPolar : ∀ (i : {p // p ∈ P.H}) (k : Fin 4),
    Erdos957Locality.IsPolarEdge
      (chart.rightOrbitCoord P i k.1)
      (chart.rightOrbitCoord P i (k.1 + 1))
      (rightRadius i k) (rightAngle i k)
  rightRadius_ge_one : ∀ i k, 1 ≤ rightRadius i k
  rightFlatAngles : ∀ i, P.IsFlat i →
    |rightAngle i 0| ≤ Real.pi / 180 ∧
    |rightAngle i 1 - rightAngle i 0| ≤ Real.pi / 180 ∧
    |rightAngle i 2 - rightAngle i 1| ≤ Real.pi / 180 ∧
    |rightAngle i 3 - rightAngle i 2| ≤ Real.pi / 180
  leftRadius : {p // p ∈ P.H} → Fin 4 → ℝ
  leftAngle : {p // p ∈ P.H} → Fin 4 → ℝ
  leftPolar : ∀ (i : {p // p ∈ P.H}) (k : Fin 4),
    Erdos957Locality.IsPolarEdge
      (chart.leftOrbitReflectedCoord P i k.1)
      (chart.leftOrbitReflectedCoord P i (k.1 + 1))
      (leftRadius i k) (leftAngle i k)
  leftRadius_ge_one : ∀ i k, 1 ≤ leftRadius i k
  leftFlatAngles : ∀ i, P.IsFlat i →
    |leftAngle i 0| ≤ Real.pi / 180 ∧
    |leftAngle i 1 - leftAngle i 0| ≤ Real.pi / 180 ∧
    |leftAngle i 2 - leftAngle i 1| ≤ Real.pi / 180 ∧
    |leftAngle i 3 - leftAngle i 2| ≤ Real.pi / 180

namespace FlatAlignedFrameData

variable (F : FlatAlignedFrameData (P := P))
include F

/-- Four forward one-separated flat hull edges leave the expanded source
rectangle through its right side. -/
theorem right_four_steps_exit (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    (399 / 100 : ℝ) < (F.chart.rightOrbitCoord P i 4).1 := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    FlatAlignedFrameData.rightFlatAngles F i hi
  exact Erdos957Locality.four_polar_flat_edges_exit_right
    (p₀ := F.chart.rightOrbitCoord P i 0)
    (p₁ := F.chart.rightOrbitCoord P i 1)
    (p₂ := F.chart.rightOrbitCoord P i 2)
    (p₃ := F.chart.rightOrbitCoord P i 3)
    (p₄ := F.chart.rightOrbitCoord P i 4)
    (r₀ := F.rightRadius i 0) (r₁ := F.rightRadius i 1)
    (r₂ := F.rightRadius i 2) (r₃ := F.rightRadius i 3)
    (θ₀ := F.rightAngle i 0) (θ₁ := F.rightAngle i 1)
    (θ₂ := F.rightAngle i 2) (θ₃ := F.rightAngle i 3)
    (by simp) (F.rightPolar i 0) (F.rightPolar i 1)
    (F.rightPolar i 2) (F.rightPolar i 3)
    (F.rightRadius_ge_one i 0) (F.rightRadius_ge_one i 1)
    (F.rightRadius_ge_one i 2) (F.rightRadius_ge_one i 3)
    h0 h1 h2 h3

/-- The reflected four backward edges satisfy the same right-exit bound;
equivalently, the actual fourth predecessor lies left of `-399/100`. -/
theorem left_four_steps_exit (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    (399 / 100 : ℝ) < (F.chart.leftOrbitReflectedCoord P i 4).1 := by
  obtain ⟨h0, h1, h2, h3⟩ :=
    FlatAlignedFrameData.leftFlatAngles F i hi
  exact Erdos957Locality.four_polar_flat_edges_exit_right
    (p₀ := F.chart.leftOrbitReflectedCoord P i 0)
    (p₁ := F.chart.leftOrbitReflectedCoord P i 1)
    (p₂ := F.chart.leftOrbitReflectedCoord P i 2)
    (p₃ := F.chart.leftOrbitReflectedCoord P i 3)
    (p₄ := F.chart.leftOrbitReflectedCoord P i 4)
    (r₀ := F.leftRadius i 0) (r₁ := F.leftRadius i 1)
    (r₂ := F.leftRadius i 2) (r₃ := F.leftRadius i 3)
    (θ₀ := F.leftAngle i 0) (θ₁ := F.leftAngle i 1)
    (θ₂ := F.leftAngle i 2) (θ₃ := F.leftAngle i 3)
    (by simp) (F.leftPolar i 0) (F.leftPolar i 1)
    (F.leftPolar i 2) (F.leftPolar i 3)
    (F.leftRadius_ge_one i 0) (F.leftRadius_ge_one i 1)
    (F.leftRadius_ge_one i 2) (F.leftRadius_ge_one i 3)
    h0 h1 h2 h3

end FlatAlignedFrameData

end CyclicHullData

/- The separation assumption is kept outside `CyclicHullData`, so the same
cyclic hull record can also be used before shortest-distance normalization. -/

/-- Genuine farthest-point witnesses for selected hull vertices. -/
structure DiameterWitnessData {A : Finset Point} (P : CyclicHullData A) where
  D : Finset (Vertex A)
  radius : ℝ
  radius_ge_101 : 101 ≤ radius
  endpoint_mem_hull : D ⊆ P.H
  opposite : (p : Vertex A) → p ∈ D → Vertex A
  opposite_ne : ∀ (p : Vertex A) (hp : p ∈ D), opposite p hp ≠ p
  opposite_distance : ∀ (p : Vertex A) (hp : p ∈ D),
    dist (p : Point) (opposite p hp : Point) = radius
  endpoint_complete : ∀ (p q : Vertex A), q ≠ p →
    dist (p : Point) (q : Point) = radius → p ∈ D
  maximal : ∀ x y : Vertex A, dist (x : Point) (y : Point) ≤ radius

namespace DiameterWitnessData

variable {A : Finset Point} {P : CyclicHullData A} (W : DiameterWitnessData P)

/-- Membership in the selected endpoint finset is exactly incidence to a
pair at the recorded maximum distance.  The forward implication uses the
stored genuine opposite; the reverse implication is `endpoint_complete`. -/
theorem mem_D_iff (p : Vertex A) :
    p ∈ W.D ↔ ∃ q : Vertex A, q ≠ p ∧
      dist (p : Point) (q : Point) = W.radius := by
  constructor
  · intro hp
    exact ⟨W.opposite p hp, W.opposite_ne p hp, W.opposite_distance p hp⟩
  · rintro ⟨q, hqp, hpq⟩
    exact W.endpoint_complete p q hqp hpq

/-- The chosen opposite is itself an endpoint of a radius pair. -/
theorem opposite_mem_D (p : Vertex A) (hp : p ∈ W.D) :
    W.opposite p hp ∈ W.D := by
  apply W.endpoint_complete (W.opposite p hp) p
  · exact (W.opposite_ne p hp).symm
  · simpa [dist_comm] using W.opposite_distance p hp

/-- The chosen opposite, regarded as a genuine cyclic hull index. -/
def oppositeIndex (p : Vertex A) (hp : p ∈ W.D) : {q // q ∈ P.H} :=
  ⟨W.opposite p hp, W.endpoint_mem_hull (W.opposite_mem_D p hp)⟩

/-- Maximality of the opposite pair forces a positive projection onto every
displacement from the endpoint.  This is the coordinate-free algebraic core
of the diameter-direction lemma. -/
theorem displacement_sq_le_two_inner_opposite
    (p : Vertex A) (hp : p ∈ W.D) (a : Vertex A) :
    ‖(a : Point) - p‖ ^ 2 ≤
      2 * ⟪(W.opposite p hp : Point) - p, (a : Point) - p⟫ := by
  let q : Vertex A := W.opposite p hp
  have hmax : dist (q : Point) (a : Point) ≤ W.radius := W.maximal q a
  have hqnorm : ‖(q : Point) - p‖ = W.radius := by
    rw [← dist_eq_norm]
    simpa [q, dist_comm] using W.opposite_distance p hp
  have hsq : ‖((q : Point) - p) - ((a : Point) - p)‖ ^ 2 ≤
      ‖(q : Point) - p‖ ^ 2 := by
    have hnonneg : 0 ≤ dist (q : Point) (a : Point) := dist_nonneg
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hqnorm]
    nlinarith
  rw [norm_sub_sq_real] at hsq
  nlinarith

/-- Under one-separation, every other configuration point has projection at
least `1/2` onto the diameter vector. -/
theorem one_le_two_inner_opposite
    (hA : IsOneSeparated A) (p : Vertex A) (hp : p ∈ W.D)
    (a : Vertex A) (hap : a ≠ p) :
    1 ≤ 2 * ⟪(W.opposite p hp : Point) - p, (a : Point) - p⟫ := by
  have hdist : 1 ≤ dist (a : Point) (p : Point) :=
    hA a a.property p p.property (fun h ↦ hap (Subtype.ext h))
  have hnorm : 1 ≤ ‖(a : Point) - p‖ := by
    simpa [dist_eq_norm] using hdist
  have hsquare : 1 ≤ ‖(a : Point) - p‖ ^ 2 := by
    nlinarith [norm_nonneg ((a : Point) - p)]
  exact hsquare.trans (W.displacement_sq_le_two_inner_opposite p hp a)

/-- Ambient maximum-distance endpoints, lifted to the actual vertex type. -/
def liftedDistanceEndpoints : Finset (Vertex A) :=
  Finset.univ.filter fun p ↦
    (p : Point) ∈ Erdos957.distanceEndpoints A W.radius

@[simp]
theorem mem_liftedDistanceEndpoints (p : Vertex A) :
    p ∈ W.liftedDistanceEndpoints ↔
      (p : Point) ∈ Erdos957.distanceEndpoints A W.radius := by
  simp [liftedDistanceEndpoints]

/-- The witness endpoint set is not an arbitrary subset: it is precisely
the production ambient endpoint set, lifted to the vertex subtype. -/
theorem D_eq_liftedDistanceEndpoints : W.D = W.liftedDistanceEndpoints := by
  classical
  ext p
  rw [W.mem_D_iff, W.mem_liftedDistanceEndpoints,
    Erdos957.mem_distanceEndpoints]
  constructor
  · rintro ⟨q, hqp, hpq⟩
    exact ⟨p.property, (q : Point), q.property,
      fun h ↦ hqp (Subtype.ext h.symm), hpq⟩
  · rintro ⟨_hpA, q, hqA, hpq, hdist⟩
    exact ⟨⟨q, hqA⟩, fun h ↦ hpq (congrArg Subtype.val h).symm, hdist⟩

/-- Consequently the endpoint cardinality agrees exactly with the ambient
`distanceEndpoints` cardinality used by final assembly. -/
theorem card_D_eq_distanceEndpoints :
    W.D.card = (Erdos957.distanceEndpoints A W.radius).card := by
  classical
  rw [W.D_eq_liftedDistanceEndpoints]
  apply Finset.card_bij
    (s := W.liftedDistanceEndpoints)
    (t := Erdos957.distanceEndpoints A W.radius)
    (fun p _ ↦ (p : Point))
  · intro p hp
    exact (W.mem_liftedDistanceEndpoints p).mp hp
  · intro p _ q _ hpq
    exact Subtype.ext hpq
  · intro p hp
    refine ⟨⟨p, (Erdos957.mem_distanceEndpoints.mp hp).1⟩, ?_, rfl⟩
    exact (W.mem_liftedDistanceEndpoints ⟨p,
      (Erdos957.mem_distanceEndpoints.mp hp).1⟩).mpr hp

end DiameterWitnessData

/-- Genuine maximum-distance data canonically supplies the complete endpoint
set and an opposite witness for every endpoint. -/
noncomputable def diameterWitnessDataOfMaximumDistance
    {A : Finset Point} (P : CyclicHullData A) {r : ℝ}
    (hr : 101 ≤ r) (hmax : Erdos957.IsMaximumDistance A r) :
    DiameterWitnessData P := by
  classical
  let D : Finset (Vertex A) :=
    Finset.univ.filter fun p ↦ ∃ q : Vertex A, q ≠ p ∧ dist (p : Point) (q : Point) = r
  have hmemD (p : Vertex A) :
      p ∈ D ↔ ∃ q : Vertex A, q ≠ p ∧ dist (p : Point) (q : Point) = r := by
    simp [D]
  have hopposite (p : Vertex A) (hp : p ∈ D) :
      ∃ q : Vertex A, q ≠ p ∧ dist (p : Point) (q : Point) = r :=
    (hmemD p).mp hp
  let opposite : (p : Vertex A) → p ∈ D → Vertex A :=
    fun p hp ↦ Classical.choose (hopposite p hp)
  have hoppositeSpec (p : Vertex A) (hp : p ∈ D) :
      opposite p hp ≠ p ∧ dist (p : Point) (opposite p hp : Point) = r :=
    Classical.choose_spec (hopposite p hp)
  refine {
    D := D
    radius := r
    radius_ge_101 := hr
    endpoint_mem_hull := ?_
    opposite := opposite
    opposite_ne := fun p hp ↦ (hoppositeSpec p hp).1
    opposite_distance := fun p hp ↦ (hoppositeSpec p hp).2
    endpoint_complete := ?_
    maximal := ?_ }
  · intro p hp
    apply (P.hull_exact p).mpr
    let q := opposite p hp
    have hpA : (p : Point) ∈ (A : Set Point) := p.property
    have hpq : (p : Point) ≠ (q : Point) := by
      exact fun h ↦ (hoppositeSpec p hp).1 (Subtype.ext h.symm)
    apply Erdos957.farthestPoint_mem_extremePoints_convexHull
      (A : Set Point) hpA hpq
    intro z hzA
    by_cases hzq : z = (q : Point)
    · subst z
      simp [q, (hoppositeSpec p hp).2]
      linarith
    · have hbound := hmax.2 (dist z (q : Point))
          (Erdos957.dist_mem_distanceSet hzA q.property hzq)
      simpa [q, (hoppositeSpec p hp).2] using hbound
  · intro p q hpq hdist
    apply (hmemD p).mpr
    exact ⟨q, hpq, hdist⟩
  · intro x y
    by_cases hxy : (x : Point) = (y : Point)
    · rw [hxy, dist_self]
      linarith
    · exact hmax.2 (dist (x : Point) (y : Point))
        (Erdos957.dist_mem_distanceSet x.property y.property hxy)

/-- All flat diameter endpoints, including those already of degree at most two. -/
def distinguishedVertices {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) : Finset (Vertex A) :=
  W.D ∩ P.flatVertices

/-- Degree-three distinguished endpoints: exactly the vertices which must emit two tokens. -/
def sourceVertices {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) : Finset (Vertex A) :=
  (distinguishedVertices P W).filter fun p ↦ (unitDistanceGraph A).degree p = 3

lemma distinguishedVertices_subset_hull {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) : distinguishedVertices P W ⊆ P.H := by
  intro p hp
  exact W.endpoint_mem_hull (Finset.mem_inter.mp hp).1

lemma sourceVertices_subset_hull {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) : sourceVertices P W ⊆ P.H := by
  intro p hp
  exact distinguishedVertices_subset_hull P W (Finset.mem_filter.mp hp).1

lemma sourceVertices_subset_distinguished {A : Finset Point} (P : CyclicHullData A)
    (W : DiameterWitnessData P) : sourceVertices P W ⊆ distinguishedVertices P W := by
  exact Finset.filter_subset _ _

/-- At most `2520` diameter endpoints fail to be distinguished. -/
theorem card_diameterEndpoints_le_card_distinguished_add_2520
    {A : Finset Point} (P : CyclicHullData A) (W : DiameterWitnessData P) :
    W.D.card ≤ (distinguishedVertices P W).card + 2520 := by
  have hbadSubset : W.D \ P.flatVertices ⊆ P.H \ P.flatVertices := by
    intro p hp
    rcases Finset.mem_sdiff.mp hp with ⟨hpD, hpFlat⟩
    exact Finset.mem_sdiff.mpr ⟨W.endpoint_mem_hull hpD, hpFlat⟩
  have hbadCard : (W.D \ P.flatVertices).card ≤ 2520 :=
    (Finset.card_le_card hbadSubset).trans P.card_hull_sdiff_flatVertices_le_2520
  have hpartition := Finset.card_inter_add_card_sdiff W.D P.flatVertices
  change W.D.card ≤ (W.D ∩ P.flatVertices).card + 2520
  omega

/-! ## Fully checked special case: no degree-three source -/

private def zeroTransfer {A : Finset Point} : Vertex A → Vertex A → ℕ :=
  fun _ _ ↦ 0

/-- If the problematic source set is empty, all certificate fields follow
from angular packing and strict hull support, with no transfer at all. -/
theorem transferCert_of_sourceVertices_eq_empty {A : Finset Point}
    (hA : IsOneSeparated A) (P : CyclicHullData A) (W : DiameterWitnessData P)
    (hB : sourceVertices P W = ∅) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A) P.H
      (distinguishedVertices P W) (sourceVertices P W)) := by
  classical
  refine ⟨{
    transfer := zeroTransfer
    source_subset_distinguished := sourceVertices_subset_distinguished P W
    distinguished_subset_hull := distinguishedVertices_subset_hull P W
    hull_degree_le_three := ?_
    distinguished_nonsource_degree_le_two := ?_
    source_row_sum := ?_
    target_not_hull := ?_
    nonhull_target_capacity := ?_ }⟩
  · intro v hv
    exact P.hull_degree_le_three hA ⟨v, hv⟩
  · intro v hvQ hvB
    have hvH : v ∈ P.H := distinguishedVertices_subset_hull P W hvQ
    have hdeg := P.hull_degree_le_three hA ⟨v, hvH⟩
    change (unitDistanceGraph A).degree v ≤ 3 at hdeg
    have hne : (unitDistanceGraph A).degree v ≠ 3 := by
      intro heq
      apply hvB
      exact Finset.mem_filter.mpr ⟨hvQ, heq⟩
    omega
  · intro u
    simp [zeroTransfer, hB]
  · intro u v hpos
    simp [zeroTransfer] at hpos
  · intro v hv
    have hdeg := degree_unitDistanceGraph_le_six hA v
    simp [zeroTransfer]
    omega

end Erdos957GeometryCore
