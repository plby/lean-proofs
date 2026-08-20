import ErdosProblems.Erdos957.TransferCert
import ErdosProblems.Erdos957.Overcharge
import ErdosProblems.Erdos957.GeometryLocalRows
import ErdosProblems.Erdos957.GeometryCollisions

/-!
# Global collision bookkeeping for the Erdős 957 transfer

This file performs the finite, source-indexed part of the no-overcharge
argument.  It deliberately does not assume the desired column-capacity
inequality.  Instead, it starts from the conclusions supplied by the local
geometry:

* every positive arrival is at most two doubled tokens;
* a positive target has degree at most five;
* a two-token arrival can occur only at a target of degree at most four;
* the ten unordered case-pair exclusions rule out two distinct sources on
  the same side of a target.

The last item gives at most one source on each of two sides, hence at most two
sources in a column.  The remaining capacity estimate is then arithmetic:
two half arrivals fit at degree five, while any column containing a whole
arrival has degree at most four and total arrival at most four.
-/

namespace Erdos957CollisionGlue

open scoped BigOperators
open Erdos957Overcharge

abbrev ArrivalSide := Bool

def ArrivalSide.left : ArrivalSide := false
def ArrivalSide.right : ArrivalSide := true

@[simp] lemma card_arrivalSide : Fintype.card ArrivalSide = 2 := by
  decide

section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Global row data after each local row has been extended by zero. -/
structure CollisionRows (H Q B : Finset V) where
  transfer : V → V → ℕ
  caseOf : V → CaseNumber
  sideOf : V → V → ArrivalSide
  source_subset_distinguished : B ⊆ Q
  distinguished_subset_hull : Q ⊆ H
  hull_degree_le_three : ∀ v ∈ H, G.degree v ≤ 3
  distinguished_nonsource_degree_le_two :
    ∀ v, v ∈ Q → v ∉ B → G.degree v ≤ 2
  source_row_sum : ∀ u, ∑ v, transfer u v = if u ∈ B then 2 else 0
  target_not_hull : ∀ {u v}, 0 < transfer u v → v ∉ H
  arrival_le_two : ∀ u v, transfer u v ≤ 2
  positive_target_degree_le_five :
    ∀ {u v}, 0 < transfer u v → G.degree v ≤ 5
  whole_target_degree_le_four :
    ∀ {u v}, 2 ≤ transfer u v → G.degree v ≤ 4
  same_side_case_pair_exclusion :
    ∀ {u w v}, u ≠ w → 0 < transfer u v → 0 < transfer w v →
      sideOf u v = sideOf w v →
      ((caseOf u).rank ≤ (caseOf w).rank ∧
          (caseOf u, caseOf w) ∈ casePairs ∨
        (caseOf w).rank ≤ (caseOf u).rank ∧
          (caseOf w, caseOf u) ∈ casePairs) → False

/-- One honest source row before it is extended by zero to all vertices. -/
structure LocalRow (H : Finset V) (source : V) where
  caseNumber : CaseNumber
  side : V → ArrivalSide
  tokens : V → ℕ
  row_sum : ∑ v, tokens v = 2
  target_not_hull : ∀ {v}, 0 < tokens v → v ∉ H
  arrival_le_two : ∀ v, tokens v ≤ 2
  positive_target_degree_le_five : ∀ {v}, 0 < tokens v → G.degree v ≤ 5
  whole_target_degree_le_four : ∀ {v}, 2 ≤ tokens v → G.degree v ≤ 4

/-- A family of local rows indexed by precisely the emitting source set. -/
structure SourceRows (H Q B : Finset V) where
  source_subset_distinguished : B ⊆ Q
  distinguished_subset_hull : Q ⊆ H
  hull_degree_le_three : ∀ v ∈ H, G.degree v ≤ 3
  distinguished_nonsource_degree_le_two :
    ∀ v, v ∈ Q → v ∉ B → G.degree v ≤ 2
  row : ∀ u, u ∈ B → LocalRow G H u
  same_side_case_pair_exclusion :
    ∀ {u w : V} (hu : u ∈ B) (hw : w ∈ B) {v}, u ≠ w →
      0 < (row u hu).tokens v → 0 < (row w hw).tokens v →
      (row u hu).side v = (row w hw).side v →
      (((row u hu).caseNumber).rank ≤ ((row w hw).caseNumber).rank ∧
          ((row u hu).caseNumber, (row w hw).caseNumber) ∈ casePairs ∨
        ((row w hw).caseNumber).rank ≤ ((row u hu).caseNumber).rank ∧
          ((row w hw).caseNumber, (row u hu).caseNumber) ∈ casePairs) → False

namespace SourceRows

variable {G} {H Q B : Finset V}

/-- Extend every local source row by zero outside the source set. -/
noncomputable def sourceIndexedTransfer (R : SourceRows G H Q B) (u v : V) : ℕ :=
  if hu : u ∈ B then (R.row u hu).tokens v else 0

noncomputable def sourceCase (R : SourceRows G H Q B) (u : V) : CaseNumber :=
  if hu : u ∈ B then (R.row u hu).caseNumber else .one

noncomputable def arrivalSide (R : SourceRows G H Q B) (u v : V) : ArrivalSide :=
  if hu : u ∈ B then (R.row u hu).side v else .left

lemma mem_source_of_positive (R : SourceRows G H Q B) {u v : V}
    (hpos : 0 < R.sourceIndexedTransfer u v) : u ∈ B := by
  by_contra hu
  simp [sourceIndexedTransfer, hu] at hpos

/-- Assemble the separately constructed rows into the global collision data.
The proof uses proof irrelevance to identify the membership witnesses selected
by the dependent `if` with the witnesses used by the row family. -/
noncomputable def toCollisionRows (R : SourceRows G H Q B) :
    CollisionRows G H Q B where
  transfer := R.sourceIndexedTransfer
  caseOf := R.sourceCase
  sideOf := R.arrivalSide
  source_subset_distinguished := R.source_subset_distinguished
  distinguished_subset_hull := R.distinguished_subset_hull
  hull_degree_le_three := R.hull_degree_le_three
  distinguished_nonsource_degree_le_two :=
    R.distinguished_nonsource_degree_le_two
  source_row_sum := by
    intro u
    by_cases hu : u ∈ B
    · simp only [sourceIndexedTransfer, dif_pos hu, if_pos hu]
      exact (R.row u hu).row_sum
    · simp [sourceIndexedTransfer, hu]
  target_not_hull := by
    intro u v hpos
    have hu : u ∈ B := R.mem_source_of_positive hpos
    have hpos' : 0 < (R.row u hu).tokens v := by
      simpa only [sourceIndexedTransfer, dif_pos hu] using hpos
    exact (R.row u hu).target_not_hull hpos'
  arrival_le_two := by
    intro u v
    by_cases hu : u ∈ B
    · simpa only [sourceIndexedTransfer, dif_pos hu] using
        (R.row u hu).arrival_le_two v
    · simp [sourceIndexedTransfer, hu]
  positive_target_degree_le_five := by
    intro u v hpos
    have hu : u ∈ B := R.mem_source_of_positive hpos
    exact (R.row u hu).positive_target_degree_le_five (by
      simpa only [sourceIndexedTransfer, dif_pos hu] using hpos)
  whole_target_degree_le_four := by
    intro u v hwhole
    have hpos : 0 < R.sourceIndexedTransfer u v := by omega
    have hu : u ∈ B := R.mem_source_of_positive hpos
    exact (R.row u hu).whole_target_degree_le_four (by
      simpa only [sourceIndexedTransfer, dif_pos hu] using hwhole)
  same_side_case_pair_exclusion := by
    intro u w v hne huPos hwPos hside hpairs
    have hu : u ∈ B := R.mem_source_of_positive huPos
    have hw : w ∈ B := R.mem_source_of_positive hwPos
    apply R.same_side_case_pair_exclusion hu hw hne
    · simpa only [sourceIndexedTransfer, dif_pos hu] using huPos
    · simpa only [sourceIndexedTransfer, dif_pos hw] using hwPos
    · simpa only [arrivalSide, dif_pos hu, dif_pos hw] using hside
    · simpa only [sourceCase, dif_pos hu, dif_pos hw] using hpairs

end SourceRows

namespace CollisionRows

variable {G} {H Q B : Finset V}

/-- The sources which make a positive contribution to the column at `v`. -/
def incomingSources (C : CollisionRows G H Q B) (v : V) : Finset V :=
  Finset.univ.filter fun u ↦ 0 < C.transfer u v

@[simp] lemma mem_incomingSources (C : CollisionRows G H Q B) {u v : V} :
    u ∈ C.incomingSources v ↔ 0 < C.transfer u v := by
  simp [incomingSources]

/-- The ten-pair table excludes two distinct incoming sources on one side. -/
lemma eq_of_mem_incomingSources_of_same_side (C : CollisionRows G H Q B)
    {u w v : V} (hu : u ∈ C.incomingSources v)
    (hw : w ∈ C.incomingSources v)
    (hside : C.sideOf u v = C.sideOf w v) : u = w := by
  by_contra hne
  apply C.same_side_case_pair_exclusion hne
      (C.mem_incomingSources.mp hu) (C.mem_incomingSources.mp hw) hside
  rcases le_total (C.caseOf u).rank (C.caseOf w).rank with huw | hwu
  · exact Or.inl ⟨huw, mem_casePairs_of_le _ _ huw⟩
  · exact Or.inr ⟨hwu, mem_casePairs_of_le _ _ hwu⟩

/-- There is at most one incoming source on each of the two sides. -/
theorem card_incomingSources_le_two (C : CollisionRows G H Q B) (v : V) :
    (C.incomingSources v).card ≤ 2 := by
  classical
  have hinj : Set.InjOn (fun u ↦ C.sideOf u v) (C.incomingSources v) := by
    intro u hu w hw hside
    exact C.eq_of_mem_incomingSources_of_same_side hu hw hside
  have hcard : (C.incomingSources v).card ≤ Fintype.card ArrivalSide := by
    exact Finset.card_le_card_of_injOn (fun u ↦ C.sideOf u v)
      (by
        intro u hu
        exact Finset.mem_univ (C.sideOf u v)) hinj
  simpa using hcard

/-- Replacing the full incoming sum by the positive-source fiber. -/
lemma sum_incoming_eq_sum_incomingSources (C : CollisionRows G H Q B) (v : V) :
    ∑ u, C.transfer u v = ∑ u ∈ C.incomingSources v, C.transfer u v := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  have hnot : ¬ 0 < C.transfer u v := by
    simpa [incomingSources] using hu
  omega

/-- If every arrival in a column is a half arrival, the total is at most two. -/
lemma sum_incoming_le_two_of_all_le_one (C : CollisionRows G H Q B) (v : V)
    (hhalf : ∀ u, C.transfer u v ≤ 1) :
    ∑ u, C.transfer u v ≤ 2 := by
  rw [C.sum_incoming_eq_sum_incomingSources v]
  calc
    ∑ u ∈ C.incomingSources v, C.transfer u v
        ≤ ∑ _u ∈ C.incomingSources v, 1 := by
          exact Finset.sum_le_sum fun u _ ↦ hhalf u
    _ = (C.incomingSources v).card := by simp
    _ ≤ 2 := C.card_incomingSources_le_two v

/-- With at most two sources and at most two tokens per source, a column has
at most four incoming doubled tokens. -/
lemma sum_incoming_le_four (C : CollisionRows G H Q B) (v : V) :
    ∑ u, C.transfer u v ≤ 4 := by
  rw [C.sum_incoming_eq_sum_incomingSources v]
  calc
    ∑ u ∈ C.incomingSources v, C.transfer u v
        ≤ ∑ _u ∈ C.incomingSources v, 2 := by
          exact Finset.sum_le_sum fun u _ ↦ C.arrival_le_two u v
    _ = 2 * (C.incomingSources v).card := by simp [Nat.mul_comm]
    _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 (C.card_incomingSources_le_two v)
    _ = 4 := by norm_num

/-- Version of the capacity theorem with the ambient kissing-number bound
made explicit.  This hypothesis is needed only for columns receiving no
tokens and is supplied globally by one-separation. -/
theorem nonhull_target_capacity_of_degree_le_six
    (C : CollisionRows G H Q B) (hdegree : ∀ v, G.degree v ≤ 6)
    (v : V) (_hv : v ∉ H) :
    2 * G.degree v + ∑ u, C.transfer u v ≤ 12 := by
  classical
  by_cases hin : C.incomingSources v = ∅
  · have hzero : ∑ u, C.transfer u v = 0 := by
      rw [C.sum_incoming_eq_sum_incomingSources v, hin]
      simp
    have hdeg := hdegree v
    omega
  · by_cases hwhole : ∃ u, 2 ≤ C.transfer u v
    · obtain ⟨u, hu⟩ := hwhole
      have hdeg : G.degree v ≤ 4 := C.whole_target_degree_le_four hu
      have hsum : ∑ w, C.transfer w v ≤ 4 := C.sum_incoming_le_four v
      omega
    · have hhalf : ∀ u, C.transfer u v ≤ 1 := by
        intro u
        have hnot : ¬ 2 ≤ C.transfer u v := by
          intro hu
          exact hwhole ⟨u, hu⟩
        omega
      have hsum : ∑ u, C.transfer u v ≤ 2 :=
        C.sum_incoming_le_two_of_all_le_one v hhalf
      have hmem : (C.incomingSources v).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hin
      obtain ⟨u, hu⟩ := hmem
      have hdeg : G.degree v ≤ 5 :=
        C.positive_target_degree_le_five (C.mem_incomingSources.mp hu)
      omega

/-- Assemble the source rows into the production `TransferCert`. -/
def toTransferCert (C : CollisionRows G H Q B)
    (hdegree : ∀ v, G.degree v ≤ 6) : Erdos957.TransferCert G H Q B where
  transfer := C.transfer
  source_subset_distinguished := C.source_subset_distinguished
  distinguished_subset_hull := C.distinguished_subset_hull
  hull_degree_le_three := C.hull_degree_le_three
  distinguished_nonsource_degree_le_two :=
    C.distinguished_nonsource_degree_le_two
  source_row_sum := C.source_row_sum
  target_not_hull := C.target_not_hull
  nonhull_target_capacity := C.nonhull_target_capacity_of_degree_le_six hdegree

end CollisionRows

end

end Erdos957CollisionGlue

/-!
## Instantiation on actual geometric source rows

The declarations below connect the genuine per-source rows to the checked
ten-pair collision table.  The witness structure stores only primitive
same-side uniqueness and Figure 10/13/14/15 picture data, never a capacity
bound.
-/

noncomputable section

namespace Erdos957CollisionInstantiation

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957GeometryCollisions
open Erdos957Overcharge
open scoped BigOperators RealInnerProductSpace

variable {A : Finset Point} (P : CyclicHullData A)
variable (W : DiameterWitnessData P)
variable (chart : P.AlignedChartData)

abbrev Source := {u : Vertex A // u ∈ sourceVertices P W}

variable (hlocal : HasLocalCases P W chart)

noncomputable def selectedCase (s : Source P W) :
    LocalCase P chart (sourceIndex P W s.1 s.property) :=
  hlocal s.1 s.property

noncomputable def sourceTokens (s : Source P W) (v : Vertex A) : ℕ :=
  (selectedCase P W chart hlocal s).tokens v

noncomputable def sourceCaseTag (s : Source P W) : CaseNumber :=
  (selectedCase P W chart hlocal s).caseTag

def actualExtremeNeighbors (v : Vertex A) : Finset (Vertex A) :=
  P.H.filter fun w ↦ (unitDistanceGraph A).Adj v w

def actualNeighbors (_P : CyclicHullData A) (v : Vertex A) : Finset (Vertex A) :=
  (unitDistanceGraph A).neighborFinset v

@[simp] lemma card_actualNeighbors (v : Vertex A) :
    (actualNeighbors P v).card = (unitDistanceGraph A).degree v := rfl

private lemma three_bool_pair (a b c : Bool) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- The primitive actual-coordinate data used by the four dangerous entries
of the ten-pair overcharge table.  These are degree, coordinate, and
incidence statements only; they contain no incoming-sum or capacity bound. -/
structure CollisionPictures where
  one_four_picture : ∀ {s t v}, s ≠ t →
    sourceCaseTag P W chart hlocal s = .one →
    sourceCaseTag P W chart hlocal t = .four →
    sourceTokens P W chart hlocal s v = 1 →
    sourceTokens P W chart hlocal t v = 2 →
    (unitDistanceGraph A).degree v = 5 →
    ∃ (height : ℝ) (w c : ℝ × ℝ), w = c ∧
      Real.sqrt 3 ≤ horizontalLineDistance height w ∧
      horizontalLineDistance height c < 1
  two_four_picture : ∀ {s t v}, s ≠ t →
    sourceCaseTag P W chart hlocal s = .two →
    sourceCaseTag P W chart hlocal t = .four →
    sourceTokens P W chart hlocal s v = 1 →
    sourceTokens P W chart hlocal t v = 2 →
    (unitDistanceGraph A).degree v = 5 →
    ∃ (u j d : ℝ × ℝ),
      Erdos957Overcharge.sqDist u d = 1 ∧
      Erdos957Overcharge.sqDist j d = 1 ∧
      Erdos957Overcharge.sqDist u j = 1 ∧
      d.2 = -(Real.sqrt 3 / 2) ∧ d.2 < u.2 ∧ d.2 < j.2 ∧
      u.2 < 0 ∧ j.2 < 0
  three_four_counts : ∀ {s t v}, s ≠ t →
    sourceCaseTag P W chart hlocal s = .three →
    sourceCaseTag P W chart hlocal t = .four →
    sourceTokens P W chart hlocal s v = 1 →
    sourceTokens P W chart hlocal t v = 2 →
    (unitDistanceGraph A).degree v = 5 →
    (actualExtremeNeighbors P v).card = 1 ∧
      ((actualExtremeNeighbors P v).card = 0 ∨
        (actualExtremeNeighbors P v).card = 2)
  four_four_forced_six : ∀ {s t v}, s ≠ t →
    sourceCaseTag P W chart hlocal s = .four →
    sourceCaseTag P W chart hlocal t = .four →
    0 < sourceTokens P W chart hlocal s v →
    0 < sourceTokens P W chart hlocal t v →
    3 ≤ sourceTokens P W chart hlocal s v +
      sourceTokens P W chart hlocal t v →
    (unitDistanceGraph A).degree v = 5 →
    ∃ displayed : Fin 6 → Vertex A, Function.Injective displayed ∧
      ∀ i, displayed i ∈ actualNeighbors P v

/-- The generalized Case 4 construction makes the four formerly dangerous
degree-five pictures vacuous.  A whole arrival is emitted only by an
explicit degree-at-most-four constructor; every five-valent Case 4 row is
split into two half arrivals. -/
theorem automaticCollisionPictures :
    CollisionPictures P W chart hlocal where
  one_four_picture := by
    intro s t v hst hs ht hqs hqt hd
    exfalso
    have hdeg :=
      (selectedCase P W chart hlocal t).whole_target_degree_le_four hqt
    omega
  two_four_picture := by
    intro s t v hst hs ht hqs hqt hd
    exfalso
    have hdeg :=
      (selectedCase P W chart hlocal t).whole_target_degree_le_four hqt
    omega
  three_four_counts := by
    intro s t v hst hs ht hqs hqt hd
    exfalso
    have hdeg :=
      (selectedCase P W chart hlocal t).whole_target_degree_le_four hqt
    omega
  four_four_forced_six := by
    intro s t v hst hs ht hps hpt hheavy hd
    exfalso
    have hsw : sourceTokens P W chart hlocal s v = 1 ∨
        sourceTokens P W chart hlocal s v = 2 :=
      (selectedCase P W chart hlocal s).positive_weight hps
    have htw : sourceTokens P W chart hlocal t v = 1 ∨
        sourceTokens P W chart hlocal t v = 2 :=
      (selectedCase P W chart hlocal t).positive_weight hpt
    rcases hsw with hs1 | hs2
    · rcases htw with ht1 | ht2
      · omega
      · have hdeg :=
          (selectedCase P W chart hlocal t).whole_target_degree_le_four ht2
        omega
    · have hdeg :=
        (selectedCase P W chart hlocal s).whole_target_degree_le_four hs2
      omega

/-- Primitive actual-vertex collision witnesses, with the older two-side
form of the no-three-sources argument. -/
structure CollisionWitnesses extends CollisionPictures P W chart hlocal where
  sideOf : Source P W → Vertex A → Bool
  same_side_unique : ∀ {s t : Source P W} {v},
    0 < sourceTokens P W chart hlocal s v →
    0 < sourceTokens P W chart hlocal t v →
    sideOf s v = sideOf t v → s = t

/-- The precise interface expected from the remaining geometric collision
argument.  Locality first places every competing source in the actual
seven-vertex window; the genuinely case/role-specific theorem then proves
uniqueness only inside that window and only for arrivals assigned the same
side.  Neither field is an incoming-sum or capacity inequality. -/
structure WindowedCollisionWitnesses extends CollisionPictures P W chart hlocal where
  sideOf : Source P W → Vertex A → Bool
  competing_source_in_window : ∀ {s t : Source P W} {v},
    0 < sourceTokens P W chart hlocal s v →
    0 < sourceTokens P W chart hlocal t v →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1)
  same_side_unique_in_window : ∀ {s t : Source P W} {v},
    0 < sourceTokens P W chart hlocal s v →
    0 < sourceTokens P W chart hlocal t v →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    sideOf s v = sideOf t v → s = t

namespace WindowedCollisionWitnesses

variable {P W chart hlocal}

/-- The smallest window-local side theorem is sufficient for the existing
Boolean-pigeonhole and ten-pair assembly. -/
noncomputable def toCollisionWitnesses
    (C : WindowedCollisionWitnesses P W chart hlocal) :
    CollisionWitnesses P W chart hlocal where
  toCollisionPictures := C.toCollisionPictures
  sideOf := C.sideOf
  same_side_unique := by
    intro s t v hs ht hside
    exact C.same_side_unique_in_window hs ht
      (C.competing_source_in_window hs ht) hside

end WindowedCollisionWitnesses

namespace CollisionWitnesses

variable {P W chart hlocal}

/-- Any two distinct actual arrivals satisfy the local capacity estimate.
This no longer needs the historical degree-five pictures: every whole
arrival in the strengthened local-row datatype already targets degree at
most four. -/
theorem actual_pair_fits {s t : Source P W} {v : Vertex A}
    (_hst : s ≠ t)
    (hsp : 0 < sourceTokens P W chart hlocal s v)
    (htp : 0 < sourceTokens P W chart hlocal t v) :
    Fits ((unitDistanceGraph A).degree v)
      (sourceTokens P W chart hlocal s v +
        sourceTokens P W chart hlocal t v) := by
  have hdeg5 :=
    (selectedCase P W chart hlocal s).positive_target_degree_le_five hsp
  have hsw := (selectedCase P W chart hlocal s).positive_weight hsp
  have htw := (selectedCase P W chart hlocal t).positive_weight htp
  rcases hsw with hs1 | hs2 <;> rcases htw with ht1 | ht2
  · change sourceTokens P W chart hlocal s v = 1 at hs1
    change sourceTokens P W chart hlocal t v = 1 at ht1
    simp only [Fits]
    omega
  · have hdeg4 :=
      (selectedCase P W chart hlocal t).whole_target_degree_le_four ht2
    change sourceTokens P W chart hlocal s v = 1 at hs1
    change sourceTokens P W chart hlocal t v = 2 at ht2
    simp only [Fits]
    omega
  · have hdeg4 :=
      (selectedCase P W chart hlocal s).whole_target_degree_le_four hs2
    change sourceTokens P W chart hlocal s v = 2 at hs2
    change sourceTokens P W chart hlocal t v = 1 at ht1
    simp only [Fits]
    omega
  · have hdeg4 :=
      (selectedCase P W chart hlocal s).whole_target_degree_le_four hs2
    change sourceTokens P W chart hlocal s v = 2 at hs2
    change sourceTokens P W chart hlocal t v = 2 at ht2
    simp only [Fits]
    omega

lemma no_three_sources (C : CollisionWitnesses P W chart hlocal)
    {a b c : Source P W} {v : Vertex A}
    (ha : 0 < sourceTokens P W chart hlocal a v)
    (hb : 0 < sourceTokens P W chart hlocal b v)
    (hc : 0 < sourceTokens P W chart hlocal c v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  rcases three_bool_pair (C.sideOf a v) (C.sideOf b v) (C.sideOf c v) with
    hside | hside | hside
  · exact hab (C.same_side_unique ha hb hside)
  · exact hac (C.same_side_unique ha hc hside)
  · exact hbc (C.same_side_unique hb hc hside)

noncomputable def primitiveCollisionDataOfNoThree
    (hA : IsOneSeparated A)
    (hnoThree : ∀ {a b c : Source P W} {v : Vertex A},
      0 < sourceTokens P W chart hlocal a v →
      0 < sourceTokens P W chart hlocal b v →
      0 < sourceTokens P W chart hlocal c v →
      a ≠ b → a ≠ c → b ≠ c → False) :
    PrimitiveCollisionData (Source P W) (Vertex A) (Vertex A) where
  caseTag := sourceCaseTag P W chart hlocal
  degree := fun v ↦ (unitDistanceGraph A).degree v
  tokens := sourceTokens P W chart hlocal
  degree_le_six := degree_unitDistanceGraph_le_six hA
  occupied_degree_le_five := by
    intro s v hpos
    exact (selectedCase P W chart hlocal s).positive_target_degree_le_five hpos
  positive_weight := by
    intro s v hpos
    exact (selectedCase P W chart hlocal s).positive_weight hpos
  case_one_weight := by
    intro s v htag hpos
    exact (selectedCase P W chart hlocal s).case_one_weight htag hpos
  case_two_weight := by
    intro s v htag hpos
    exact (selectedCase P W chart hlocal s).case_two_weight htag hpos
  case_three_whole_degree_le_four := by
    intro s v htag hwhole
    exact (selectedCase P W chart hlocal s).case_three_whole_degree_le_four
      htag hwhole
  no_three_sources := by
    intro a b c v ha hb hc hab hac hbc
    exact hnoThree ha hb hc hab hac hbc
  extremeNeighbors := actualExtremeNeighbors P
  neighbors := actualNeighbors P
  neighbors_card := card_actualNeighbors P
  one_four_picture := (automaticCollisionPictures P W chart hlocal).one_four_picture
  two_four_picture := (automaticCollisionPictures P W chart hlocal).two_four_picture
  three_four_counts := (automaticCollisionPictures P W chart hlocal).three_four_counts
  four_four_forced_six :=
    (automaticCollisionPictures P W chart hlocal).four_four_forced_six

noncomputable def toPrimitiveCollisionData
    (hA : IsOneSeparated A) (C : CollisionWitnesses P W chart hlocal) :
    PrimitiveCollisionData (Source P W) (Vertex A) (Vertex A) :=
  primitiveCollisionDataOfNoThree hA fun ha hb hc hab hac hbc ↦
    C.no_three_sources ha hb hc hab hac hbc

theorem actual_incoming_capacity_of_noThree
    (hA : IsOneSeparated A)
    (hnoThree : ∀ {a b c : Source P W} {v : Vertex A},
      0 < sourceTokens P W chart hlocal a v →
      0 < sourceTokens P W chart hlocal b v →
      0 < sourceTokens P W chart hlocal c v →
      a ≠ b → a ≠ c → b ≠ c → False)
    (v : Vertex A) :
    2 * (unitDistanceGraph A).degree v +
        ∑ s : Source P W, sourceTokens P W chart hlocal s v ≤ 12 := by
  exact (primitiveCollisionDataOfNoThree hA hnoThree).incoming_capacity v

theorem actual_incoming_capacity
    (hA : IsOneSeparated A) (C : CollisionWitnesses P W chart hlocal)
    (v : Vertex A) :
    2 * (unitDistanceGraph A).degree v +
        ∑ s : Source P W, sourceTokens P W chart hlocal s v ≤ 12 := by
  exact actual_incoming_capacity_of_noThree hA
    (fun ha hb hc hab hac hbc ↦ C.no_three_sources ha hb hc hab hac hbc) v

lemma sum_sourceTokens_eq_sum_combinedTransfer (v : Vertex A) :
    ∑ s : Source P W, sourceTokens P W chart hlocal s v =
      ∑ u : Vertex A, combinedTransfer P W chart hlocal u v := by
  classical
  have hsubtype := @Finset.sum_subtype (Vertex A) ℕ _
    (fun u ↦ u ∈ sourceVertices P W) (inferInstance : Fintype (Source P W))
    (sourceVertices P W) (fun u ↦ Iff.rfl)
    (fun u ↦ combinedTransfer P W chart hlocal u v)
  have hfull :
      ∑ u : Vertex A, combinedTransfer P W chart hlocal u v =
        ∑ u ∈ sourceVertices P W, combinedTransfer P W chart hlocal u v := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro u _ hu
    have huB : u ∉ sourceVertices P W := by
      simpa using hu
    simp [combinedTransfer, huB]
  rw [hfull, hsubtype]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [sourceTokens, selectedCase, combinedTransfer, dif_pos s.property]

theorem transferCert_of_noThree
    (hA : IsOneSeparated A)
    (hnoThree : ∀ {a b c : Source P W} {v : Vertex A},
      0 < sourceTokens P W chart hlocal a v →
      0 < sourceTokens P W chart hlocal b v →
      0 < sourceTokens P W chart hlocal c v →
      a ≠ b → a ≠ c → b ≠ c → False) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A) P.H
      (distinguishedVertices P W) (sourceVertices P W)) := by
  classical
  refine ⟨{
    transfer := combinedTransfer P W chart hlocal
    source_subset_distinguished := sourceVertices_subset_distinguished P W
    distinguished_subset_hull := distinguishedVertices_subset_hull P W
    hull_degree_le_three := ?_
    distinguished_nonsource_degree_le_two := ?_
    source_row_sum := combinedTransfer_row_sum P W chart hlocal
    target_not_hull := combinedTransfer_target_not_hull P W chart hlocal
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
  · intro v hv
    rw [← CollisionWitnesses.sum_sourceTokens_eq_sum_combinedTransfer
      (P := P) (W := W)
      (chart := chart) (hlocal := hlocal) v]
    exact actual_incoming_capacity_of_noThree hA hnoThree v

theorem transferCert_of_collisionWitnesses
    (hA : IsOneSeparated A) (C : CollisionWitnesses P W chart hlocal) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A) P.H
      (distinguishedVertices P W) (sourceVertices P W)) :=
  transferCert_of_noThree hA fun ha hb hc hab hac hbc ↦
    C.no_three_sources ha hb hc hab hac hbc

end CollisionWitnesses

end Erdos957CollisionInstantiation

namespace Erdos957GeometryLocalityBridge

open Erdos957GeometryCore
open Erdos957GeometryLocalRows

variable {A : Finset Point} {P : CyclicHullData A}

/-- Two actual unit edges give Euclidean distance at most two. -/
lemma dist_le_two_of_withinTwoUnitEdges {u v : Vertex A}
    (h : WithinTwoUnitEdges u v) : dist (u : Point) (v : Point) ≤ 2 := by
  rcases h with huv | ⟨m, hum, hmv⟩
  · have huv' : dist (u : Point) (v : Point) ≤ 1 := by
      simpa [unitDistanceGraph] using huv.le
    exact huv'.trans (by norm_num)
  · calc
      dist (u : Point) (v : Point) ≤ dist (u : Point) (m : Point) +
          dist (m : Point) (v : Point) := dist_triangle _ _ _
      _ = 2 := by
        rw [show dist (u : Point) (m : Point) = 1 by
              simpa [unitDistanceGraph] using hum,
            show dist (m : Point) (v : Point) = 1 by
              simpa [unitDistanceGraph] using hmv]
        norm_num

/-- A Euclidean distance bound of two controls both genuine local coordinates. -/
lemma abs_localCoord_sub_le_two (i : {p // p ∈ P.H}) {v w : Vertex A}
    (h : dist (v : Point) (w : Point) ≤ 2) :
    |(P.localCoord i w).1 - (P.localCoord i v).1| ≤ 2 ∧
      |(P.localCoord i w).2 - (P.localCoord i v).2| ≤ 2 := by
  have hsq := P.sqDist_localCoord i w v
  simp only [Erdos957Cases13.sqDist] at hsq
  have hdist : 0 ≤ dist (w : Point) (v : Point) := dist_nonneg
  have hdist' : dist (w : Point) (v : Point) ≤ 2 := by simpa [dist_comm] using h
  have hxSq : ((P.localCoord i w).1 - (P.localCoord i v).1) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg ((P.localCoord i w).2 - (P.localCoord i v).2)]
  have hySq : ((P.localCoord i w).2 - (P.localCoord i v).2) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg ((P.localCoord i w).1 - (P.localCoord i v).1)]
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

/-- The same coordinatewise metric estimate in any honest aligned chart. -/
lemma abs_chartCoord_sub_le_two
    (C : P.AlignedChartData) (i : {p // p ∈ P.H}) {v w : Vertex A}
    (h : dist (v : Point) (w : Point) ≤ 2) :
    |(C.coord i w).1 - (C.coord i v).1| ≤ 2 ∧
      |(C.coord i w).2 - (C.coord i v).2| ≤ 2 := by
  have hsq := C.sqDist_coord i w v
  simp only [Erdos957Cases13.sqDist] at hsq
  have hdist : 0 ≤ dist (w : Point) (v : Point) := dist_nonneg
  have hdist' : dist (w : Point) (v : Point) ≤ 2 := by
    simpa [dist_comm] using h
  have hxSq : ((C.coord i w).1 - (C.coord i v).1) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg ((C.coord i w).2 - (C.coord i v).2)]
  have hySq : ((C.coord i w).2 - (C.coord i v).2) ^ 2 ≤ 4 := by
    nlinarith [sq_nonneg ((C.coord i w).1 - (C.coord i v).1)]
  constructor
  · rw [abs_le]
    constructor <;> nlinarith
  · rw [abs_le]
    constructor <;> nlinarith

/-- Every actual configuration point is weakly below the source support line. -/
lemma localCoord_snd_nonpos (i : {p // p ∈ P.H}) (w : Vertex A) :
    (P.localCoord i w).2 ≤ 0 := by
  by_cases hwi : w = i.1
  · subst w
    simp
  · exact (P.localCoord_snd_neg i w hwi).le

lemma chartCoord_snd_nonpos (C : P.AlignedChartData)
    (i : {p // p ∈ P.H}) (w : Vertex A) : (C.coord i w).2 ≤ 0 := by
  exact C.coord_snd_nonpos i w

/-- The sharp Case 2/4 transport arithmetic.  Their rigid edge chart gives
`|x| ≤ 3/2`; changing to the common bisector axis moves a length-at-most-two
recipient horizontally by at most `2/45`.  The sum is strictly below the
standard recipient bound `7/4`.  The vertical bounds use only the genuine
two-edge path and the common supporting half-plane. -/
lemma recipient_rectangle_of_edge_horizontal_bound
    (C : P.AlignedChartData) (i : {p // p ∈ P.H}) {v : Vertex A}
    (hv : WithinTwoUnitEdges i.1 v) (edgeX : ℝ)
    (hedgeX : |edgeX| ≤ 3 / 2)
    (hchange : |(C.coord i v).1 - edgeX| ≤ 2 / 45) :
    Erdos957Locality.InRecipientRectangle (C.coord i v) := by
  have hd : dist (i.1 : Point) (v : Point) ≤ 2 :=
    dist_le_two_of_withinTwoUnitEdges hv
  obtain ⟨hx, hy⟩ := abs_chartCoord_sub_le_two C i hd
  have hsource := C.coord_source i
  rw [hsource] at hy
  simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at hy
  rw [abs_le] at hedgeX hchange hy
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · exact hy.1
  · exact chartCoord_snd_nonpos C i v

/--
An actual recipient rectangle in the honest aligned chart, together with a
graph-distance-two path, implies the enlarged-rectangle premise for every
competing source.  No chart identification, cyclic-window conclusion, or
capacity statement is assumed here.
-/
theorem competing_source_in_enlarged_rectangle
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) {v w : Vertex A}
    (hvRect : Erdos957Locality.InRecipientRectangle (F.chart.coord i v))
    (hwv : WithinTwoUnitEdges w v) :
    Erdos957Locality.InCompetingSourceRectangle
      (F.chart.coord i w) := by
  have hd : dist (w : Point) (v : Point) ≤ 2 :=
    dist_le_two_of_withinTwoUnitEdges hwv
  obtain ⟨hx, hy⟩ := abs_chartCoord_sub_le_two F.chart i hd
  rw [abs_sub_comm] at hx hy
  exact Erdos957Locality.competing_source_mem_rectangle hvRect hx hy
    (chartCoord_snd_nonpos F.chart i w)

/-- The seven actual hull vertices centered at `i`. -/
def sevenHullWindow (P : CyclicHullData A) (i : {p // p ∈ P.H}) :
    Finset (Vertex A) :=
  Finset.univ.image fun j : Fin 7 ↦ (sevenShift P.next j i).1

/-- A source index is flat because `sourceVertices` is filtered from the
intersection with `flatVertices`. -/
lemma sourceIndex_isFlat (W : DiameterWitnessData P) (s : {u : Vertex A //
    u ∈ sourceVertices P W}) :
    P.IsFlat (sourceIndex P W s.1 s.property) := by
  classical
  let i := sourceIndex P W s.1 s.property
  have hsFlat : s.1 ∈ P.flatVertices :=
    (Finset.mem_inter.mp (Finset.mem_filter.mp s.property).1).2
  rcases Finset.mem_map.mp hsFlat with ⟨j, hj, hji⟩
  have hjFlat : P.IsFlat j := (Finset.mem_filter.mp hj).2
  have hji' : j = i := by
    apply Subtype.ext
    exact hji
  simpa [hji'] using hjFlat

/-- Every emitting source is an actual diameter endpoint. -/
lemma source_mem_diameter (W : DiameterWitnessData P) (s : {u : Vertex A //
    u ∈ sourceVertices P W}) : s.1 ∈ W.D :=
  (Finset.mem_inter.mp (Finset.mem_filter.mp s.property).1).1

lemma sin_gt_neg_cos_div_fifty_of_abs_le_pi_div_180 {θ : ℝ}
    (hθ : |θ| ≤ Real.pi / 180) : -Real.cos θ / 50 < Real.sin θ := by
  have hθ' : |θ| ≤ Real.pi / 45 := by nlinarith [Real.pi_pos]
  have hcMono := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
    (by nlinarith [Real.pi_pos] : Real.pi / 45 ≤ Real.pi) hθ'
  rw [Real.cos_abs] at hcMono
  have hc : (399 / 400 : ℝ) < Real.cos θ :=
    Erdos957Locality.three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le
      hcMono
  have hsabs : |Real.sin θ| ≤ |θ| := Real.abs_sin_le_abs
  have hnegabs := neg_abs_le (Real.sin θ)
  nlinarith [Real.pi_lt_d2]

lemma positive_dot_of_sqDist_le {x y r c s : ℝ} (hr : 1 ≤ r)
    (htrig : s ^ 2 + c ^ 2 = 1)
    (hdist : (x - r * c) ^ 2 + (y - r * s) ^ 2 ≤ x ^ 2 + y ^ 2) :
    0 < x * c + y * s := by
  have hid : (x - r * c) ^ 2 + (y - r * s) ^ 2 =
      x ^ 2 + y ^ 2 + r ^ 2 - 2 * r * (x * c + y * s) := by
    calc
      _ = x ^ 2 + y ^ 2 + r ^ 2 * (s ^ 2 + c ^ 2) -
          2 * r * (x * c + y * s) := by ring
      _ = _ := by rw [htrig]; ring
  rw [hid] at hdist
  by_contra hdot
  have hdot' : x * c + y * s ≤ 0 := not_lt.mp hdot
  have hmul := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ r) hdot'
  nlinarith

lemma vertical_le_neg_one_hundred_of_cone {x y r : ℝ}
    (hr : 101 ≤ r) (hnorm : x ^ 2 + y ^ 2 = r ^ 2)
    (hy : y < 0) (hxLower : y / 50 ≤ x) (hxUpper : x ≤ -(y / 50)) :
    y ≤ -(100 : ℝ) := by
  have hproduct : 0 ≤ (-y / 50 - x) * (x - y / 50) :=
    mul_nonneg (by linarith) (by linarith)
  by_contra h
  have hy' : -(100 : ℝ) < y := lt_of_not_ge h
  have hySq : y ^ 2 < (100 : ℝ) ^ 2 := by nlinarith
  have hrSq : (101 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith
  nlinarith

/-- Maximality against the two adjacent hull vertices forces the chosen
diameter endpoint into the narrow inward cone of the genuine aligned
source chart.  Thus the coarse opposite bounds used by locality are
consequences of geometry, rather than fields of the cyclic-window record. -/
lemma opposite_coordinate_bounds
    (W : DiameterWitnessData P) (F : P.FlatAlignedFrameData)
    (s : {u : Vertex A // u ∈ sourceVertices P W}) :
    let i := sourceIndex P W s.1 s.property
    let q := F.chart.coord i (W.opposite s.1 (source_mem_diameter W s))
    q.2 ≤ -(100 : ℝ) ∧ q.2 / 50 ≤ q.1 ∧ q.1 ≤ -(q.2 / 50) := by
  let i := sourceIndex P W s.1 s.property
  let qv := W.opposite s.1 (source_mem_diameter W s)
  let q := F.chart.coord i qv
  let rv : Vertex A := ((P.next ^ 1) i).1
  let lv : Vertex A := (((P.next⁻¹) ^ 1) i).1
  let pr := F.chart.rightOrbitCoord P i 1
  let pl := F.chart.leftOrbitReflectedCoord P i 1
  have hrad : 0 ≤ W.radius := by linarith [W.radius_ge_101]
  have hqnorm : q.1 ^ 2 + q.2 ^ 2 = W.radius ^ 2 := by
    have h := F.chart.sqDist_coord i qv s.1
    change Erdos957Cases13.sqDist (F.chart.coord i qv) (F.chart.coord i i.1) =
      dist (qv : Point) (i.1 : Point) ^ 2 at h
    rw [F.chart.coord_source] at h
    change Erdos957Cases13.sqDist (F.chart.coord i qv) (0, 0) =
      dist (qv : Point) (s.1 : Point) ^ 2 at h
    have hd : dist (qv : Point) (s.1 : Point) = W.radius := by
      simpa [qv, dist_comm] using W.opposite_distance s.1 (source_mem_diameter W s)
    rw [hd] at h
    simpa [q, Erdos957Cases13.sqDist] using h
  have hrightDist : Erdos957Cases13.sqDist q pr ≤ W.radius ^ 2 := by
    have hm := W.maximal qv rv
    have hd0 : 0 ≤ dist (qv : Point) (rv : Point) := dist_nonneg
    have hmsq : dist (qv : Point) (rv : Point) ^ 2 ≤ W.radius ^ 2 := by
      nlinarith
    have hc := F.chart.sqDist_coord i qv rv
    have hcoord : F.chart.coord i rv = pr := by rfl
    calc
      Erdos957Cases13.sqDist q pr =
          Erdos957Cases13.sqDist (F.chart.coord i qv) (F.chart.coord i rv) := by
            rw [hcoord]
      _ = dist (qv : Point) (rv : Point) ^ 2 := hc
      _ ≤ W.radius ^ 2 := hmsq
  have hleftDist : Erdos957Cases13.sqDist q (-pl.1, pl.2) ≤ W.radius ^ 2 := by
    have hm := W.maximal qv lv
    have hd0 : 0 ≤ dist (qv : Point) (lv : Point) := dist_nonneg
    have hmsq : dist (qv : Point) (lv : Point) ^ 2 ≤ W.radius ^ 2 := by
      nlinarith
    have hc := F.chart.sqDist_coord i qv lv
    have hcoord : F.chart.coord i lv = (-pl.1, pl.2) := by
      simp [lv, pl, CyclicHullData.AlignedChartData.leftOrbitReflectedCoord]
    calc
      Erdos957Cases13.sqDist q (-pl.1, pl.2) =
          Erdos957Cases13.sqDist (F.chart.coord i qv) (F.chart.coord i lv) := by
            rw [hcoord]
      _ = dist (qv : Point) (lv : Point) ^ 2 := hc
      _ ≤ W.radius ^ 2 := hmsq
  have hrPolar := F.rightPolar i 0
  have hlPolar := F.leftPolar i 0
  have hrcoord : pr.1 = F.rightRadius i 0 * Real.cos (F.rightAngle i 0) ∧
      pr.2 = F.rightRadius i 0 * Real.sin (F.rightAngle i 0) := by
    simpa [pr, Erdos957Locality.IsPolarEdge] using hrPolar
  have hlcoord : pl.1 = F.leftRadius i 0 * Real.cos (F.leftAngle i 0) ∧
      pl.2 = F.leftRadius i 0 * Real.sin (F.leftAngle i 0) := by
    simpa [pl, Erdos957Locality.IsPolarEdge] using hlPolar
  have hrightDot : 0 < q.1 * Real.cos (F.rightAngle i 0) +
      q.2 * Real.sin (F.rightAngle i 0) := by
    have hrr := F.rightRadius_ge_one i 0
    have htrig := Real.sin_sq_add_cos_sq (F.rightAngle i 0)
    rw [← hqnorm] at hrightDist
    simp only [Erdos957Cases13.sqDist] at hrightDist
    rw [hrcoord.1, hrcoord.2] at hrightDist
    exact positive_dot_of_sqDist_le hrr htrig hrightDist
  have hleftDot : 0 < -q.1 * Real.cos (F.leftAngle i 0) +
      q.2 * Real.sin (F.leftAngle i 0) := by
    have hlr := F.leftRadius_ge_one i 0
    have htrig := Real.sin_sq_add_cos_sq (F.leftAngle i 0)
    rw [← hqnorm] at hleftDist
    simp only [Erdos957Cases13.sqDist] at hleftDist
    rw [hlcoord.1, hlcoord.2] at hleftDist
    have htrig' : Real.sin (F.leftAngle i 0) ^ 2 +
        (-Real.cos (F.leftAngle i 0)) ^ 2 = 1 := by nlinarith
    have hleftDist' :
        (q.1 - F.leftRadius i 0 * (-Real.cos (F.leftAngle i 0))) ^ 2 +
            (q.2 - F.leftRadius i 0 * Real.sin (F.leftAngle i 0)) ^ 2 ≤
          q.1 ^ 2 + q.2 ^ 2 := by
      convert hleftDist using 1 <;> ring
    simpa only [mul_neg, neg_mul, sub_neg_eq_add, neg_sq] using
      (positive_dot_of_sqDist_le hlr htrig' hleftDist')
  have hflat := sourceIndex_isFlat W s
  obtain ⟨hθr, _, _, _⟩ := F.rightFlatAngles i hflat
  obtain ⟨hθl, _, _, _⟩ := F.leftFlatAngles i hflat
  have hcosr : (399 / 400 : ℝ) < Real.cos (F.rightAngle i 0) := by
    have hθr' : |F.rightAngle i 0| ≤ Real.pi / 45 := by
      nlinarith [Real.pi_pos]
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (F.rightAngle i 0))
      (by nlinarith [Real.pi_pos] : Real.pi / 45 ≤ Real.pi) hθr'
    rw [Real.cos_abs] at hc
    exact Erdos957Locality.three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le hc
  have hcosl : (399 / 400 : ℝ) < Real.cos (F.leftAngle i 0) := by
    have hθl' : |F.leftAngle i 0| ≤ Real.pi / 45 := by
      nlinarith [Real.pi_pos]
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (F.leftAngle i 0))
      (by nlinarith [Real.pi_pos] : Real.pi / 45 ≤ Real.pi) hθl'
    rw [Real.cos_abs] at hc
    exact Erdos957Locality.three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five.trans_le hc
  have hsinr : Real.sin (F.rightAngle i 0) ≤ 0 := by
    have hy := chartCoord_snd_nonpos F.chart i rv
    rw [show F.chart.coord i rv = pr by rfl, hrcoord.2] at hy
    nlinarith [F.rightRadius_ge_one i 0]
  have hsinl : Real.sin (F.leftAngle i 0) ≤ 0 := by
    have hy := chartCoord_snd_nonpos F.chart i lv
    have hc : F.chart.coord i lv = (-pl.1, pl.2) := by
      simp [lv, pl, CyclicHullData.AlignedChartData.leftOrbitReflectedCoord]
    rw [hc, hlcoord.2] at hy
    nlinarith [F.leftRadius_ge_one i 0]
  have hsinConeR : -Real.cos (F.rightAngle i 0) / 50 <
      Real.sin (F.rightAngle i 0) :=
    sin_gt_neg_cos_div_fifty_of_abs_le_pi_div_180 hθr
  have hsinConeL : -Real.cos (F.leftAngle i 0) / 50 <
      Real.sin (F.leftAngle i 0) :=
    sin_gt_neg_cos_div_fifty_of_abs_le_pi_div_180 hθl
  have hqy : q.2 < 0 := by
    by_contra hy
    have hy0 : 0 ≤ q.2 := le_of_not_gt hy
    have hyr : q.2 * Real.sin (F.rightAngle i 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy0 hsinr
    have hyl : q.2 * Real.sin (F.leftAngle i 0) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hy0 hsinl
    have hxrcos : 0 < q.1 * Real.cos (F.rightAngle i 0) := by linarith
    have hxlcos : 0 < (-q.1) * Real.cos (F.leftAngle i 0) := by linarith
    have hxr : 0 < q.1 := by
      rcases (mul_pos_iff.mp hxrcos) with h | h
      · exact h.1
      · linarith [h.2, hcosr]
    have hxneg : 0 < -q.1 := by
      rcases (mul_pos_iff.mp hxlcos) with h | h
      · exact h.1
      · linarith [h.2, hcosl]
    have hxl : q.1 < 0 := by linarith
    linarith
  have hqxLower : q.2 / 50 ≤ q.1 := by
    by_contra hx
    have hx' : q.1 < q.2 / 50 := lt_of_not_ge hx
    have h1 := mul_lt_mul_of_pos_right hx' (by linarith :
      0 < Real.cos (F.rightAngle i 0))
    have h2 := mul_lt_mul_of_neg_left hsinConeR hqy
    linarith
  have hqxUpper : q.1 ≤ -(q.2 / 50) := by
    by_contra hx
    have hx' : -(q.2 / 50) < q.1 := lt_of_not_ge hx
    have h1 := mul_lt_mul_of_pos_right hx' (by linarith :
      0 < Real.cos (F.leftAngle i 0))
    have h2 := mul_lt_mul_of_neg_left hsinConeL hqy
    linarith
  have hqyBound : q.2 ≤ -(100 : ℝ) :=
    vertical_le_neg_one_hundred_of_cone W.radius_ge_101 hqnorm hqy hqxLower hqxUpper
  exact ⟨hqyBound, hqxLower, hqxUpper⟩

/--
Pure cyclic geometry needed after the four-step flat-edge estimate.

`outside_window_arc` is only the genuine convex-chain chord orientation for
a hull vertex outside the seven-window.  The opposite endpoint bounds are
derived by `opposite_coordinate_bounds`; no coordinate estimate, transfer,
or capacity assertion is a field of this record.
-/
structure CyclicWindowGeometry (W : DiameterWitnessData P)
    (F : P.FlatAlignedFrameData) where
  outside_window_arc : ∀ (s : {u : Vertex A // u ∈ sourceVertices P W})
      (z : Vertex A), z ∈ P.H → z ∉ sevenHullWindow P
        (sourceIndex P W s.1 s.property) →
    let i := sourceIndex P W s.1 s.property
    let q := F.chart.coord i (W.opposite s.1 (source_mem_diameter W s))
    let zr := F.chart.coord i z
    let pRight := F.chart.rightOrbitCoord P i 4
    let pLeft := F.chart.leftOrbitReflectedCoord P i 4
    Erdos957Locality.ExteriorOfRightChord pRight q zr ∨
      Erdos957Locality.ExteriorOfRightChord pLeft (-q.1, q.2) (-zr.1, zr.2)

/-- Three forward edges in a flat source window already separate their
endpoint horizontally from the source by more than two units. -/
lemma right_three_steps_exit_two
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    2 < (F.chart.rightOrbitCoord P i 3).1 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.rightFlatAngles i hi
  obtain ⟨ha0, ha1, ha2, ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  have hx0 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 0) ha0 (F.rightPolar i 0).1
  have hx1 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 1) ha1 (F.rightPolar i 1).1
  have hx2 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one i 2) ha2 (F.rightPolar i 2).1
  norm_num at hx0 hx1 hx2
  have hz : (F.chart.rightOrbitCoord P i 0).1 = 0 := by simp
  linarith

/-- Reflected backward analogue of `right_three_steps_exit_two`. -/
lemma left_three_steps_exit_two
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    2 < (F.chart.leftOrbitReflectedCoord P i 3).1 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.leftFlatAngles i hi
  obtain ⟨ha0, ha1, ha2, ha3⟩ :=
    Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3
  have hx0 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 0) ha0 (F.leftPolar i 0).1
  have hx1 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 1) ha1 (F.leftPolar i 1).1
  have hx2 :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one i 2) ha2 (F.leftPolar i 2).1
  norm_num at hx0 hx1 hx2
  have hz : (F.chart.leftOrbitReflectedCoord P i 0).1 = 0 := by simp
  linarith

private lemma dist_gt_two_of_coord_fst_gt_two
    (C : P.AlignedChartData) (i : {p // p ∈ P.H}) (q : Vertex A)
    (hx : 2 < (C.coord i q).1) : 2 < dist (i.1 : Point) (q : Point) := by
  have hsq := C.sqDist_coord i i.1 q
  rw [C.coord_source] at hsq
  simp only [Erdos957Cases13.sqDist, Prod.fst_zero, Prod.snd_zero,
    sub_zero] at hsq
  nlinarith [sq_nonneg (C.coord i q).2,
    dist_nonneg (x := (i.1 : Point)) (y := (q : Point))]

private lemma dist_gt_two_of_reflected_coord_fst_gt_two
    (C : P.AlignedChartData) (i : {p // p ∈ P.H}) (q : Vertex A)
    (hx : 2 < -(C.coord i q).1) : 2 < dist (i.1 : Point) (q : Point) := by
  have hsq := C.sqDist_coord i i.1 q
  rw [C.coord_source] at hsq
  simp only [Erdos957Cases13.sqDist, Prod.fst_zero, Prod.snd_zero,
    sub_zero] at hsq
  nlinarith [sq_nonneg (C.coord i q).2,
    dist_nonneg (x := (i.1 : Point)) (y := (q : Point))]

/-- A flat source and its third successor are more than two units apart. -/
lemma dist_third_successor_gt_two
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    2 < dist (i.1 : Point) (((P.next ^ 3) i).1 : Point) := by
  apply dist_gt_two_of_coord_fst_gt_two F.chart i
  exact right_three_steps_exit_two F i hi

/-- A flat source and its fourth successor are more than two units apart. -/
lemma dist_fourth_successor_gt_two
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    2 < dist (i.1 : Point) (((P.next ^ 4) i).1 : Point) := by
  apply dist_gt_two_of_coord_fst_gt_two F.chart i
  exact (show (2 : ℝ) < 399 / 100 by norm_num).trans
    (CyclicHullData.FlatAlignedFrameData.right_four_steps_exit P F i hi)

/-- A flat source and its third predecessor are more than two units apart. -/
lemma dist_third_predecessor_gt_two
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    2 < dist (i.1 : Point) ((((P.next⁻¹) ^ 3) i).1 : Point) := by
  apply dist_gt_two_of_reflected_coord_fst_gt_two F.chart i
  simpa [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord] using
    left_three_steps_exit_two F i hi

/-- A flat source and its fourth predecessor are more than two units apart. -/
lemma dist_fourth_predecessor_gt_two
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    2 < dist (i.1 : Point) ((((P.next⁻¹) ^ 4) i).1 : Point) := by
  apply dist_gt_two_of_reflected_coord_fst_gt_two F.chart i
  have hx := (show (2 : ℝ) < 399 / 100 by norm_num).trans
    (CyclicHullData.FlatAlignedFrameData.left_four_steps_exit P F i hi)
  simpa [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord] using hx

/-- The four forward flat edges stay in the cone needed by the chord
exclusion.  This is a consequence of the polar-edge data and the four
one-degree turn bounds, not an extra cyclic-geometry assumption. -/
lemma right_four_steps_flat_cone
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    (let p := F.chart.rightOrbitCoord P i 4; -p.2 ≤ p.1 / 10) := by
  obtain ⟨h0, h1, h2, h3⟩ := F.rightFlatAngles i hi
  have ha1 : |F.rightAngle i 1| ≤ 2 * (Real.pi / 180) := by
    calc
      |F.rightAngle i 1| =
          |(F.rightAngle i 1 - F.rightAngle i 0) + F.rightAngle i 0| := by ring_nf
      _ ≤ |F.rightAngle i 1 - F.rightAngle i 0| + |F.rightAngle i 0| :=
        abs_add_le _ _
      _ ≤ 2 * (Real.pi / 180) := by linarith
  have ha2 : |F.rightAngle i 2| ≤ 3 * (Real.pi / 180) := by
    calc
      |F.rightAngle i 2| =
          |(F.rightAngle i 2 - F.rightAngle i 1) + F.rightAngle i 1| := by ring_nf
      _ ≤ |F.rightAngle i 2 - F.rightAngle i 1| + |F.rightAngle i 1| :=
        abs_add_le _ _
      _ ≤ 3 * (Real.pi / 180) := by linarith
  have ha3 : |F.rightAngle i 3| ≤ 4 * (Real.pi / 180) := by
    calc
      |F.rightAngle i 3| =
          |(F.rightAngle i 3 - F.rightAngle i 2) + F.rightAngle i 2| := by ring_nf
      _ ≤ |F.rightAngle i 3 - F.rightAngle i 2| + |F.rightAngle i 2| :=
        abs_add_le _ _
      _ ≤ 4 * (Real.pi / 180) := by linarith
  apply Erdos957Locality.four_polar_edges_flat_cone
    (p₀ := F.chart.rightOrbitCoord P i 0)
    (p₁ := F.chart.rightOrbitCoord P i 1)
    (p₂ := F.chart.rightOrbitCoord P i 2)
    (p₃ := F.chart.rightOrbitCoord P i 3)
    (p₄ := F.chart.rightOrbitCoord P i 4)
    (r₀ := F.rightRadius i 0) (r₁ := F.rightRadius i 1)
    (r₂ := F.rightRadius i 2) (r₃ := F.rightRadius i 3)
    (θ₀ := F.rightAngle i 0) (θ₁ := F.rightAngle i 1)
    (θ₂ := F.rightAngle i 2) (θ₃ := F.rightAngle i 3)
  · simp
  · exact F.rightPolar i 0
  · exact F.rightPolar i 1
  · exact F.rightPolar i 2
  · exact F.rightPolar i 3
  · linarith [F.rightRadius_ge_one i 0]
  · linarith [F.rightRadius_ge_one i 1]
  · linarith [F.rightRadius_ge_one i 2]
  · linarith [F.rightRadius_ge_one i 3]
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- Reflected backward analogue of `right_four_steps_flat_cone`. -/
lemma left_four_steps_flat_cone
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H}) (hi : P.IsFlat i) :
    (let p := F.chart.leftOrbitReflectedCoord P i 4; -p.2 ≤ p.1 / 10) := by
  obtain ⟨h0, h1, h2, h3⟩ := F.leftFlatAngles i hi
  have ha1 : |F.leftAngle i 1| ≤ 2 * (Real.pi / 180) := by
    calc
      |F.leftAngle i 1| =
          |(F.leftAngle i 1 - F.leftAngle i 0) + F.leftAngle i 0| := by ring_nf
      _ ≤ |F.leftAngle i 1 - F.leftAngle i 0| + |F.leftAngle i 0| :=
        abs_add_le _ _
      _ ≤ 2 * (Real.pi / 180) := by linarith
  have ha2 : |F.leftAngle i 2| ≤ 3 * (Real.pi / 180) := by
    calc
      |F.leftAngle i 2| =
          |(F.leftAngle i 2 - F.leftAngle i 1) + F.leftAngle i 1| := by ring_nf
      _ ≤ |F.leftAngle i 2 - F.leftAngle i 1| + |F.leftAngle i 1| :=
        abs_add_le _ _
      _ ≤ 3 * (Real.pi / 180) := by linarith
  have ha3 : |F.leftAngle i 3| ≤ 4 * (Real.pi / 180) := by
    calc
      |F.leftAngle i 3| =
          |(F.leftAngle i 3 - F.leftAngle i 2) + F.leftAngle i 2| := by ring_nf
      _ ≤ |F.leftAngle i 3 - F.leftAngle i 2| + |F.leftAngle i 2| :=
        abs_add_le _ _
      _ ≤ 4 * (Real.pi / 180) := by linarith
  apply Erdos957Locality.four_polar_edges_flat_cone
    (p₀ := F.chart.leftOrbitReflectedCoord P i 0)
    (p₁ := F.chart.leftOrbitReflectedCoord P i 1)
    (p₂ := F.chart.leftOrbitReflectedCoord P i 2)
    (p₃ := F.chart.leftOrbitReflectedCoord P i 3)
    (p₄ := F.chart.leftOrbitReflectedCoord P i 4)
    (r₀ := F.leftRadius i 0) (r₁ := F.leftRadius i 1)
    (r₂ := F.leftRadius i 2) (r₃ := F.leftRadius i 3)
    (θ₀ := F.leftAngle i 0) (θ₁ := F.leftAngle i 1)
    (θ₂ := F.leftAngle i 2) (θ₃ := F.leftAngle i 3)
  · simp
  · exact F.leftPolar i 0
  · exact F.leftPolar i 1
  · exact F.leftPolar i 2
  · exact F.leftPolar i 3
  · linarith [F.leftRadius_ge_one i 0]
  · linarith [F.leftRadius_ge_one i 1]
  · linarith [F.leftRadius_ge_one i 2]
  · linarith [F.leftRadius_ge_one i 3]
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- The aligned four-edge estimate plus the diameter chord data prove the
actual cyclic-window locality conclusion. -/
theorem mem_sevenHullWindow_of_mem_competingRectangle
    (W : DiameterWitnessData P) (F : P.FlatAlignedFrameData)
    (L : CyclicWindowGeometry W F)
    (s : {u : Vertex A // u ∈ sourceVertices P W})
    (z : Vertex A) (hzHull : z ∈ P.H)
    (hzRect : Erdos957Locality.InCompetingSourceRectangle
      (F.chart.coord (sourceIndex P W s.1 s.property) z)) :
    z ∈ sevenHullWindow P (sourceIndex P W s.1 s.property) := by
  let i := sourceIndex P W s.1 s.property
  let qv := W.opposite s.1 (source_mem_diameter W s)
  let q := F.chart.coord i qv
  let zr := F.chart.coord i z
  let pRight := F.chart.rightOrbitCoord P i 4
  let pLeft := F.chart.leftOrbitReflectedCoord P i 4
  by_contra hzWindow
  rcases L.outside_window_arc s z hzHull hzWindow with hright | hleft
  · have hpx : (399 / 100 : ℝ) ≤ pRight.1 :=
      (CyclicHullData.FlatAlignedFrameData.right_four_steps_exit P F i
        (sourceIndex_isFlat W s)).le
    have hpUpper : pRight.2 ≤ 0 := by
      exact chartCoord_snd_nonpos F.chart i ((P.next ^ 4) i).1
    have hpCone : -pRight.2 ≤ pRight.1 / 10 :=
      right_four_steps_flat_cone F i (sourceIndex_isFlat W s)
    have hzyLower : -(4 : ℝ) ≤ zr.2 := hzRect.2.2.1
    have hzyUpper : zr.2 ≤ 0 := hzRect.2.2.2
    obtain ⟨hqy, hqxLower, hqxUpper⟩ := opposite_coordinate_bounds W F s
    have hout :=
      Erdos957Locality.right_chain_avoids_competing_rectangle_of_flat_cone
        hpx hpUpper hpCone hqy hqxLower hqxUpper hzRect.1 hzyLower hzyUpper hright
    exact (not_lt_of_ge hzRect.2.1) hout
  · have hpx : (399 / 100 : ℝ) ≤ pLeft.1 :=
      (CyclicHullData.FlatAlignedFrameData.left_four_steps_exit P F i
        (sourceIndex_isFlat W s)).le
    have hpUpper : pLeft.2 ≤ 0 := by
      exact chartCoord_snd_nonpos F.chart i (((P.next⁻¹) ^ 4) i).1
    have hpCone : -pLeft.2 ≤ pLeft.1 / 10 :=
      left_four_steps_flat_cone F i (sourceIndex_isFlat W s)
    have hzyLower : -(4 : ℝ) ≤ zr.2 := hzRect.2.2.1
    have hzyUpper : zr.2 ≤ 0 := hzRect.2.2.2
    obtain ⟨hqy, hqxLower, hqxUpper⟩ := opposite_coordinate_bounds W F s
    have hout :=
      Erdos957Locality.right_chain_avoids_competing_rectangle_of_flat_cone
      (p := pLeft) (q := (-q.1, q.2)) (z := (-zr.1, zr.2))
      hpx hpUpper hpCone hqy (by dsimp; linarith) (by dsimp; linarith)
      (by dsimp; linarith [hzRect.2.1]) hzyLower hzyUpper hleft
    have hzLeft : -(15 / 4 : ℝ) ≤ zr.1 := hzRect.1
    change (15 / 4 : ℝ) < -zr.1 at hout
    linarith

end Erdos957GeometryLocalityBridge

namespace Erdos957CollisionInstantiation

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957GeometryLocalityBridge
open Erdos957GeometryCollisions
open Erdos957Overcharge

variable {A : Finset Point} (P : CyclicHullData A)
variable (W : DiameterWitnessData P) (F : P.FlatAlignedFrameData)
variable (hlocal : HasLocalCases P W F.chart)

/-- Geometric locality certificates in the single honest bisector chart.
The rigid edge charts used to construct Cases 2 and 4 retain their formula
witnesses upstream, but their recipient bounds are transported into this
common chart before reaching the collision layer. -/
structure SourceLocalityCertificates where
  windowGeometry : CyclicWindowGeometry W F

namespace SourceLocalityCertificates

variable {P W F hlocal}

/-- The common-chart metric and chord data prove the actual window premise
required by the minimal side-uniqueness theorem. -/
theorem competing_source_in_window
    (L : SourceLocalityCertificates P W F)
    {s t : Source P W} {v : Vertex A}
    (hs : 0 < sourceTokens P W F.chart hlocal s v)
    (ht : 0 < sourceTokens P W F.chart hlocal t v) :
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) := by
  let i := sourceIndex P W s.1 s.property
  have hsRecipient : Erdos957Locality.InRecipientRectangle
      (F.chart.coord i v) := by
    have hrow := (selectedCase P W F.chart hlocal s).target_in_rectangle hs
    simp only [i, Erdos957GeometryLocalRows.InLocalRectangle,
      Erdos957GeometryLocalRows.sourceCoordinates,
      Erdos957Cases13.InSourceRectangle] at hrow
    rcases hrow with ⟨hxl, hxu, hyl, hyu⟩
    exact ⟨by linarith, hxu, hyl, hyu⟩
  have htRect : Erdos957Locality.InCompetingSourceRectangle
      (F.chart.coord i t.1) :=
    Erdos957GeometryLocalityBridge.competing_source_in_enlarged_rectangle
      F i hsRecipient
      ((selectedCase P W F.chart hlocal t).target_within_two ht)
  exact mem_sevenHullWindow_of_mem_competingRectangle W F
    L.windowGeometry s t.1
    (sourceVertices_subset_hull P W t.property) htRect

end SourceLocalityCertificates

/-- A side-free collision interface.  This is the smallest finite statement
needed after metric locality: three pairwise distinct formula-retaining rows
inside one actual seven-window cannot select the same target.  It is useful
for geometric constructions where introducing an auxiliary Boolean side
coloring would only obscure the role analysis. -/
structure NoThreeRoleCollisionWitnesses where
  locality : SourceLocalityCertificates P W F
  no_three_in_window : ∀ {a b c : Source P W} {v},
    0 < sourceTokens P W F.chart hlocal a v →
    0 < sourceTokens P W F.chart hlocal b v →
    0 < sourceTokens P W F.chart hlocal c v →
    b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1) →
    c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1) →
    a ≠ b → a ≠ c → b ≠ c → False

namespace NoThreeRoleCollisionWitnesses

variable {P W F hlocal}

theorem no_three_sources (C : NoThreeRoleCollisionWitnesses P W F hlocal)
    {a b c : Source P W} {v : Vertex A}
    (ha : 0 < sourceTokens P W F.chart hlocal a v)
    (hb : 0 < sourceTokens P W F.chart hlocal b v)
    (hc : 0 < sourceTokens P W F.chart hlocal c v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  exact C.no_three_in_window ha hb hc
    (C.locality.competing_source_in_window ha hb)
    (C.locality.competing_source_in_window ha hc) hab hac hbc

/-- Genuine window locality plus the finite no-three role theorem suffices
for the production transfer certificate; all degree-five picture branches
are automatic. -/
theorem transferCert
    (hA : IsOneSeparated A)
    (C : NoThreeRoleCollisionWitnesses P W F hlocal) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A) P.H
      (distinguishedVertices P W) (sourceVertices P W)) :=
  CollisionWitnesses.transferCert_of_noThree hA fun
    ha hb hc hab hac hbc ↦ C.no_three_sources ha hb hc hab hac hbc

end NoThreeRoleCollisionWitnesses

/-!
## Weight-aware production collision interface

Three and four contributing sources are allowed here.  Geometry must prove
that there are at most four and establish the local capacity estimate for
actual triples and quadruples.  This is the weakest interface consumed by the cardinal split in
`WeightedCollisionData.incoming_capacity`.
-/

/-- Window-local geometric data sufficient for weight-aware column
capacity.  No field states a sum over all incoming source rows. -/
structure WeightedCollisionWitnesses where
  locality : SourceLocalityCertificates P W F
  /-- Equivalent no-five formulation, stated directly on the finite source
  fiber to avoid an artificial ordering of five witnesses. -/
  contributors_card_le_four : ∀ v,
    (Finset.univ.filter fun s : Source P W ↦
      0 < sourceTokens P W F.chart hlocal s v).card ≤ 4
  triple_fits_in_window : ∀ {a b c : Source P W} {v},
    0 < sourceTokens P W F.chart hlocal a v →
    0 < sourceTokens P W F.chart hlocal b v →
    0 < sourceTokens P W F.chart hlocal c v →
    b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1) →
    c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1) →
    a ≠ b → a ≠ c → b ≠ c →
    Fits ((unitDistanceGraph A).degree v)
      (sourceTokens P W F.chart hlocal a v +
        sourceTokens P W F.chart hlocal b v +
        sourceTokens P W F.chart hlocal c v)
  quadruple_fits_in_window : ∀ {a b c d : Source P W} {v},
    0 < sourceTokens P W F.chart hlocal a v →
    0 < sourceTokens P W F.chart hlocal b v →
    0 < sourceTokens P W F.chart hlocal c v →
    0 < sourceTokens P W F.chart hlocal d v →
    b.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1) →
    c.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1) →
    d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W a.1 a.property)).1) →
    a ≠ b → a ≠ c → a ≠ d →
    b ≠ c → b ≠ d → c ≠ d →
    Fits ((unitDistanceGraph A).degree v)
      (sourceTokens P W F.chart hlocal a v +
        sourceTokens P W F.chart hlocal b v +
        sourceTokens P W F.chart hlocal c v +
        sourceTokens P W F.chart hlocal d v)

namespace WeightedCollisionWitnesses

variable {P W F hlocal}

/-- Globalize the local triple estimate by the same genuine seven-window
locality theorem. -/
theorem triple_fits (C : WeightedCollisionWitnesses P W F hlocal)
    {a b c : Source P W} {v : Vertex A}
    (ha : 0 < sourceTokens P W F.chart hlocal a v)
    (hb : 0 < sourceTokens P W F.chart hlocal b v)
    (hc : 0 < sourceTokens P W F.chart hlocal c v)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fits ((unitDistanceGraph A).degree v)
      (sourceTokens P W F.chart hlocal a v +
        sourceTokens P W F.chart hlocal b v +
        sourceTokens P W F.chart hlocal c v) := by
  exact C.triple_fits_in_window ha hb hc
    (C.locality.competing_source_in_window ha hb)
    (C.locality.competing_source_in_window ha hc) hab hac hbc

/-- Globalize the local quadruple estimate by metric locality. -/
theorem quadruple_fits (C : WeightedCollisionWitnesses P W F hlocal)
    {a b c d : Source P W} {v : Vertex A}
    (ha : 0 < sourceTokens P W F.chart hlocal a v)
    (hb : 0 < sourceTokens P W F.chart hlocal b v)
    (hc : 0 < sourceTokens P W F.chart hlocal c v)
    (hd : 0 < sourceTokens P W F.chart hlocal d v)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Fits ((unitDistanceGraph A).degree v)
      (sourceTokens P W F.chart hlocal a v +
        sourceTokens P W F.chart hlocal b v +
        sourceTokens P W F.chart hlocal c v +
        sourceTokens P W F.chart hlocal d v) := by
  exact C.quadruple_fits_in_window ha hb hc hd
    (C.locality.competing_source_in_window ha hb)
    (C.locality.competing_source_in_window ha hc)
    (C.locality.competing_source_in_window ha hd)
    hab hac had hbc hbd hcd

/-- Instantiate the generic weight-aware cardinal arithmetic with the
actual source-indexed local rows. -/
noncomputable def toWeightedCollisionData
    (hA : IsOneSeparated A) (C : WeightedCollisionWitnesses P W F hlocal) :
    WeightedCollisionData (Source P W) (Vertex A) where
  degree := fun v ↦ (unitDistanceGraph A).degree v
  tokens := sourceTokens P W F.chart hlocal
  degree_le_six := degree_unitDistanceGraph_le_six hA
  occupied_degree_le_five := by
    intro s v hpos
    exact (selectedCase P W F.chart hlocal s).positive_target_degree_le_five hpos
  positive_weight := by
    intro s v hpos
    exact (selectedCase P W F.chart hlocal s).positive_weight hpos
  pair_fits := by
    intro a b v hab ha hb
    exact CollisionWitnesses.actual_pair_fits hab ha hb
  contributors_card_le_four := by
    intro v
    exact C.contributors_card_le_four v
  triple_fits := by
    intro a b c v ha hb hc hab hac hbc
    exact C.triple_fits ha hb hc hab hac hbc
  quadruple_fits := by
    intro a b c d v ha hb hc hd hab hac had hbc hbd hcd
    exact C.quadruple_fits ha hb hc hd hab hac had hbc hbd hcd

/-- Weight-aware incoming capacity for the actual local rows. -/
theorem actual_incoming_capacity
    (hA : IsOneSeparated A) (C : WeightedCollisionWitnesses P W F hlocal)
    (v : Vertex A) :
    2 * (unitDistanceGraph A).degree v +
        ∑ s : Source P W, sourceTokens P W F.chart hlocal s v ≤ 12 := by
  exact (C.toWeightedCollisionData hA).incoming_capacity v

/-- Assemble the actual local rows and the weight-aware collision theorem
into the production transfer certificate. -/
theorem transferCert
    (hA : IsOneSeparated A) (C : WeightedCollisionWitnesses P W F hlocal) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A) P.H
      (distinguishedVertices P W) (sourceVertices P W)) := by
  classical
  refine ⟨{
    transfer := combinedTransfer P W F.chart hlocal
    source_subset_distinguished := sourceVertices_subset_distinguished P W
    distinguished_subset_hull := distinguishedVertices_subset_hull P W
    hull_degree_le_three := ?_
    distinguished_nonsource_degree_le_two := ?_
    source_row_sum := combinedTransfer_row_sum P W F.chart hlocal
    target_not_hull := combinedTransfer_target_not_hull P W F.chart hlocal
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
  · intro v _hv
    rw [← CollisionWitnesses.sum_sourceTokens_eq_sum_combinedTransfer
      (P := P) (W := W) (chart := F.chart) (hlocal := hlocal) v]
    exact C.actual_incoming_capacity hA v

end WeightedCollisionWitnesses

/-- Final collision-facing geometric interface.  All locality is derived
in the common bisector chart; the sole remaining combinatorial input is the
case/role-specific uniqueness of two same-side identifications inside one
actual seven-window. -/
structure RoleCollisionWitnesses where
  locality : SourceLocalityCertificates P W F
  sideOf : Source P W → Vertex A → Bool
  same_side_unique_in_window : ∀ {s t : Source P W} {v},
    0 < sourceTokens P W F.chart hlocal s v →
    0 < sourceTokens P W F.chart hlocal t v →
    t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
    sideOf s v = sideOf t v → s = t

namespace RoleCollisionWitnesses

variable {P W F hlocal}

noncomputable def toWindowedCollisionWitnesses
    (C : RoleCollisionWitnesses P W F hlocal) :
    WindowedCollisionWitnesses P W F.chart hlocal where
  toCollisionPictures := automaticCollisionPictures P W F.chart hlocal
  sideOf := C.sideOf
  competing_source_in_window := by
    intro s t v hs ht
    exact C.locality.competing_source_in_window hs ht
  same_side_unique_in_window := C.same_side_unique_in_window

/-- Source-specific locality and role uniqueness assemble the production
transfer certificate.  The former degree-five picture obligations are
discharged uniformly by `automaticCollisionPictures`. -/
theorem transferCert
    (hA : IsOneSeparated A) (C : RoleCollisionWitnesses P W F hlocal) :
    Nonempty (Erdos957.TransferCert (unitDistanceGraph A) P.H
      (distinguishedVertices P W) (sourceVertices P W)) :=
  (C.toWindowedCollisionWitnesses.toCollisionWitnesses)
    |>.transferCert_of_collisionWitnesses hA

end RoleCollisionWitnesses

end Erdos957CollisionInstantiation

#print axioms Erdos957CollisionInstantiation.CollisionWitnesses.transferCert_of_collisionWitnesses
#print axioms Erdos957CollisionInstantiation.NoThreeRoleCollisionWitnesses.transferCert
#print axioms Erdos957CollisionInstantiation.WeightedCollisionWitnesses.transferCert
#print axioms Erdos957CollisionInstantiation.RoleCollisionWitnesses.transferCert
