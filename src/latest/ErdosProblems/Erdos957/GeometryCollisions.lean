import Mathlib
import ErdosProblems.Erdos957.Overcharge

/-!
# Global collision assembly for the charging proof of Erdős 957

This file isolates the last *finite bookkeeping* step in Dumitrescu's
charging argument.  Its input contains only the following primitive data.

* every source is tagged by one of the four cases;
* a source sends either one or two doubled tokens to a target;
* every occupied target has degree at most five, and a whole Case 3 target
  has degree at most four;
* cyclic locality excludes three distinct sources at one target;
* the four dangerous case-pairs carry exactly the coordinate, extreme-
  neighbour-count, or neighbour-incidence data used in Figures 10, 13, 14,
  and 15.

In particular, neither `PrimitiveCollisionData` nor any of its fields states
an incoming-token or final-capacity inequality.  The theorem
`incoming_capacity` derives

`2 * degree v + sum of all incoming tokens at v <= 12`

from those primitive facts.  The proof invokes the checked kernels in
`Erdos957Overcharge` for precisely the four dangerous pairs.  The other six
unordered pairs are discharged directly from their token values and degree
thresholds.
-/

open scoped BigOperators

namespace Erdos957GeometryCollisions

open Erdos957Overcharge

variable {S V E : Type*}
variable [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V]
variable [DecidableEq E]

/--
Primitive geometric information needed to assemble all local transfers.

The point triples in `two_four_picture` and the displayed neighbours in
`four_four_forced_six` are witnesses extracted from the corresponding local
coordinate pictures.  Their fields are only equalities, strict inequalities,
degree equalities, and incidences.  Thus the record does not assume the
capacity conclusion it is designed to prove.
-/
structure PrimitiveCollisionData (S V E : Type*)
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
    [DecidableEq E] where
  /-- The four-case tag attached to each emitting hull vertex. -/
  caseTag : S → CaseNumber
  /-- The degree in the normalized shortest-distance graph. -/
  degree : V → ℕ
  /-- Doubled tokens sent by a source to a target. -/
  tokens : S → V → ℕ
  /-- The planar kissing bound, including targets which receive no token. -/
  degree_le_six : ∀ v, degree v ≤ 6
  /-- Every target actually used by a local rule has degree at most five. -/
  occupied_degree_le_five : ∀ {s v}, 0 < tokens s v → degree v ≤ 5
  /-- Every positive local weight is a half-unit or a whole unit. -/
  positive_weight : ∀ {s v}, 0 < tokens s v →
    tokens s v = 1 ∨ tokens s v = 2
  /-- Case 1 always splits its source unit into two half-units. -/
  case_one_weight : ∀ {s v}, caseTag s = .one → 0 < tokens s v →
    tokens s v = 1
  /-- Case 2 also uses only half-units. -/
  case_two_weight : ∀ {s v}, caseTag s = .two → 0 < tokens s v →
    tokens s v = 1
  /-- A whole Case 3 recipient is selected only in the low-degree branch. -/
  case_three_whole_degree_le_four : ∀ {s v}, caseTag s = .three →
    tokens s v = 2 → degree v ≤ 4
  /--
  Cyclic locality in incidence form: no three distinct source windows can
  contain the same target.  This is strictly weaker than a capacity bound.
  -/
  no_three_sources : ∀ {a b c v},
    0 < tokens a v → 0 < tokens b v → 0 < tokens c v →
    a ≠ b → a ≠ c → b ≠ c → False
  /-- Actual extreme-neighbour set of a target, used only in Figure 14. -/
  extremeNeighbors : V → Finset E
  /-- Actual graph-neighbour set of a target, used only in Figure 15. -/
  neighbors : V → Finset V
  neighbors_card : ∀ v, (neighbors v).card = degree v
  /--
  Figure 10 data for the only dangerous `(1,4)` identification.  The same
  point would have perpendicular distance at least `sqrt 3` and less than
  one from the normalized supporting line.
  -/
  one_four_picture : ∀ {s t v}, s ≠ t → caseTag s = .one →
    caseTag t = .four → tokens s v = 1 → tokens t v = 2 → degree v = 5 →
    ∃ (height : ℝ) (w c : ℝ × ℝ), w = c ∧
      Real.sqrt 3 ≤ horizontalLineDistance height w ∧
      horizontalLineDistance height c < 1
  /--
  Figure 13 data for the dangerous `(2,4)` identification: the identified
  point and two consecutive hull vertices would form the displayed unit
  equilateral triangle with the incompatible height inequalities.
  -/
  two_four_picture : ∀ {s t v}, s ≠ t → caseTag s = .two →
    caseTag t = .four → tokens s v = 1 → tokens t v = 2 → degree v = 5 →
    ∃ (u j d : ℝ × ℝ),
      sqDist u d = 1 ∧ sqDist j d = 1 ∧ sqDist u j = 1 ∧
      d.2 = -(Real.sqrt 3 / 2) ∧ d.2 < u.2 ∧ d.2 < j.2 ∧
      u.2 < 0 ∧ j.2 < 0
  /--
  Figure 14 data for the dangerous `(3,4)` identification.  The same actual
  target would have exactly one extreme neighbour and either zero or two.
  -/
  three_four_counts : ∀ {s t v}, s ≠ t → caseTag s = .three →
    caseTag t = .four → tokens s v = 1 → tokens t v = 2 → degree v = 5 →
    (extremeNeighbors v).card = 1 ∧
      ((extremeNeighbors v).card = 0 ∨ (extremeNeighbors v).card = 2)
  /--
  Figure 15 data for a dangerous `(4,4)` identification.  At the alleged
  degree-five target, the local pictures exhibit six distinct genuine
  neighbours.
  -/
  four_four_forced_six : ∀ {s t v}, s ≠ t → caseTag s = .four →
    caseTag t = .four → 0 < tokens s v → 0 < tokens t v →
    3 ≤ tokens s v + tokens t v → degree v = 5 →
    ∃ displayed : Fin 6 → V, Function.Injective displayed ∧
      ∀ i, displayed i ∈ neighbors v

namespace PrimitiveCollisionData

variable (C : PrimitiveCollisionData S V E)

/-- Sources sending a positive token to a fixed target. -/
def contributors (v : V) : Finset S :=
  Finset.univ.filter fun s ↦ 0 < C.tokens s v

@[simp]
lemma mem_contributors {s : S} {v : V} :
    s ∈ C.contributors v ↔ 0 < C.tokens s v := by
  simp [contributors]

/-- The incidence form of cyclic locality implies at most two contributors. -/
lemma card_contributors_le_two (v : V) : (C.contributors v).card ≤ 2 := by
  by_contra h
  have hthree : 2 < (C.contributors v).card := by omega
  rcases Finset.two_lt_card.mp hthree with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  exact C.no_three_sources
    (C.mem_contributors.mp ha) (C.mem_contributors.mp hb)
    (C.mem_contributors.mp hc) hab hac hbc

/-- Removing zero rows does not change the incoming sum. -/
lemma sum_contributors (v : V) :
    ∑ s, C.tokens s v = ∑ s ∈ C.contributors v, C.tokens s v := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have hnpos : ¬ 0 < C.tokens s v := by
    intro hpos
    exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hpos⟩)
  exact Nat.eq_zero_of_not_pos hnpos

private lemma one_four_not_dangerous {s t : S} {v : V}
    (hst : s ≠ t) (hs : C.caseTag s = .one)
    (ht : C.caseTag t = .four) (hqs : C.tokens s v = 1)
    (hqt : C.tokens t v = 2) (hd : C.degree v = 5) : False := by
  rcases C.one_four_picture hst hs ht hqs hqt hd with
    ⟨height, w, c, hwc, hw, hc⟩
  exact (figure10_supportingLine_exclusion hw hc) hwc

private lemma two_four_not_dangerous {s t : S} {v : V}
    (hst : s ≠ t) (hs : C.caseTag s = .two)
    (ht : C.caseTag t = .four) (hqs : C.tokens s v = 1)
    (hqt : C.tokens t v = 2) (hd : C.degree v = 5) : False := by
  rcases C.two_four_picture hst hs ht hqs hqt hd with
    ⟨u, j, d, hud, hjd, huj, hdheight, hdu, hdj, hu0, hj0⟩
  exact figure13_equilateral_hull_exclusion
    hud hjd huj hdheight hdu hdj hu0 hj0

private lemma three_four_not_dangerous {s t : S} {v : V}
    (hst : s ≠ t) (hs : C.caseTag s = .three)
    (ht : C.caseTag t = .four) (hqs : C.tokens s v = 1)
    (hqt : C.tokens t v = 2) (hd : C.degree v = 5) : False := by
  rcases C.three_four_counts hst hs ht hqs hqt hd with
    ⟨hone, hzero | htwo⟩
  · exact figure14_one_extreme_ne_zero_extreme (C.extremeNeighbors v) hone hzero
  · exact figure14_one_extreme_ne_two_extreme (C.extremeNeighbors v) hone htwo

private lemma four_four_not_dangerous {s t : S} {v : V}
    (hst : s ≠ t) (hs : C.caseTag s = .four)
    (ht : C.caseTag t = .four) (hps : 0 < C.tokens s v)
    (hpt : 0 < C.tokens t v) (hheavy : 3 ≤ C.tokens s v + C.tokens t v)
    (hd : C.degree v = 5) : False := by
  rcases C.four_four_forced_six hst hs ht hps hpt hheavy hd with
    ⟨displayed, hinj, hmem⟩
  apply figure15_six_neighbors_contradict_degree_five
    (C.neighbors v) displayed hinj hmem
  rw [C.neighbors_card, hd]

/--
For two distinct contributors, the ten unordered case pairs imply the exact
local capacity.  This is the formal assembly of the ten paragraphs following
Figures 10--16.
-/
lemma pair_fits {s t : S} {v : V} (hst : s ≠ t)
    (hps : 0 < C.tokens s v) (hpt : 0 < C.tokens t v) :
    Fits (C.degree v) (C.tokens s v + C.tokens t v) := by
  have hdeg5 : C.degree v ≤ 5 := C.occupied_degree_le_five hps
  have hqs : C.tokens s v = 1 ∨ C.tokens s v = 2 := C.positive_weight hps
  have hqt : C.tokens t v = 1 ∨ C.tokens t v = 2 := C.positive_weight hpt
  have hheavy : 3 ≤ C.tokens s v + C.tokens t v → C.degree v ≤ 4 := by
    intro hsum
    cases hs : C.caseTag s <;> cases ht : C.caseTag t
    · have hs1 := C.case_one_weight hs hps
      have ht1 := C.case_one_weight ht hpt
      omega
    · have hs1 := C.case_one_weight hs hps
      have ht1 := C.case_two_weight ht hpt
      omega
    · have hs1 := C.case_one_weight hs hps
      have ht2 : C.tokens t v = 2 := by omega
      exact C.case_three_whole_degree_le_four ht ht2
    · have hs1 := C.case_one_weight hs hps
      have ht2 : C.tokens t v = 2 := by omega
      by_contra hnot
      have hd : C.degree v = 5 := by omega
      exact C.one_four_not_dangerous hst hs ht hs1 ht2 hd
    · have hs1 := C.case_two_weight hs hps
      have ht1 := C.case_one_weight ht hpt
      omega
    · have hs1 := C.case_two_weight hs hps
      have ht1 := C.case_two_weight ht hpt
      omega
    · have hs1 := C.case_two_weight hs hps
      have ht2 : C.tokens t v = 2 := by omega
      exact C.case_three_whole_degree_le_four ht ht2
    · have hs1 := C.case_two_weight hs hps
      have ht2 : C.tokens t v = 2 := by omega
      by_contra hnot
      have hd : C.degree v = 5 := by omega
      exact C.two_four_not_dangerous hst hs ht hs1 ht2 hd
    · have ht1 := C.case_one_weight ht hpt
      have hs2 : C.tokens s v = 2 := by omega
      exact C.case_three_whole_degree_le_four hs hs2
    · have ht1 := C.case_two_weight ht hpt
      have hs2 : C.tokens s v = 2 := by omega
      exact C.case_three_whole_degree_le_four hs hs2
    · rcases hqs with hs1 | hs2
      · have ht2 : C.tokens t v = 2 := by omega
        exact C.case_three_whole_degree_le_four ht ht2
      · exact C.case_three_whole_degree_le_four hs hs2
    · rcases hqs with hs1 | hs2
      · have ht2 : C.tokens t v = 2 := by omega
        by_contra hnot
        have hd : C.degree v = 5 := by omega
        exact C.three_four_not_dangerous hst hs ht hs1 ht2 hd
      · exact C.case_three_whole_degree_le_four hs hs2
    · have ht1 := C.case_one_weight ht hpt
      have hs2 : C.tokens s v = 2 := by omega
      by_contra hnot
      have hd : C.degree v = 5 := by omega
      exact C.one_four_not_dangerous hst.symm ht hs ht1 hs2 hd
    · have ht1 := C.case_two_weight ht hpt
      have hs2 : C.tokens s v = 2 := by omega
      by_contra hnot
      have hd : C.degree v = 5 := by omega
      exact C.two_four_not_dangerous hst.symm ht hs ht1 hs2 hd
    · rcases hqt with ht1 | ht2
      · have hs2 : C.tokens s v = 2 := by omega
        by_contra hnot
        have hd : C.degree v = 5 := by omega
        exact C.three_four_not_dangerous hst.symm ht hs ht1 hs2 hd
      · exact C.case_three_whole_degree_le_four ht ht2
    · by_contra hnot
      have hd : C.degree v = 5 := by omega
      exact C.four_four_not_dangerous hst hs ht hps hpt hsum hd
  simp only [Fits]
  omega

/--
The globally assembled incoming-token bound.  Its proof splits only on the
number (zero, one, or two) of contributors and uses `pair_fits` in the last
case.
-/
theorem incoming_capacity (v : V) :
    2 * C.degree v + ∑ s, C.tokens s v ≤ 12 := by
  rw [C.sum_contributors]
  have hcard := C.card_contributors_le_two v
  rcases Nat.eq_zero_or_pos (C.contributors v).card with hzero | hpos
  · have hempty : C.contributors v = ∅ := Finset.card_eq_zero.mp hzero
    have hdeg := C.degree_le_six v
    simp [hempty]
    omega
  · by_cases hone : (C.contributors v).card = 1
    · rcases Finset.card_eq_one.mp hone with ⟨s, hs⟩
      have hsp : 0 < C.tokens s v := by
        apply C.mem_contributors.mp
        simp [hs]
      have hdeg := C.occupied_degree_le_five hsp
      have hw := C.positive_weight hsp
      simp [hs]
      omega
    · have htwo : (C.contributors v).card = 2 := by omega
      rcases Finset.card_eq_two.mp htwo with ⟨s, t, hst, hs⟩
      have hsp : 0 < C.tokens s v := by
        apply C.mem_contributors.mp
        simp [hs]
      have htp : 0 < C.tokens t v := by
        apply C.mem_contributors.mp
        simp [hs]
      have hfit := C.pair_fits hst hsp htp
      simpa [hs, hst, Fits, Nat.add_comm] using hfit

end PrimitiveCollisionData

/-!
## Weight-aware collision assembly

The original `PrimitiveCollisionData` above uses the stronger assertion that
there are at most two contributing sources.  Dumitrescu's local
classification naturally allows some three- and four-source columns.  The
following interface therefore keeps the honest geometric division of
labour: at most four rows contribute, every two-source column satisfies the
checked pair estimate, and genuine three- and four-source columns satisfy
their separately proved local estimates.

The last two fields are local two- and three-row conclusions, not a bound on
the full incoming sum over all sources.
-/

/-- Primitive weight-aware information for one family of transfer rows. -/
structure WeightedCollisionData (S V : Type*)
    [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] where
  degree : V → ℕ
  tokens : S → V → ℕ
  degree_le_six : ∀ v, degree v ≤ 6
  occupied_degree_le_five : ∀ {s v}, 0 < tokens s v → degree v ≤ 5
  positive_weight : ∀ {s v}, 0 < tokens s v →
    tokens s v = 1 ∨ tokens s v = 2
  /-- The already checked ten-pair analysis for two distinct contributors. -/
  pair_fits : ∀ {a b v}, a ≠ b → 0 < tokens a v → 0 < tokens b v →
    Fits (degree v) (tokens a v + tokens b v)
  /-- The genuine role classification permits at most four source rows at
  one target.  This is a contributor-count statement, not a charge bound. -/
  contributors_card_le_four : ∀ v,
    (Finset.univ.filter fun s ↦ 0 < tokens s v).card ≤ 4
  /-- The genuine local estimate for three distinct contributing rows. -/
  triple_fits : ∀ {a b c v},
    0 < tokens a v → 0 < tokens b v → 0 < tokens c v →
    a ≠ b → a ≠ c → b ≠ c →
    Fits (degree v) (tokens a v + tokens b v + tokens c v)
  /-- The genuine local estimate for four distinct contributing rows. -/
  quadruple_fits : ∀ {a b c d v},
    0 < tokens a v → 0 < tokens b v →
    0 < tokens c v → 0 < tokens d v →
    a ≠ b → a ≠ c → a ≠ d →
    b ≠ c → b ≠ d → c ≠ d →
    Fits (degree v)
      (tokens a v + tokens b v + tokens c v + tokens d v)

namespace WeightedCollisionData

variable (C : WeightedCollisionData S V)

/-- Sources making a positive contribution to a fixed target. -/
def weightedContributors (v : V) : Finset S :=
  Finset.univ.filter fun s ↦ 0 < C.tokens s v

@[simp] lemma mem_weightedContributors {s : S} {v : V} :
    s ∈ C.weightedContributors v ↔ 0 < C.tokens s v := by
  simp [weightedContributors]

/-- The geometric source-count field gives at most four contributors. -/
lemma card_weightedContributors_le_four (v : V) :
    (C.weightedContributors v).card ≤ 4 := by
  simpa [weightedContributors] using C.contributors_card_le_four v

/-- Removing the zero rows does not change the incoming sum. -/
lemma sum_weightedContributors (v : V) :
    ∑ s, C.tokens s v =
      ∑ s ∈ C.weightedContributors v, C.tokens s v := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro s _ hs
  have hnpos : ¬ 0 < C.tokens s v := by
    intro hpos
    exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hpos⟩)
  exact Nat.eq_zero_of_not_pos hnpos

/-- Global capacity obtained by splitting on the honest possibilities of
zero, one, two, three, or four contributing source rows. -/
theorem incoming_capacity (v : V) :
    2 * C.degree v + ∑ s, C.tokens s v ≤ 12 := by
  rw [C.sum_weightedContributors v]
  have hcard := C.card_weightedContributors_le_four v
  rcases Nat.eq_zero_or_pos (C.weightedContributors v).card with hzero | hpos
  · have hempty : C.weightedContributors v = ∅ := Finset.card_eq_zero.mp hzero
    have hdeg := C.degree_le_six v
    simp [hempty]
    omega
  · by_cases hone : (C.weightedContributors v).card = 1
    · rcases Finset.card_eq_one.mp hone with ⟨s, hs⟩
      have hsp : 0 < C.tokens s v := by
        apply C.mem_weightedContributors.mp
        simp [hs]
      have hdeg := C.occupied_degree_le_five hsp
      have hw := C.positive_weight hsp
      simp [hs]
      omega
    · by_cases htwo : (C.weightedContributors v).card = 2
      · rcases Finset.card_eq_two.mp htwo with ⟨s, t, hst, hs⟩
        have hsp : 0 < C.tokens s v := by
          apply C.mem_weightedContributors.mp
          simp [hs]
        have htp : 0 < C.tokens t v := by
          apply C.mem_weightedContributors.mp
          simp [hs]
        have hfit := C.pair_fits hst hsp htp
        simpa [hs, hst, Fits, Nat.add_comm] using hfit
      · by_cases hthree : (C.weightedContributors v).card = 3
        · rcases Finset.card_eq_three.mp hthree with
            ⟨a, b, c, hab, hac, hbc, hs⟩
          have hap : 0 < C.tokens a v := by
            apply C.mem_weightedContributors.mp
            simp [hs]
          have hbp : 0 < C.tokens b v := by
            apply C.mem_weightedContributors.mp
            simp [hs]
          have hcp : 0 < C.tokens c v := by
            apply C.mem_weightedContributors.mp
            simp [hs]
          have hfit := C.triple_fits hap hbp hcp hab hac hbc
          simpa [hs, hab, hac, hbc, Fits, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hfit
        · have hfour : (C.weightedContributors v).card = 4 := by omega
          rcases Finset.card_eq_four.mp hfour with
            ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hs⟩
          have hap : 0 < C.tokens a v := by
            apply C.mem_weightedContributors.mp
            simp [hs]
          have hbp : 0 < C.tokens b v := by
            apply C.mem_weightedContributors.mp
            simp [hs]
          have hcp : 0 < C.tokens c v := by
            apply C.mem_weightedContributors.mp
            simp [hs]
          have hdp : 0 < C.tokens d v := by
            apply C.mem_weightedContributors.mp
            simp [hs]
          have hfit := C.quadruple_fits hap hbp hcp hdp
            hab hac had hbc hbd hcd
          simpa [hs, hab, hac, had, hbc, hbd, hcd, Fits,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfit

end WeightedCollisionData

end Erdos957GeometryCollisions

#print axioms Erdos957GeometryCollisions.PrimitiveCollisionData.incoming_capacity
#print axioms Erdos957GeometryCollisions.WeightedCollisionData.incoming_capacity
