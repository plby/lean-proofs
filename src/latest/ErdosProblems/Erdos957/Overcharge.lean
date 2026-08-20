import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The local no-overcharge checks in Dumitrescu's proof of Erdős 957

This module isolates the *checked* algebraic and geometric kernels of Lemma 4
(`Lemma 3` in the author's longer preprint) of

* A. Dumitrescu, *A Product Inequality for Extreme Distances*, SoCG 2019.

The source considers the ten unordered pairs `(1,1)`, `(1,2)`, `(1,3)`, `(1,4)`, `(2,2)`,
`(2,3)`, `(2,4)`, `(3,3)`, `(3,4)`, and `(4,4)`.  Charges are doubled below, so a half-unit
is `1`, a unit is `2`, and the capacity above a vertex of degree `d` is `12 - 2*d`.

The genuinely pictorial exclusions are separated from the bookkeeping:

* Figure 10: incompatible perpendicular distances to the supporting line;
* Figure 13: the lower equilateral apex lies strictly below the fixed lattice point;
* Figure 14: a primary Case 3 target cannot have zero or two extreme neighbours;
* Figure 15: identifying the targets forces a sixth distinct neighbour at a degree-five vertex.

All hypotheses in those lemmas are coordinate inequalities, membership assertions, or exact
cardinalities.  In particular, none assumes that the target is not overcharged.
-/

namespace Erdos957Overcharge

/-! ## Doubled-charge bookkeeping -/

/-- `Fits d q` says that adding doubled charge `q` to a vertex of degree `d` leaves final
charge at most six. -/
def Fits (d q : ℕ) : Prop := 2 * d + q ≤ 12

/-- Two half-units fit at every target of degree at most five.  This is the arithmetic used in
the pairs `(1,1)`, `(1,2)`, `(2,2)`, `(2,3)`, the safe branch of `(3,3)`, Figure 14, and the
safe branch of `(4,4)`. -/
lemma two_halves_fit {d : ℕ} (hd : d ≤ 5) : Fits d 2 := by
  simp only [Fits]
  omega

/-- A whole unit and a half-unit fit at a target of degree at most four.  This is the low-degree
branch in `(1,3)` and `(2,3)`. -/
lemma half_and_whole_fit {d : ℕ} (hd : d ≤ 4) : Fits d 3 := by
  simp only [Fits]
  omega

/-- Two whole units fit at a target of degree at most four.  This includes the Case 4 primary
target when its two source units are both sent to that target. -/
lemma two_wholes_fit {d : ℕ} (hd : d ≤ 4) : Fits d 4 := by
  simp only [Fits]
  omega

/-- A half-unit and a whole unit do *not* fit at degree five.  These are precisely the dangerous
branches excluded geometrically in Figures 10 and 13. -/
lemma half_and_whole_do_not_fit_degree_five : ¬ Fits 5 3 := by
  norm_num [Fits]

/-- A whole unit plus another whole unit does not fit at degree five. -/
lemma two_wholes_do_not_fit_degree_five : ¬ Fits 5 4 := by
  norm_num [Fits]

/-- A Case 3 primary target of degree at most four remains safe even if it gets a half-unit from
each side in addition to its own whole unit, exactly as stated in the `(1,3)` paragraph. -/
lemma whole_and_two_halves_fit {d : ℕ} (hd : d ≤ 4) : Fits d 4 := by
  exact two_wholes_fit hd

/-! ## Figure 10: the supporting-line distance contradiction -/

/-- The vertical distance to a horizontal supporting line in the coordinates used in the paper. -/
def horizontalLineDistance (height : ℝ) (p : ℝ × ℝ) : ℝ := |p.2 - height|

lemma one_lt_sqrt_three : (1 : ℝ) < Real.sqrt 3 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  nlinarith

/-- Figure 10's second identification is impossible: the Case 4 point is at perpendicular
distance at least `sqrt 3` from the supporting line, whereas the Case 1 point is at distance
strictly less than one. -/
lemma figure10_supportingLine_exclusion {height : ℝ} {w c : ℝ × ℝ}
    (hw : Real.sqrt 3 ≤ horizontalLineDistance height w)
    (hc : horizontalLineDistance height c < 1) :
    w ≠ c := by
  intro hwc
  subst c
  linarith [one_lt_sqrt_three]

/-- A coordinate-specialized form of `figure10_supportingLine_exclusion`, with the supporting
line normalized to the x-axis. -/
lemma figure10_xAxis_exclusion {w c : ℝ × ℝ}
    (hw : Real.sqrt 3 ≤ |w.2|) (hc : |c.2| < 1) : w ≠ c := by
  apply figure10_supportingLine_exclusion (height := 0)
  · simpa [horizontalLineDistance]
  · simpa [horizontalLineDistance]

/-! ## Figure 13: an exact lower-apex comparison -/

/-- The lower equilateral apex on the oriented segment `uv`.  The formula is the midpoint minus
`sqrt 3 / 2` times the counterclockwise quarter-turn of `v-u`.  It is meaningful without assuming
`dist u v = 1`; in the unit-edge application it is the third vertex of the equilateral triangle. -/
noncomputable def lowerEquilateralApex (u v : ℝ × ℝ) : ℝ × ℝ :=
  ((u.1 + v.1) / 2 + (Real.sqrt 3 / 2) * (v.2 - u.2),
    (u.2 + v.2) / 2 - (Real.sqrt 3 / 2) * (v.1 - u.1))

@[simp] lemma lowerEquilateralApex_snd (u v : ℝ × ℝ) :
    (lowerEquilateralApex u v).2 =
      (u.2 + v.2) / 2 - (Real.sqrt 3 / 2) * (v.1 - u.1) := rfl

lemma sqrt_three_pos : (0 : ℝ) < Real.sqrt 3 := by
  linarith [one_lt_sqrt_three]

/-- If both endpoints of an oriented edge lie strictly below the old supporting line and its
horizontal advance is at least one, its lower equilateral apex is strictly below height
`-sqrt 3 / 2`.  This is the quantitative coordinate kernel of Figure 13. -/
lemma lowerEquilateralApex_snd_lt_neg_half_sqrt_three {u v : ℝ × ℝ}
    (hu : u.2 < 0) (hv : v.2 < 0) (hx : 1 ≤ v.1 - u.1) :
    (lowerEquilateralApex u v).2 < -(Real.sqrt 3 / 2) := by
  rw [lowerEquilateralApex_snd]
  have hs : 0 < Real.sqrt 3 / 2 := by positivity
  have havg : (u.2 + v.2) / 2 < 0 := by linarith
  have hprod : Real.sqrt 3 / 2 ≤ (Real.sqrt 3 / 2) * (v.1 - u.1) := by
    nlinarith
  linarith

/-- Figure 13's proposed equality `d = v_j` is impossible once the Case 2 lattice point `d` is
at height `-sqrt 3/2` and the Case 4 equilateral triangle is based on the strictly lower hull edge
`u_j u_{j+1}`. -/
lemma figure13_lowerApex_exclusion {u j d : ℝ × ℝ}
    (hu : u.2 < 0) (hj : j.2 < 0) (hx : 1 ≤ j.1 - u.1)
    (hd : d.2 = -(Real.sqrt 3 / 2)) :
    d ≠ lowerEquilateralApex u j := by
  intro hEq
  have hlt := lowerEquilateralApex_snd_lt_neg_half_sqrt_three hu hj hx
  have hsnd := congrArg Prod.snd hEq
  rw [hd] at hsnd
  linarith

/-- Squared Euclidean distance in the paper's orthonormal coordinate system.  We use an explicit
formula rather than the product metric on `ℝ × ℝ`, which is not the Euclidean product metric. -/
def sqDist (p q : ℝ × ℝ) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Two unit vectors with unit separation whose vertical components are positive cannot both have
vertical component strictly less than `sqrt 3 / 2`.  This is the orientation-free equilateral
triangle fact needed in Figure 13. -/
lemma equilateral_positive_vertical_component
    {px py qx qy : ℝ}
    (hp : px ^ 2 + py ^ 2 = 1) (hq : qx ^ 2 + qy ^ 2 = 1)
    (hpq : (px - qx) ^ 2 + (py - qy) ^ 2 = 1)
    (hpy : 0 < py) (hqy : 0 < qy) :
    Real.sqrt 3 / 2 ≤ py ∨ Real.sqrt 3 / 2 ≤ qy := by
  by_contra hsmall
  push Not at hsmall
  have hdot : px * qx + py * qy = 1 / 2 := by
    nlinarith [hp, hq, hpq]
  have hpx : px ^ 2 = 1 - py ^ 2 := by linarith
  have hqx : qx ^ 2 = 1 - qy ^ 2 := by linarith
  have hxprod : px * qx = 1 / 2 - py * qy := by linarith
  have hsquare : (1 / 2 - py * qy) ^ 2 =
      (1 - py ^ 2) * (1 - qy ^ 2) := by
    calc
      (1 / 2 - py * qy) ^ 2 = (px * qx) ^ 2 := by rw [hxprod]
      _ = px ^ 2 * qx ^ 2 := by ring
      _ = (1 - py ^ 2) * (1 - qy ^ 2) := by rw [hpx, hqx]
  have hquad : py ^ 2 + qy ^ 2 - py * qy = 3 / 4 := by
    nlinarith [hsquare]
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  rcases le_total py qy with hle | hle
  · have hcross : py * (py - qy) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpy.le (sub_nonpos.mpr hle)
    have hqy_sq : qy ^ 2 < 3 / 4 := by
      nlinarith [sq_nonneg (Real.sqrt 3 / 2 - qy), sqrt_three_pos]
    nlinarith
  · have hcross : qy * (qy - py) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hqy.le (sub_nonpos.mpr hle)
    have hpy_sq : py ^ 2 < 3 / 4 := by
      nlinarith [sq_nonneg (Real.sqrt 3 / 2 - py), sqrt_three_pos]
    nlinarith

/-- A stronger Figure 13 exclusion that uses only the primitive picture data.  The points `u,j,d`
form an equilateral unit triangle; `d` is the lower vertex at the Case 2 lattice height
`-sqrt 3/2`; and both consecutive hull endpoints lie strictly between `d` and the old supporting
line.  Those six assertions are inconsistent, because one endpoint of an upward equilateral
triangle has vertical rise at least `sqrt 3/2`. -/
lemma figure13_equilateral_hull_exclusion {u j d : ℝ × ℝ}
    (hud : sqDist u d = 1) (hjd : sqDist j d = 1) (huj : sqDist u j = 1)
    (hd : d.2 = -(Real.sqrt 3 / 2))
    (hdu : d.2 < u.2) (hdj : d.2 < j.2) (hu0 : u.2 < 0) (hj0 : j.2 < 0) : False := by
  have hvertical := equilateral_positive_vertical_component
    (px := u.1 - d.1) (py := u.2 - d.2)
    (qx := j.1 - d.1) (qy := j.2 - d.2)
    (by simpa [sqDist] using hud)
    (by simpa [sqDist] using hjd)
    (by
      have h := huj
      simp only [sqDist] at h
      ring_nf at h ⊢
      exact h)
    (by linarith) (by linarith)
  rcases hvertical with hvertical | hvertical
  · rw [hd] at hvertical
    linarith
  · rw [hd] at hvertical
    linarith

/-! ## Figure 14: incompatible numbers of extreme neighbours -/

/-- A target cannot simultaneously have exactly one and exactly two extreme neighbours.  These
are the primitive target-role conditions for a Case 3 primary and a Case 4 primary. -/
lemma figure14_one_extreme_ne_two_extreme {α : Type*} [DecidableEq α]
    (extremeNeighbors : Finset α) (hone : extremeNeighbors.card = 1)
    (htwo : extremeNeighbors.card = 2) : False := by
  omega

/-- A target cannot simultaneously have exactly one and no extreme neighbours.  This excludes a
Case 3 primary from being the lower whole-unit target in the left branch of Case 4. -/
lemma figure14_one_extreme_ne_zero_extreme {α : Type*} [DecidableEq α]
    (extremeNeighbors : Finset α) (hone : extremeNeighbors.card = 1)
    (hzero : extremeNeighbors.card = 0) : False := by
  omega

/-! ## Figure 15: the forced sixth edge -/

/-- Six distinct displayed neighbours cannot all belong to a neighbour set of cardinality five.
This is the exact finite counting kernel of Figure 15: the five already incident edges are indexed
by five elements of `Fin 6`, and the additional edge `v_i v_j` is the sixth. -/
lemma figure15_six_neighbors_contradict_degree_five {α : Type*} [DecidableEq α]
    (neighbors : Finset α) (displayed : Fin 6 → α)
    (hdisplayed : Function.Injective displayed)
    (hmem : ∀ i, displayed i ∈ neighbors) (hdegree : neighbors.card = 5) : False := by
  have hcard : Fintype.card (Fin 6) ≤ neighbors.card := by
    apply Finset.card_le_card_of_injOn displayed
        (s := Finset.univ) (t := neighbors)
    · intro i hi
      exact hmem i
    · intro i hi j hj hij
      exact hdisplayed hij
  simp only [Fintype.card_fin] at hcard
  omega

/-! ## Exact correspondence with the ten source paragraphs

Here is the complete case-pair map from the proof, in source order.

1. `(1,1)`: the target is `b` from the left and `a` from the right in Figure 4.  Both arrivals
   are half-units, hence `two_halves_fit`.
2. `(1,2)`: the target is `b` or `d` in Figure 5 from the left and `a` in Figure 4 from the
   right.  Again both arrivals are half-units.
3. `(1,3)`: a whole Case 3 arrival occurs only at degree at most four and is covered by
   `half_and_whole_fit` (even two external halves are covered by `whole_and_two_halves_fit`).
   At degree five Case 3 splits its source unit, so only two half-units meet.
4. `(1,4)`: the only numerical danger is a Case 4 whole unit plus a Case 1 half-unit at degree
   five.  Locality gives `j=i+2`.  In Figure 10's degree-five-lower-target branch, `v_i=c`
   would make `c` adjacent to three consecutive extreme vertices, while `w_i=c` contradicts
   the line-height comparison formalized by `figure10_supportingLine_exclusion`.  In Figure 11's
   degree-six-lower-target branch the only identification is `b=c`, receiving half plus half.
5. `(2,2)`: Case 2 only sends half-units, at most one from either side.
6. `(2,3)`: at degree five both relevant arrivals are halves.  A whole Case 3 primary arrival
   has degree at most four, so the whole-plus-half arithmetic is safe.
7. `(2,4)`: the only danger is half plus whole at degree five.  Figure 13 shows that it would
   force `w_{i+2}=w_j`, `b=e`, and `d=v_j`; the old Case 2 lattice fixes the height of `d`, while
   the strictly lower consecutive hull edge makes the equilateral point `v_j` lower.  The
   orientation-free analytic core is `figure13_equilateral_hull_exclusion`.
8. `(3,3)`: a Case 3 primary has exactly one extreme neighbour and therefore cannot be primary
   for two sources.  Every secondary Case 3 arrival is a half-unit.
9. `(3,4)`: a Case 4 primary has exactly two extreme neighbours, and its whole-unit lower target
   has none; neither can be a Case 3 primary, which has exactly one.  These contradictions are
   `figure14_one_extreme_ne_two_extreme` and `figure14_one_extreme_ne_zero_extreme`.  All remaining
   identifications in Figure 14 receive half plus half.
10. `(4,4)`: in Figure 15, identifying the left whole-unit lower target `w_i` with the right
    half-unit target `a` forces the additional edge `v_i v_j` beyond the five displayed neighbours
    of `v_j`, contradicted by `figure15_six_neighbors_contradict_degree_five`.  Figure 16's other
    identification `b=c` receives half plus half.

Thus the checked local kernels account for every arithmetic branch and for the final contradictions
inside Figures 10, 13, 14, and 15.  A full integration still has to derive their primitive hypotheses
from a formal cyclic hull, flatness, angular order of unit neighbours, and the four charging rules.
-/

inductive CaseNumber
  | one | two | three | four
  deriving DecidableEq

def CaseNumber.rank : CaseNumber → ℕ
  | .one => 0
  | .two => 1
  | .three => 2
  | .four => 3

/-- The ten unordered pairs, in precisely the order of the paper's proof. -/
def casePairs : Finset (CaseNumber × CaseNumber) :=
  {(.one, .one), (.one, .two), (.one, .three), (.one, .four),
   (.two, .two), (.two, .three), (.two, .four),
   (.three, .three), (.three, .four), (.four, .four)}

lemma card_casePairs : casePairs.card = 10 := by
  decide

/-- Every pair ordered by its case number is represented in `casePairs`. -/
lemma mem_casePairs_of_le (a b : CaseNumber) (h : a.rank ≤ b.rank) :
    (a, b) ∈ casePairs := by
  cases a <;> cases b <;> simp_all [CaseNumber.rank, casePairs]

end Erdos957Overcharge
