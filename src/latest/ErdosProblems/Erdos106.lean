/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 106.
https://www.erdosproblems.com/forum/thread/106

Informal authors:
- A. Raj Singh

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos106.md
-/
/-
This is a Lean formalization of a counterexample to the proposed equality in
Erdős Problem 106.

https://www.erdosproblems.com/forum/thread/106

The construction consists of sixteen axis-parallel squares and one rotated
square.  It is first described in a square of side four and then scaled by
one quarter.

Formal author:
- OpenAI Codex
-/

import Mathlib

open scoped BigOperators

namespace Erdos106

noncomputable section

/-! ## Geometric squares and packings -/

/-- The ambient plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/--
Data defining a square: `center` is its center, `direction` is one unit side
direction, and `side` is its side length.  The other side direction is the
counterclockwise quarter-turn `(-direction.2, direction.1)`.
-/
structure Square where
  center : Point
  direction : Point
  side : ℝ

/-- The point with local coordinates `(λ, μ)` in a square. -/
def Square.point (S : Square) (lam mu : ℝ) : Point :=
  (S.center.1 + lam * S.direction.1 - mu * S.direction.2,
    S.center.2 + lam * S.direction.2 + mu * S.direction.1)

/-- The closed geometric square. -/
def Square.carrier (S : Square) : Set Point :=
  {p | ∃ lam mu : ℝ,
    |lam| ≤ S.side / 2 ∧ |mu| ≤ S.side / 2 ∧ p = S.point lam mu}

/--
The geometric interior of the square, expressed in the square's local
coordinates.  Under `Square.IsGenuine`, this is exactly the usual interior.
-/
def Square.openCarrier (S : Square) : Set Point :=
  {p | ∃ lam mu : ℝ,
    |lam| < S.side / 2 ∧ |mu| < S.side / 2 ∧ p = S.point lam mu}

/-- Positivity of the side and orthonormality of the displayed directions. -/
def Square.IsGenuine (S : Square) : Prop :=
  0 < S.side ∧ S.direction.1 ^ 2 + S.direction.2 ^ 2 = 1

/-- The closed axis-parallel square `[0,L] × [0,L]`. -/
def box (L : ℝ) : Set Point :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ L ∧ 0 ≤ p.2 ∧ p.2 ≤ L}

/-- A packing consists of genuine squares contained in the box, with pairwise
disjoint geometric interiors. -/
def IsPackingIn (L : ℝ) {n : ℕ} (P : Fin n → Square) : Prop :=
  (∀ i, (P i).IsGenuine) ∧
  (∀ i, (P i).carrier ⊆ box L) ∧
  (∀ i j, i ≠ j → Disjoint (P i).openCarrier (P j).openCarrier)

/-- The sum of the side lengths in a finite packing. -/
def totalSideLength {n : ℕ} (P : Fin n → Square) : ℝ :=
  ∑ i, (P i).side

/-- Values attained by `n`-square packings inside the unit square. -/
def attainableSideSums (n : ℕ) : Set ℝ :=
  {t | ∃ P : Fin n → Square, IsPackingIn 1 P ∧ totalSideLength P = t}

/-- The supremal total side length for `n` squares in the unit square. -/
noncomputable def f (n : ℕ) : ℝ :=
  sSup (attainableSideSums n)

/-! ## Projection certificates -/

/-- Scalar projection onto a (not necessarily unit) direction. -/
def projection (w p : Point) : ℝ :=
  w.1 * p.1 + w.2 * p.2

/-- Coefficient of the first local coordinate under projection by `w`. -/
def Square.projU (w : Point) (S : Square) : ℝ :=
  w.1 * S.direction.1 + w.2 * S.direction.2

/-- Coefficient of the second local coordinate under projection by `w`. -/
def Square.projV (w : Point) (S : Square) : ℝ :=
  -w.1 * S.direction.2 + w.2 * S.direction.1

/-- Half-width of a square after projection onto `w`. -/
def Square.projRadius (w : Point) (S : Square) : ℝ :=
  S.side / 2 * (|S.projU w| + |S.projV w|)

lemma Square.projection_point (S : Square) (w : Point) (lam mu : ℝ) :
    projection w (S.point lam mu) =
      projection w S.center + lam * S.projU w + mu * S.projV w := by
  simp only [projection, Square.point, Square.projU, Square.projV]
  ring

lemma Square.projU_projV_not_both_zero
    (S : Square) (w : Point) (hS : S.IsGenuine) (hw : w ≠ (0, 0)) :
    S.projU w ≠ 0 ∨ S.projV w ≠ 0 := by
  by_contra h
  push Not at h
  have hx :
      S.direction.1 * S.projU w - S.direction.2 * S.projV w =
        w.1 * (S.direction.1 ^ 2 + S.direction.2 ^ 2) := by
    simp only [Square.projU, Square.projV]
    ring
  have hy :
      S.direction.2 * S.projU w + S.direction.1 * S.projV w =
        w.2 * (S.direction.1 ^ 2 + S.direction.2 ^ 2) := by
    simp only [Square.projU, Square.projV]
    ring
  rw [h.1, h.2, hS.2] at hx hy
  norm_num at hx hy
  exact hw (Prod.ext hx.symm hy.symm)

lemma abs_local_projection_lt
    {s lam mu A B : ℝ}
    (hlam : |lam| < s / 2) (hmu : |mu| < s / 2)
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    |lam * A + mu * B| < s / 2 * (|A| + |B|) := by
  rcases hAB with hA | hB
  · have hApos : 0 < |A| := abs_pos.mpr hA
    calc
      |lam * A + mu * B| ≤ |lam * A| + |mu * B| := abs_add_le _ _
      _ = |lam| * |A| + |mu| * |B| := by rw [abs_mul, abs_mul]
      _ < s / 2 * |A| + s / 2 * |B| := by
        exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_right hlam hApos)
          (mul_le_mul_of_nonneg_right hmu.le (abs_nonneg B))
      _ = s / 2 * (|A| + |B|) := by ring
  · have hBpos : 0 < |B| := abs_pos.mpr hB
    calc
      |lam * A + mu * B| ≤ |lam * A| + |mu * B| := abs_add_le _ _
      _ = |lam| * |A| + |mu| * |B| := by rw [abs_mul, abs_mul]
      _ < s / 2 * |A| + s / 2 * |B| := by
        exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_right hlam.le (abs_nonneg A))
          (mul_lt_mul_of_pos_right hmu hBpos)
      _ = s / 2 * (|A| + |B|) := by ring

lemma Square.openCarrier_projection_bounds
    (S : Square) (w : Point) (hS : S.IsGenuine) (hw : w ≠ (0, 0))
    {p : Point} (hp : p ∈ S.openCarrier) :
    projection w S.center - S.projRadius w <
      projection w p ∧
      projection w p < projection w S.center + S.projRadius w := by
  obtain ⟨lam, mu, hlam, hmu, rfl⟩ := hp
  rw [S.projection_point]
  have habs :
      |lam * S.projU w + mu * S.projV w| < S.projRadius w := by
    exact abs_local_projection_lt hlam hmu
      (S.projU_projV_not_both_zero w hS hw)
  rw [abs_lt] at habs
  constructor <;> linarith

/-- A closed separating-line certificate for two squares. -/
def SeparatedBy (w : Point) (S T : Square) : Prop :=
  projection w S.center + S.projRadius w ≤
      projection w T.center - T.projRadius w ∨
    projection w T.center + T.projRadius w ≤
      projection w S.center - S.projRadius w

lemma disjoint_openCarriers_of_separatedBy
    {S T : Square} {w : Point}
    (hS : S.IsGenuine) (hT : T.IsGenuine) (hw : w ≠ (0, 0))
    (hsep : SeparatedBy w S T) :
    Disjoint S.openCarrier T.openCarrier := by
  rw [Set.disjoint_left]
  intro p hpS hpT
  have hSb := S.openCarrier_projection_bounds w hS hw hpS
  have hTb := T.openCarrier_projection_bounds w hT hw hpT
  rcases hsep with hsep | hsep <;> linarith

/-! ## Rational certificates for the explicit construction -/

/-- Rational square data, used so all construction checks are decidable exact
computations rather than floating-point calculations. -/
structure QSquare where
  cx : ℚ
  cy : ℚ
  ux : ℚ
  uy : ℚ
  side : ℚ
deriving DecidableEq, Repr

/-- Coerce exact rational square data to geometric square data over `ℝ`. -/
def QSquare.toSquare (S : QSquare) : Square where
  center := (S.cx, S.cy)
  direction := (S.ux, S.uy)
  side := S.side

/-- Scale positions and side lengths, leaving orientation unchanged. -/
def QSquare.scale (r : ℚ) (S : QSquare) : QSquare where
  cx := r * S.cx
  cy := r * S.cy
  ux := S.ux
  uy := S.uy
  side := r * S.side

/-- Exact rational validity test. -/
def QSquare.IsGenuine (S : QSquare) : Prop :=
  0 < S.side ∧ S.ux ^ 2 + S.uy ^ 2 = 1

instance QSquare.instDecidableIsGenuine (S : QSquare) :
    Decidable S.IsGenuine := by
  unfold QSquare.IsGenuine
  infer_instance

/-- Radius of the axis-parallel bounding box. -/
def QSquare.boxRadius (S : QSquare) : ℚ :=
  S.side / 2 * (|S.ux| + |S.uy|)

/-- Exact certificate that the bounding box lies in `[0,L]²`. -/
def QSquare.IsInBox (L : ℚ) (S : QSquare) : Prop :=
  S.boxRadius ≤ S.cx ∧ S.cx + S.boxRadius ≤ L ∧
  S.boxRadius ≤ S.cy ∧ S.cy + S.boxRadius ≤ L

instance QSquare.instDecidableIsInBox (L : ℚ) (S : QSquare) :
    Decidable (S.IsInBox L) := by
  unfold QSquare.IsInBox
  infer_instance

abbrev QPoint := ℚ × ℚ

def qProjection (w p : QPoint) : ℚ :=
  w.1 * p.1 + w.2 * p.2

def QSquare.qProjU (w : QPoint) (S : QSquare) : ℚ :=
  w.1 * S.ux + w.2 * S.uy

def QSquare.qProjV (w : QPoint) (S : QSquare) : ℚ :=
  -w.1 * S.uy + w.2 * S.ux

def QSquare.qProjRadius (w : QPoint) (S : QSquare) : ℚ :=
  S.side / 2 * (|S.qProjU w| + |S.qProjV w|)

def QSquare.IsSeparatedBy (w : QPoint) (S T : QSquare) : Prop :=
  qProjection w (S.cx, S.cy) + S.qProjRadius w ≤
      qProjection w (T.cx, T.cy) - T.qProjRadius w ∨
    qProjection w (T.cx, T.cy) + T.qProjRadius w ≤
      qProjection w (S.cx, S.cy) - S.qProjRadius w

instance QSquare.instDecidableIsSeparatedBy (w : QPoint) (S T : QSquare) :
    Decidable (S.IsSeparatedBy w T) := by
  unfold QSquare.IsSeparatedBy
  infer_instance

/-- The four directions used by the finite separation check: the coordinate
axes and the two special supporting directions for the rotated square. -/
def certificateDirections : List QPoint :=
  [(1, 0), (0, 1), (40 / 41, 9 / 41), (9 / 41, -40 / 41)]

def QSquare.IsSeparated (S T : QSquare) : Prop :=
  certificateDirections.any (fun w ↦ decide (S.IsSeparatedBy w T)) = true

instance QSquare.instDecidableIsSeparated (S T : QSquare) :
    Decidable (S.IsSeparated T) := by
  unfold QSquare.IsSeparated
  infer_instance

lemma QSquare.toSquare_isGenuine {S : QSquare} (hS : S.IsGenuine) :
    S.toSquare.IsGenuine := by
  change 0 < (S.side : ℝ) ∧ (S.ux : ℝ) ^ 2 + (S.uy : ℝ) ^ 2 = 1
  constructor
  · exact_mod_cast hS.1
  · exact_mod_cast hS.2

lemma qProjection_cast (w p : QPoint) :
    projection ((w.1 : ℝ), (w.2 : ℝ)) ((p.1 : ℝ), (p.2 : ℝ)) =
      (qProjection w p : ℝ) := by
  simp [projection, qProjection]

lemma QSquare.projRadius_cast (w : QPoint) (S : QSquare) :
    S.toSquare.projRadius ((w.1 : ℝ), (w.2 : ℝ)) =
      (S.qProjRadius w : ℝ) := by
  simp [Square.projRadius, Square.projU, Square.projV,
    QSquare.toSquare, QSquare.qProjRadius, QSquare.qProjU, QSquare.qProjV,
    Rat.cast_abs]

lemma QSquare.separatedBy_toSquare
    {w : QPoint} {S T : QSquare} (h : S.IsSeparatedBy w T) :
    SeparatedBy ((w.1 : ℝ), (w.2 : ℝ)) S.toSquare T.toSquare := by
  rcases h with h | h
  · left
    change
      projection ((w.1 : ℝ), (w.2 : ℝ)) ((S.cx : ℝ), (S.cy : ℝ)) +
          S.toSquare.projRadius ((w.1 : ℝ), (w.2 : ℝ)) ≤
        projection ((w.1 : ℝ), (w.2 : ℝ)) ((T.cx : ℝ), (T.cy : ℝ)) -
          T.toSquare.projRadius ((w.1 : ℝ), (w.2 : ℝ))
    rw [QSquare.projRadius_cast, QSquare.projRadius_cast]
    simp only [projection]
    exact_mod_cast h
  · right
    change
      projection ((w.1 : ℝ), (w.2 : ℝ)) ((T.cx : ℝ), (T.cy : ℝ)) +
          T.toSquare.projRadius ((w.1 : ℝ), (w.2 : ℝ)) ≤
        projection ((w.1 : ℝ), (w.2 : ℝ)) ((S.cx : ℝ), (S.cy : ℝ)) -
          S.toSquare.projRadius ((w.1 : ℝ), (w.2 : ℝ))
    rw [QSquare.projRadius_cast, QSquare.projRadius_cast]
    simp only [projection]
    exact_mod_cast h

lemma certificateDirection_ne_zero
    {w : QPoint} (hw : w ∈ certificateDirections) :
    ((w.1 : ℝ), (w.2 : ℝ)) ≠ (0, 0) := by
  simp only [certificateDirections, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> norm_num

lemma QSquare.disjoint_toSquare_of_separated
    {S T : QSquare} (hS : S.IsGenuine) (hT : T.IsGenuine)
    (hsep : S.IsSeparated T) :
    Disjoint S.toSquare.openCarrier T.toSquare.openCarrier := by
  have hex : ∃ w ∈ certificateDirections, S.IsSeparatedBy w T := by
    apply List.any_iff_exists_prop.mp
    exact hsep
  obtain ⟨w, hw, hsep⟩ := hex
  exact disjoint_openCarriers_of_separatedBy
    (S.toSquare_isGenuine hS) (T.toSquare_isGenuine hT)
    (certificateDirection_ne_zero hw) (S.separatedBy_toSquare hsep)

lemma Square.carrier_coordinate_bounds
    (S : Square) {p : Point} (hp : p ∈ S.carrier) :
    |p.1 - S.center.1| ≤
        S.side / 2 * (|S.direction.1| + |S.direction.2|) ∧
      |p.2 - S.center.2| ≤
        S.side / 2 * (|S.direction.1| + |S.direction.2|) := by
  obtain ⟨lam, mu, hlam, hmu, rfl⟩ := hp
  constructor
  · simp only [Square.point]
    have hLam :
        |lam| * |S.direction.1| ≤
          (S.side / 2) * |S.direction.1| :=
      mul_le_mul_of_nonneg_right hlam (abs_nonneg _)
    have hMu :
        |mu| * |S.direction.2| ≤
          (S.side / 2) * |S.direction.2| :=
      mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    calc
      |(S.center.1 + lam * S.direction.1 - mu * S.direction.2) -
          S.center.1| =
          |lam * S.direction.1 - mu * S.direction.2| := by ring_nf
      _ ≤ |lam * S.direction.1| + |mu * S.direction.2| := by
        simpa [sub_eq_add_neg] using
          (abs_add_le (lam * S.direction.1) (-mu * S.direction.2))
      _ = |lam| * |S.direction.1| + |mu| * |S.direction.2| := by
        rw [abs_mul, abs_mul]
      _ ≤ (S.side / 2) * |S.direction.1| +
          (S.side / 2) * |S.direction.2| := add_le_add hLam hMu
      _ = S.side / 2 * (|S.direction.1| + |S.direction.2|) := by ring
  · simp only [Square.point]
    have hLam :
        |lam| * |S.direction.2| ≤
          (S.side / 2) * |S.direction.2| :=
      mul_le_mul_of_nonneg_right hlam (abs_nonneg _)
    have hMu :
        |mu| * |S.direction.1| ≤
          (S.side / 2) * |S.direction.1| :=
      mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
    calc
      |(S.center.2 + lam * S.direction.2 + mu * S.direction.1) -
          S.center.2| =
          |lam * S.direction.2 + mu * S.direction.1| := by ring_nf
      _ ≤ |lam * S.direction.2| + |mu * S.direction.1| := abs_add_le _ _
      _ = |lam| * |S.direction.2| + |mu| * |S.direction.1| := by
        rw [abs_mul, abs_mul]
      _ ≤ (S.side / 2) * |S.direction.2| +
          (S.side / 2) * |S.direction.1| := add_le_add hLam hMu
      _ = S.side / 2 * (|S.direction.1| + |S.direction.2|) := by ring

lemma QSquare.carrier_subset_box
    {L : ℚ} {S : QSquare} (hbox : S.IsInBox L) :
    S.toSquare.carrier ⊆ box (L : ℝ) := by
  intro p hp
  have hcoord := S.toSquare.carrier_coordinate_bounds hp
  have hradius :
      S.toSquare.side / 2 *
          (|S.toSquare.direction.1| + |S.toSquare.direction.2|) =
        (S.boxRadius : ℝ) := by
    simp [QSquare.toSquare, QSquare.boxRadius, Rat.cast_abs]
  rw [hradius] at hcoord
  have hxlo : (S.boxRadius : ℝ) ≤ S.cx := by exact_mod_cast hbox.1
  have hxhi : (S.cx : ℝ) + S.boxRadius ≤ L := by exact_mod_cast hbox.2.1
  have hylo : (S.boxRadius : ℝ) ≤ S.cy := by exact_mod_cast hbox.2.2.1
  have hyhi : (S.cy : ℝ) + S.boxRadius ≤ L := by exact_mod_cast hbox.2.2.2
  have hxcoord := abs_le.mp hcoord.1
  have hycoord := abs_le.mp hcoord.2
  simp [QSquare.toSquare] at hxcoord hycoord
  simpa [box, QSquare.toSquare] using
    (show 0 ≤ p.1 ∧ p.1 ≤ (L : ℝ) ∧ 0 ≤ p.2 ∧ p.2 ≤ (L : ℝ) by
      constructor
      · linarith [hxcoord.1]
      constructor
      · linarith [hxcoord.2]
      constructor
      · linarith [hycoord.1]
      · linarith [hycoord.2])

/-! ## The seventeen exact squares -/

def a : ℚ := 851228 / 1048735
def C : ℚ := 1073566 / 1048735
def b : ℚ := 2 - a
def D : ℚ := 2 - C
def E : ℚ := 2 * a + C - 2
def q : ℚ := 49 / 41
def h : ℚ := E / q

def axisSquare (x y s : ℚ) : QSquare where
  cx := x + s / 2
  cy := y + s / 2
  ux := 1
  uy := 0
  side := s

def rotatedH : QSquare where
  cx := 4 - 3 * E / 2
  cy := 2 * b + E / 2
  ux := 40 / 41
  uy := 9 / 41
  side := h

/-- The packing in the `[0,4]²` container, in the order used in the proof. -/
def fourPackingQ : Fin 17 → QSquare :=
  ![
    axisSquare 0 0 1,
    axisSquare 0 1 1,
    axisSquare 0 2 1,
    axisSquare 0 3 1,
    axisSquare 1 0 1,
    axisSquare 1 1 1,
    axisSquare 1 2 1,
    axisSquare 1 3 1,
    axisSquare 2 0 a,
    axisSquare 2 a a,
    axisSquare 2 (2 * a) a,
    axisSquare (2 + a) 0 b,
    axisSquare (2 + a) b b,
    axisSquare 2 (4 - C) C,
    axisSquare (2 + C) (4 - D) D,
    axisSquare (4 - E) (2 * b) E,
    rotatedH
  ]

/-- Scaling the displayed packing by one quarter places it in the unit square. -/
def unitPackingQ : Fin 17 → QSquare :=
  fun i ↦ (fourPackingQ i).scale (1 / 4)

def unitPacking : Fin 17 → Square :=
  fun i ↦ (unitPackingQ i).toSquare

lemma unitPackingQ_genuine : ∀ i, (unitPackingQ i).IsGenuine := by
  intro i
  fin_cases i <;>
    norm_num [unitPackingQ, fourPackingQ, QSquare.scale,
      QSquare.IsGenuine, axisSquare, rotatedH, a, b, C, D, E, q, h]

lemma unitPackingQ_in_box : ∀ i, (unitPackingQ i).IsInBox 1 := by
  intro i
  fin_cases i <;>
    norm_num [unitPackingQ, fourPackingQ, QSquare.scale,
      QSquare.IsInBox, QSquare.boxRadius, axisSquare, rotatedH,
      a, b, C, D, E, q, h, abs_of_nonneg, abs_of_nonpos]

set_option maxHeartbeats 4000000 in
-- The kernel checks all 272 ordered non-diagonal pairs by exact rational normalization.
lemma unitPackingQ_pairwise_separated :
    ∀ i j, i ≠ j → (unitPackingQ i).IsSeparated (unitPackingQ j) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals
    norm_num [unitPackingQ, fourPackingQ, QSquare.scale,
      QSquare.IsSeparated, certificateDirections, QSquare.IsSeparatedBy,
      qProjection, QSquare.qProjRadius, QSquare.qProjU, QSquare.qProjV,
      axisSquare, rotatedH, a, b, C, D, E, q, h,
      abs_of_nonneg, abs_of_nonpos]

lemma unitPacking_isPacking : IsPackingIn 1 unitPacking := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact QSquare.toSquare_isGenuine (unitPackingQ_genuine i)
  · intro i
    simpa [unitPacking] using QSquare.carrier_subset_box
      (unitPackingQ_in_box i)
  · intro i j hij
    exact QSquare.disjoint_toSquare_of_separated
      (unitPackingQ_genuine i) (unitPackingQ_genuine j)
      (unitPackingQ_pairwise_separated i j hij)

lemma unitPacking_totalSideLength :
    totalSideLength unitPacking =
      4 + 78 / (4 * 1048735 : ℝ) := by
  norm_num [totalSideLength, unitPacking, unitPackingQ, fourPackingQ,
    QSquare.scale, QSquare.toSquare, axisSquare, rotatedH, a, b, C, D, E, q, h,
    Fin.sum_univ_succ]

theorem exists_seventeen_square_packing :
    ∃ P : Fin 17 → Square,
      IsPackingIn 1 P ∧ 4 < totalSideLength P := by
  refine ⟨unitPacking, unitPacking_isPacking, ?_⟩
  rw [unitPacking_totalSideLength]
  norm_num

/-! ## Relating the construction to the extremal function `f` -/

lemma carrier_contains_side_endpoints (S : Square) (hS : S.IsGenuine) :
    S.point (S.side / 2) 0 ∈ S.carrier ∧
      S.point (-S.side / 2) 0 ∈ S.carrier := by
  constructor
  · refine ⟨S.side / 2, 0, ?_, ?_, rfl⟩
    · have hhalf : 0 ≤ S.side / 2 := by linarith [hS.1]
      rw [abs_of_nonneg hhalf]
    · norm_num
      linarith [hS.1]
  · refine ⟨-S.side / 2, 0, ?_, ?_, rfl⟩
    · have hhalf : 0 ≤ S.side / 2 := by linarith [hS.1]
      rw [show -S.side / 2 = -(S.side / 2) by ring, abs_neg,
        abs_of_nonneg hhalf]
    · norm_num
      linarith [hS.1]

lemma side_le_two_of_mem_unit_box
    (S : Square) (hS : S.IsGenuine) (hbox : S.carrier ⊆ box 1) :
    S.side ≤ 2 := by
  obtain ⟨hp, hm⟩ := carrier_contains_side_endpoints S hS
  have hpbox := hbox hp
  have hmbox := hbox hm
  simp only [box, Set.mem_ofPred_eq] at hpbox hmbox
  have hx :
      -1 ≤
          (S.point (S.side / 2) 0).1 -
            (S.point (-S.side / 2) 0).1 ∧
        (S.point (S.side / 2) 0).1 -
            (S.point (-S.side / 2) 0).1 ≤ 1 := by
    constructor <;> linarith [hpbox.1, hpbox.2.1, hmbox.1, hmbox.2.1]
  have hy :
      -1 ≤
          (S.point (S.side / 2) 0).2 -
            (S.point (-S.side / 2) 0).2 ∧
        (S.point (S.side / 2) 0).2 -
            (S.point (-S.side / 2) 0).2 ≤ 1 := by
    constructor <;> linarith [hpbox.2.2.1, hpbox.2.2.2, hmbox.2.2.1, hmbox.2.2.2]
  have hx' : (S.side * S.direction.1) ^ 2 ≤ 1 := by
    have heq :
        (S.point (S.side / 2) 0).1 -
            (S.point (-S.side / 2) 0).1 =
          S.side * S.direction.1 := by
      simp [Square.point]
      ring
    rw [heq] at hx
    nlinarith
  have hy' : (S.side * S.direction.2) ^ 2 ≤ 1 := by
    have heq :
        (S.point (S.side / 2) 0).2 -
            (S.point (-S.side / 2) 0).2 =
          S.side * S.direction.2 := by
      simp [Square.point]
      ring
    rw [heq] at hy
    nlinarith
  have hsq :
      (S.side * S.direction.1) ^ 2 +
          (S.side * S.direction.2) ^ 2 =
        S.side ^ 2 := by
    calc
      (S.side * S.direction.1) ^ 2 +
          (S.side * S.direction.2) ^ 2 =
        S.side ^ 2 *
          (S.direction.1 ^ 2 + S.direction.2 ^ 2) := by ring
      _ = S.side ^ 2 := by rw [hS.2]; ring
  nlinarith

lemma attainableSideSums_bddAbove (n : ℕ) :
    BddAbove (attainableSideSums n) := by
  refine ⟨2 * n, ?_⟩
  rintro t ⟨P, hP, rfl⟩
  calc
    totalSideLength P = ∑ i, (P i).side := rfl
    _ ≤ ∑ _i : Fin n, (2 : ℝ) := by
      exact Finset.sum_le_sum fun i _ ↦
        side_le_two_of_mem_unit_box (P i) (hP.1 i) (hP.2.1 i)
    _ = 2 * n := by simp [mul_comm]

/-- The explicit construction disproves the proposed equality at `k = 4`. -/
theorem four_lt_f_seventeen : 4 < f 17 := by
  obtain ⟨P, hpack, htotal⟩ := exists_seventeen_square_packing
  apply lt_csSup_of_lt (attainableSideSums_bddAbove 17)
  · exact ⟨P, hpack, rfl⟩
  · exact htotal

/-- In the notation of the problem, `17 = 4² + 1`, so the proposed universal
identity `f(k²+1)=k` is false. -/
theorem not_erdos_106 :
    ¬ ∀ k : ℕ, f (k ^ 2 + 1) = k := by
  intro hall
  have hfour := hall 4
  norm_num at hfour
  linarith [four_lt_f_seventeen]

end

end Erdos106
