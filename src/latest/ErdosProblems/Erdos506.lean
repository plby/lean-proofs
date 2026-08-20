/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 506

For a finite set `P` of points in the real plane, a determined circle is a
proper circle through three non-collinear points of `P`.  Elliott's 1967
argument, with the correction of Purdy and Smith, proves that if `P` is not
contained in a line or a circle and `P.card = n > 393`, then it determines at
least

`Nat.choose (n - 1) 2 + 1 - (n - 1) / 2`

distinct circles.  A circle with `n - 1` suitably paired points and its center
attains the bound.

Circles are represented by their unique monic equations
`x² + y² + u*x + v*y + w = 0`.  A coefficient triple occurring below always
contains a non-collinear triple, hence is exactly a proper Euclidean circle.

References:

* P. D. T. A. Elliott, *On the number of circles determined by n points*,
  Acta Math. Acad. Sci. Hungar. 18 (1967), 181--188.
* L. M. Kelly and W. O. J. Moser, *On the number of ordinary lines determined
  by n points*, Canad. J. Math. 10 (1958), 210--219.
* G. Purdy and J. Smith, *Lines, circles, planes and spheres*, arXiv:0907.0724.
-/

namespace Erdos506

abbrev Point := ℝ × ℝ

/-- Twice the signed area of the triangle `a b c`. -/
def det (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Three points are collinear precisely when their signed-area determinant
vanishes. -/
def Collinear (a b c : Point) : Prop := det a b c = 0

/-- Three points are non-collinear.  This condition already implies that the
three points are pairwise distinct. -/
def Noncollinear (a b c : Point) : Prop := det a b c ≠ 0

@[simp] lemma collinear_iff_det_eq_zero (a b c : Point) :
    Collinear a b c ↔ det a b c = 0 := Iff.rfl

@[simp] lemma noncollinear_iff_det_ne_zero (a b c : Point) :
    Noncollinear a b c ↔ det a b c ≠ 0 := Iff.rfl

lemma noncollinear_ne_left {a b c : Point} (h : Noncollinear a b c) : a ≠ b := by
  intro hab
  subst b
  exact h (by simp [det])

lemma noncollinear_ne_right {a b c : Point} (h : Noncollinear a b c) : a ≠ c := by
  intro hac
  subst c
  exact h (by simp [det])

lemma noncollinear_ne_last {a b c : Point} (h : Noncollinear a b c) : b ≠ c := by
  intro hbc
  subst c
  exact h (by simp [det]; ring)

/-- Coefficients of the monic circle equation
`x² + y² + u*x + v*y + w = 0`. -/
structure Circle where
  u : ℝ
  v : ℝ
  w : ℝ

@[ext] lemma Circle.ext {C D : Circle}
    (hu : C.u = D.u) (hv : C.v = D.v) (hw : C.w = D.w) : C = D := by
  cases C
  cases D
  simp_all

/-- Squared Euclidean norm in coordinate form. -/
def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2

/-- Incidence of a point with a circle equation. -/
def OnCircle (C : Circle) (p : Point) : Prop :=
  normSq p + C.u * p.1 + C.v * p.2 + C.w = 0

/-- The total algebraic formula for the circle through `a`, `b`, and `c`.
Its geometric specification is used only under `Noncollinear a b c`. -/
noncomputable def circleThrough (a b c : Point) : Circle :=
  let d := det a b c
  let qab := normSq a - normSq b
  let qac := normSq a - normSq c
  let u := (qab * (c.2 - a.2) - (b.2 - a.2) * qac) / d
  let v := ((b.1 - a.1) * qac - qab * (c.1 - a.1)) / d
  { u := u
    v := v
    w := -normSq a - u * a.1 - v * a.2 }

lemma circleThrough_on_left (a b c : Point) : OnCircle (circleThrough a b c) a := by
  simp [circleThrough, OnCircle]

lemma circleThrough_on_middle {a b c : Point} (h : Noncollinear a b c) :
    OnCircle (circleThrough a b c) b := by
  have hd : det a b c ≠ 0 := h
  simp only [circleThrough, OnCircle]
  field_simp [hd]
  simp only [det, normSq] at *
  ring

lemma circleThrough_on_right {a b c : Point} (h : Noncollinear a b c) :
    OnCircle (circleThrough a b c) c := by
  have hd : det a b c ≠ 0 := h
  simp only [circleThrough, OnCircle]
  field_simp [hd]
  simp only [det, normSq] at *
  ring

/-- Subtracting two circle equations leaves an affine-linear equation. -/
lemma circle_difference {C D : Circle} {p : Point}
    (hC : OnCircle C p) (hD : OnCircle D p) :
    (C.u - D.u) * p.1 + (C.v - D.v) * p.2 + (C.w - D.w) = 0 := by
  simp only [OnCircle] at hC hD
  linarith

/-- A non-collinear triple determines at most one monic circle equation. -/
lemma circle_eq_of_three {C D : Circle} {a b c : Point}
    (hnc : Noncollinear a b c)
    (hCa : OnCircle C a) (hCb : OnCircle C b) (hCc : OnCircle C c)
    (hDa : OnCircle D a) (hDb : OnCircle D b) (hDc : OnCircle D c) : C = D := by
  have ha := circle_difference hCa hDa
  have hb := circle_difference hCb hDb
  have hc := circle_difference hCc hDc
  have hd : det a b c ≠ 0 := hnc
  let U := C.u - D.u
  let V := C.v - D.v
  let W := C.w - D.w
  have hba : U * (b.1 - a.1) + V * (b.2 - a.2) = 0 := by
    dsimp [U, V, W] at *
    linarith
  have hca : U * (c.1 - a.1) + V * (c.2 - a.2) = 0 := by
    dsimp [U, V, W] at *
    linarith
  have hUdet : U * det a b c = 0 := by
    calc
      U * det a b c =
          (U * (b.1 - a.1)) * (c.2 - a.2) -
            (U * (c.1 - a.1)) * (b.2 - a.2) := by
              simp only [det]
              ring
      _ = (-V * (b.2 - a.2)) * (c.2 - a.2) -
            (-V * (c.2 - a.2)) * (b.2 - a.2) := by
              rw [show U * (b.1 - a.1) = -V * (b.2 - a.2) by linarith,
                show U * (c.1 - a.1) = -V * (c.2 - a.2) by linarith]
      _ = 0 := by ring
  have hVdet : V * det a b c = 0 := by
    calc
      V * det a b c =
          (b.1 - a.1) * (V * (c.2 - a.2)) -
            (c.1 - a.1) * (V * (b.2 - a.2)) := by
              simp only [det]
              ring
      _ = (b.1 - a.1) * (-U * (c.1 - a.1)) -
            (c.1 - a.1) * (-U * (b.1 - a.1)) := by
              rw [show V * (c.2 - a.2) = -U * (c.1 - a.1) by linarith,
                show V * (b.2 - a.2) = -U * (b.1 - a.1) by linarith]
      _ = 0 := by ring
  have hU : U = 0 := (mul_eq_zero.mp hUdet).resolve_right hd
  have hV : V = 0 := (mul_eq_zero.mp hVdet).resolve_right hd
  have hu : C.u = D.u := sub_eq_zero.mp hU
  have hv : C.v = D.v := sub_eq_zero.mp hV
  apply Circle.ext hu hv
  have hw0 : C.w - D.w = 0 := by
    simpa [hu, hv] using ha
  exact sub_eq_zero.mp hw0

lemma circleThrough_eq_of_on {C : Circle} {a b c : Point}
    (hnc : Noncollinear a b c)
    (ha : OnCircle C a) (hb : OnCircle C b) (hc : OnCircle C c) :
    circleThrough a b c = C := by
  exact circle_eq_of_three hnc (circleThrough_on_left a b c)
    (circleThrough_on_middle hnc) (circleThrough_on_right hnc) ha hb hc

/-- Three distinct points on one proper circle equation cannot be collinear.
This is the algebraic form of the fact that a line meets a circle at most
twice. -/
lemma noncollinear_of_onCircle_of_pairwise {C : Circle} {a b c : Point}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : OnCircle C a) (hb : OnCircle C b) (hc : OnCircle C c) :
    Noncollinear a b c := by
  intro hdet
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let ex := c.1 - a.1
  let ey := c.2 - a.2
  let d2 := dx ^ 2 + dy ^ 2
  let e2 := ex ^ 2 + ey ^ 2
  let de := dx * ex + dy * ey
  let lx := 2 * a.1 + C.u
  let ly := 2 * a.2 + C.v
  have hd2pos : 0 < d2 := by
    have hd2nonneg : 0 ≤ d2 := by
      dsimp [d2]
      positivity
    have hd2ne : d2 ≠ 0 := by
      intro hz
      have hdx : dx = 0 := by
        dsimp [d2] at hz
        nlinarith [sq_nonneg dx, sq_nonneg dy]
      have hdy : dy = 0 := by
        dsimp [d2] at hz
        nlinarith [sq_nonneg dx, sq_nonneg dy]
      apply hab
      apply Prod.ext
      · dsimp [dx] at hdx
        linarith
      · dsimp [dy] at hdy
        linarith
    exact lt_of_le_of_ne hd2nonneg (Ne.symm hd2ne)
  have he2pos : 0 < e2 := by
    have he2nonneg : 0 ≤ e2 := by
      dsimp [e2]
      positivity
    have he2ne : e2 ≠ 0 := by
      intro hz
      have hex : ex = 0 := by
        dsimp [e2] at hz
        nlinarith [sq_nonneg ex, sq_nonneg ey]
      have hey : ey = 0 := by
        dsimp [e2] at hz
        nlinarith [sq_nonneg ex, sq_nonneg ey]
      apply hac
      apply Prod.ext
      · dsimp [ex] at hex
        linarith
      · dsimp [ey] at hey
        linarith
    exact lt_of_le_of_ne he2nonneg (Ne.symm he2ne)
  have hbdiff : lx * dx + ly * dy + d2 = 0 := by
    simp only [OnCircle, normSq] at ha hb
    dsimp [lx, ly, dx, dy, d2]
    nlinarith
  have hcdiff : lx * ex + ly * ey + e2 = 0 := by
    simp only [OnCircle, normSq] at ha hc
    dsimp [lx, ly, ex, ey, e2]
    nlinarith
  have hparallel : dx * ey - dy * ex = 0 := by
    simpa only [det, dx, dy, ex, ey] using hdet
  have hlinearIdentity :
      d2 * (lx * ex + ly * ey) - de * (lx * dx + ly * dy) = 0 := by
    have hid :
        d2 * (lx * ex + ly * ey) - de * (lx * dx + ly * dy) =
          (dx * ey - dy * ex) * (-lx * dy + ly * dx) := by
      dsimp [d2, de]
      ring
    rw [hid, hparallel, zero_mul]
  have hde : de = e2 := by
    have hbd : lx * dx + ly * dy = -d2 := by
      linarith only [hbdiff]
    have hcd : lx * ex + ly * ey = -e2 := by
      linarith only [hcdiff]
    rw [hcd, hbd] at hlinearIdentity
    have hfactor : d2 * (de - e2) = 0 := by
      nlinarith only [hlinearIdentity]
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hfactor).resolve_left (ne_of_gt hd2pos))
  have hlagrange : d2 * e2 - de ^ 2 = 0 := by
    have hid : d2 * e2 - de ^ 2 = (dx * ey - dy * ex) ^ 2 := by
      dsimp [d2, e2, de]
      ring
    rw [hid, hparallel, zero_pow (by norm_num)]
  have hd2eq : d2 = e2 := by
    rw [hde] at hlagrange
    nlinarith only [hlagrange, he2pos]
  have hsame : (ex - dx) ^ 2 + (ey - dy) ^ 2 = 0 := by
    calc
      (ex - dx) ^ 2 + (ey - dy) ^ 2 = e2 + d2 - 2 * de := by
        dsimp [d2, e2, de]
        ring
      _ = 0 := by rw [hd2eq, hde]; ring
  have hex : ex = dx := by
    have hx2 : (ex - dx) ^ 2 = 0 := by
      nlinarith only [hsame, sq_nonneg (ex - dx), sq_nonneg (ey - dy)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx2)
  have hey : ey = dy := by
    have hy2 : (ey - dy) ^ 2 = 0 := by
      nlinarith only [hsame, sq_nonneg (ex - dx), sq_nonneg (ey - dy)]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hy2)
  apply hbc
  apply Prod.ext
  · dsimp [ex, dx] at hex
    linarith
  · dsimp [ey, dy] at hey
    linarith

lemma circle_eq_of_three_distinct {C D : Circle} {a b c : Point}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hCa : OnCircle C a) (hCb : OnCircle C b) (hCc : OnCircle C c)
    (hDa : OnCircle D a) (hDb : OnCircle D b) (hDc : OnCircle D c) : C = D := by
  exact circle_eq_of_three
    (noncollinear_of_onCircle_of_pairwise hab hac hbc hCa hCb hCc)
    hCa hCb hCc hDa hDb hDc

lemma noncollinear_swap_right_iff {a b c : Point} :
    Noncollinear a b c ↔ Noncollinear a c b := by
  simp only [Noncollinear, det]
  constructor <;> intro h hzero <;> apply h <;> nlinarith

lemma noncollinear_swap_left_iff {a b c : Point} :
    Noncollinear a b c ↔ Noncollinear b a c := by
  simp only [Noncollinear, det]
  constructor <;> intro h hzero <;> apply h <;> nlinarith

lemma noncollinear_rotate_iff {a b c : Point} :
    Noncollinear a b c ↔ Noncollinear b c a := by
  simp only [Noncollinear, det]
  constructor <;> intro h hzero <;> apply h <;> nlinarith

lemma circleThrough_swap_right {a b c : Point} (h : Noncollinear a b c) :
    circleThrough a b c = circleThrough a c b := by
  have h' : Noncollinear a c b := noncollinear_swap_right_iff.mp h
  exact circle_eq_of_three h
    (circleThrough_on_left a b c) (circleThrough_on_middle h)
    (circleThrough_on_right h)
    (circleThrough_on_left a c b) (circleThrough_on_right h')
    (circleThrough_on_middle h')

/-- A harmless value used to make the unordered-pair construction below
total on degenerate pairs. -/
def zeroCircle : Circle := ⟨0, 0, 0⟩

/-- The circle through `p` and an unordered pair.  On a degenerate triple it
is assigned a fixed dummy value; all applications filter those triples out. -/
noncomputable def circleOfPair (p : Point) : Sym2 Point → Circle := by
  classical
  exact Sym2.lift ⟨fun a b ↦
    if Noncollinear p a b then circleThrough p a b else zeroCircle, by
      intro a b
      by_cases h : Noncollinear p a b
      · have h' := noncollinear_swap_right_iff.mp h
        change
          (if Noncollinear p a b then circleThrough p a b else zeroCircle) =
            (if Noncollinear p b a then circleThrough p b a else zeroCircle)
        rw [if_pos h, if_pos h']
        exact circleThrough_swap_right h
      · have h' : ¬Noncollinear p b a := by
          simpa only [noncollinear_swap_right_iff] using h
        change
          (if Noncollinear p a b then circleThrough p a b else zeroCircle) =
            (if Noncollinear p b a then circleThrough p b a else zeroCircle)
        rw [if_neg h, if_neg h']⟩

lemma circleOfPair_mk {p a b : Point} (h : Noncollinear p a b) :
    circleOfPair p s(a, b) = circleThrough p a b := by
  classical
  change (if Noncollinear p a b then circleThrough p a b else zeroCircle) = _
  rw [if_pos h]

/-- All unordered pairs of distinct points of `A`. -/
noncomputable def unorderedPairs (A : Finset Point) : Finset (Sym2 Point) := by
  classical
  exact A.offDiag.image Sym2.mk.uncurry

lemma card_unorderedPairs (A : Finset Point) :
    (unorderedPairs A).card = Nat.choose A.card 2 := by
  classical
  exact Sym2.card_image_offDiag A

lemma mem_unorderedPairs {A : Finset Point} {a b : Point} :
    s(a, b) ∈ unorderedPairs A ↔ a ∈ A ∧ b ∈ A ∧ a ≠ b := by
  classical
  simp only [unorderedPairs, Finset.mem_image, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨c, d⟩, ⟨hc, hd, hcd⟩, heq⟩
    simp only at hc hd hcd
    change s(c, d) = s(a, b) at heq
    rw [Sym2.eq_iff] at heq
    rcases heq with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hc, hd, hcd⟩
    · exact ⟨hd, hc, Ne.symm hcd⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨(a, b), ⟨ha, hb, hab⟩, rfl⟩

/-- Circles obtained by adjoining `p` to an unordered pair from `A`. -/
noncomputable def circlesFromPairs (p : Point) (A : Finset Point) : Finset Circle := by
  classical
  exact (unorderedPairs A).image (circleOfPair p)

lemma mem_circlesFromPairs {p : Point} {A : Finset Point} {C : Circle} :
    C ∈ circlesFromPairs p A ↔
      (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ Noncollinear p a b ∧
        C = circleThrough p a b) ∨
      (C = zeroCircle ∧ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ Collinear p a b) := by
  classical
  rw [circlesFromPairs, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      rw [mem_unorderedPairs] at hz
      by_cases h : Noncollinear p a b
      · left
        exact ⟨a, hz.1, b, hz.2.1, hz.2.2, h, circleOfPair_mk h⟩
      · right
        refine ⟨?_, a, hz.1, b, hz.2.1, hz.2.2, ?_⟩
        · change (if Noncollinear p a b then circleThrough p a b else zeroCircle) = zeroCircle
          rw [if_neg h]
        · exact not_ne_iff.mp h
  · intro h
    rcases h with ⟨a, ha, b, hb, hab, hnc, rfl⟩ |
      ⟨rfl, a, ha, b, hb, hab, hcol⟩
    · exact ⟨s(a, b), mem_unorderedPairs.mpr ⟨ha, hb, hab⟩,
        circleOfPair_mk hnc⟩
    · refine ⟨s(a, b), mem_unorderedPairs.mpr ⟨ha, hb, hab⟩, ?_⟩
      change (if Noncollinear p a b then circleThrough p a b else zeroCircle) = zeroCircle
      rw [if_neg]
      exact fun hnc ↦ hnc hcol

/-- Ordered non-collinear triples from a finite point set. -/
noncomputable def noncollinearTriples (P : Finset Point) :
    Finset ((Point × Point) × Point) := by
  classical
  exact (((P ×ˢ P) ×ˢ P).filter fun t ↦ Noncollinear t.1.1 t.1.2 t.2)

/-- The finite set of distinct circles determined by `P`.  Taking an image
identifies all orderings and all triples lying on the same circle. -/
noncomputable def determinedCircles (P : Finset Point) : Finset Circle := by
  classical
  exact (noncollinearTriples P).image fun t ↦ circleThrough t.1.1 t.1.2 t.2

lemma mem_noncollinearTriples {P : Finset Point} {a b c : Point} :
    ((a, b), c) ∈ noncollinearTriples P ↔
      a ∈ P ∧ b ∈ P ∧ c ∈ P ∧ Noncollinear a b c := by
  simp [noncollinearTriples, and_assoc]

lemma mem_determinedCircles {P : Finset Point} {C : Circle} :
    C ∈ determinedCircles P ↔
      ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P,
        Noncollinear a b c ∧
        OnCircle C a ∧ OnCircle C b ∧ OnCircle C c := by
  classical
  constructor
  · intro hC
    rcases Finset.mem_image.mp hC with ⟨⟨⟨a, b⟩, c⟩, habc, rfl⟩
    rw [mem_noncollinearTriples] at habc
    exact ⟨a, habc.1, b, habc.2.1, c, habc.2.2.1, habc.2.2.2,
      circleThrough_on_left a b c, circleThrough_on_middle habc.2.2.2,
      circleThrough_on_right habc.2.2.2⟩
  · rintro ⟨a, ha, b, hb, c, hc, hnc, hCa, hCb, hCc⟩
    apply Finset.mem_image.mpr
    refine ⟨((a, b), c), ?_, ?_⟩
    · exact mem_noncollinearTriples.mpr ⟨ha, hb, hc, hnc⟩
    · exact circleThrough_eq_of_on hnc hCa hCb hCc

/-- A finite point set is contained in one affine line. -/
def ContainedInLine (P : Finset Point) : Prop :=
  ∃ a b : Point, a ≠ b ∧ ∀ p ∈ P, Collinear a b p

/-- A finite point set is contained in one circle equation.  For a
non-collinear set this equation necessarily represents a proper circle. -/
def ContainedInCircle (P : Finset Point) : Prop :=
  ∃ C : Circle, ∀ p ∈ P, OnCircle C p

/-- The exact non-degeneracy condition in the corrected resolution. -/
def Admissible (n : ℕ) (P : Finset Point) : Prop :=
  P.card = n ∧ ¬ ContainedInLine P ∧ ¬ ContainedInCircle P

/-- Purdy--Smith's corrected lower bound. -/
def correctedBound (n : ℕ) : ℕ :=
  Nat.choose (n - 1) 2 + 1 - (n - 1) / 2

/-- All circle counts attained by admissible `n`-point configurations. -/
def circleCounts (n : ℕ) : Set ℕ :=
  {m | ∃ P : Finset Point, Admissible n P ∧ (determinedCircles P).card = m}

/-! ## Connecting lines as finite incidence blocks -/

lemma collinear_left (a b : Point) : Collinear a b a := by
  simp [Collinear, det]

lemma collinear_right (a b : Point) : Collinear a b b := by
  simp [Collinear, det]
  ring

lemma collinear_swap_left {a b c : Point} :
    Collinear a b c ↔ Collinear b a c := by
  simp only [Collinear, det]
  constructor <;> intro h <;> nlinarith

lemma collinear_rotate {a b c : Point} :
    Collinear a b c ↔ Collinear b c a := by
  simp only [Collinear, det]
  constructor <;> intro h <;> nlinarith

lemma collinear_swap_right {a b c : Point} :
    Collinear a b c ↔ Collinear a c b := by
  simp only [Collinear, det]
  constructor <;> intro h <;> nlinarith

lemma collinear_iff_slope {a b p : Point} (h : b.1 - a.1 ≠ 0) :
    Collinear a b p ↔
      p.2 - a.2 = (b.2 - a.2) / (b.1 - a.1) * (p.1 - a.1) := by
  simp only [Collinear, det]
  constructor
  · intro hcol
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff h).2
    nlinarith
  · intro hslope
    rw [div_mul_eq_mul_div, eq_div_iff h] at hslope
    nlinarith

lemma collinear_iff_vertical {a b p : Point} (hfst : b.1 = a.1)
    (hne : a ≠ b) : Collinear a b p ↔ p.1 = a.1 := by
  have hsnd : b.2 - a.2 ≠ 0 := by
    intro hz
    apply hne
    apply Prod.ext hfst.symm
    linarith
  simp only [Collinear, det, hfst, sub_self, zero_mul, zero_sub]
  constructor
  · intro h
    have : p.1 - a.1 = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_left hsnd
    linarith
  · intro h
    rw [h, sub_self, mul_zero, neg_zero]

/-- Two distinct points on the line through another distinct pair determine
the same affine line. -/
lemma collinear_line_unique {a b c d p : Point} (hab : a ≠ b) (hcd : c ≠ d)
    (hc : Collinear a b c) (hd : Collinear a b d) :
    Collinear a b p ↔ Collinear c d p := by
  by_cases hdx : b.1 - a.1 = 0
  · have hba : b.1 = a.1 := sub_eq_zero.mp hdx
    have hc1 : c.1 = a.1 := (collinear_iff_vertical hba hab).mp hc
    have hd1 : d.1 = a.1 := (collinear_iff_vertical hba hab).mp hd
    have hdc : d.1 = c.1 := by rw [hd1, hc1]
    rw [collinear_iff_vertical hba hab,
      collinear_iff_vertical hdc hcd]
    exact ⟨fun h ↦ h.trans hc1.symm, fun h ↦ h.trans hc1⟩
  · have hcp :
        c.2 - a.2 = (b.2 - a.2) / (b.1 - a.1) * (c.1 - a.1) :=
      (collinear_iff_slope hdx).mp hc
    have hdp :
        d.2 - a.2 = (b.2 - a.2) / (b.1 - a.1) * (d.1 - a.1) :=
      (collinear_iff_slope hdx).mp hd
    have hdcx : d.1 - c.1 ≠ 0 := by
      intro hz
      apply hcd
      apply Prod.ext
      · linarith
      · have hdc1 : d.1 = c.1 := by linarith
        rw [hdc1] at hdp
        linarith
    rw [collinear_iff_slope hdx, collinear_iff_slope hdcx]
    have hslope :
        (d.2 - c.2) / (d.1 - c.1) =
          (b.2 - a.2) / (b.1 - a.1) := by
      apply (div_eq_iff hdcx).2
      nlinarith
    rw [hslope]
    constructor <;> intro hp <;> linarith

/-- Two distinct points chosen on one line form a non-collinear triple with
any point off that line. -/
lemma noncollinear_off_common_line {a b p x y : Point}
    (hab : a ≠ b) (hxy : x ≠ y)
    (hx : Collinear a b x) (hy : Collinear a b y)
    (hp : Noncollinear a b p) : Noncollinear p x y := by
  intro hpxy
  have hxyp : Collinear x y p := collinear_rotate.mp hpxy
  have habp : Collinear a b p :=
    (collinear_line_unique hab hxy hx hy).mpr hxyp
  exact hp habp

/-- On a common line, different unordered pairs give different circles after
adjoining a fixed point off the line. -/
lemma circleOfPair_injOn_common_line {A : Finset Point} {a b p : Point}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hp : Noncollinear a b p) :
    Set.InjOn (circleOfPair p) (unorderedPairs A) := by
  classical
  intro z hz z' hz' hcircle
  induction z using Sym2.inductionOn with
  | _ x y =>
    induction z' using Sym2.inductionOn with
    | _ u v =>
      change s(x, y) ∈ unorderedPairs A at hz
      change s(u, v) ∈ unorderedPairs A at hz'
      rw [mem_unorderedPairs] at hz hz'
      have hpxy : Noncollinear p x y :=
        noncollinear_off_common_line hab hz.2.2 (hA x hz.1) (hA y hz.2.1) hp
      have hpuv : Noncollinear p u v :=
        noncollinear_off_common_line hab hz'.2.2 (hA u hz'.1) (hA v hz'.2.1) hp
      rw [circleOfPair_mk hpxy, circleOfPair_mk hpuv] at hcircle
      have hCx : OnCircle (circleThrough p x y) x := circleThrough_on_middle hpxy
      have hCy : OnCircle (circleThrough p x y) y := circleThrough_on_right hpxy
      have hCu : OnCircle (circleThrough p x y) u := by
        rw [hcircle]
        exact circleThrough_on_middle hpuv
      have hCv : OnCircle (circleThrough p x y) v := by
        rw [hcircle]
        exact circleThrough_on_right hpuv
      have hu : u = x ∨ u = y := by
        by_cases hux : u = x
        · exact Or.inl hux
        by_cases huy : u = y
        · exact Or.inr huy
        exfalso
        have hnc : Noncollinear x y u :=
          noncollinear_of_onCircle_of_pairwise hz.2.2 (Ne.symm hux) (Ne.symm huy)
            hCx hCy hCu
        exact hnc ((collinear_line_unique hab hz.2.2
          (hA x hz.1) (hA y hz.2.1)).mp (hA u hz'.1))
      have hv : v = x ∨ v = y := by
        by_cases hvx : v = x
        · exact Or.inl hvx
        by_cases hvy : v = y
        · exact Or.inr hvy
        exfalso
        have hnc : Noncollinear x y v :=
          noncollinear_of_onCircle_of_pairwise hz.2.2 (Ne.symm hvx) (Ne.symm hvy)
            hCx hCy hCv
        exact hnc ((collinear_line_unique hab hz.2.2
          (hA x hz.1) (hA y hz.2.1)).mp (hA v hz'.2.1))
      rw [Sym2.eq_iff]
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (hz'.2.2 rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (hz'.2.2 rfl).elim

lemma card_circlesFromPairs_common_line {A : Finset Point} {a b p : Point}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hp : Noncollinear a b p) :
    (circlesFromPairs p A).card = Nat.choose A.card 2 := by
  classical
  rw [circlesFromPairs, Finset.card_image_iff.mpr
    (circleOfPair_injOn_common_line hab hA hp), card_unorderedPairs]

/-- Every circle obtained from a pair on `A` and an off-line point `p`
is genuinely determined by any ambient set containing those points. -/
lemma circlesFromPairs_subset_determined {P A : Finset Point} {a b p : Point}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hp : Noncollinear a b p) (hAP : A ⊆ P) (hpP : p ∈ P) :
    circlesFromPairs p A ⊆ determinedCircles P := by
  intro C hC
  rw [mem_circlesFromPairs] at hC
  rcases hC with ⟨x, hx, y, hy, hxy, hn, rfl⟩ |
    ⟨rfl, x, hx, y, hy, hxy, hcol⟩
  · exact mem_determinedCircles.mpr
      ⟨p, hpP, x, hAP hx, y, hAP hy, hn,
        circleThrough_on_left p x y, circleThrough_on_middle hn,
        circleThrough_on_right hn⟩
  · exact (noncollinear_off_common_line hab hxy (hA x hx) (hA y hy) hp hcol).elim

/-- Points of `A` lying on a circle. -/
noncomputable def circleTrace (A : Finset Point) (C : Circle) : Finset Point := by
  classical
  exact A.filter (OnCircle C)

lemma mem_circleTrace {A : Finset Point} {C : Circle} {x : Point} :
    x ∈ circleTrace A C ↔ x ∈ A ∧ OnCircle C x := by
  classical
  simp [circleTrace]

lemma circleTrace_subset (A : Finset Point) (C : Circle) : circleTrace A C ⊆ A := by
  intro x hx
  exact (mem_circleTrace.mp hx).1

lemma onCircle_fixed_of_mem_circlesFromPairs_common_line
    {A : Finset Point} {a b p : Point} {C : Circle}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hp : Noncollinear a b p) (hC : C ∈ circlesFromPairs p A) :
    OnCircle C p := by
  rw [mem_circlesFromPairs] at hC
  rcases hC with ⟨x, hx, y, hy, hxy, hn, rfl⟩ |
    ⟨rfl, x, hx, y, hy, hxy, hcol⟩
  · exact circleThrough_on_left p x y
  · exact (noncollinear_off_common_line hab hxy (hA x hx) (hA y hy) hp hcol).elim

lemma two_le_circleTrace_of_mem_circlesFromPairs_common_line
    {A : Finset Point} {a b p : Point} {C : Circle}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hp : Noncollinear a b p) (hC : C ∈ circlesFromPairs p A) :
    2 ≤ (circleTrace A C).card := by
  rw [mem_circlesFromPairs] at hC
  rcases hC with ⟨x, hx, y, hy, hxy, hn, rfl⟩ |
    ⟨rfl, x, hx, y, hy, hxy, hcol⟩
  · have hsub : ({x, y} : Finset Point) ⊆ circleTrace A (circleThrough p x y) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_circleTrace.mpr ⟨hx, circleThrough_on_middle hn⟩
      · exact mem_circleTrace.mpr ⟨hy, circleThrough_on_right hn⟩
    have := Finset.card_le_card hsub
    simpa [hxy] using this
  · exact (noncollinear_off_common_line hab hxy (hA x hx) (hA y hy) hp hcol).elim

/-- Common circles in two pair-families. -/
noncomputable def commonCircles (p q : Point) (A : Finset Point) : Finset Circle := by
  classical
  exact circlesFromPairs p A ∩ circlesFromPairs q A

lemma mem_commonCircles {p q : Point} {A : Finset Point} {C : Circle} :
    C ∈ commonCircles p q A ↔
      C ∈ circlesFromPairs p A ∧ C ∈ circlesFromPairs q A := by
  classical
  simp [commonCircles]

/-- Two different common circles through two fixed off-line points use
disjoint pairs of points on the line. -/
lemma circleTrace_pairwiseDisjoint_common_line
    {A : Finset Point} {a b p q : Point}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hp : Noncollinear a b p) (hq : Noncollinear a b q) (hpq : p ≠ q) :
    (((commonCircles p q A : Finset Circle) : Set Circle)).PairwiseDisjoint
      (circleTrace A) := by
  classical
  intro C hC D hD hCD
  rw [Finset.mem_coe, mem_commonCircles] at hC hD
  change Disjoint (circleTrace A C) (circleTrace A D)
  rw [Finset.disjoint_left]
  intro x hxC hxD
  have hxA : x ∈ A := (mem_circleTrace.mp hxC).1
  have hpx : p ≠ x := by
    intro h
    subst x
    exact hp (hA p hxA)
  have hqx : q ≠ x := by
    intro h
    subst x
    exact hq (hA q hxA)
  apply hCD
  exact circle_eq_of_three_distinct hpq hpx hqx
    (onCircle_fixed_of_mem_circlesFromPairs_common_line hab hA hp hC.1)
    (onCircle_fixed_of_mem_circlesFromPairs_common_line hab hA hq hC.2)
    (mem_circleTrace.mp hxC).2
    (onCircle_fixed_of_mem_circlesFromPairs_common_line hab hA hp hD.1)
    (onCircle_fixed_of_mem_circlesFromPairs_common_line hab hA hq hD.2)
    (mem_circleTrace.mp hxD).2

lemma card_inter_circlesFromPairs_common_line
    {A : Finset Point} {a b p q : Point}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hp : Noncollinear a b p) (hq : Noncollinear a b q) (hpq : p ≠ q) :
    2 * (commonCircles p q A).card ≤ A.card := by
  classical
  let I := commonCircles p q A
  have hdisj : ((I : Finset Circle) : Set Circle).PairwiseDisjoint (circleTrace A) := by
    dsimp [I]
    exact circleTrace_pairwiseDisjoint_common_line hab hA hp hq hpq
  have hsum : ∑ C ∈ I, (circleTrace A C).card =
      (I.biUnion (circleTrace A)).card := by
    exact (Finset.card_biUnion hdisj).symm
  have hunion : I.biUnion (circleTrace A) ⊆ A := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨C, hCI, hxC⟩
    exact circleTrace_subset A C hxC
  have hsmall : 2 * I.card ≤ ∑ C ∈ I, (circleTrace A C).card := by
    calc
      2 * I.card = ∑ C ∈ I, 2 := by simp [mul_comm]
      _ ≤ ∑ C ∈ I, (circleTrace A C).card := by
        apply Finset.sum_le_sum
        intro C hCI
        exact two_le_circleTrace_of_mem_circlesFromPairs_common_line
          hab hA hp (mem_commonCircles.mp hCI).1
  rw [hsum] at hsmall
  exact hsmall.trans (Finset.card_le_card hunion)

/-- Union of all pair-circle families indexed by a finite set of off-line
points. -/
noncomputable def circleUnionFromPairs (Q A : Finset Point) : Finset Circle := by
  classical
  exact Q.biUnion fun p ↦ circlesFromPairs p A

lemma circleUnionFromPairs_subset_determined
    {P Q A : Finset Point} {a b : Point}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hQ : ∀ p ∈ Q, Noncollinear a b p)
    (hAP : A ⊆ P) (hQP : Q ⊆ P) :
    circleUnionFromPairs Q A ⊆ determinedCircles P := by
  classical
  intro C hC
  rw [circleUnionFromPairs, Finset.mem_biUnion] at hC
  rcases hC with ⟨p, hpQ, hCp⟩
  exact circlesFromPairs_subset_determined hab hA (hQ p hpQ) hAP (hQP hpQ) hCp

/-! ## Pair-circle families over a fixed proper circle -/

lemma eq_origin_of_on_zeroCircle {x : Point} (hx : OnCircle zeroCircle x) :
    x = (0, 0) := by
  have hs : x.1 ^ 2 + x.2 ^ 2 = 0 := by
    simpa [OnCircle, zeroCircle, normSq] using hx
  have hx1 : x.1 = 0 := by
    have : x.1 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    exact sq_eq_zero_iff.mp this
  have hx2 : x.2 = 0 := by
    have : x.2 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    exact sq_eq_zero_iff.mp this
  exact Prod.ext hx1 hx2

lemma circleThrough_ne_zeroCircle {p a b : Point} (h : Noncollinear p a b) :
    circleThrough p a b ≠ zeroCircle := by
  intro heq
  have hp : p = (0, 0) := eq_origin_of_on_zeroCircle (heq ▸ circleThrough_on_left p a b)
  have ha : a = (0, 0) :=
    eq_origin_of_on_zeroCircle (heq ▸ circleThrough_on_middle h)
  exact (noncollinear_ne_left h) (hp.trans ha.symm)

/-- Non-collinear unordered pairs from `A`, recognized by the total circle
map not taking its dummy value. -/
noncomputable def goodPairs (p : Point) (A : Finset Point) : Finset (Sym2 Point) := by
  classical
  exact (unorderedPairs A).filter fun z ↦ circleOfPair p z ≠ zeroCircle

/-- Collinear unordered pairs from `A`. -/
noncomputable def badPairs (p : Point) (A : Finset Point) : Finset (Sym2 Point) := by
  classical
  exact (unorderedPairs A).filter fun z ↦ circleOfPair p z = zeroCircle

lemma mem_goodPairs_mk {p : Point} {A : Finset Point} {a b : Point} :
    s(a, b) ∈ goodPairs p A ↔
      a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ Noncollinear p a b := by
  classical
  rw [goodPairs, Finset.mem_filter, mem_unorderedPairs]
  constructor
  · rintro ⟨⟨ha, hb, hab⟩, hne⟩
    refine ⟨ha, hb, hab, ?_⟩
    by_contra hnc
    apply hne
    change (if Noncollinear p a b then circleThrough p a b else zeroCircle) = zeroCircle
    rw [if_neg hnc]
  · rintro ⟨ha, hb, hab, hnc⟩
    refine ⟨⟨ha, hb, hab⟩, ?_⟩
    rw [circleOfPair_mk hnc]
    exact circleThrough_ne_zeroCircle hnc

lemma mem_badPairs_mk {p : Point} {A : Finset Point} {a b : Point} :
    s(a, b) ∈ badPairs p A ↔
      a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ Collinear p a b := by
  classical
  rw [badPairs, Finset.mem_filter, mem_unorderedPairs]
  constructor
  · rintro ⟨⟨ha, hb, hab⟩, heq⟩
    refine ⟨ha, hb, hab, ?_⟩
    by_contra hcol
    have hnc : Noncollinear p a b := hcol
    rw [circleOfPair_mk hnc] at heq
    exact circleThrough_ne_zeroCircle hnc heq
  · rintro ⟨ha, hb, hab, hcol⟩
    refine ⟨⟨ha, hb, hab⟩, ?_⟩
    change (if Noncollinear p a b then circleThrough p a b else zeroCircle) = zeroCircle
    rw [if_neg]
    exact fun hnc ↦ hnc hcol

lemma goodPairs_union_badPairs (p : Point) (A : Finset Point) :
    goodPairs p A ∪ badPairs p A = unorderedPairs A := by
  classical
  ext z
  simp only [goodPairs, badPairs, Finset.mem_union, Finset.mem_filter]
  tauto

lemma goodPairs_disjoint_badPairs (p : Point) (A : Finset Point) :
    Disjoint (goodPairs p A) (badPairs p A) := by
  classical
  rw [Finset.disjoint_left]
  intro z hg hb
  exact (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hb).2

/-- Genuine circles from non-collinear pairs on a fixed base circle. -/
noncomputable def goodCircles (p : Point) (A : Finset Point) : Finset Circle := by
  classical
  exact (goodPairs p A).image (circleOfPair p)

lemma mem_goodCircles {p : Point} {A : Finset Point} {C : Circle} :
    C ∈ goodCircles p A ↔
      ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ Noncollinear p a b ∧
        C = circleThrough p a b := by
  classical
  rw [goodCircles, Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      rw [mem_goodPairs_mk] at hz
      exact ⟨a, hz.1, b, hz.2.1, hz.2.2.1, hz.2.2.2,
        circleOfPair_mk hz.2.2.2⟩
  · rintro ⟨a, ha, b, hb, hab, hnc, rfl⟩
    exact ⟨s(a, b), mem_goodPairs_mk.mpr ⟨ha, hb, hab, hnc⟩,
      circleOfPair_mk hnc⟩

lemma circleOfPair_injOn_goodPairs_on_circle
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p) :
    Set.InjOn (circleOfPair p) (goodPairs p A) := by
  classical
  intro z hz z' hz' hcircle
  induction z using Sym2.inductionOn with
  | _ x y =>
    induction z' using Sym2.inductionOn with
    | _ u v =>
      change s(x, y) ∈ goodPairs p A at hz
      change s(u, v) ∈ goodPairs p A at hz'
      rw [mem_goodPairs_mk] at hz hz'
      rw [circleOfPair_mk hz.2.2.2, circleOfPair_mk hz'.2.2.2] at hcircle
      have hCx : OnCircle (circleThrough p x y) x :=
        circleThrough_on_middle hz.2.2.2
      have hCy : OnCircle (circleThrough p x y) y :=
        circleThrough_on_right hz.2.2.2
      have hCu : OnCircle (circleThrough p x y) u := by
        rw [hcircle]
        exact circleThrough_on_middle hz'.2.2.2
      have hCv : OnCircle (circleThrough p x y) v := by
        rw [hcircle]
        exact circleThrough_on_right hz'.2.2.2
      have hu : u = x ∨ u = y := by
        by_cases hux : u = x
        · exact Or.inl hux
        by_cases huy : u = y
        · exact Or.inr huy
        exfalso
        have heq : circleThrough p x y = G :=
          circle_eq_of_three_distinct hz.2.2.1 (Ne.symm hux) (Ne.symm huy)
            hCx hCy hCu (hA x hz.1) (hA y hz.2.1) (hA u hz'.1)
        exact hp (heq ▸ circleThrough_on_left p x y)
      have hv : v = x ∨ v = y := by
        by_cases hvx : v = x
        · exact Or.inl hvx
        by_cases hvy : v = y
        · exact Or.inr hvy
        exfalso
        have heq : circleThrough p x y = G :=
          circle_eq_of_three_distinct hz.2.2.1 (Ne.symm hvx) (Ne.symm hvy)
            hCx hCy hCv (hA x hz.1) (hA y hz.2.1) (hA v hz'.2.1)
        exact hp (heq ▸ circleThrough_on_left p x y)
      rw [Sym2.eq_iff]
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact (hz'.2.2.1 rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (hz'.2.2.1 rfl).elim

lemma card_goodCircles_on_circle
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p) :
    (goodCircles p A).card = (goodPairs p A).card := by
  classical
  exact Finset.card_image_iff.mpr (circleOfPair_injOn_goodPairs_on_circle hA hp)

/-- On one proper circle, two points collinear with an off-circle point and
the same circle point must coincide. -/
lemma eq_of_common_radial_point_on_circle
    {G : Circle} {p x y z : Point}
    (hGx : OnCircle G x) (hGy : OnCircle G y) (hGz : OnCircle G z)
    (hp : ¬ OnCircle G p) (hxy : x ≠ y) (hxz : x ≠ z)
    (hpxy : Collinear p x y) (hpxz : Collinear p x z) : y = z := by
  by_contra hyz
  have hpx : p ≠ x := by
    intro h
    subst x
    exact hp hGx
  have hxyz : Collinear x y z :=
    (collinear_line_unique hpx hxy (collinear_right p x) hpxy).mp hpxz
  exact (noncollinear_of_onCircle_of_pairwise hxy hxz hyz hGx hGy hGz) hxyz

lemma badPairs_pairwiseDisjoint_on_circle
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p) :
    (((badPairs p A : Finset (Sym2 Point)) : Set (Sym2 Point))).PairwiseDisjoint
      Sym2.toFinset := by
  classical
  intro z hz z' hz' hzz'
  change Disjoint z.toFinset z'.toFinset
  rw [Finset.disjoint_left]
  intro w hw hw'
  induction z using Sym2.inductionOn with
  | _ x y =>
    induction z' using Sym2.inductionOn with
    | _ u v =>
      change s(x, y) ∈ badPairs p A at hz
      change s(u, v) ∈ badPairs p A at hz'
      rw [mem_badPairs_mk] at hz hz'
      simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
        Finset.mem_singleton] at hw hw'
      rcases hw with hwx | hwy <;> rcases hw' with hwu | hwv
      · have hxu : x = u := hwx.symm.trans hwu
        have hxv : x ≠ v := fun h ↦ hz'.2.2.1 (hxu.symm.trans h)
        have hpxv : Collinear p x v := by
          simpa only [hxu] using hz'.2.2.2
        have hyv : y = v := eq_of_common_radial_point_on_circle
          (hA x hz.1) (hA y hz.2.1) (hA v hz'.2.1) hp
          hz.2.2.1 hxv hz.2.2.2 hpxv
        apply hzz'
        rw [Sym2.eq_iff]
        exact Or.inl ⟨hxu, hyv⟩
      · have hxv' : x = v := hwx.symm.trans hwv
        have hxu : x ≠ u := fun h ↦ hz'.2.2.1 (h.symm.trans hxv')
        have hpxu : Collinear p x u := by
          have := collinear_swap_right.mpr hz'.2.2.2
          simpa only [hxv'] using this
        have hyu : y = u := eq_of_common_radial_point_on_circle
          (hA x hz.1) (hA y hz.2.1) (hA u hz'.1) hp
          hz.2.2.1 hxu hz.2.2.2 hpxu
        apply hzz'
        rw [Sym2.eq_iff]
        exact Or.inr ⟨hxv', hyu⟩
      · have hyu' : y = u := hwy.symm.trans hwu
        have hyv : y ≠ v := fun h ↦ hz'.2.2.1 (hyu'.symm.trans h)
        have hpyx : Collinear p y x := collinear_swap_right.mpr hz.2.2.2
        have hpyv : Collinear p y v := by
          simpa only [hyu'] using hz'.2.2.2
        have hxv : x = v := eq_of_common_radial_point_on_circle
          (hA y hz.2.1) (hA x hz.1) (hA v hz'.2.1) hp
          (Ne.symm hz.2.2.1) hyv hpyx hpyv
        apply hzz'
        rw [Sym2.eq_iff]
        exact Or.inr ⟨hxv, hyu'⟩
      · have hyv' : y = v := hwy.symm.trans hwv
        have hyu : y ≠ u := fun h ↦ hz'.2.2.1 (h.symm.trans hyv')
        have hpyx : Collinear p y x := collinear_swap_right.mpr hz.2.2.2
        have hpyu : Collinear p y u := by
          have := collinear_swap_right.mpr hz'.2.2.2
          simpa only [hyv'] using this
        have hxu : x = u := eq_of_common_radial_point_on_circle
          (hA y hz.2.1) (hA x hz.1) (hA u hz'.1) hp
          (Ne.symm hz.2.2.1) hyu hpyx hpyu
        apply hzz'
        rw [Sym2.eq_iff]
        exact Or.inl ⟨hxu, hyv'⟩

lemma two_mul_card_badPairs_le
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p) :
    2 * (badPairs p A).card ≤ A.card := by
  classical
  have hdisj := badPairs_pairwiseDisjoint_on_circle hA hp
  have hsum : ∑ z ∈ badPairs p A, z.toFinset.card =
      ((badPairs p A).biUnion Sym2.toFinset).card :=
    (Finset.card_biUnion hdisj).symm
  have hsub : (badPairs p A).biUnion Sym2.toFinset ⊆ A := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨z, hz, hxz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
      change s(a, b) ∈ badPairs p A at hz
      rw [mem_badPairs_mk] at hz
      rw [Sym2.toFinset_mk_eq] at hxz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxz
      rcases hxz with rfl | rfl
      · exact hz.1
      · exact hz.2.1
  have htwo : ∑ _z ∈ badPairs p A, 2 =
      ∑ z ∈ badPairs p A, z.toFinset.card := by
    apply Finset.sum_congr rfl
    intro z hz
    induction z using Sym2.inductionOn with
    | _ a b =>
      change s(a, b) ∈ badPairs p A at hz
      rw [mem_badPairs_mk] at hz
      simp [Sym2.toFinset_mk_eq, hz.2.2.1]
  rw [← htwo] at hsum
  have hcard := Finset.card_le_card hsub
  rw [← hsum] at hcard
  simpa [mul_comm] using hcard

lemma card_goodPairs_eq_sub_badPairs (p : Point) (A : Finset Point) :
    (goodPairs p A).card = Nat.choose A.card 2 - (badPairs p A).card := by
  classical
  have hcard := Finset.card_union_of_disjoint (goodPairs_disjoint_badPairs p A)
  rw [goodPairs_union_badPairs, card_unorderedPairs] at hcard
  omega

lemma choose_sub_half_le_card_goodCircles
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p) :
    Nat.choose A.card 2 - A.card / 2 ≤ (goodCircles p A).card := by
  rw [card_goodCircles_on_circle hA hp, card_goodPairs_eq_sub_badPairs]
  have hbad := two_mul_card_badPairs_le hA hp
  have : (badPairs p A).card ≤ A.card / 2 := by omega
  omega

lemma onCircle_fixed_of_mem_goodCircles
    {p : Point} {A : Finset Point} {C : Circle}
    (hC : C ∈ goodCircles p A) : OnCircle C p := by
  rw [mem_goodCircles] at hC
  rcases hC with ⟨a, ha, b, hb, hab, hnc, rfl⟩
  exact circleThrough_on_left p a b

lemma two_le_circleTrace_of_mem_goodCircles
    {p : Point} {A : Finset Point} {C : Circle}
    (hC : C ∈ goodCircles p A) : 2 ≤ (circleTrace A C).card := by
  rw [mem_goodCircles] at hC
  rcases hC with ⟨a, ha, b, hb, hab, hnc, rfl⟩
  have hsub : ({a, b} : Finset Point) ⊆ circleTrace A (circleThrough p a b) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_circleTrace.mpr ⟨ha, circleThrough_on_middle hnc⟩
    · exact mem_circleTrace.mpr ⟨hb, circleThrough_on_right hnc⟩
  have := Finset.card_le_card hsub
  simpa [hab] using this

noncomputable def commonGoodCircles (p q : Point) (A : Finset Point) : Finset Circle := by
  classical
  exact goodCircles p A ∩ goodCircles q A

lemma mem_commonGoodCircles {p q : Point} {A : Finset Point} {C : Circle} :
    C ∈ commonGoodCircles p q A ↔ C ∈ goodCircles p A ∧ C ∈ goodCircles q A := by
  classical
  simp [commonGoodCircles]

lemma circleTrace_pairwiseDisjoint_commonGoodCircles
    {A : Finset Point} {G : Circle} {p q : Point}
    (hA : ∀ x ∈ A, OnCircle G x)
    (hp : ¬ OnCircle G p) (hq : ¬ OnCircle G q) (hpq : p ≠ q) :
    (((commonGoodCircles p q A : Finset Circle) : Set Circle)).PairwiseDisjoint
      (circleTrace A) := by
  classical
  intro C hC D hD hCD
  rw [Finset.mem_coe, mem_commonGoodCircles] at hC hD
  change Disjoint (circleTrace A C) (circleTrace A D)
  rw [Finset.disjoint_left]
  intro x hxC hxD
  have hxA := (mem_circleTrace.mp hxC).1
  have hpx : p ≠ x := by
    intro h
    subst x
    exact hp (hA p hxA)
  have hqx : q ≠ x := by
    intro h
    subst x
    exact hq (hA q hxA)
  apply hCD
  exact circle_eq_of_three_distinct hpq hpx hqx
    (onCircle_fixed_of_mem_goodCircles hC.1)
    (onCircle_fixed_of_mem_goodCircles hC.2)
    (mem_circleTrace.mp hxC).2
    (onCircle_fixed_of_mem_goodCircles hD.1)
    (onCircle_fixed_of_mem_goodCircles hD.2)
    (mem_circleTrace.mp hxD).2

lemma card_inter_goodCircles_le_half
    {A : Finset Point} {G : Circle} {p q : Point}
    (hA : ∀ x ∈ A, OnCircle G x)
    (hp : ¬ OnCircle G p) (hq : ¬ OnCircle G q) (hpq : p ≠ q) :
    (commonGoodCircles p q A).card ≤ A.card / 2 := by
  classical
  let I := commonGoodCircles p q A
  have hdisj : ((I : Finset Circle) : Set Circle).PairwiseDisjoint (circleTrace A) := by
    dsimp [I]
    exact circleTrace_pairwiseDisjoint_commonGoodCircles hA hp hq hpq
  have hsum : ∑ C ∈ I, (circleTrace A C).card =
      (I.biUnion (circleTrace A)).card := (Finset.card_biUnion hdisj).symm
  have hsub : I.biUnion (circleTrace A) ⊆ A := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨C, hCI, hxC⟩
    exact circleTrace_subset A C hxC
  have hsmall : 2 * I.card ≤ ∑ C ∈ I, (circleTrace A C).card := by
    calc
      2 * I.card = ∑ _C ∈ I, 2 := by simp [mul_comm]
      _ ≤ ∑ C ∈ I, (circleTrace A C).card := by
        apply Finset.sum_le_sum
        intro C hCI
        exact two_le_circleTrace_of_mem_goodCircles (mem_commonGoodCircles.mp hCI).1
  rw [hsum] at hsmall
  have := hsmall.trans (Finset.card_le_card hsub)
  change I.card ≤ A.card / 2
  omega

noncomputable def circleUnionGoodPairs (Q A : Finset Point) : Finset Circle := by
  classical
  exact Q.biUnion fun p ↦ goodCircles p A

lemma circleUnionGoodPairs_subset_determined
    {P Q A : Finset Point} (hAP : A ⊆ P) (hQP : Q ⊆ P) :
    circleUnionGoodPairs Q A ⊆ determinedCircles P := by
  classical
  intro C hC
  rw [circleUnionGoodPairs, Finset.mem_biUnion] at hC
  rcases hC with ⟨p, hpQ, hCp⟩
  rw [mem_goodCircles] at hCp
  rcases hCp with ⟨a, ha, b, hb, hab, hnc, rfl⟩
  exact mem_determinedCircles.mpr
    ⟨p, hQP hpQ, a, hAP ha, b, hAP hb, hnc,
      circleThrough_on_left p a b, circleThrough_on_middle hnc,
      circleThrough_on_right hnc⟩

lemma baseCircle_not_mem_circleUnionGoodPairs
    {Q A : Finset Point} {G : Circle}
    (hQ : ∀ p ∈ Q, ¬ OnCircle G p) : G ∉ circleUnionGoodPairs Q A := by
  classical
  intro hG
  rw [circleUnionGoodPairs, Finset.mem_biUnion] at hG
  rcases hG with ⟨p, hpQ, hGp⟩
  exact hQ p hpQ (onCircle_fixed_of_mem_goodCircles hGp)

lemma baseCircle_mem_determined
    {P A : Finset Point} {G : Circle}
    (hAP : A ⊆ P) (hA : ∀ x ∈ A, OnCircle G x) (hcard : 3 ≤ A.card) :
    G ∈ determinedCircles P := by
  have hthree : 2 < A.card := by omega
  rcases Finset.two_lt_card.mp hthree with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have hnc : Noncollinear a b c :=
    noncollinear_of_onCircle_of_pairwise hab hac hbc (hA a ha) (hA b hb) (hA c hc)
  exact mem_determinedCircles.mpr
    ⟨a, hAP ha, b, hAP hb, c, hAP hc, hnc, hA a ha, hA b hb, hA c hc⟩

noncomputable def sharpCircleSet (G : Circle) (p : Point) (A : Finset Point) :
    Finset Circle := by
  classical
  exact insert G (goodCircles p A)

lemma mem_sharpCircleSet {G : Circle} {p : Point} {A : Finset Point} {C : Circle} :
    C ∈ sharpCircleSet G p A ↔ C = G ∨ C ∈ goodCircles p A := by
  classical
  simp [sharpCircleSet]

/-- A base circle together with one point off it determines exactly the base
circle and the circles through that point and a good unordered base pair. -/
lemma determinedCircles_insert_off_circle
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p)
    (hcard : 3 ≤ A.card) :
    determinedCircles (insert p A) = sharpCircleSet G p A := by
  classical
  ext C
  rw [mem_sharpCircleSet]
  constructor
  · intro hC
    rw [mem_determinedCircles] at hC
    rcases hC with ⟨x, hx, y, hy, z, hz, hnc, hCx, hCy, hCz⟩
    simp only [Finset.mem_insert] at hx hy hz
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · exact (noncollinear_ne_left hnc rfl).elim
      · rcases hz with rfl | hz
        · exact (noncollinear_ne_right hnc rfl).elim
        · right
          exact mem_goodCircles.mpr
            ⟨y, hy, z, hz, noncollinear_ne_last hnc, hnc,
              (circleThrough_eq_of_on hnc hCx hCy hCz).symm⟩
    · rcases hy with rfl | hy
      · rcases hz with rfl | hz
        · exact (noncollinear_ne_last hnc rfl).elim
        · right
          have hnc' := noncollinear_swap_left_iff.mp hnc
          exact mem_goodCircles.mpr
            ⟨x, hx, z, hz, noncollinear_ne_last hnc', hnc',
              (circleThrough_eq_of_on hnc' hCy hCx hCz).symm⟩
      · rcases hz with rfl | hz
        · right
          have hnc' :=
            noncollinear_rotate_iff.mp (noncollinear_rotate_iff.mp hnc)
          exact mem_goodCircles.mpr
            ⟨x, hx, y, hy, noncollinear_ne_last hnc', hnc',
              (circleThrough_eq_of_on hnc' hCz hCx hCy).symm⟩
        · left
          exact circle_eq_of_three hnc hCx hCy hCz
            (hA x hx) (hA y hy) (hA z hz)
  · rintro (rfl | hC)
    · exact baseCircle_mem_determined (P := insert p A)
        (fun x hx ↦ Finset.mem_insert_of_mem hx) hA hcard
    · rw [mem_goodCircles] at hC
      rcases hC with ⟨a, ha, b, hb, hab, hnc, rfl⟩
      exact mem_determinedCircles.mpr
        ⟨p, Finset.mem_insert_self p A,
          a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb,
          hnc, circleThrough_on_left p a b, circleThrough_on_middle hnc,
          circleThrough_on_right hnc⟩

lemma card_determinedCircles_insert_off_circle
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p)
    (hcard : 3 ≤ A.card) :
    (determinedCircles (insert p A)).card =
      1 + Nat.choose A.card 2 - (badPairs p A).card := by
  classical
  rw [determinedCircles_insert_off_circle hA hp hcard]
  have hnot : G ∉ goodCircles p A := by
    intro hG
    exact hp (onCircle_fixed_of_mem_goodCircles hG)
  rw [sharpCircleSet, Finset.card_insert_of_notMem hnot,
    card_goodCircles_on_circle hA hp,
    card_goodPairs_eq_sub_badPairs]
  have hbadle : (badPairs p A).card ≤ Nat.choose A.card 2 := by
    rw [← card_unorderedPairs A]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- The points of `P` on the line through `a` and `b`. -/
noncomputable def lineBlock (P : Finset Point) (a b : Point) : Finset Point := by
  classical
  exact P.filter fun p ↦ Collinear a b p

/-- Ordered distinct pairs from `P`; using an image below removes both order
and repeated presentations of a connecting line. -/
noncomputable def distinctPairs (P : Finset Point) : Finset (Point × Point) := by
  classical
  exact (P ×ˢ P).filter fun ab ↦ ab.1 ≠ ab.2

/-- The finite set of connecting lines of `P`, represented by their incident
point blocks. -/
noncomputable def connectingLines (P : Finset Point) : Finset (Finset Point) := by
  classical
  exact (distinctPairs P).image fun ab ↦ lineBlock P ab.1 ab.2

lemma mem_lineBlock {P : Finset Point} {a b p : Point} :
    p ∈ lineBlock P a b ↔ p ∈ P ∧ Collinear a b p := by
  classical
  simp [lineBlock]

lemma mem_distinctPairs {P : Finset Point} {a b : Point} :
    (a, b) ∈ distinctPairs P ↔ a ∈ P ∧ b ∈ P ∧ a ≠ b := by
  classical
  simp [distinctPairs, and_assoc]

lemma mem_connectingLines {P : Finset Point} {L : Finset Point} :
    L ∈ connectingLines P ↔
      ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ L = lineBlock P a b := by
  classical
  constructor
  · intro hL
    rcases Finset.mem_image.mp hL with ⟨⟨a, b⟩, hab, rfl⟩
    rw [mem_distinctPairs] at hab
    exact ⟨a, hab.1, b, hab.2.1, hab.2.2, rfl⟩
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨(a, b), mem_distinctPairs.mpr ⟨ha, hb, hab⟩, rfl⟩

lemma lineBlock_subset (P : Finset Point) (a b : Point) : lineBlock P a b ⊆ P := by
  intro p hp
  exact (mem_lineBlock.mp hp).1

lemma left_mem_lineBlock {P : Finset Point} {a b : Point} (ha : a ∈ P) :
    a ∈ lineBlock P a b :=
  mem_lineBlock.mpr ⟨ha, collinear_left a b⟩

lemma right_mem_lineBlock {P : Finset Point} {a b : Point} (hb : b ∈ P) :
    b ∈ lineBlock P a b :=
  mem_lineBlock.mpr ⟨hb, collinear_right a b⟩

lemma lineBlock_eq_of_mem {P : Finset Point} {a b c d : Point}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hc : c ∈ lineBlock P a b) (hd : d ∈ lineBlock P a b) :
    lineBlock P c d = lineBlock P a b := by
  classical
  apply Finset.ext
  intro p
  simp only [mem_lineBlock]
  have hline := collinear_line_unique hab hcd
    (mem_lineBlock.mp hc).2 (mem_lineBlock.mp hd).2 (p := p)
  tauto

lemma connectingLine_card_two_le {P : Finset Point} {L : Finset Point}
    (hL : L ∈ connectingLines P) : 2 ≤ L.card := by
  rcases mem_connectingLines.mp hL with ⟨a, ha, b, hb, hab, rfl⟩
  have hsub : ({a, b} : Finset Point) ⊆ lineBlock P a b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact left_mem_lineBlock ha
    · exact right_mem_lineBlock hb
  have hcard := Finset.card_le_card hsub
  simpa [hab] using hcard

/-- Connecting lines containing exactly `r` points. -/
noncomputable def linesOfSize (P : Finset Point) (r : ℕ) :
    Finset (Finset Point) := by
  classical
  exact (connectingLines P).filter fun L ↦ L.card = r

/-- Number of connecting lines through a point. -/
noncomputable def pointDegree (P : Finset Point) (p : Point) : ℕ := by
  classical
  exact ∑ L ∈ connectingLines P, if p ∈ L then 1 else 0

lemma connectingLine_eq_of_two_mem {P : Finset Point} {L M : Finset Point}
    (hL : L ∈ connectingLines P) (hM : M ∈ connectingLines P)
    {a b : Point} (hab : a ≠ b) (haL : a ∈ L) (hbL : b ∈ L)
    (haM : a ∈ M) (hbM : b ∈ M) : L = M := by
  rcases mem_connectingLines.mp hL with ⟨c, hc, d, hd, hcd, rfl⟩
  rcases mem_connectingLines.mp hM with ⟨e, he, f, hf, hef, rfl⟩
  have h₁ : lineBlock P a b = lineBlock P c d :=
    lineBlock_eq_of_mem hcd hab haL hbL
  have h₂ : lineBlock P a b = lineBlock P e f :=
    lineBlock_eq_of_mem hef hab haM hbM
  exact h₁.symm.trans h₂

lemma powersetCard_two_pairwiseDisjoint (P : Finset Point) :
    ((connectingLines P : Finset (Finset Point)) : Set (Finset Point)).PairwiseDisjoint
      (fun L ↦ L.powersetCard 2) := by
  classical
  intro L hL M hM hLM
  change Disjoint (L.powersetCard 2) (M.powersetCard 2)
  rw [Finset.disjoint_left]
  intro A hAL hAM
  rw [Finset.mem_powersetCard] at hAL hAM
  rcases Finset.card_eq_two.mp hAL.2 with ⟨a, b, hab, rfl⟩
  have haL : a ∈ L := hAL.1 (by simp)
  have hbL : b ∈ L := hAL.1 (by simp)
  have haM : a ∈ M := hAM.1 (by simp)
  have hbM : b ∈ M := hAM.1 (by simp)
  exact hLM (connectingLine_eq_of_two_mem hL hM hab haL hbL haM hbM)

/-- Every unordered pair of points belongs to exactly one connecting block. -/
lemma biUnion_linePairs (P : Finset Point) :
    (connectingLines P).biUnion (fun L ↦ L.powersetCard 2) = P.powersetCard 2 := by
  classical
  apply Finset.ext
  intro A
  constructor
  · intro hA
    rcases Finset.mem_biUnion.mp hA with ⟨L, hL, hAL⟩
    rw [Finset.mem_powersetCard] at hAL ⊢
    refine ⟨hAL.1.trans ?_, hAL.2⟩
    rcases mem_connectingLines.mp hL with ⟨a, ha, b, hb, hab, rfl⟩
    exact lineBlock_subset P a b
  · intro hA
    rw [Finset.mem_powersetCard] at hA
    rcases Finset.card_eq_two.mp hA.2 with ⟨a, b, hab, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨lineBlock P a b, ?_, ?_⟩
    · exact mem_connectingLines.mpr
        ⟨a, hA.1 (by simp), b, hA.1 (by simp), hab, rfl⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, by simp [hab]⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact left_mem_lineBlock (hA.1 (by simp))
      · exact right_mem_lineBlock (hA.1 (by simp))

/-- Pair partition identity for connecting lines. -/
lemma sum_choose_two_line_card (P : Finset Point) :
    ∑ L ∈ connectingLines P, Nat.choose L.card 2 = Nat.choose P.card 2 := by
  classical
  rw [← Finset.card_powersetCard]
  rw [← biUnion_linePairs P]
  rw [Finset.card_biUnion (powersetCard_two_pairwiseDisjoint P)]
  apply Finset.sum_congr rfl
  intro L hL
  exact (Finset.card_powersetCard 2 L).symm

lemma connectingLine_subset {P : Finset Point} {L : Finset Point}
    (hL : L ∈ connectingLines P) : L ⊆ P := by
  rcases mem_connectingLines.mp hL with ⟨a, ha, b, hb, hab, rfl⟩
  exact lineBlock_subset P a b

/-- Handshake identity between point degrees and line multiplicities. -/
lemma sum_pointDegree (P : Finset Point) :
    ∑ p ∈ P, pointDegree P p = ∑ L ∈ connectingLines P, L.card := by
  classical
  simp only [pointDegree]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro L hL
  have hsub := connectingLine_subset hL
  have hfilter : P.filter (fun x ↦ x ∈ L) = L := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx ↦ hx.2
    · exact fun hx ↦ ⟨hsub hx, hx⟩
  calc
    ∑ x ∈ P, (if x ∈ L then (1 : ℕ) else 0) =
        ((P.filter fun x ↦ x ∈ L).card : ℕ) := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = L.card := by rw [hfilter]

/-! ## The numerical form of Melchior's inequality -/

/-- The projective-arrangement defect `sum (3 - multiplicity)`.  Melchior's
inequality says that this integer is at least three for every non-collinear
real point configuration. -/
noncomputable def lineDefect (P : Finset Point) : ℤ :=
  ∑ L ∈ connectingLines P, ((3 : ℤ) - L.card)

/-! ### A dual-line sweep

The eventual incidence estimate is proved by sweeping a dual affine line
arrangement.  The preliminary shear `sweepSlope` is chosen so that the dual
lines have pairwise distinct slopes. -/

def sweepSlope (t : ℝ) (p : Point) : ℝ := p.1 + t * p.2

def dualHeight (t : ℝ) (p : Point) (x : ℝ) : ℝ :=
  sweepSlope t p * x - p.2

noncomputable def sortByKey {α β : Type*} [DecidableEq α] [LinearOrder β]
    (s : Finset α) (key : α → β) (hinj : Function.Injective key) : List α := by
  letI : LinearOrder α := LinearOrder.lift' key hinj
  exact s.sort

lemma sortByKey_pairwise {α β : Type*} [DecidableEq α] [LinearOrder β]
    (s : Finset α) (key : α → β) (hinj : Function.Injective key) :
    (sortByKey s key hinj).Pairwise fun x y ↦ key x ≤ key y := by
  letI : LinearOrder α := LinearOrder.lift' key hinj
  change (s.sort (fun x y ↦ key x ≤ key y)).Pairwise (fun x y ↦ key x ≤ key y)
  exact Finset.pairwise_sort s _

lemma sortByKey_perm {α β : Type*} [DecidableEq α] [LinearOrder β]
    (s : Finset α) (key : α → β) (hinj : Function.Injective key) :
    (sortByKey s key hinj).Perm s.toList := by
  letI : LinearOrder α := LinearOrder.lift' key hinj
  exact Finset.sort_perm_toList s _

lemma sortByKey_eq_of_pairwise_perm {α β : Type*} [DecidableEq α] [LinearOrder β]
    (s : Finset α) (key : α → β) (hinj : Function.Injective key)
    (l : List α) (hl : l.Pairwise fun x y ↦ key x ≤ key y)
    (hp : l.Perm s.toList) : sortByKey s key hinj = l := by
  apply List.Perm.eq_of_pairwise
      (fun x y _ _ hxy hyx ↦ hinj (le_antisymm hxy hyx))
      (sortByKey_pairwise s key hinj) hl
  exact (sortByKey_perm s key hinj).trans hp.symm

noncomputable def descentCount {α : Type*} (f : α → ℝ) : List α → ℕ
  | x :: y :: l => (if f y < f x then 1 else 0) + descentCount f (y :: l)
  | _ => 0

noncomputable def descentBoundary {α : Type*} (f : α → ℝ) (l₁ l₂ : List α) : ℕ :=
  match l₁.getLast?, l₂.head? with
  | some x, some y => if f y < f x then 1 else 0
  | _, _ => 0

lemma descentCount_append {α : Type*} (f : α → ℝ) (l₁ l₂ : List α) :
    descentCount f (l₁ ++ l₂) =
      descentCount f l₁ + descentCount f l₂ + descentBoundary f l₁ l₂ := by
  induction l₁ with
  | nil => simp [descentCount, descentBoundary]
  | cons x l ih =>
      cases l with
      | nil => cases l₂ <;> simp [descentCount, descentBoundary, Nat.add_comm]
      | cons y l =>
          simp only [List.cons_append, descentCount]
          rw [show y :: (l ++ l₂) = (y :: l) ++ l₂ by rfl, ih]
          simp only [descentBoundary, List.getLast?_cons_cons]
          omega

lemma descentBoundary_le_one {α : Type*} (f : α → ℝ) (l₁ l₂ : List α) :
    descentBoundary f l₁ l₂ ≤ 1 := by
  unfold descentBoundary
  cases h₁ : l₁.getLast? with
  | none => simp [h₁]
  | some x =>
      cases h₂ : l₂.head? with
      | none => simp [h₁, h₂]
      | some y => simp only [h₁, h₂]; split_ifs <;> omega

lemma descentCount_eq_length_sub_one_of_pairwise_gt
    {α : Type*} {f : α → ℝ} {l : List α}
    (h : l.Pairwise fun x y ↦ f y < f x) :
    descentCount f l = l.length - 1 := by
  induction l with
  | nil => simp [descentCount]
  | cons x l ih =>
      cases l with
      | nil => simp [descentCount]
      | cons y l =>
          rw [List.pairwise_cons] at h
          have hxy : f y < f x := h.1 y (by simp)
          have htail : (y :: l).Pairwise fun u v ↦ f v < f u := h.2
          simp only [descentCount, if_pos hxy, ih htail, List.length_cons]
          omega

lemma descentCount_eq_zero_of_pairwise_lt
    {α : Type*} {f : α → ℝ} {l : List α}
    (h : l.Pairwise fun x y ↦ f x < f y) : descentCount f l = 0 := by
  induction l with
  | nil => simp [descentCount]
  | cons x l ih =>
      cases l with
      | nil => simp [descentCount]
      | cons y l =>
          rw [List.pairwise_cons] at h
          have hxy : ¬ f y < f x := not_lt.mpr (le_of_lt (h.1 y (by simp)))
          have htail : (y :: l).Pairwise fun u v ↦ f u < f v := h.2
          simp only [descentCount, if_neg hxy, ih htail, zero_add]

lemma descentCount_reverse_block_bound
    {α : Type*} (f : α → ℝ) (pre block post : List α)
    (hblock : block.Pairwise fun x y ↦ f y < f x) :
    block.length ≤
      descentCount f (pre ++ block ++ post) -
        descentCount f (pre ++ block.reverse ++ post) + 3 := by
  have hdesc := descentCount_eq_length_sub_one_of_pairwise_gt hblock
  have hasc : block.reverse.Pairwise fun x y ↦ f x < f y := by
    rw [List.pairwise_reverse]
    exact hblock
  have hzero := descentCount_eq_zero_of_pairwise_lt hasc
  rw [descentCount_append, descentCount_append,
    descentCount_append, descentCount_append, hdesc, hzero]
  have h₁ := descentBoundary_le_one f pre block
  have h₂ := descentBoundary_le_one f (pre ++ block) post
  have h₃ := descentBoundary_le_one f pre block.reverse
  have h₄ := descentBoundary_le_one f (pre ++ block.reverse) post
  omega

lemma descentCount_reverse_block_add_bound
    {α : Type*} (f : α → ℝ) (pre block post : List α)
    (hblock : block.Pairwise fun x y ↦ f y < f x) :
    block.length + descentCount f (pre ++ block.reverse ++ post) ≤
      descentCount f (pre ++ block ++ post) + 3 := by
  have hdesc := descentCount_eq_length_sub_one_of_pairwise_gt hblock
  have hasc : block.reverse.Pairwise fun x y ↦ f x < f y := by
    rw [List.pairwise_reverse]
    exact hblock
  have hzero := descentCount_eq_zero_of_pairwise_lt hasc
  rw [descentCount_append, descentCount_append,
    descentCount_append, descentCount_append, hdesc, hzero]
  have h₁ := descentBoundary_le_one f pre block
  have h₂ := descentBoundary_le_one f (pre ++ block) post
  have h₃ := descentBoundary_le_one f pre block.reverse
  have h₄ := descentBoundary_le_one f (pre ++ block.reverse) post
  omega

lemma chain_telescope_sum {ε : Type*} (r before after : ε → ℕ)
    (hlocal : ∀ e, r e + after e ≤ before e + 3) (x : ε) :
    ∀ xs : List ε,
      List.Chain (fun e e' ↦ after e = before e') x xs →
      (r x :: xs.map r).sum + after (xs.getLast?.getD x) ≤
        before x + 3 * (xs.length + 1) := by
  intro xs
  induction xs generalizing x with
  | nil =>
      intro _
      simpa using hlocal x
  | cons y ys ih =>
      intro hchain
      change List.IsChain (fun e e' ↦ after e = before e') (x :: y :: ys) at hchain
      rw [List.chain_cons] at hchain
      have htail := ih y hchain.2
      have hhead := hlocal x
      rw [hchain.1] at hhead
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        List.getLast?_cons, Option.getD_some]
      calc
        r x + (r y :: List.map r ys).sum + after (ys.getLast?.getD y) =
            r x + ((r y :: List.map r ys).sum +
              after (ys.getLast?.getD y)) := by omega
        _ ≤ r x + (before y + 3 * (ys.length + 1)) :=
          Nat.add_le_add_left htail _
        _ = (r x + before y) + 3 * (ys.length + 1) := by omega
        _ ≤ (before x + 3) + 3 * (ys.length + 1) :=
          Nat.add_le_add_right hhead _
        _ = before x + 3 * (ys.length + 1 + 1) := by omega

def beforeTieKey {α : Type*} (h f : α → ℝ) (x : α) : Lex (ℝ × ℝ) :=
  toLex (h x, -f x)

def afterTieKey {α : Type*} (h f : α → ℝ) (x : α) : Lex (ℝ × ℝ) :=
  toLex (h x, f x)

lemma beforeTieKey_injective {α : Type*} {h f : α → ℝ}
    (hf : Function.Injective f) : Function.Injective (beforeTieKey h f) := by
  intro x z hxz
  apply hf
  have hpair := congrArg ofLex hxz
  exact neg_injective (congrArg Prod.snd hpair)

lemma afterTieKey_injective {α : Type*} {h f : α → ℝ}
    (hf : Function.Injective f) : Function.Injective (afterTieKey h f) := by
  intro x z hxz
  apply hf
  have hpair := congrArg ofLex hxz
  exact congrArg Prod.snd hpair

noncomputable def beforeTieOrder {α : Type*} [Fintype α] [DecidableEq α]
    (h f : α → ℝ) (hf : Function.Injective f) : List α :=
  sortByKey Finset.univ (beforeTieKey h f) (beforeTieKey_injective hf)

noncomputable def afterTieOrder {α : Type*} [Fintype α] [DecidableEq α]
    (h f : α → ℝ) (hf : Function.Injective f) : List α :=
  sortByKey Finset.univ (afterTieKey h f) (afterTieKey_injective hf)

noncomputable def tieBlock {α : Type*} [Fintype α] [DecidableEq α]
    (h f : α → ℝ) (hf : Function.Injective f) (y : ℝ) : List α :=
  (beforeTieOrder h f hf).filter fun x ↦ h x = y

lemma tieBlock_pairwise_descending {α : Type*} [Fintype α] [DecidableEq α]
    {h f : α → ℝ} (hf : Function.Injective f) (y : ℝ) :
    (tieBlock h f hf y).Pairwise fun x z ↦ f z < f x := by
  classical
  have hpair := (sortByKey_pairwise Finset.univ (beforeTieKey h f)
    (beforeTieKey_injective hf)).filter fun x ↦ h x = y
  have hnodup : (tieBlock h f hf y).Nodup := by
    apply List.Nodup.filter
    exact (sortByKey_perm Finset.univ (beforeTieKey h f)
      (beforeTieKey_injective hf)).nodup_iff.mpr
        (Finset.nodup_toList (Finset.univ : Finset α))
  apply (hpair.and hnodup).imp_of_mem
  intro x z hx hz hxz
  rw [List.mem_filter] at hx hz
  have hhyx : h x = y := of_decide_eq_true hx.2
  have hhyz : h z = y := of_decide_eq_true hz.2
  change (toLex (h x, -f x) ≤ toLex (h z, -f z)) ∧ x ≠ z at hxz
  rw [Prod.Lex.toLex_le_toLex] at hxz
  rcases hxz.1 with hlt | ⟨heq, hneg⟩
  · linarith
  · have hle : f z ≤ f x := by linarith
    exact lt_of_le_of_ne hle (fun heqf ↦ hxz.2 (hf heqf.symm))

lemma list_partition_three_of_pairwise {α : Type*} {h : α → ℝ}
    (y : ℝ) {l : List α} (hl : l.Pairwise fun x z ↦ h x ≤ h z) :
    l = l.filter (fun x ↦ h x < y) ++
      l.filter (fun x ↦ h x = y) ++ l.filter (fun x ↦ y < h x) := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [List.pairwise_cons] at hl
      have hi := ih hl.2
      rcases lt_trichotomy (h x) y with hx | hx | hx
      · have htail := congrArg (List.cons x) hi
        simpa [List.filter_cons, hx, ne_of_lt hx, not_lt_of_ge hx.le] using htail
      · have hnotlt : ∀ z ∈ l, ¬ h z < y := by
          intro z hz hzlt
          have hxz := hl.1 z hz
          linarith
        have hfilterlt : l.filter (fun z ↦ h z < y) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz
          simpa using hnotlt z hz
        have hitail : l = l.filter (fun z ↦ h z = y) ++
            l.filter (fun z ↦ y < h z) := by
          simpa [hfilterlt] using hi
        have hxl : ¬ h x < y := by linarith
        have hxg : ¬ y < h x := by linarith
        simp only [List.filter_cons, hxl, hx, hxg, lt_irrefl, decide_false, decide_true,
          if_false, if_true, hfilterlt, List.nil_append, List.cons_append]
        exact congrArg (List.cons x) hitail
      · have hgt : ∀ z ∈ l, y < h z := by
          intro z hz
          exact hx.trans_le (hl.1 z hz)
        have hfilterlt : l.filter (fun z ↦ h z < y) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz
          have := hgt z hz
          simp only [decide_eq_true_eq, not_lt]
          linarith
        have hfiltereq : l.filter (fun z ↦ h z = y) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz
          have := hgt z hz
          simp only [decide_eq_true_eq]
          linarith
        have hfiltergt : l.filter (fun z ↦ y < h z) = l := by
          rw [List.filter_eq_self]
          intro z hz
          simpa using hgt z hz
        simp [List.filter_cons, hx, ne_of_gt hx, not_lt_of_ge hx.le,
          hfilterlt, hfiltereq, hfiltergt]

lemma beforeTieOrder_pairwise_height_le {α : Type*} [Fintype α] [DecidableEq α]
    {h f : α → ℝ} (hf : Function.Injective f) :
    (beforeTieOrder h f hf).Pairwise fun x z ↦ h x ≤ h z := by
  have hp := sortByKey_pairwise Finset.univ (beforeTieKey h f)
    (beforeTieKey_injective hf)
  apply hp.imp
  intro x z hxz
  change toLex (h x, -f x) ≤ toLex (h z, -f z) at hxz
  rw [Prod.Lex.toLex_le_toLex] at hxz
  rcases hxz with hxz | ⟨hxz, _⟩
  · exact hxz.le
  · exact hxz.le

lemma afterTieOrder_pairwise_height_le {α : Type*} [Fintype α] [DecidableEq α]
    {h f : α → ℝ} (hf : Function.Injective f) :
    (afterTieOrder h f hf).Pairwise fun x z ↦ h x ≤ h z := by
  have hp := sortByKey_pairwise Finset.univ (afterTieKey h f)
    (afterTieKey_injective hf)
  apply hp.imp
  intro x z hxz
  change toLex (h x, f x) ≤ toLex (h z, f z) at hxz
  rw [Prod.Lex.toLex_le_toLex] at hxz
  rcases hxz with hxz | ⟨hxz, _⟩
  · exact hxz.le
  · exact hxz.le

lemma beforeTieOrder_partition {α : Type*} [Fintype α] [DecidableEq α]
    {h f : α → ℝ} (hf : Function.Injective f) (y : ℝ) :
    beforeTieOrder h f hf =
      (beforeTieOrder h f hf).filter (fun x ↦ h x < y) ++
      tieBlock h f hf y ++
      (beforeTieOrder h f hf).filter (fun x ↦ y < h x) := by
  exact list_partition_three_of_pairwise y (beforeTieOrder_pairwise_height_le hf)

lemma afterTieOrder_partition {α : Type*} [Fintype α] [DecidableEq α]
    {h f : α → ℝ} (hf : Function.Injective f) (y : ℝ) :
    afterTieOrder h f hf =
      (afterTieOrder h f hf).filter (fun x ↦ h x < y) ++
      (afterTieOrder h f hf).filter (fun x ↦ h x = y) ++
      (afterTieOrder h f hf).filter (fun x ↦ y < h x) := by
  exact list_partition_three_of_pairwise y (afterTieOrder_pairwise_height_le hf)

lemma before_after_filter_lt_eq_of_unique
    {α : Type*} [Fintype α] [DecidableEq α] {h f : α → ℝ}
    (hf : Function.Injective f) (y : ℝ)
    (hunique : ∀ x z, h x = h z → x = z ∨ h x = y) :
    (beforeTieOrder h f hf).filter (fun x ↦ h x < y) =
      (afterTieOrder h f hf).filter (fun x ↦ h x < y) := by
  have hbefore : ((beforeTieOrder h f hf).filter (fun x ↦ h x < y)).Pairwise
      (fun x z ↦ h x ≤ h z) :=
    (beforeTieOrder_pairwise_height_le hf).filter _
  have hafter : ((afterTieOrder h f hf).filter (fun x ↦ h x < y)).Pairwise
      (fun x z ↦ h x ≤ h z) :=
    (afterTieOrder_pairwise_height_le hf).filter _
  apply List.Perm.eq_of_pairwise
      (fun x z hx _ hxz hzx ↦ by
        rcases hunique x z (le_antisymm hxz hzx) with hxz | hxy
        · exact hxz
        · rw [List.mem_filter] at hx
          have hlt : h x < y := of_decide_eq_true hx.2
          linarith)
      hbefore hafter
  exact ((sortByKey_perm Finset.univ (beforeTieKey h f)
      (beforeTieKey_injective hf)).filter (fun x ↦ h x < y)).trans
    ((sortByKey_perm Finset.univ (afterTieKey h f)
      (afterTieKey_injective hf)).filter (fun x ↦ h x < y)).symm

lemma before_after_filter_gt_eq_of_unique
    {α : Type*} [Fintype α] [DecidableEq α] {h f : α → ℝ}
    (hf : Function.Injective f) (y : ℝ)
    (hunique : ∀ x z, h x = h z → x = z ∨ h x = y) :
    (beforeTieOrder h f hf).filter (fun x ↦ y < h x) =
      (afterTieOrder h f hf).filter (fun x ↦ y < h x) := by
  have hbefore : ((beforeTieOrder h f hf).filter (fun x ↦ y < h x)).Pairwise
      (fun x z ↦ h x ≤ h z) :=
    (beforeTieOrder_pairwise_height_le hf).filter _
  have hafter : ((afterTieOrder h f hf).filter (fun x ↦ y < h x)).Pairwise
      (fun x z ↦ h x ≤ h z) :=
    (afterTieOrder_pairwise_height_le hf).filter _
  apply List.Perm.eq_of_pairwise
      (fun x z hx _ hxz hzx ↦ by
        rcases hunique x z (le_antisymm hxz hzx) with hxz | hxy
        · exact hxz
        · rw [List.mem_filter] at hx
          have hgt : y < h x := of_decide_eq_true hx.2
          linarith)
      hbefore hafter
  exact ((sortByKey_perm Finset.univ (beforeTieKey h f)
      (beforeTieKey_injective hf)).filter (fun x ↦ y < h x)).trans
    ((sortByKey_perm Finset.univ (afterTieKey h f)
      (afterTieKey_injective hf)).filter (fun x ↦ y < h x)).symm

lemma afterTieBlock_pairwise_ascending {α : Type*} [Fintype α] [DecidableEq α]
    {h f : α → ℝ} (hf : Function.Injective f) (y : ℝ) :
    ((afterTieOrder h f hf).filter (fun x ↦ h x = y)).Pairwise
      fun x z ↦ f x < f z := by
  classical
  have hpair := (sortByKey_pairwise Finset.univ (afterTieKey h f)
    (afterTieKey_injective hf)).filter fun x ↦ h x = y
  have hnodup : ((afterTieOrder h f hf).filter (fun x ↦ h x = y)).Nodup := by
    apply List.Nodup.filter
    exact (sortByKey_perm Finset.univ (afterTieKey h f)
      (afterTieKey_injective hf)).nodup_iff.mpr
        (Finset.nodup_toList (Finset.univ : Finset α))
  apply (hpair.and hnodup).imp_of_mem
  intro x z hx hz hxz
  rw [List.mem_filter] at hx hz
  have hhyx : h x = y := of_decide_eq_true hx.2
  have hhyz : h z = y := of_decide_eq_true hz.2
  change (toLex (h x, f x) ≤ toLex (h z, f z)) ∧ x ≠ z at hxz
  rw [Prod.Lex.toLex_le_toLex] at hxz
  rcases hxz.1 with hlt | ⟨_, hle⟩
  · linarith
  · exact lt_of_le_of_ne hle (fun heqf ↦ hxz.2 (hf heqf))

lemma afterTieBlock_eq_reverse {α : Type*} [Fintype α] [DecidableEq α]
    {h f : α → ℝ} (hf : Function.Injective f) (y : ℝ) :
    (afterTieOrder h f hf).filter (fun x ↦ h x = y) =
      (tieBlock h f hf y).reverse := by
  have hafter : ((afterTieOrder h f hf).filter (fun x ↦ h x = y)).Pairwise
      (fun x z ↦ f x ≤ f z) := by
    apply (afterTieBlock_pairwise_ascending hf y).imp
    intro x z hxz
    exact hxz.le
  have hreverse : (tieBlock h f hf y).reverse.Pairwise
      (fun x z ↦ f x ≤ f z) := by
    have hr : (tieBlock h f hf y).reverse.Pairwise (fun x z ↦ f x < f z) := by
      rw [List.pairwise_reverse]
      exact tieBlock_pairwise_descending hf y
    apply hr.imp
    intro x z hxz
    exact hxz.le
  apply List.Perm.eq_of_pairwise
      (fun x z _ _ hxz hzx ↦ hf (le_antisymm hxz hzx))
      hafter hreverse
  have ha := (sortByKey_perm Finset.univ (afterTieKey h f)
    (afterTieKey_injective hf)).filter (fun x ↦ h x = y)
  have hb := (sortByKey_perm Finset.univ (beforeTieKey h f)
    (beforeTieKey_injective hf)).filter (fun x ↦ h x = y)
  exact ha.trans (hb.symm.trans (List.reverse_perm _).symm)

lemma afterTieOrder_eq_reversed_parts_of_unique
    {α : Type*} [Fintype α] [DecidableEq α] {h f : α → ℝ}
    (hf : Function.Injective f) (y : ℝ)
    (hunique : ∀ x z, h x = h z → x = z ∨ h x = y) :
    afterTieOrder h f hf =
      (beforeTieOrder h f hf).filter (fun x ↦ h x < y) ++
      (tieBlock h f hf y).reverse ++
      (beforeTieOrder h f hf).filter (fun x ↦ y < h x) := by
  rw [afterTieOrder_partition hf y,
    ← before_after_filter_lt_eq_of_unique hf y hunique,
    afterTieBlock_eq_reverse hf y,
    ← before_after_filter_gt_eq_of_unique hf y hunique]

lemma tie_order_descent_drop
    {α : Type*} [Fintype α] [DecidableEq α] {h f : α → ℝ}
    (hf : Function.Injective f) (y : ℝ)
    (hunique : ∀ x z, h x = h z → x = z ∨ h x = y) :
    (tieBlock h f hf y).length ≤
      descentCount f (beforeTieOrder h f hf) -
        descentCount f (afterTieOrder h f hf) + 3 := by
  rw [beforeTieOrder_partition hf y,
    afterTieOrder_eq_reversed_parts_of_unique hf y hunique]
  exact descentCount_reverse_block_bound f _ _ _
    (tieBlock_pairwise_descending hf y)

lemma tie_order_descent_add_bound
    {α : Type*} [Fintype α] [DecidableEq α] {h f : α → ℝ}
    (hf : Function.Injective f) (y : ℝ)
    (hunique : ∀ x z, h x = h z → x = z ∨ h x = y) :
    (tieBlock h f hf y).length + descentCount f (afterTieOrder h f hf) ≤
      descentCount f (beforeTieOrder h f hf) + 3 := by
  rw [beforeTieOrder_partition hf y,
    afterTieOrder_eq_reversed_parts_of_unique hf y hunique]
  exact descentCount_reverse_block_add_bound f _ _ _
    (tieBlock_pairwise_descending hf y)


noncomputable def dualMeetX (t : ℝ) (a b : Point) : ℝ :=
  (a.2 - b.2) / (sweepSlope t a - sweepSlope t b)

lemma dualHeight_dualMeetX_eq {t : ℝ} {a b : Point}
    (hab : sweepSlope t a ≠ sweepSlope t b) :
    dualHeight t a (dualMeetX t a b) =
      dualHeight t b (dualMeetX t a b) := by
  simp only [dualHeight, dualMeetX]
  field_simp [hab]
  ring

lemma dualHeight_dualMeetX_eq_iff_collinear {t : ℝ} {a b c : Point}
    (hab : sweepSlope t a ≠ sweepSlope t b) :
    dualHeight t c (dualMeetX t a b) =
        dualHeight t a (dualMeetX t a b) ↔ Collinear a b c := by
  have hd : a.1 + t * a.2 - (b.1 + t * b.2) ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa only [sweepSlope] using hab)
  simp only [dualHeight, dualMeetX, sweepSlope, Collinear, det]
  constructor <;> intro h
  · field_simp [hd] at h
    ring_nf at h ⊢
    linarith
  · field_simp [hd]
    ring_nf at h ⊢
    linarith

noncomputable def badSweepParameters (P : Finset Point) : Finset ℝ := by
  classical
  exact ((distinctPairs P).filter fun ab ↦ ab.1.2 ≠ ab.2.2).image fun ab ↦
    -(ab.1.1 - ab.2.1) / (ab.1.2 - ab.2.2)

lemma exists_sweepSlope_injOn (P : Finset Point) :
    ∃ t : ℝ, Set.InjOn (sweepSlope t) P := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ badSweepParameters P := by
    apply Finset.exists_not_mem_of_card_lt_enatCard
    rw [ENat.card_eq_top.mpr (inferInstance : Infinite ℝ)]
    exact ENat.coe_lt_top _
  refine ⟨t, fun a ha b hb hab ↦ ?_⟩
  by_contra hne
  have habP : (a, b) ∈ distinctPairs P :=
    mem_distinctPairs.mpr ⟨ha, hb, hne⟩
  by_cases hy : a.2 = b.2
  · have hx : a.1 ≠ b.1 := by
      intro hx
      exact hne (Prod.ext hx hy)
    simp only [sweepSlope, hy] at hab
    exact hx (by linarith)
  · apply ht
    rw [badSweepParameters, Finset.mem_image]
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨habP, hy⟩
    · simp only [sweepSlope] at hab
      have hden : a.2 - b.2 ≠ 0 := sub_ne_zero.mpr hy
      field_simp [hden]
      nlinarith

lemma exists_sweepSlope_injOn_avoiding (P : Finset Point) (B : Finset ℝ) :
    ∃ t : ℝ, Set.InjOn (sweepSlope t) P ∧ t ∉ B := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ badSweepParameters P ∪ B := by
    apply Finset.exists_not_mem_of_card_lt_enatCard
    rw [ENat.card_eq_top.mpr (inferInstance : Infinite ℝ)]
    exact ENat.natCast_lt_top _
  have hbad : t ∉ badSweepParameters P := fun h ↦ ht (Finset.mem_union_left B h)
  have hB : t ∉ B := fun h ↦ ht (Finset.mem_union_right _ h)
  refine ⟨t, ?_, hB⟩
  intro a ha b hb hab
  by_contra hne
  have habP : (a, b) ∈ distinctPairs P :=
    mem_distinctPairs.mpr ⟨ha, hb, hne⟩
  by_cases hy : a.2 = b.2
  · have hx : a.1 ≠ b.1 := by
      intro hx
      exact hne (Prod.ext hx hy)
    simp only [sweepSlope, hy] at hab
    exact hx (by linarith)
  · apply hbad
    rw [badSweepParameters, Finset.mem_image]
    refine ⟨(a, b), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨habP, hy⟩
    · simp only [sweepSlope] at hab
      have hden : a.2 - b.2 ≠ 0 := sub_ne_zero.mpr hy
      field_simp [hden]
      nlinarith

lemma mem_linesOfSize {P : Finset Point} {r : ℕ} {L : Finset Point} :
    L ∈ linesOfSize P r ↔ L ∈ connectingLines P ∧ L.card = r := by
  classical
  simp [linesOfSize]

lemma card_linesOfSize_eq_sum_indicator (P : Finset Point) (r : ℕ) :
    (linesOfSize P r).card =
      ∑ L ∈ connectingLines P, if L.card = r then 1 else 0 := by
  classical
  exact (Finset.sum_boole (fun L : Finset Point ↦ L.card = r)
    (connectingLines P)).symm

/-- The first numerical consequence of Melchior: three times the number of
connecting lines dominates three plus the number of point-line incidences. -/
lemma three_mul_line_count_ge_incidence_of_lineDefect
    (P : Finset Point) (hM : (3 : ℤ) ≤ lineDefect P) :
    (3 : ℤ) + ∑ L ∈ connectingLines P, (L.card : ℤ) ≤
      3 * (connectingLines P).card := by
  rw [lineDefect] at hM
  have hcard :
      ∑ L ∈ connectingLines P, (3 : ℤ) =
        3 * (connectingLines P).card := by
    rw [Finset.sum_const]
    simp [mul_comm]
  rw [Finset.sum_sub_distrib, hcard] at hM
  omega

/-- The second numerical consequence of Melchior: lines containing two or
three points already account for at least half of all connecting lines. -/
lemma small_lines_of_lineDefect
    (P : Finset Point) (hM : (3 : ℤ) ≤ lineDefect P) :
    (connectingLines P).card + 3 ≤
      2 * (linesOfSize P 2).card + (linesOfSize P 3).card := by
  classical
  have hpointwise : ∀ L ∈ connectingLines P,
      ((3 : ℤ) - L.card) ≤
        (if L.card = 2 then (2 : ℤ) else if L.card = 3 then 1 else 0) - 1 := by
    intro L hL
    have hr := connectingLine_card_two_le hL
    split_ifs with h2 h3
    · omega
    · omega
    · omega
  have hsum : lineDefect P ≤
      ∑ L ∈ connectingLines P,
        ((if L.card = 2 then (2 : ℤ) else if L.card = 3 then 1 else 0) - 1) := by
    rw [lineDefect]
    exact Finset.sum_le_sum fun L hL ↦ hpointwise L hL
  have hcount2 := card_linesOfSize_eq_sum_indicator P 2
  have hcount3 := card_linesOfSize_eq_sum_indicator P 3
  have hcount2z := congrArg (fun z : ℕ ↦ (z : ℤ)) hcount2
  have hcount3z := congrArg (fun z : ℕ ↦ (z : ℤ)) hcount3
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hcount2z hcount3z
  have hrewrite :
      ∑ L ∈ connectingLines P,
          ((if L.card = 2 then (2 : ℤ) else if L.card = 3 then 1 else 0) - 1) =
        2 * (linesOfSize P 2).card + (linesOfSize P 3).card -
          (connectingLines P).card := by
    rw [Finset.sum_sub_distrib]
    have hindicator :
        ∑ L ∈ connectingLines P,
            (if L.card = 2 then (2 : ℤ) else if L.card = 3 then 1 else 0) =
          2 * ∑ L ∈ connectingLines P, (if L.card = 2 then (1 : ℤ) else 0) +
            ∑ L ∈ connectingLines P, (if L.card = 3 then (1 : ℤ) else 0) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro L hL
      by_cases h2 : L.card = 2
      · simp [h2]
      · by_cases h3 : L.card = 3 <;> simp [h2, h3]
    rw [hindicator, ← hcount2z, ← hcount3z, Finset.sum_const]
    simp
  rw [hrewrite] at hsum
  omega

/-! ## Finite two-term inclusion--exclusion -/

/-- The total overlap over ordered pairs of distinct members of a finite
family.  Each unordered pair occurs twice; this avoids division in the
natural-number Bonferroni inequality below. -/
def orderedOverlap {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) : ℕ :=
  ∑ i ∈ I, ∑ j ∈ I, if i = j then 0 else (F i ∩ F j).card

lemma orderedOverlap_insert {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (F : ι → Finset α) {a : ι} {I : Finset ι} (ha : a ∉ I) :
  orderedOverlap (insert a I) F =
      orderedOverlap I F + 2 * ∑ i ∈ I, (F a ∩ F i).card := by
  classical
  have hsymm :
      ∑ i ∈ I, (F i ∩ F a).card = ∑ i ∈ I, (F a ∩ F i).card := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.inter_comm]
  rw [orderedOverlap, Finset.sum_insert ha]
  simp_rw [Finset.sum_insert ha]
  simp only [ite_true, zero_add]
  have hfirst :
      ∑ j ∈ I, (if a = j then 0 else (F a ∩ F j).card) =
        ∑ j ∈ I, (F a ∩ F j).card := by
    apply Finset.sum_congr rfl
    intro j hj
    have hne : a ≠ j := by
      intro haj
      subst j
      exact ha hj
    simp [hne]
  have hsecond :
      ∑ i ∈ I,
          ((if i = a then 0 else (F i ∩ F a).card) +
            ∑ j ∈ I, if i = j then 0 else (F i ∩ F j).card) =
        (∑ i ∈ I, (F i ∩ F a).card) + orderedOverlap I F := by
    rw [Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hne : i ≠ a := by
      intro hia
      subst i
      exact ha hi
    simp [hne]
  rw [hfirst, hsecond, hsymm]
  omega

/-- The first Bonferroni inequality, in a denominator-free ordered-pair
form convenient for natural-number estimates. -/
lemma two_mul_sum_card_le_two_mul_union_add_ordered_overlap
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) :
    2 * ∑ i ∈ I, (F i).card ≤
      2 * (I.biUnion F).card +
        orderedOverlap I F := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [orderedOverlap]
  | @insert a I ha ih =>
      rw [Finset.sum_insert ha, orderedOverlap_insert F ha]
      simp only [Finset.biUnion_insert]
      have hset :
          F a ∩ I.biUnion F = I.biUnion (fun i ↦ F a ∩ F i) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_biUnion]
        aesop
      have hinter :
          (F a ∩ I.biUnion F).card ≤ ∑ i ∈ I, (F a ∩ F i).card := by
        rw [hset]
        exact Finset.card_biUnion_le
      have hunion := Finset.card_union_add_card_inter (F a) (I.biUnion F)
      omega

lemma orderedOverlap_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (q : ℕ)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ q) :
    orderedOverlap I F ≤ I.card * (I.card - 1) * q := by
  classical
  rw [orderedOverlap]
  calc
    _ ≤ ∑ i ∈ I, ((I.card - 1) * q) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ ≤ ∑ j ∈ I, if i = j then 0 else q := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hij : i = j
          · simp [hij]
          · simpa [hij] using hinter i hi j hj hij
        _ = (I.card - 1) * q := by
          rw [← Finset.card_erase_of_mem hi]
          have hfilter : I.filter (fun j ↦ ¬i = j) = I.erase i := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_erase]
            tauto
          simp only [Finset.sum_ite, Finset.sum_const, hfilter]
          simp
    _ = _ := by simp [mul_assoc]

/-- Two-term inclusion--exclusion when all pairwise intersections have a
uniform cardinality bound. -/
lemma two_mul_sum_card_le_two_mul_union_add_pair_bound
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (F : ι → Finset α) (q : ℕ)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (F i ∩ F j).card ≤ q) :
    2 * ∑ i ∈ I, (F i).card ≤
      2 * (I.biUnion F).card + I.card * (I.card - 1) * q := by
  exact (two_mul_sum_card_le_two_mul_union_add_ordered_overlap I F).trans
    (Nat.add_le_add_left (orderedOverlap_le I F q hinter) _)

lemma two_mul_choose_two (r : ℕ) :
    2 * Nat.choose r 2 = r * (r - 1) := by
  rw [Nat.choose_two_right, mul_comm 2]
  exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)

/-! ## The Kelly--Moser line bound from Melchior's inequality -/

/-- The connecting lines through one specified point. -/
noncomputable def linesThrough (P : Finset Point) (p : Point) :
    Finset (Finset Point) := by
  classical
  exact (connectingLines P).filter fun L ↦ p ∈ L

lemma mem_linesThrough {P : Finset Point} {p : Point} {L : Finset Point} :
    L ∈ linesThrough P p ↔ L ∈ connectingLines P ∧ p ∈ L := by
  classical
  simp [linesThrough]

lemma card_linesThrough (P : Finset Point) (p : Point) :
    (linesThrough P p).card = pointDegree P p := by
  classical
  rw [linesThrough, pointDegree, Finset.card_filter]

lemma lineBlock_mem_connectingLines {P : Finset Point} {a b : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    lineBlock P a b ∈ connectingLines P :=
  mem_connectingLines.mpr ⟨a, ha, b, hb, hab, rfl⟩

lemma lineBlock_ne_of_noncollinear {P : Finset Point} {p q r : Point}
    (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P)
    (hnc : Noncollinear p q r) :
    lineBlock P p q ≠ lineBlock P p r := by
  intro h
  have hr' : r ∈ lineBlock P p q := by
    rw [h]
    exact right_mem_lineBlock hr
  exact hnc (mem_lineBlock.mp hr').2

/-- In a non-collinear finite configuration every point is incident with at
least two connecting lines. -/
lemma two_le_pointDegree_of_not_contained
    {P : Finset Point} (hP : ¬ ContainedInLine P) {p : Point} (hp : p ∈ P) :
    2 ≤ pointDegree P p := by
  classical
  have hcard : 2 ≤ P.card := by
    by_contra h
    have hle : P.card ≤ 1 := by omega
    have hall := Finset.card_le_one.mp hle
    apply hP
    refine ⟨p, (p.1 + 1, p.2), ?_, ?_⟩
    · intro heq
      have heq' := congrArg Prod.fst heq
      simp at heq'
    · intro x hx
      have hxp : x = p := hall x hx p hp
      subst x
      exact collinear_left _ _
  have hexq : ∃ q ∈ P, q ≠ p := by
    by_contra h
    push_neg at h
    have hsub : P ⊆ {p} := by
      intro q hq
      simpa [h q hq]
    have := Finset.card_le_card hsub
    simp at this
    omega
  obtain ⟨q, hq, hpq⟩ := hexq
  have hq' : q ≠ p := hpq
  have hpq' : p ≠ q := Ne.symm hq'
  have hex : ∃ r ∈ P, Noncollinear p q r := by
    by_contra h
    push_neg at h
    apply hP
    refine ⟨p, q, hpq', fun r hr ↦ ?_⟩
    simpa [Noncollinear, Collinear] using not_ne_iff.mp (h r hr)
  obtain ⟨r, hr, hnc⟩ := hex
  let L := lineBlock P p q
  let M := lineBlock P p r
  have hL : L ∈ linesThrough P p := by
    rw [mem_linesThrough]
    exact ⟨lineBlock_mem_connectingLines hp hq hpq', left_mem_lineBlock hp⟩
  have hpr : p ≠ r := noncollinear_ne_right hnc
  have hM : M ∈ linesThrough P p := by
    rw [mem_linesThrough]
    exact ⟨lineBlock_mem_connectingLines hp hr hpr, left_mem_lineBlock hp⟩
  have hLM : L ≠ M := lineBlock_ne_of_noncollinear hp hq hr hnc
  have hsub : ({L, M} : Finset (Finset Point)) ⊆ linesThrough P p := by
    intro N hN
    simp only [Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  rw [card_linesThrough] at hc
  simpa [hLM] using hc

/-- The family of connecting lines joining `p` to the points of `A`. -/
noncomputable def crossLines (P A : Finset Point) (p : Point) :
    Finset (Finset Point) := by
  classical
  exact A.image fun a ↦ lineBlock P p a

lemma mem_crossLines {P A : Finset Point} {p : Point} {L : Finset Point} :
    L ∈ crossLines P A p ↔ ∃ a ∈ A, L = lineBlock P p a := by
  classical
  constructor
  · intro hL
    rcases Finset.mem_image.mp hL with ⟨a, ha, hLa⟩
    exact ⟨a, ha, hLa.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

lemma crossLines_subset_connectingLines
    {P A : Finset Point} {p : Point} (hAP : A ⊆ P) (hp : p ∈ P)
    (hpA : p ∉ A) :
    crossLines P A p ⊆ connectingLines P := by
  intro L hL
  rw [mem_crossLines] at hL
  obtain ⟨a, ha, rfl⟩ := hL
  exact lineBlock_mem_connectingLines hp (hAP ha) (fun hpa ↦ hpA (hpa ▸ ha))

lemma card_crossLines_on_common_line
    {P A : Finset Point} {a b p : Point}
    (hAP : A ⊆ P) (hp : p ∈ P) (hab : a ≠ b)
    (hA : ∀ x ∈ A, Collinear a b x)
    (hoff : Noncollinear a b p) :
    (crossLines P A p).card = A.card := by
  classical
  rw [crossLines, Finset.card_image_iff]
  intro x hx y hy hxy
  by_contra hne
  have hpxy : Noncollinear p x y :=
    noncollinear_off_common_line hab hne (hA x hx) (hA y hy) hoff
  have hyline : y ∈ lineBlock P p x := by
    change lineBlock P p x = lineBlock P p y at hxy
    rw [hxy]
    exact right_mem_lineBlock (hAP hy)
  exact hpxy (mem_lineBlock.mp hyline).2

lemma card_inter_crossLines_le_one
    {P A : Finset Point} {p q : Point}
    (hAP : A ⊆ P) (hp : p ∈ P) (hq : q ∈ P)
    (hpA : p ∉ A) (hqA : q ∉ A) (hpq : p ≠ q) :
    (crossLines P A p ∩ crossLines P A q).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro L hL M hM
  rw [Finset.mem_inter, mem_crossLines, mem_crossLines] at hL hM
  have hLconn : L ∈ connectingLines P :=
    crossLines_subset_connectingLines hAP hp hpA (mem_crossLines.mpr hL.1)
  have hMconn : M ∈ connectingLines P :=
    crossLines_subset_connectingLines hAP hp hpA (mem_crossLines.mpr hM.1)
  obtain ⟨⟨x, hx, hLx⟩, y, hy, hLy⟩ := hL
  obtain ⟨⟨u, hu, hMu⟩, v, hv, hMv⟩ := hM
  have hLp : p ∈ L := by rw [hLx]; exact left_mem_lineBlock hp
  have hLq : q ∈ L := by rw [hLy]; exact left_mem_lineBlock hq
  have hMp : p ∈ M := by rw [hMu]; exact left_mem_lineBlock hp
  have hMq : q ∈ M := by rw [hMv]; exact left_mem_lineBlock hq
  exact connectingLine_eq_of_two_mem
    hLconn hMconn
    hpq hLp hLq hMp hMq

/-- All connecting lines joining one of the points of `Q` to `A`. -/
noncomputable def crossLineUnion (P Q A : Finset Point) :
    Finset (Finset Point) := by
  classical
  exact Q.biUnion fun p ↦ crossLines P A p

lemma crossLineUnion_subset_connectingLines
    {P Q A : Finset Point} (hAP : A ⊆ P) (hQP : Q ⊆ P)
    (hdisj : Disjoint Q A) :
    crossLineUnion P Q A ⊆ connectingLines P := by
  intro L hL
  rw [crossLineUnion, Finset.mem_biUnion] at hL
  obtain ⟨p, hpQ, hpL⟩ := hL
  exact crossLines_subset_connectingLines hAP (hQP hpQ)
    (Finset.disjoint_left.mp hdisj hpQ) hpL

/-- Bonferroni's estimate for the cross-lines from an off-line set to a
collinear block. -/
lemma crossLineUnion_bound
    {P Q A : Finset Point} {a b : Point}
    (hAP : A ⊆ P) (hQP : Q ⊆ P) (hdisj : Disjoint Q A)
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hQ : ∀ p ∈ Q, Noncollinear a b p) :
    2 * (Q.card * A.card) ≤
      2 * (crossLineUnion P Q A).card + Q.card * (Q.card - 1) := by
  classical
  have hinter : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q →
      (crossLines P A p ∩ crossLines P A q).card ≤ 1 := by
    intro p hp q hq hpq
    exact card_inter_crossLines_le_one hAP (hQP hp) (hQP hq)
      (Finset.disjoint_left.mp hdisj hp)
      (Finset.disjoint_left.mp hdisj hq) hpq
  have hbon := two_mul_sum_card_le_two_mul_union_add_pair_bound
    Q (fun p ↦ crossLines P A p) 1 hinter
  have hsum : ∑ p ∈ Q, (crossLines P A p).card = Q.card * A.card := by
    calc
      _ = ∑ _p ∈ Q, A.card := by
        apply Finset.sum_congr rfl
        intro p hp
        exact card_crossLines_on_common_line hAP (hQP hp) hab hA (hQ p hp)
      _ = _ := by simp
  simpa only [hsum, crossLineUnion, mul_one] using hbon

/-- Lines through `p`, with one specified line removed. -/
noncomputable def linesThroughExcept (P : Finset Point) (p : Point)
    (L : Finset Point) : Finset (Finset Point) := by
  classical
  exact (linesThrough P p).erase L

lemma mem_linesThroughExcept {P : Finset Point} {p : Point}
    {L M : Finset Point} :
    M ∈ linesThroughExcept P p L ↔
      M ∈ connectingLines P ∧ p ∈ M ∧ M ≠ L := by
  classical
  simp only [linesThroughExcept, Finset.mem_erase, mem_linesThrough]
  tauto

lemma card_linesThroughExcept {P : Finset Point} {p : Point}
    {L : Finset Point} (hL : L ∈ linesThrough P p) :
    (linesThroughExcept P p L).card = pointDegree P p - 1 := by
  classical
  rw [linesThroughExcept, Finset.card_erase_of_mem hL, card_linesThrough]

/-- Two low-degree points force their joining line to contain all but at most
`(d(x)-1)(d(y)-1)` points. -/
lemma card_off_line_le_degree_product
    {P Q : Finset Point} {x y : Point}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y)
    (hQ : Q = P \ lineBlock P x y) :
    Q.card ≤ (pointDegree P x - 1) * (pointDegree P y - 1) := by
  classical
  subst Q
  let L := lineBlock P x y
  have hLconn : L ∈ connectingLines P := lineBlock_mem_connectingLines hx hy hxy
  have hxL : x ∈ L := left_mem_lineBlock hx
  have hyL : y ∈ L := right_mem_lineBlock hy
  have hLx : L ∈ linesThrough P x := mem_linesThrough.mpr ⟨hLconn, hxL⟩
  have hLy : L ∈ linesThrough P y := mem_linesThrough.mpr ⟨hLconn, hyL⟩
  let X := linesThroughExcept P x L
  let Y := linesThroughExcept P y L
  let f : {q // q ∈ P \ lineBlock P x y} → {z // z ∈ X ×ˢ Y} := fun q ↦ by
    have hqmem := q.2
    have hqP : q.1 ∈ P := by
      exact (Finset.mem_sdiff.mp hqmem).1
    have hqL : q.1 ∉ L := by
      exact (Finset.mem_sdiff.mp hqmem).2
    have hxq : x ≠ q.1 := fun h ↦ hqL (h ▸ hxL)
    have hyq : y ≠ q.1 := fun h ↦ hqL (h ▸ hyL)
    refine ⟨(lineBlock P x q.1, lineBlock P y q.1), ?_⟩
    rw [Finset.mem_product]
    constructor
    · rw [mem_linesThroughExcept]
      refine ⟨lineBlock_mem_connectingLines hx hqP hxq,
        left_mem_lineBlock hx, ?_⟩
      intro heq
      exact hqL (heq ▸ right_mem_lineBlock hqP)
    · rw [mem_linesThroughExcept]
      refine ⟨lineBlock_mem_connectingLines hy hqP hyq,
        left_mem_lineBlock hy, ?_⟩
      intro heq
      exact hqL (heq ▸ right_mem_lineBlock hqP)
  have hf : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    have hpair := congrArg Subtype.val hqr
    dsimp [f] at hpair
    have hfirst : lineBlock P x q.1 = lineBlock P x r.1 := by
      simpa using congrArg Prod.fst hpair
    have hsecond : lineBlock P y q.1 = lineBlock P y r.1 := by
      simpa using congrArg Prod.snd hpair
    by_contra hne
    have hqmem := q.2
    have hrmem := r.2
    have hqP : q.1 ∈ P := by
      exact (Finset.mem_sdiff.mp hqmem).1
    have hrP : r.1 ∈ P := by
      exact (Finset.mem_sdiff.mp hrmem).1
    have hqL : q.1 ∉ L := by
      exact (Finset.mem_sdiff.mp hqmem).2
    have hxq : x ≠ q.1 := fun h ↦ hqL (h ▸ hxL)
    let M := lineBlock P x q.1
    let N := lineBlock P y q.1
    have hMconn : M ∈ connectingLines P := lineBlock_mem_connectingLines hx hqP hxq
    have hyq : y ≠ q.1 := fun h ↦ hqL (h ▸ hyL)
    have hNconn : N ∈ connectingLines P := lineBlock_mem_connectingLines hy hqP hyq
    have hqM : q.1 ∈ M := right_mem_lineBlock hqP
    have hrM : r.1 ∈ M := by
      dsimp [M]
      rw [hfirst]
      exact right_mem_lineBlock hrP
    have hqN : q.1 ∈ N := right_mem_lineBlock hqP
    have hrN : r.1 ∈ N := by
      dsimp [N]
      rw [hsecond]
      exact right_mem_lineBlock hrP
    have hMN : M = N :=
      connectingLine_eq_of_two_mem hMconn hNconn hne hqM hrM hqN hrN
    have hyM : y ∈ M := by rw [hMN]; exact left_mem_lineBlock hy
    have hLM : L = M :=
      connectingLine_eq_of_two_mem hLconn hMconn hxy hxL hyL
        (left_mem_lineBlock hx) hyM
    exact hqL (hLM ▸ hqM)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe, Fintype.card_coe, Finset.card_product,
    show X.card = pointDegree P x - 1 by
      exact card_linesThroughExcept hLx,
    show Y.card = pointDegree P y - 1 by
      exact card_linesThroughExcept hLy] at hcard
  exact hcard

/-- The line itself and all cross-lines give this explicit lower bound for
the number of connecting lines. -/
lemma connectingLines_lower_of_lineBlock
    {P Q : Finset Point} {a b : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b)
    (hQ : Q = P \ lineBlock P a b) :
    1 + Q.card * (lineBlock P a b).card - Nat.choose Q.card 2 ≤
      (connectingLines P).card := by
  classical
  let A := lineBlock P a b
  have hAP : A ⊆ P := lineBlock_subset P a b
  have hQP : Q ⊆ P := by
    rw [hQ]
    exact Finset.sdiff_subset
  have hdisj : Disjoint Q A := by
    rw [Finset.disjoint_left]
    intro p hpQ hpA
    have hpQ' := hpQ
    rw [hQ, Finset.mem_sdiff] at hpQ'
    exact hpQ'.2 hpA
  have hA : ∀ x ∈ A, Collinear a b x := fun x hx ↦ (mem_lineBlock.mp hx).2
  have hQoff : ∀ p ∈ Q, Noncollinear a b p := by
    intro p hp
    have hp' := hp
    rw [hQ, Finset.mem_sdiff] at hp'
    intro hcol
    exact hp'.2 (mem_lineBlock.mpr ⟨hp'.1, hcol⟩)
  have hcross := crossLineUnion_bound hAP hQP hdisj hab hA hQoff
  have hchoose := two_mul_choose_two Q.card
  have hunion : Q.card * A.card - Nat.choose Q.card 2 ≤
      (crossLineUnion P Q A).card := by omega
  have hLconn : A ∈ connectingLines P := lineBlock_mem_connectingLines ha hb hab
  have hLnot : A ∉ crossLineUnion P Q A := by
    intro hL
    rw [crossLineUnion, Finset.mem_biUnion] at hL
    obtain ⟨p, hpQ, hpL⟩ := hL
    rw [mem_crossLines] at hpL
    obtain ⟨x, hxA, hEq⟩ := hpL
    have hpCross : p ∈ lineBlock P p x := left_mem_lineBlock (hQP hpQ)
    have hpA : p ∈ A := by rw [hEq]; exact hpCross
    exact hQoff p hpQ (mem_lineBlock.mp hpA).2
  have hsub : insert A (crossLineUnion P Q A) ⊆ connectingLines P := by
    intro L hL
    simp only [Finset.mem_insert] at hL
    rcases hL with rfl | hL
    · exact hLconn
    · exact crossLineUnion_subset_connectingLines hAP hQP hdisj hL
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hLnot] at hcard
  dsimp [A] at hunion hcard ⊢
  omega

lemma six_mul_sub_fifty_le_line_expression
    {N s m : ℕ} (hN : N = m + s) (hNlarge : 393 ≤ N)
    (hs6 : 6 ≤ s) (hs256 : s ≤ 256) :
    6 * N - 50 ≤ 1 + s * m - Nat.choose s 2 := by
  have hchoose := two_mul_choose_two s
  have hm : 137 ≤ m := by omega
  have hs_sub : s - 6 + 6 = s := by omega
  have hm_sub : 2 * m - s - 17 + s + 17 = 2 * m := by omega
  have hs_one : s - 1 + 1 = s := by omega
  have hid :
      2 * (51 + s * m) =
        2 * (6 * N + Nat.choose s 2) +
          (s - 6) * (2 * m - s - 17) := by
    nlinarith
  have hraw : 6 * N + Nat.choose s 2 ≤ 51 + s * m := by
    omega
  omega

/-- Kelly and Moser's specialization at `k = 6`.  The only geometric input
is Melchior's defect inequality, supplied explicitly as `hM`. -/
lemma kellyMoser_six_of_lineDefect
    {P : Finset Point} (hN : 393 ≤ P.card)
    (hP : ¬ ContainedInLine P)
    (hmax : ∀ L ∈ connectingLines P, L.card ≤ P.card - 6)
    (hM : (3 : ℤ) ≤ lineDefect P) :
    6 * P.card - 50 ≤ (connectingLines P).card := by
  classical
  by_cases hlow : ∃ x ∈ P, ∃ y ∈ P,
      x ≠ y ∧ pointDegree P x ≤ 17 ∧ pointDegree P y ≤ 17
  · obtain ⟨x, hx, y, hy, hxy, hdx, hdy⟩ := hlow
    let L := lineBlock P x y
    let Q := P \ L
    have hLconn : L ∈ connectingLines P := lineBlock_mem_connectingLines hx hy hxy
    have hLcard : L.card ≤ P.card - 6 := hmax L hLconn
    have hQcard : Q.card = P.card - L.card := by
      dsimp [Q]
      rw [Finset.card_sdiff_of_subset (lineBlock_subset P x y)]
    have hsumcard : P.card = L.card + Q.card := by omega
    have hQdegree : Q.card ≤
        (pointDegree P x - 1) * (pointDegree P y - 1) := by
      exact card_off_line_le_degree_product hx hy hxy rfl
    have hdx16 : pointDegree P x - 1 ≤ 16 := by omega
    have hdy16 : pointDegree P y - 1 ≤ 16 := by omega
    have hQ256 : Q.card ≤ 256 := by
      exact hQdegree.trans (by
        simpa using Nat.mul_le_mul hdx16 hdy16)
    have hQ6 : 6 ≤ Q.card := by omega
    have hnum : 6 * P.card - 50 ≤
        1 + Q.card * L.card - Nat.choose Q.card 2 :=
      six_mul_sub_fifty_le_line_expression hsumcard hN hQ6 hQ256
    exact hnum.trans (connectingLines_lower_of_lineBlock hx hy hxy rfl)
  · have hincZ := three_mul_line_count_ge_incidence_of_lineDefect P hM
    have hinc : 3 + ∑ p ∈ P, pointDegree P p ≤
        3 * (connectingLines P).card := by
      rw [sum_pointDegree]
      exact_mod_cast hincZ
    have hsum : 18 * P.card - 16 ≤ ∑ p ∈ P, pointDegree P p := by
      by_cases hex : ∃ p ∈ P, pointDegree P p ≤ 17
      · obtain ⟨p, hp, hdp⟩ := hex
        have hother : ∀ q ∈ P.erase p, 18 ≤ pointDegree P q := by
          intro q hq
          have hqP := (Finset.mem_erase.mp hq).2
          have hqp := (Finset.mem_erase.mp hq).1
          by_contra hdeg
          have hdeg' : pointDegree P q ≤ 17 := by omega
          exact hlow ⟨p, hp, q, hqP, Ne.symm hqp, hdp, hdeg'⟩
        have herase : 18 * (P.erase p).card ≤
            ∑ q ∈ P.erase p, pointDegree P q := by
          calc
            _ = ∑ _q ∈ P.erase p, 18 := by simp [mul_comm]
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro q hq
              exact hother q hq
        have hpdeg := two_le_pointDegree_of_not_contained hP hp
        have hdecomp := P.sum_erase_add (fun q ↦ pointDegree P q) hp
        have hcarderase := Finset.card_erase_of_mem hp
        omega
      · push_neg at hex
        have hall : ∀ p ∈ P, 18 ≤ pointDegree P p := by
          intro p hp
          have := hex p hp
          omega
        calc
          18 * P.card - 16 ≤ 18 * P.card := Nat.sub_le _ _
          _ = ∑ _p ∈ P, 18 := by simp [mul_comm]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro p hp
            exact hall p hp
    omega

/-! ## Inversion about a point -/

/-- Squared distance from `p` to `x`, in coordinates. -/
def distSq (p x : Point) : ℝ :=
  (x.1 - p.1) ^ 2 + (x.2 - p.2) ^ 2

lemma distSq_pos {p x : Point} (hpx : x ≠ p) : 0 < distSq p x := by
  have h₁ : 0 ≤ (x.1 - p.1) ^ 2 := sq_nonneg _
  have h₂ : 0 ≤ (x.2 - p.2) ^ 2 := sq_nonneg _
  rw [distSq]
  by_contra h
  have hz₁ : x.1 - p.1 = 0 := by nlinarith
  have hz₂ : x.2 - p.2 = 0 := by nlinarith
  apply hpx
  apply Prod.ext <;> linarith

lemma distSq_ne_zero {p x : Point} (hpx : x ≠ p) : distSq p x ≠ 0 :=
  ne_of_gt (distSq_pos hpx)

/-- Euclidean inversion in the unit circle centered at `p`.  Its value at the
center is immaterial; all uses below explicitly exclude the center. -/
noncomputable def pointInversion (p x : Point) : Point :=
  (p.1 + (x.1 - p.1) / distSq p x,
    p.2 + (x.2 - p.2) / distSq p x)

lemma pointInversion_ne_center {p x : Point} (hpx : x ≠ p) :
    pointInversion p x ≠ p := by
  intro h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have hd := distSq_ne_zero hpx
  simp only [pointInversion] at h₁ h₂
  have hx₁ : x.1 - p.1 = 0 := by
    apply (div_eq_zero_iff).mp (by linarith : (x.1 - p.1) / distSq p x = 0) |>.resolve_right hd
  have hx₂ : x.2 - p.2 = 0 := by
    apply (div_eq_zero_iff).mp (by linarith : (x.2 - p.2) / distSq p x = 0) |>.resolve_right hd
  apply hpx
  apply Prod.ext <;> linarith

lemma pointInversion_involutive {p x : Point} (hpx : x ≠ p) :
    pointInversion p (pointInversion p x) = x := by
  have hd := distSq_ne_zero hpx
  have hdval : distSq p (pointInversion p x) = (distSq p x)⁻¹ := by
    calc
      distSq p (pointInversion p x) =
          ((x.1 - p.1) / distSq p x) ^ 2 +
            ((x.2 - p.2) / distSq p x) ^ 2 := by
              simp only [distSq, pointInversion, Prod.fst, Prod.snd]
              ring
      _ = ((x.1 - p.1) ^ 2 + (x.2 - p.2) ^ 2) /
          (distSq p x) ^ 2 := by ring
      _ = distSq p x / (distSq p x) ^ 2 := by rw [distSq]
      _ = (distSq p x)⁻¹ := by field_simp [hd]
  apply Prod.ext
  · change p.1 + ((pointInversion p x).1 - p.1) /
        distSq p (pointInversion p x) = x.1
    rw [hdval]
    simp only [pointInversion, Prod.fst]
    field_simp [hd]
    ring
  · change p.2 + ((pointInversion p x).2 - p.2) /
        distSq p (pointInversion p x) = x.2
    rw [hdval]
    simp only [pointInversion, Prod.snd]
    field_simp [hd]
    ring

lemma pointInversion_injective_off (p : Point) :
    Set.InjOn (pointInversion p) {x | x ≠ p} := by
  intro x hx y hy hxy
  have := congrArg (pointInversion p) hxy
  simpa [pointInversion_involutive hx, pointInversion_involutive hy] using this

/-- Inverted copy of `P \ {p}`. -/
noncomputable def invertedPoints (P : Finset Point) (p : Point) : Finset Point := by
  classical
  exact (P.erase p).image (pointInversion p)

lemma mem_invertedPoints {P : Finset Point} {p y : Point} :
    y ∈ invertedPoints P p ↔
      ∃ x ∈ P, x ≠ p ∧ pointInversion p x = y := by
  classical
  constructor
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    rw [Finset.mem_erase] at hx
    exact ⟨x, hx.2, hx.1, rfl⟩
  · rintro ⟨x, hx, hxp, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxp, hx⟩, rfl⟩

lemma card_invertedPoints {P : Finset Point} {p : Point} (hp : p ∈ P) :
    (invertedPoints P p).card = P.card - 1 := by
  classical
  rw [invertedPoints, Finset.card_image_iff.mpr]
  · exact Finset.card_erase_of_mem hp
  · intro x hx y hy hxy
    apply pointInversion_injective_off p
    · exact Finset.mem_erase.mp hx |>.1
    · exact Finset.mem_erase.mp hy |>.1
    · exact hxy

/-- Two distinct points satisfying the same nonconstant affine equation with
constant term `1` cut out exactly their connecting line. -/
lemma collinear_iff_centered_affine_one
    {a b c o : Point} {A B : ℝ} (hab : a ≠ b)
    (ha : 1 + A * (a.1 - o.1) + B * (a.2 - o.2) = 0)
    (hb : 1 + A * (b.1 - o.1) + B * (b.2 - o.2) = 0) :
    Collinear a b c ↔
      1 + A * (c.1 - o.1) + B * (c.2 - o.2) = 0 := by
  have habEq : A * (b.1 - a.1) + B * (b.2 - a.2) = 0 := by
    linarith
  constructor
  · intro hc
    have hdet :
        (b.1 - a.1) * (c.2 - a.2) -
          (b.2 - a.2) * (c.1 - a.1) = 0 := hc
    by_cases hdx : b.1 - a.1 = 0
    · have hdy : b.2 - a.2 ≠ 0 := by
        intro hdy
        apply hab
        apply Prod.ext <;> linarith
      have hB : B = 0 := by
        rw [hdx, mul_zero, zero_add] at habEq
        exact (mul_eq_zero.mp habEq).resolve_right hdy
      have hcx : c.1 = a.1 := by
        have hprod : (b.2 - a.2) * (c.1 - a.1) = 0 := by
          rw [hdx, zero_mul, zero_sub] at hdet
          exact neg_eq_zero.mp hdet
        exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hdy)
      simpa [hB, hcx] using ha
    · have hscaled :
          (A * (c.1 - a.1) + B * (c.2 - a.2)) *
              (b.1 - a.1) = 0 := by
        calc
          _ = (c.1 - a.1) *
              (A * (b.1 - a.1) + B * (b.2 - a.2)) +
              B * ((b.1 - a.1) * (c.2 - a.2) -
                (b.2 - a.2) * (c.1 - a.1)) := by ring
          _ = 0 := by rw [habEq, hdet]; ring
      have hzero : A * (c.1 - a.1) + B * (c.2 - a.2) = 0 :=
        (mul_eq_zero.mp hscaled).resolve_right hdx
      linarith
  · intro hc
    have hacEq : A * (c.1 - a.1) + B * (c.2 - a.2) = 0 := by
      linarith
    have hnormal : A ≠ 0 ∨ B ≠ 0 := by
      by_contra h
      push_neg at h
      rw [h.1, h.2] at ha
      norm_num at ha
    rw [Collinear, det]
    rcases hnormal with hA | hB
    · apply (mul_eq_zero.mp ?_).resolve_left hA
      calc
        A * ((b.1 - a.1) * (c.2 - a.2) -
            (b.2 - a.2) * (c.1 - a.1)) =
          (c.2 - a.2) *
              (A * (b.1 - a.1) + B * (b.2 - a.2)) -
            (b.2 - a.2) *
              (A * (c.1 - a.1) + B * (c.2 - a.2)) := by ring
        _ = 0 := by rw [habEq, hacEq]; ring
    · apply (mul_eq_zero.mp ?_).resolve_left hB
      calc
        B * ((b.1 - a.1) * (c.2 - a.2) -
            (b.2 - a.2) * (c.1 - a.1)) =
          (b.1 - a.1) *
              (A * (c.1 - a.1) + B * (c.2 - a.2)) -
            (c.1 - a.1) *
              (A * (b.1 - a.1) + B * (b.2 - a.2)) := by ring
        _ = 0 := by rw [habEq, hacEq]; ring

/-- A circle through the inversion center becomes an affine line under
inversion. -/
lemma inversionLine_iff_onCircle
    {C : Circle} {p x : Point} (hpC : OnCircle C p) (hxp : x ≠ p) :
    1 + (2 * p.1 + C.u) * ((pointInversion p x).1 - p.1) +
        (2 * p.2 + C.v) * ((pointInversion p x).2 - p.2) = 0 ↔
      OnCircle C x := by
  have hd := distSq_ne_zero hxp
  simp only [pointInversion, sub_eq_add_neg, OnCircle, normSq, distSq,
    Prod.fst, Prod.snd] at hpC hd ⊢
  field_simp [hd]
  constructor <;> intro h <;> nlinarith [sq_nonneg (x.1 - p.1), sq_nonneg (x.2 - p.2)]

/-- Three points other than the center are concyclic with the center exactly
when their inverses are collinear. -/
lemma collinear_inversions_iff_onCircle
    {p x y z : Point} (hxp : x ≠ p) (hyp : y ≠ p) (hzp : z ≠ p)
    (hnc : Noncollinear p x y) :
    Collinear (pointInversion p x) (pointInversion p y) (pointInversion p z) ↔
      OnCircle (circleThrough p x y) z := by
  let C := circleThrough p x y
  have hxy : x ≠ y := noncollinear_ne_last hnc
  have hinvxy : pointInversion p x ≠ pointInversion p y := by
    intro h
    exact hxy (pointInversion_injective_off p hxp hyp h)
  have hpC : OnCircle C p := circleThrough_on_left p x y
  have hxC : OnCircle C x := circleThrough_on_middle hnc
  have hyC : OnCircle C y := circleThrough_on_right hnc
  have hxline :
      1 + (2 * p.1 + C.u) * ((pointInversion p x).1 - p.1) +
          (2 * p.2 + C.v) * ((pointInversion p x).2 - p.2) = 0 :=
    (inversionLine_iff_onCircle hpC hxp).2 hxC
  have hyline :
      1 + (2 * p.1 + C.u) * ((pointInversion p y).1 - p.1) +
          (2 * p.2 + C.v) * ((pointInversion p y).2 - p.2) = 0 :=
    (inversionLine_iff_onCircle hpC hyp).2 hyC
  rw [collinear_iff_centered_affine_one hinvxy hxline hyline]
  exact inversionLine_iff_onCircle hpC hzp

/-- Inversion preserves every line through its center. -/
lemma collinear_center_inversions_iff
    {p x y : Point} (hxp : x ≠ p) (hyp : y ≠ p) :
    Collinear p (pointInversion p x) (pointInversion p y) ↔
      Collinear p x y := by
  have hdx := distSq_ne_zero hxp
  have hdy := distSq_ne_zero hyp
  simp only [Collinear, det, pointInversion, Prod.fst, Prod.snd]
  field_simp [hdx, hdy]
  constructor <;> intro h <;> nlinarith

lemma noncollinear_center_inversions_iff
    {p x y : Point} (hxp : x ≠ p) (hyp : y ≠ p) :
    Noncollinear p (pointInversion p x) (pointInversion p y) ↔
      Noncollinear p x y := by
  exact not_congr (collinear_center_inversions_iff hxp hyp)

lemma center_not_mem_invertedPoints {P : Finset Point} {p : Point} :
    p ∉ invertedPoints P p := by
  intro hp
  rw [mem_invertedPoints] at hp
  obtain ⟨x, hxP, hxp, hx⟩ := hp
  exact pointInversion_ne_center hxp hx

lemma pointInversion_mem_original_of_mem_inverted
    {P : Finset Point} {p y : Point} (hy : y ∈ invertedPoints P p) :
    pointInversion p y ∈ P ∧ pointInversion p y ≠ p := by
  rw [mem_invertedPoints] at hy
  obtain ⟨x, hxP, hxp, rfl⟩ := hy
  rw [pointInversion_involutive hxp]
  exact ⟨hxP, hxp⟩

/-- A packaged deterministic pair of distinct points on a connecting line. -/
structure ChosenLinePair (L : Finset Point) where
  left : Point
  left_mem : left ∈ L
  right : Point
  right_mem : right ∈ L
  left_ne_right : left ≠ right

noncomputable def chosenLinePair {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) : ChosenLinePair L.1 := by
  have hcard : 1 < L.1.card := by
    have htwo := connectingLine_card_two_le L.2
    omega
  let hpair := Finset.one_lt_card.mp hcard
  let a := Classical.choose hpair
  have ha : a ∈ L.1 := (Classical.choose_spec hpair).1
  let hright := (Classical.choose_spec hpair).2
  let b := Classical.choose hright
  have hb : b ∈ L.1 := (Classical.choose_spec hright).1
  have hab : a ≠ b := (Classical.choose_spec hright).2
  exact ⟨a, ha, b, hb, hab⟩

/-- A deterministic pair of distinct points on a connecting line. -/
noncomputable def chosenLineFirst {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) : Point :=
  (chosenLinePair L).left

noncomputable def chosenLineSecond {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) : Point :=
  (chosenLinePair L).right

lemma chosenLineFirst_mem {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) : chosenLineFirst L ∈ L.1 :=
  (chosenLinePair L).left_mem

lemma chosenLineSecond_mem {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) : chosenLineSecond L ∈ L.1 :=
  (chosenLinePair L).right_mem

lemma chosenLineFirst_ne_second {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) :
    chosenLineFirst L ≠ chosenLineSecond L :=
  (chosenLinePair L).left_ne_right

lemma chosenLineFirst_mem_points {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) : chosenLineFirst L ∈ P :=
  connectingLine_subset L.2 (chosenLineFirst_mem L)

lemma chosenLineSecond_mem_points {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) : chosenLineSecond L ∈ P :=
  connectingLine_subset L.2 (chosenLineSecond_mem L)

lemma lineBlock_chosenLine_eq {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) :
    lineBlock P (chosenLineFirst L) (chosenLineSecond L) = L.1 := by
  have hblock : lineBlock P (chosenLineFirst L) (chosenLineSecond L) ∈
      connectingLines P :=
    lineBlock_mem_connectingLines (chosenLineFirst_mem_points L)
      (chosenLineSecond_mem_points L) (chosenLineFirst_ne_second L)
  exact connectingLine_eq_of_two_mem hblock L.2 (chosenLineFirst_ne_second L)
    (left_mem_lineBlock (chosenLineFirst_mem_points L))
    (right_mem_lineBlock (chosenLineSecond_mem_points L))
    (chosenLineFirst_mem L) (chosenLineSecond_mem L)

lemma chosenLine_collinear_of_mem {P : Finset Point}
    (L : {L // L ∈ connectingLines P}) {x : Point} (hx : x ∈ L.1) :
    Collinear (chosenLineFirst L) (chosenLineSecond L) x := by
  have hx' : x ∈ lineBlock P (chosenLineFirst L) (chosenLineSecond L) := by
    rw [lineBlock_chosenLine_eq L]
    exact hx
  exact (mem_lineBlock.mp hx').2

noncomputable def dualEventPoint {P : Finset Point} (t : ℝ)
    (L : {L // L ∈ connectingLines P}) : Point :=
  let x := dualMeetX t (chosenLineFirst L) (chosenLineSecond L)
  (x, dualHeight t (chosenLineFirst L) x)

lemma dualEventPoint_on_wire {P : Finset Point} {t : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (L : {L // L ∈ connectingLines P}) {z : Point} (hz : z ∈ L.1) :
    dualHeight t z (dualEventPoint t L).1 = (dualEventPoint t L).2 := by
  have hab : sweepSlope t (chosenLineFirst L) ≠
      sweepSlope t (chosenLineSecond L) := by
    exact fun h ↦ chosenLineFirst_ne_second L
      (ht (chosenLineFirst_mem_points L) (chosenLineSecond_mem_points L) h)
  rw [dualEventPoint]
  dsimp only
  exact (dualHeight_dualMeetX_eq_iff_collinear hab).2
    (chosenLine_collinear_of_mem L hz)

lemma dualEventPoint_injective {P : Finset Point} {t : ℝ}
    (ht : Set.InjOn (sweepSlope t) P) :
    Function.Injective (dualEventPoint (P := P) t) := by
  intro L M hLM
  apply Subtype.ext
  apply Finset.Subset.antisymm
  · intro z hzL
    have hzP : z ∈ P := connectingLine_subset L.2 hzL
    have hwireL := dualEventPoint_on_wire ht L hzL
    have hwireM : dualHeight t z (dualEventPoint t M).1 =
        (dualEventPoint t M).2 := by simpa only [hLM] using hwireL
    have habM : sweepSlope t (chosenLineFirst M) ≠
        sweepSlope t (chosenLineSecond M) := by
      exact fun h ↦ chosenLineFirst_ne_second M
        (ht (chosenLineFirst_mem_points M) (chosenLineSecond_mem_points M) h)
    have hcolM : Collinear (chosenLineFirst M) (chosenLineSecond M) z := by
      rw [dualEventPoint] at hwireM
      dsimp only at hwireM
      exact (dualHeight_dualMeetX_eq_iff_collinear habM).1 hwireM
    rw [← lineBlock_chosenLine_eq M, mem_lineBlock]
    exact ⟨hzP, hcolM⟩
  · intro z hzM
    have hzP : z ∈ P := connectingLine_subset M.2 hzM
    have hwireM := dualEventPoint_on_wire ht M hzM
    have hwireL : dualHeight t z (dualEventPoint t L).1 =
        (dualEventPoint t L).2 := by simpa only [hLM] using hwireM
    have habL : sweepSlope t (chosenLineFirst L) ≠
        sweepSlope t (chosenLineSecond L) := by
      exact fun h ↦ chosenLineFirst_ne_second L
        (ht (chosenLineFirst_mem_points L) (chosenLineSecond_mem_points L) h)
    have hcolL : Collinear (chosenLineFirst L) (chosenLineSecond L) z := by
      rw [dualEventPoint] at hwireL
      dsimp only at hwireL
      exact (dualHeight_dualMeetX_eq_iff_collinear habL).1 hwireL
    rw [← lineBlock_chosenLine_eq L, mem_lineBlock]
    exact ⟨hzP, hcolL⟩

noncomputable def dualEventPoints (P : Finset Point) (t : ℝ) : Finset Point := by
  classical
  exact (connectingLines P).attach.image (dualEventPoint t)

lemma mem_dualEventPoints {P : Finset Point} {t : ℝ} {v : Point} :
    v ∈ dualEventPoints P t ↔
      ∃ L : {L // L ∈ connectingLines P}, dualEventPoint t L = v := by
  classical
  simp [dualEventPoints]

noncomputable def dualDenominatorBad (P : Finset Point) (t : ℝ) : Finset ℝ := by
  classical
  exact (P.filter fun p ↦ sweepSlope t p ≠ 0).image fun p ↦
    -1 / sweepSlope t p

lemma one_add_mul_sweepSlope_ne_zero_of_not_mem_bad
    {P : Finset Point} {t a : ℝ} (ha : a ∉ dualDenominatorBad P t)
    {p : Point} (hp : p ∈ P) : 1 + a * sweepSlope t p ≠ 0 := by
  intro hzero
  by_cases hm : sweepSlope t p = 0
  · simp [hm] at hzero
  · apply ha
    rw [dualDenominatorBad, Finset.mem_image]
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, hm⟩, ?_⟩
    have hmul : a * sweepSlope t p = -1 := by linarith
    exact (div_eq_iff hm).2 (by nlinarith)

lemma exists_generic_dual_sweep (P : Finset Point) :
    ∃ t a : ℝ,
      Set.InjOn (sweepSlope t) P ∧
      Set.InjOn (sweepSlope a) (dualEventPoints P t) ∧
      ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0 := by
  classical
  obtain ⟨t, ht⟩ := exists_sweepSlope_injOn P
  obtain ⟨a, ha, habad⟩ :=
    exists_sweepSlope_injOn_avoiding (dualEventPoints P t) (dualDenominatorBad P t)
  exact ⟨t, a, ht, ha,
    fun p hp ↦ one_add_mul_sweepSlope_ne_zero_of_not_mem_bad habad hp⟩

noncomputable def sweptDualSlope (t a : ℝ) (p : Point) : ℝ :=
  sweepSlope t p / (1 + a * sweepSlope t p)

noncomputable def sweptDualIntercept (t a : ℝ) (p : Point) : ℝ :=
  -p.2 / (1 + a * sweepSlope t p)

noncomputable def sweptDualHeight (t a : ℝ) (p : Point) (s : ℝ) : ℝ :=
  sweptDualSlope t a p * s + sweptDualIntercept t a p

noncomputable def dualEventCoord {P : Finset Point} (t a : ℝ)
    (L : {L // L ∈ connectingLines P}) : ℝ :=
  sweepSlope a (dualEventPoint t L)

lemma sweptDualSlope_injOn {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0) :
    Set.InjOn (sweptDualSlope t a) P := by
  intro p hp q hq hpq
  have hdp := hden p hp
  have hdq := hden q hq
  simp only [sweptDualSlope] at hpq
  have hcross := (div_eq_div_iff hdp hdq).1 hpq
  have hm : sweepSlope t p = sweepSlope t q := by
    ring_nf at hcross
    linarith
  exact ht hp hq hm

lemma dualEventCoord_injective {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (ha : Set.InjOn (sweepSlope a) (dualEventPoints P t)) :
    Function.Injective (dualEventCoord (P := P) t a) := by
  intro L M hLM
  apply dualEventPoint_injective ht
  apply ha
  · exact mem_dualEventPoints.mpr ⟨L, rfl⟩
  · exact mem_dualEventPoints.mpr ⟨M, rfl⟩
  · exact hLM

lemma sweptDualHeight_at_event {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P}) {p : Point} (hp : p ∈ L.1) :
    sweptDualHeight t a p (dualEventCoord t a L) =
      (dualEventPoint t L).2 := by
  have hpP : p ∈ P := connectingLine_subset L.2 hp
  have hdp := hden p hpP
  have hwire := dualEventPoint_on_wire ht L hp
  -- Work directly with the original dual incidence equation at the event.
  rw [sweptDualHeight, sweptDualSlope, sweptDualIntercept]
  rw [div_mul_eq_mul_div, ← add_div]
  apply (div_eq_iff hdp).2
  simp only [dualEventCoord, sweepSlope, dualHeight] at hwire ⊢
  ring_nf at hwire ⊢
  nlinarith

lemma sweptDualHeight_at_projected_point_iff {t a : ℝ} {p v : Point}
    (hden : 1 + a * sweepSlope t p ≠ 0) :
    sweptDualHeight t a p (sweepSlope a v) = v.2 ↔
      dualHeight t p v.1 = v.2 := by
  rw [sweptDualHeight, sweptDualSlope, sweptDualIntercept]
  rw [div_mul_eq_mul_div, ← add_div, div_eq_iff hden]
  simp only [sweepSlope, dualHeight]
  constructor <;> intro h <;> nlinarith

lemma sweptDualHeight_event_eq_iff_mem {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P}) {p : Point} (hp : p ∈ P) :
    sweptDualHeight t a p (dualEventCoord t a L) =
        (dualEventPoint t L).2 ↔ p ∈ L.1 := by
  constructor
  · intro heq
    have hwire : dualHeight t p (dualEventPoint t L).1 =
        (dualEventPoint t L).2 := by
      exact (sweptDualHeight_at_projected_point_iff (hden p hp)).1 heq
    have hab : sweepSlope t (chosenLineFirst L) ≠
        sweepSlope t (chosenLineSecond L) := by
      exact fun h ↦ chosenLineFirst_ne_second L
        (ht (chosenLineFirst_mem_points L) (chosenLineSecond_mem_points L) h)
    have hcol : Collinear (chosenLineFirst L) (chosenLineSecond L) p := by
      rw [dualEventPoint] at hwire
      dsimp only at hwire
      exact (dualHeight_dualMeetX_eq_iff_collinear hab).1 hwire
    have hpblock : p ∈ lineBlock P (chosenLineFirst L) (chosenLineSecond L) :=
      mem_lineBlock.mpr ⟨hp, hcol⟩
    rwa [lineBlock_chosenLine_eq L] at hpblock
  · exact sweptDualHeight_at_event ht hden L

lemma dualEventCoord_eq_of_wire_crossing {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    {p q : Point} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (L : {L // L ∈ connectingLines P})
    (heq : sweptDualHeight t a p (dualEventCoord t a L) =
      sweptDualHeight t a q (dualEventCoord t a L)) :
    dualEventCoord t a
        (⟨lineBlock P p q, lineBlock_mem_connectingLines hp hq hpq⟩ :
          {K // K ∈ connectingLines P}) = dualEventCoord t a L := by
  let K : {K // K ∈ connectingLines P} :=
    ⟨lineBlock P p q, lineBlock_mem_connectingLines hp hq hpq⟩
  have hpK : p ∈ K.1 := left_mem_lineBlock hp
  have hqK : q ∈ K.1 := right_mem_lineBlock hq
  have heqK : sweptDualHeight t a p (dualEventCoord t a K) =
      sweptDualHeight t a q (dualEventCoord t a K) :=
    (sweptDualHeight_at_event ht hden K hpK).trans
      (sweptDualHeight_at_event ht hden K hqK).symm
  have hslope : sweptDualSlope t a p ≠ sweptDualSlope t a q := by
    intro hs
    exact hpq (sweptDualSlope_injOn ht hden hp hq hs)
  have hmul :
      (sweptDualSlope t a p - sweptDualSlope t a q) *
        (dualEventCoord t a L - dualEventCoord t a K) = 0 := by
    simp only [sweptDualHeight] at heq heqK
    nlinarith
  have hcoord : dualEventCoord t a L - dualEventCoord t a K = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hslope)
  change dualEventCoord t a K = dualEventCoord t a L
  linarith

lemma event_height_ties_only_on_line {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (ha : Set.InjOn (sweepSlope a) (dualEventPoints P t))
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P})
    (p q : {p // p ∈ P})
    (heq : sweptDualHeight t a p.1 (dualEventCoord t a L) =
      sweptDualHeight t a q.1 (dualEventCoord t a L)) :
    p = q ∨ sweptDualHeight t a p.1 (dualEventCoord t a L) =
      (dualEventPoint t L).2 := by
  by_cases hpq : p = q
  · exact Or.inl hpq
  · right
    have hpqv : p.1 ≠ q.1 := fun h ↦ hpq (Subtype.ext h)
    let K : {K // K ∈ connectingLines P} :=
      ⟨lineBlock P p.1 q.1,
        lineBlock_mem_connectingLines p.2 q.2 hpqv⟩
    have hc : dualEventCoord t a K = dualEventCoord t a L :=
      dualEventCoord_eq_of_wire_crossing ht hden p.2 q.2 hpqv L heq
    have hKL : K = L := dualEventCoord_injective ht ha hc
    have hpK : p.1 ∈ K.1 := left_mem_lineBlock p.2
    have hpL : p.1 ∈ L.1 := by simpa only [hKL] using hpK
    exact sweptDualHeight_at_event ht hden L hpL

lemma tieBlock_length_eq_card_filter
    {α : Type*} [Fintype α] [DecidableEq α] {h f : α → ℝ}
    (hf : Function.Injective f) (y : ℝ) :
    (tieBlock h f hf y).length =
      ((Finset.univ : Finset α).filter fun x ↦ h x = y).card := by
  have hp := (sortByKey_perm Finset.univ (beforeTieKey h f)
    (beforeTieKey_injective hf)).filter (fun x ↦ h x = y)
  calc
    (tieBlock h f hf y).length =
        (Finset.univ.toList.filter (fun x ↦ h x = y)).length := hp.length_eq
    _ = ((Finset.univ : Finset α).filter fun x ↦ h x = y).card := by
      let l := Finset.univ.toList.filter (fun x ↦ h x = y)
      have hn : l.Nodup := (Finset.nodup_toList Finset.univ).filter _
      have heq : l.toFinset =
          ((Finset.univ : Finset α).filter fun x ↦ h x = y) := by
        ext x
        simp [l]
      rw [← heq, List.toFinset_card_of_nodup hn]

lemma event_tieBlock_length {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P}) :
    (tieBlock
        (fun p : {p // p ∈ P} ↦
          sweptDualHeight t a p.1 (dualEventCoord t a L))
        (fun p : {p // p ∈ P} ↦ sweptDualSlope t a p.1)
        (fun p q h ↦ Subtype.ext (sweptDualSlope_injOn ht hden p.2 q.2 h))
        (dualEventPoint t L).2).length = L.1.card := by
  classical
  let f : {p // p ∈ P} → ℝ := fun p ↦ sweptDualSlope t a p.1
  let h : {p // p ∈ P} → ℝ := fun p ↦
    sweptDualHeight t a p.1 (dualEventCoord t a L)
  have hf : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (sweptDualSlope_injOn ht hden p.2 q.2 hpq)
  change (tieBlock h f hf (dualEventPoint t L).2).length = L.1.card
  rw [tieBlock_length_eq_card_filter hf]
  let S := (Finset.univ : Finset {p // p ∈ P}).filter fun p ↦
    h p = (dualEventPoint t L).2
  have himage : S.image (fun p ↦ p.1) = L.1 := by
    ext p
    constructor
    · intro hpimage
      rw [Finset.mem_image] at hpimage
      rcases hpimage with ⟨q, hq, hqp⟩
      rw [Finset.mem_filter] at hq
      have hqeq : h q = (dualEventPoint t L).2 := hq.2
      have hqL : q.1 ∈ L.1 :=
        (sweptDualHeight_event_eq_iff_mem ht hden L q.2).1 hqeq
      simpa only [← hqp] using hqL
    · intro hpL
      have hpP : p ∈ P := connectingLine_subset L.2 hpL
      rw [Finset.mem_image]
      refine ⟨⟨p, hpP⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact (sweptDualHeight_event_eq_iff_mem ht hden L hpP).2 hpL
  calc
    ((Finset.univ : Finset {p // p ∈ P}).filter fun p ↦
        h p = (dualEventPoint t L).2).card = S.card := rfl
    _ = (S.image (fun p ↦ p.1)).card :=
      (Finset.card_image_iff.mpr Subtype.val_injective.injOn).symm
    _ = L.1.card := by rw [himage]

noncomputable def sweptPointSlope {P : Finset Point} (t a : ℝ) :
    {p // p ∈ P} → ℝ := fun p ↦ sweptDualSlope t a p.1

noncomputable def sweptPointHeight {P : Finset Point} (t a s : ℝ) :
    {p // p ∈ P} → ℝ := fun p ↦ sweptDualHeight t a p.1 s

lemma sweptPointSlope_injective {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0) :
    Function.Injective (sweptPointSlope (P := P) t a) := by
  intro p q hpq
  exact Subtype.ext (sweptDualSlope_injOn ht hden p.2 q.2 hpq)

lemma event_line_card_le_descent_drop {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (ha : Set.InjOn (sweepSlope a) (dualEventPoints P t))
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P}) :
    L.1.card ≤
      descentCount (sweptPointSlope (P := P) t a)
          (beforeTieOrder
            (sweptPointHeight t a (dualEventCoord t a L))
            (sweptPointSlope t a) (sweptPointSlope_injective ht hden)) -
        descentCount (sweptPointSlope (P := P) t a)
          (afterTieOrder
            (sweptPointHeight t a (dualEventCoord t a L))
            (sweptPointSlope t a) (sweptPointSlope_injective ht hden)) + 3 := by
  let f := sweptPointSlope (P := P) t a
  let h := sweptPointHeight (P := P) t a (dualEventCoord t a L)
  let hf : Function.Injective f := sweptPointSlope_injective ht hden
  change L.1.card ≤ descentCount f (beforeTieOrder h f hf) -
    descentCount f (afterTieOrder h f hf) + 3
  rw [← event_tieBlock_length ht hden L]
  exact tie_order_descent_drop hf (dualEventPoint t L).2
    (fun p q hpq ↦ event_height_ties_only_on_line ht ha hden L p q hpq)

lemma event_line_card_add_descent_le {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (ha : Set.InjOn (sweepSlope a) (dualEventPoints P t))
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P}) :
    L.1.card +
        descentCount (sweptPointSlope (P := P) t a)
          (afterTieOrder
            (sweptPointHeight t a (dualEventCoord t a L))
            (sweptPointSlope t a) (sweptPointSlope_injective ht hden)) ≤
      descentCount (sweptPointSlope (P := P) t a)
          (beforeTieOrder
            (sweptPointHeight t a (dualEventCoord t a L))
            (sweptPointSlope t a) (sweptPointSlope_injective ht hden)) + 3 := by
  let f := sweptPointSlope (P := P) t a
  let h := sweptPointHeight (P := P) t a (dualEventCoord t a L)
  let hf : Function.Injective f := sweptPointSlope_injective ht hden
  change L.1.card + descentCount f (afterTieOrder h f hf) ≤
    descentCount f (beforeTieOrder h f hf) + 3
  rw [← event_tieBlock_length ht hden L]
  exact tie_order_descent_add_bound hf (dualEventPoint t L).2
    (fun p q hpq ↦ event_height_ties_only_on_line ht ha hden L p q hpq)

lemma sweptPointHeight_difference_at_crossing {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    {p q : {p // p ∈ P}} (hpq : p ≠ q) (s : ℝ) :
    sweptPointHeight t a s p - sweptPointHeight t a s q =
      (sweptPointSlope t a p - sweptPointSlope t a q) *
        (s - dualEventCoord t a
          (⟨lineBlock P p.1 q.1,
            lineBlock_mem_connectingLines p.2 q.2
              (fun h ↦ hpq (Subtype.ext h))⟩ :
            {K // K ∈ connectingLines P})) := by
  let K : {K // K ∈ connectingLines P} :=
    ⟨lineBlock P p.1 q.1,
      lineBlock_mem_connectingLines p.2 q.2
        (fun h ↦ hpq (Subtype.ext h))⟩
  have hpK : p.1 ∈ K.1 := left_mem_lineBlock p.2
  have hqK : q.1 ∈ K.1 := right_mem_lineBlock q.2
  have heqK : sweptPointHeight t a (dualEventCoord t a K) p =
      sweptPointHeight t a (dualEventCoord t a K) q :=
    (sweptDualHeight_at_event ht hden K hpK).trans
      (sweptDualHeight_at_event ht hden K hqK).symm
  change sweptPointHeight t a s p - sweptPointHeight t a s q =
    (sweptPointSlope t a p - sweptPointSlope t a q) *
      (s - dualEventCoord t a K)
  simp only [sweptPointHeight, sweptPointSlope, sweptDualHeight] at heqK ⊢
  linear_combination heqK

lemma crossing_between_of_product_signs {d l c r : ℝ} (hlr : l < r)
    (hl : d * (l - c) < 0) (hr : 0 < d * (r - c)) : l < c ∧ c < r := by
  have hd : 0 < d := by
    by_contra h
    have hdle : d ≤ 0 := le_of_not_gt h
    have hmul : d * (r - l) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hdle (sub_nonneg.mpr hlr.le)
    nlinarith
  constructor
  · by_contra h
    have hnonneg := mul_nonneg hd.le (sub_nonneg.mpr (le_of_not_gt h))
    linarith
  · by_contra h
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hd.le
      (sub_nonpos.mpr (le_of_not_gt h))
    linarith

lemma no_right_reversal_at_tie {d l c r : ℝ} (hdne : d ≠ 0)
    (hlr : l < r) (hdle : d ≤ 0) (hl : d * (l - c) = 0)
    (hr : 0 < d * (r - c)) : False := by
  have hdlt : d < 0 := lt_of_le_of_ne hdle hdne
  have hlc : l - c = 0 := (mul_eq_zero.mp hl).resolve_left hdne
  have hrc : 0 < r - c := by linarith
  have := mul_neg_of_neg_of_pos hdlt hrc
  linarith

lemma no_left_reversal_at_tie {d l c r : ℝ} (hdne : d ≠ 0)
    (hlr : l < r) (hdge : 0 ≤ d) (hr : d * (r - c) = 0)
    (hl : 0 < d * (l - c)) : False := by
  have hdgt : 0 < d := lt_of_le_of_ne hdge (Ne.symm hdne)
  have hrc : r - c = 0 := (mul_eq_zero.mp hr).resolve_left hdne
  have hlc : l - c < 0 := by linarith
  have := mul_neg_of_pos_of_neg hdgt hlc
  linarith

lemma afterTieOrder_pairwise_height_between_events
    {P : Finset Point} {t a x : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P})
    (hLx : dualEventCoord t a L < x)
    (hno : ∀ K : {K // K ∈ connectingLines P},
      dualEventCoord t a L < dualEventCoord t a K →
      dualEventCoord t a K < x → False) :
    (afterTieOrder
      (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a) (sweptPointSlope_injective ht hden)).Pairwise
        fun p q ↦ sweptPointHeight t a x p ≤ sweptPointHeight t a x q := by
  have hp := sortByKey_pairwise Finset.univ
    (afterTieKey (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a))
    (afterTieKey_injective (sweptPointSlope_injective ht hden))
  apply hp.imp
  intro p q hpqkey
  by_cases hpq : p = q
  · subst q
    exact le_rfl
  have hslopene : sweptPointSlope t a p - sweptPointSlope t a q ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ hpq (sweptPointSlope_injective ht hden h))
  let K : {K // K ∈ connectingLines P} :=
    ⟨lineBlock P p.1 q.1,
      lineBlock_mem_connectingLines p.2 q.2
        (fun h ↦ hpq (Subtype.ext h))⟩
  have hformL := sweptPointHeight_difference_at_crossing ht hden hpq
    (dualEventCoord t a L)
  have hformx := sweptPointHeight_difference_at_crossing ht hden hpq x
  change toLex
      (sweptPointHeight t a (dualEventCoord t a L) p,
        sweptPointSlope t a p) ≤
    toLex
      (sweptPointHeight t a (dualEventCoord t a L) q,
        sweptPointSlope t a q) at hpqkey
  rw [Prod.Lex.toLex_le_toLex] at hpqkey
  by_contra hgoal
  have hxrev : sweptPointHeight t a x q < sweptPointHeight t a x p :=
    lt_of_not_ge hgoal
  have hposx : 0 < (sweptPointSlope t a p - sweptPointSlope t a q) *
      (x - dualEventCoord t a K) := by
    have hdifference : 0 <
        sweptPointHeight t a x p - sweptPointHeight t a x q := by linarith
    rw [hformx] at hdifference
    exact hdifference
  rcases hpqkey with hstrict | ⟨htie, hslope⟩
  · have hnegL : (sweptPointSlope t a p - sweptPointSlope t a q) *
        (dualEventCoord t a L - dualEventCoord t a K) < 0 := by
      rw [← hformL]
      linarith
    obtain ⟨hc₁, hc₂⟩ := crossing_between_of_product_signs hLx hnegL hposx
    exact hno K hc₁ hc₂
  · have hzeroL : (sweptPointSlope t a p - sweptPointSlope t a q) *
        (dualEventCoord t a L - dualEventCoord t a K) = 0 := by
      rw [← hformL]
      linarith
    have hdle : sweptPointSlope t a p - sweptPointSlope t a q ≤ 0 := by
      linarith
    exact no_right_reversal_at_tie hslopene hLx hdle hzeroL hposx

lemma beforeTieOrder_pairwise_height_between_events
    {P : Finset Point} {t a x : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (M : {M // M ∈ connectingLines P})
    (hxM : x < dualEventCoord t a M)
    (hno : ∀ K : {K // K ∈ connectingLines P},
      x < dualEventCoord t a K →
      dualEventCoord t a K < dualEventCoord t a M → False) :
    (beforeTieOrder
      (sweptPointHeight t a (dualEventCoord t a M))
      (sweptPointSlope t a) (sweptPointSlope_injective ht hden)).Pairwise
        fun p q ↦ sweptPointHeight t a x p ≤ sweptPointHeight t a x q := by
  have hp := sortByKey_pairwise Finset.univ
    (beforeTieKey (sweptPointHeight t a (dualEventCoord t a M))
      (sweptPointSlope t a))
    (beforeTieKey_injective (sweptPointSlope_injective ht hden))
  apply hp.imp
  intro p q hpqkey
  by_cases hpq : p = q
  · subst q
    exact le_rfl
  have hslopene : sweptPointSlope t a p - sweptPointSlope t a q ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ hpq (sweptPointSlope_injective ht hden h))
  let K : {K // K ∈ connectingLines P} :=
    ⟨lineBlock P p.1 q.1,
      lineBlock_mem_connectingLines p.2 q.2
        (fun h ↦ hpq (Subtype.ext h))⟩
  have hformM := sweptPointHeight_difference_at_crossing ht hden hpq
    (dualEventCoord t a M)
  have hformx := sweptPointHeight_difference_at_crossing ht hden hpq x
  change toLex
      (sweptPointHeight t a (dualEventCoord t a M) p,
        -sweptPointSlope t a p) ≤
    toLex
      (sweptPointHeight t a (dualEventCoord t a M) q,
        -sweptPointSlope t a q) at hpqkey
  rw [Prod.Lex.toLex_le_toLex] at hpqkey
  by_contra hgoal
  have hxrev : sweptPointHeight t a x q < sweptPointHeight t a x p :=
    lt_of_not_ge hgoal
  have hposx : 0 < (sweptPointSlope t a p - sweptPointSlope t a q) *
      (x - dualEventCoord t a K) := by
    have hdifference : 0 <
        sweptPointHeight t a x p - sweptPointHeight t a x q := by linarith
    rw [hformx] at hdifference
    exact hdifference
  rcases hpqkey with hstrict | ⟨htie, hslope⟩
  · have hnegM : (sweptPointSlope t a p - sweptPointSlope t a q) *
        (dualEventCoord t a M - dualEventCoord t a K) < 0 := by
      rw [← hformM]
      linarith
    have hnegx : (- (sweptPointSlope t a p - sweptPointSlope t a q)) *
        (x - dualEventCoord t a K) < 0 := by nlinarith
    have hposM : 0 < (- (sweptPointSlope t a p - sweptPointSlope t a q)) *
        (dualEventCoord t a M - dualEventCoord t a K) := by nlinarith
    obtain ⟨hc₁, hc₂⟩ := crossing_between_of_product_signs hxM hnegx hposM
    exact hno K hc₁ hc₂
  · have hzeroM : (sweptPointSlope t a p - sweptPointSlope t a q) *
        (dualEventCoord t a M - dualEventCoord t a K) = 0 := by
      rw [← hformM]
      linarith
    have hdge : 0 ≤ sweptPointSlope t a p - sweptPointSlope t a q := by
      linarith
    exact no_left_reversal_at_tie hslopene hxM hdge hzeroM hposx

lemma sweptPointHeight_injective_between_events
    {P : Finset Point} {t a x : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L M : {L // L ∈ connectingLines P})
    (hLx : dualEventCoord t a L < x)
    (hxM : x < dualEventCoord t a M)
    (hno : ∀ K : {K // K ∈ connectingLines P},
      dualEventCoord t a L < dualEventCoord t a K →
      dualEventCoord t a K < dualEventCoord t a M → False) :
    Function.Injective (sweptPointHeight (P := P) t a x) := by
  intro p q hpq
  by_contra hpqne
  have hslope : sweptPointSlope t a p - sweptPointSlope t a q ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ hpqne (sweptPointSlope_injective ht hden h))
  let K : {K // K ∈ connectingLines P} :=
    ⟨lineBlock P p.1 q.1,
      lineBlock_mem_connectingLines p.2 q.2
        (fun h ↦ hpqne (Subtype.ext h))⟩
  have hform := sweptPointHeight_difference_at_crossing ht hden hpqne x
  have hprod : (sweptPointSlope t a p - sweptPointSlope t a q) *
      (x - dualEventCoord t a K) = 0 := by
    rw [← hform]
    linarith
  have hxK : x = dualEventCoord t a K := by
    have := (mul_eq_zero.mp hprod).resolve_left hslope
    linarith
  apply hno K
  · linarith
  · linarith

lemma adjacent_event_orders_eq {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L M : {L // L ∈ connectingLines P})
    (hLM : dualEventCoord t a L < dualEventCoord t a M)
    (hno : ∀ K : {K // K ∈ connectingLines P},
      dualEventCoord t a L < dualEventCoord t a K →
      dualEventCoord t a K < dualEventCoord t a M → False) :
    afterTieOrder
        (sweptPointHeight t a (dualEventCoord t a L))
        (sweptPointSlope t a) (sweptPointSlope_injective ht hden) =
      beforeTieOrder
        (sweptPointHeight t a (dualEventCoord t a M))
        (sweptPointSlope t a) (sweptPointSlope_injective ht hden) := by
  let x := (dualEventCoord t a L + dualEventCoord t a M) / 2
  have hLx : dualEventCoord t a L < x := by dsimp [x]; linarith
  have hxM : x < dualEventCoord t a M := by dsimp [x]; linarith
  have hafter := afterTieOrder_pairwise_height_between_events ht hden L hLx
    (fun K hLK hKx ↦ hno K hLK (hKx.trans hxM))
  have hbefore := beforeTieOrder_pairwise_height_between_events ht hden M hxM
    (fun K hxK hKM ↦ hno K (hLx.trans hxK) hKM)
  have hinj := sweptPointHeight_injective_between_events ht hden L M hLx hxM hno
  apply List.Perm.eq_of_pairwise
    (fun p q _ _ hpq hqp ↦ hinj (le_antisymm hpq hqp)) hafter hbefore
  exact (sortByKey_perm Finset.univ
      (afterTieKey (sweptPointHeight t a (dualEventCoord t a L))
        (sweptPointSlope t a))
      (afterTieKey_injective (sweptPointSlope_injective ht hden))).trans
    (sortByKey_perm Finset.univ
      (beforeTieKey (sweptPointHeight t a (dualEventCoord t a M))
        (sweptPointSlope t a))
      (beforeTieKey_injective (sweptPointSlope_injective ht hden))).symm

lemma before_min_event_pairwise_slope_descending
    {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P})
    (hmin : ∀ K : {K // K ∈ connectingLines P},
      dualEventCoord t a L ≤ dualEventCoord t a K) :
    (beforeTieOrder
      (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a) (sweptPointSlope_injective ht hden)).Pairwise
        fun p q ↦ sweptPointSlope t a q < sweptPointSlope t a p := by
  have hpair := sortByKey_pairwise Finset.univ
    (beforeTieKey (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a))
    (beforeTieKey_injective (sweptPointSlope_injective ht hden))
  have hnodup : (beforeTieOrder
      (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a) (sweptPointSlope_injective ht hden)).Nodup :=
    (sortByKey_perm Finset.univ
      (beforeTieKey (sweptPointHeight t a (dualEventCoord t a L))
        (sweptPointSlope t a))
      (beforeTieKey_injective (sweptPointSlope_injective ht hden))).nodup_iff.mpr
        (Finset.nodup_toList Finset.univ)
  apply (hpair.and hnodup).imp
  intro p q hpq
  have hpqne : p ≠ q := hpq.2
  let K : {K // K ∈ connectingLines P} :=
    ⟨lineBlock P p.1 q.1,
      lineBlock_mem_connectingLines p.2 q.2
        (fun h ↦ hpqne (Subtype.ext h))⟩
  have hform := sweptPointHeight_difference_at_crossing ht hden hpqne
    (dualEventCoord t a L)
  have hpqkey := hpq.1
  change toLex
      (sweptPointHeight t a (dualEventCoord t a L) p,
        -sweptPointSlope t a p) ≤
      toLex
      (sweptPointHeight t a (dualEventCoord t a L) q,
        -sweptPointSlope t a q) at hpqkey
  rw [Prod.Lex.toLex_le_toLex] at hpqkey
  rcases hpqkey with hstrict | ⟨_, hslope⟩
  · have hprod : (sweptPointSlope t a p - sweptPointSlope t a q) *
        (dualEventCoord t a L - dualEventCoord t a K) < 0 := by
      rw [← hform]
      linarith
    have hcoord := hmin K
    by_contra hnot
    have hdle : sweptPointSlope t a p - sweptPointSlope t a q ≤ 0 := by
      linarith
    have hnonneg := mul_nonneg_of_nonpos_of_nonpos hdle (sub_nonpos.mpr hcoord)
    linarith
  · have hne : sweptPointSlope t a p ≠ sweptPointSlope t a q :=
      fun h ↦ hpqne (sweptPointSlope_injective ht hden h)
    exact lt_of_le_of_ne (by linarith) (fun h ↦ hne h.symm)

lemma after_max_event_pairwise_slope_ascending
    {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (L : {L // L ∈ connectingLines P})
    (hmax : ∀ K : {K // K ∈ connectingLines P},
      dualEventCoord t a K ≤ dualEventCoord t a L) :
    (afterTieOrder
      (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a) (sweptPointSlope_injective ht hden)).Pairwise
        fun p q ↦ sweptPointSlope t a p < sweptPointSlope t a q := by
  have hpair := sortByKey_pairwise Finset.univ
    (afterTieKey (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a))
    (afterTieKey_injective (sweptPointSlope_injective ht hden))
  have hnodup : (afterTieOrder
      (sweptPointHeight t a (dualEventCoord t a L))
      (sweptPointSlope t a) (sweptPointSlope_injective ht hden)).Nodup :=
    (sortByKey_perm Finset.univ
      (afterTieKey (sweptPointHeight t a (dualEventCoord t a L))
        (sweptPointSlope t a))
      (afterTieKey_injective (sweptPointSlope_injective ht hden))).nodup_iff.mpr
        (Finset.nodup_toList Finset.univ)
  apply (hpair.and hnodup).imp
  intro p q hpq
  have hpqne : p ≠ q := hpq.2
  let K : {K // K ∈ connectingLines P} :=
    ⟨lineBlock P p.1 q.1,
      lineBlock_mem_connectingLines p.2 q.2
        (fun h ↦ hpqne (Subtype.ext h))⟩
  have hform := sweptPointHeight_difference_at_crossing ht hden hpqne
    (dualEventCoord t a L)
  have hpqkey := hpq.1
  change toLex
      (sweptPointHeight t a (dualEventCoord t a L) p,
        sweptPointSlope t a p) ≤
      toLex
      (sweptPointHeight t a (dualEventCoord t a L) q,
        sweptPointSlope t a q) at hpqkey
  rw [Prod.Lex.toLex_le_toLex] at hpqkey
  rcases hpqkey with hstrict | ⟨_, hslope⟩
  · have hprod : (sweptPointSlope t a p - sweptPointSlope t a q) *
        (dualEventCoord t a L - dualEventCoord t a K) < 0 := by
      rw [← hform]
      linarith
    have hcoord := hmax K
    by_contra hnot
    have hdge : 0 ≤ sweptPointSlope t a p - sweptPointSlope t a q := by
      linarith
    have hnonneg := mul_nonneg hdge (sub_nonneg.mpr hcoord)
    linarith
  · have hne : sweptPointSlope t a p ≠ sweptPointSlope t a q :=
      fun h ↦ hpqne (sweptPointSlope_injective ht hden h)
    exact lt_of_le_of_ne hslope hne

noncomputable def dualEventOrder (P : Finset Point) (t a : ℝ)
    (ht : Set.InjOn (sweepSlope t) P)
    (ha : Set.InjOn (sweepSlope a) (dualEventPoints P t)) :
    List {L // L ∈ connectingLines P} :=
  sortByKey Finset.univ (dualEventCoord t a) (dualEventCoord_injective ht ha)

lemma dualEventOrder_pairwise_coord_lt {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (ha : Set.InjOn (sweepSlope a) (dualEventPoints P t)) :
    (dualEventOrder P t a ht ha).Pairwise fun L M ↦
      dualEventCoord t a L < dualEventCoord t a M := by
  have hpair := sortByKey_pairwise Finset.univ (dualEventCoord t a)
    (dualEventCoord_injective ht ha)
  have hnodup : (dualEventOrder P t a ht ha).Nodup :=
    (sortByKey_perm Finset.univ (dualEventCoord t a)
      (dualEventCoord_injective ht ha)).nodup_iff.mpr
        (Finset.nodup_toList Finset.univ)
  apply (hpair.and hnodup).imp
  intro L M hLM
  exact lt_of_le_of_ne hLM.1
    (fun heq ↦ hLM.2 (dualEventCoord_injective ht ha heq))

lemma dualEventOrder_perm_univ {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (ha : Set.InjOn (sweepSlope a) (dualEventPoints P t)) :
    (dualEventOrder P t a ht ha).Perm
      (Finset.univ : Finset {L // L ∈ connectingLines P}).toList :=
  sortByKey_perm Finset.univ (dualEventCoord t a) (dualEventCoord_injective ht ha)

lemma event_order_chain_aux {P : Finset Point} {t a : ℝ}
    (ht : Set.InjOn (sweepSlope t) P)
    (hden : ∀ p ∈ P, 1 + a * sweepSlope t p ≠ 0)
    (x : {L // L ∈ connectingLines P}) :
    ∀ xs : List {L // L ∈ connectingLines P},
      (x :: xs).Pairwise (fun L M ↦
        dualEventCoord t a L < dualEventCoord t a M) →
      (∀ K : {K // K ∈ connectingLines P}, K ∈ x :: xs ∨
        dualEventCoord t a K ≤ dualEventCoord t a x) →
      List.Chain
        (fun L M ↦
          afterTieOrder
              (sweptPointHeight t a (dualEventCoord t a L))
              (sweptPointSlope t a) (sweptPointSlope_injective ht hden) =
            beforeTieOrder
              (sweptPointHeight t a (dualEventCoord t a M))
              (sweptPointSlope t a) (sweptPointSlope_injective ht hden))
        x xs := by
  intro xs
  induction xs generalizing x with
  | nil =>
      intro _ _
      simp [List.Chain]
  | cons y ys ih =>
      intro hpair hcover
      rw [List.pairwise_cons] at hpair
      have hxy : dualEventCoord t a x < dualEventCoord t a y :=
        hpair.1 y (by simp)
      have htailpair := hpair.2
      rw [List.pairwise_cons] at htailpair
      have hno : ∀ K : {K // K ∈ connectingLines P},
          dualEventCoord t a x < dualEventCoord t a K →
          dualEventCoord t a K < dualEventCoord t a y → False := by
        intro K hxK hKy
        rcases hcover K with hmem | hle
        · rw [List.mem_cons] at hmem
          rcases hmem with hKx | hmem
          · subst K
            linarith
          · rw [List.mem_cons] at hmem
            rcases hmem with hKy' | hmem
            · subst K
              linarith
            · have hyK := htailpair.1 K hmem
              linarith
        · linarith
      have hrel := adjacent_event_orders_eq ht hden x y hxy hno
      have hcoverTail : ∀ K : {K // K ∈ connectingLines P},
          K ∈ y :: ys ∨ dualEventCoord t a K ≤ dualEventCoord t a y := by
        intro K
        by_cases hmem : K ∈ y :: ys
        · exact Or.inl hmem
        · right
          rcases hcover K with hcurrent | hle
          · rw [List.mem_cons] at hcurrent
            rcases hcurrent with hKx | hcurrent
            · subst K
              exact hxy.le
            · exact False.elim (hmem hcurrent)
          · exact hle.trans hxy.le
      have hchainTail := ih y hpair.2 hcoverTail
      change List.IsChain _ (x :: y :: ys)
      rw [List.chain_cons]
      exact ⟨hrel, hchainTail⟩

lemma connectingLines_nonempty_of_not_contained {P : Finset Point}
    (hP : ¬ ContainedInLine P) : (connectingLines P).Nonempty := by
  classical
  have hPne : P.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hP
    refine ⟨(0, 0), (1, 0), ?_, ?_⟩
    · norm_num
    · intro p hp
      simp [hne] at hp
  obtain ⟨p, hp⟩ := hPne
  have hdeg := two_le_pointDegree_of_not_contained hP hp
  have hpos : 0 < (linesThrough P p).card := by
    rw [card_linesThrough]
    omega
  obtain ⟨L, hL⟩ := Finset.card_pos.mp hpos
  exact ⟨L, (mem_linesThrough.mp hL).1⟩

lemma sum_line_card_le_card_add_three_mul_lines
    {P : Finset Point} (hP : ¬ ContainedInLine P) :
    ∑ L ∈ connectingLines P, L.card ≤
      P.card - 1 + 3 * (connectingLines P).card := by
  classical
  obtain ⟨t, a, ht, ha, hden⟩ := exists_generic_dual_sweep P
  let f := sweptPointSlope (P := P) t a
  let beforeD : {L // L ∈ connectingLines P} → ℕ := fun L ↦
    descentCount f
      (beforeTieOrder
        (sweptPointHeight t a (dualEventCoord t a L)) f
        (sweptPointSlope_injective ht hden))
  let afterD : {L // L ∈ connectingLines P} → ℕ := fun L ↦
    descentCount f
      (afterTieOrder
        (sweptPointHeight t a (dualEventCoord t a L)) f
        (sweptPointSlope_injective ht hden))
  have hlocal : ∀ L : {L // L ∈ connectingLines P},
      L.1.card + afterD L ≤ beforeD L + 3 := by
    intro L
    exact event_line_card_add_descent_le ht ha hden L
  have hnonempty := connectingLines_nonempty_of_not_contained hP
  have horderne : dualEventOrder P t a ht ha ≠ [] := by
    intro hnil
    obtain ⟨L, hL⟩ := hnonempty
    let L' : {L // L ∈ connectingLines P} := ⟨L, hL⟩
    have hmem : L' ∈ dualEventOrder P t a ht ha :=
      (dualEventOrder_perm_univ ht ha).mem_iff.mpr (by simp)
    rw [hnil] at hmem
    simp at hmem
  cases horder : dualEventOrder P t a ht ha with
  | nil => exact False.elim (horderne horder)
  | cons x xs =>
      have hpair : (x :: xs).Pairwise fun L M ↦
          dualEventCoord t a L < dualEventCoord t a M := by
        rw [← horder]
        exact dualEventOrder_pairwise_coord_lt ht ha
      have hmemall : ∀ K : {K // K ∈ connectingLines P}, K ∈ x :: xs := by
        intro K
        have hmem : K ∈ dualEventOrder P t a ht ha :=
          (dualEventOrder_perm_univ ht ha).mem_iff.mpr (by simp)
        rwa [horder] at hmem
      have hchainOrders := event_order_chain_aux ht hden x xs hpair
        (fun K ↦ Or.inl (hmemall K))
      have hchain : List.Chain (fun L M ↦ afterD L = beforeD M) x xs := by
        refine List.IsChain.imp (p := hchainOrders) ?_
        intro L M hLM
        exact congrArg (descentCount f) hLM
      have htelescope := chain_telescope_sum
        (fun L : {L // L ∈ connectingLines P} ↦ L.1.card)
        beforeD afterD hlocal x xs hchain
      have hpairle : (x :: xs).Pairwise fun L M ↦
          dualEventCoord t a L ≤ dualEventCoord t a M := by
        apply hpair.imp
        intro L M hLM
        exact hLM.le
      have hmin : ∀ K : {K // K ∈ connectingLines P},
          dualEventCoord t a x ≤ dualEventCoord t a K := by
        intro K
        have h := hpairle.rel_head (hmemall K)
        simpa using h
      let z : {L // L ∈ connectingLines P} := xs.getLast?.getD x
      have hlast : (x :: xs).getLast (by simp) = z := by
        have hopt := List.getLast?_eq_getLast (l := x :: xs) (by simp)
        have hget := congrArg (fun o ↦ o.getD x) hopt
        rw [List.getLast?_cons] at hget
        simp only [Option.getD_some] at hget
        exact hget.symm
      have hmax : ∀ K : {K // K ∈ connectingLines P},
          dualEventCoord t a K ≤ dualEventCoord t a z := by
        intro K
        have h := hpairle.rel_getLast (hmemall K)
        rwa [hlast] at h
      have hbeforePair := before_min_event_pairwise_slope_descending ht hden x hmin
      have hbeforeValue : beforeD x = P.card - 1 := by
        have hporder := (sortByKey_perm Finset.univ
          (beforeTieKey (sweptPointHeight t a (dualEventCoord t a x)) f)
          (beforeTieKey_injective (sweptPointSlope_injective ht hden)))
        have hlen' : (beforeTieOrder
            (sweptPointHeight t a (dualEventCoord t a x)) f
            (sweptPointSlope_injective ht hden)).length = P.card := by
          calc
            _ = (Finset.univ.toList : List {p // p ∈ P}).length :=
              hporder.length_eq
            _ = P.card := by simp
        dsimp only [beforeD]
        rw [descentCount_eq_length_sub_one_of_pairwise_gt hbeforePair, hlen']
      have hafterPair := after_max_event_pairwise_slope_ascending ht hden z hmax
      have hafterValue : afterD z = 0 := by
        change descentCount f
          (afterTieOrder (sweptPointHeight t a (dualEventCoord t a z)) f
            (sweptPointSlope_injective ht hden)) = 0
        exact descentCount_eq_zero_of_pairwise_lt hafterPair
      have hz : xs.getLast?.getD x = z := rfl
      rw [hz, hafterValue, Nat.add_zero, hbeforeValue] at htelescope
      have hlength : (x :: xs).length = (connectingLines P).card := by
        have hl := (dualEventOrder_perm_univ ht ha).length_eq
        rw [horder] at hl
        simpa using hl
      have hsum : (x.1.card :: xs.map fun L ↦ L.1.card).sum =
          ∑ L ∈ connectingLines P, L.card := by
        have hp := (dualEventOrder_perm_univ ht ha).map
          (fun L : {L // L ∈ connectingLines P} ↦ L.1.card)
        rw [horder] at hp
        have hsumEq := hp.sum_eq
        calc
          (x.1.card :: xs.map fun L ↦ L.1.card).sum =
              ((Finset.univ : Finset {L // L ∈ connectingLines P}).toList.map
                fun L ↦ L.1.card).sum := hsumEq
          _ = ∑ L : {L // L ∈ connectingLines P}, L.1.card := by
            symm
            simpa using List.sum_toFinset
              (fun L : {L // L ∈ connectingLines P} ↦ L.1.card)
              (Finset.nodup_toList Finset.univ)
          _ = ∑ L ∈ connectingLines P, L.card :=
            Finset.sum_coe_sort (connectingLines P) Finset.card
      rw [hsum, ← List.length_cons, hlength] at htelescope
      exact htelescope

/-- The affine sweep form of Melchior's defect estimate.  It is weaker than
the projective bound `3 ≤ lineDefect P`, but retains enough linear margin for
the sharp circle count after allowing connecting lines of size four. -/
lemma one_sub_card_le_lineDefect {P : Finset Point}
    (hP : ¬ ContainedInLine P) :
    (1 : ℤ) - P.card ≤ lineDefect P := by
  have hPne := connectingLines_nonempty_of_not_contained hP
  have hpoints : 1 ≤ P.card := by
    obtain ⟨L, hL⟩ := hPne
    have htwo := connectingLine_card_two_le hL
    have hsub := Finset.card_le_card (connectingLine_subset hL)
    omega
  have hinc := sum_line_card_le_card_add_three_mul_lines hP
  have hincz : ((∑ L ∈ connectingLines P, L.card : ℕ) : ℤ) ≤
      ((P.card - 1 + 3 * (connectingLines P).card : ℕ) : ℤ) := by
    exact_mod_cast hinc
  simp only [Nat.cast_sum, Nat.cast_sub hpoints, Nat.cast_one,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hincz
  rw [lineDefect, Finset.sum_sub_distrib, Finset.sum_const]
  simp only [nsmul_eq_mul]
  omega

/-- Kelly--Moser's degree dichotomy combined with the affine sweep bound.
The denominator-free form is convenient for the later size-four-line count. -/
lemma seventeen_mul_card_sub_fifteen_le_three_mul_lines
    {P : Finset Point} (hN : 393 ≤ P.card)
    (hP : ¬ ContainedInLine P)
    (hmax : ∀ L ∈ connectingLines P, L.card ≤ P.card - 6) :
    17 * P.card - 15 ≤ 3 * (connectingLines P).card := by
  classical
  by_cases hlow : ∃ x ∈ P, ∃ y ∈ P,
      x ≠ y ∧ pointDegree P x ≤ 17 ∧ pointDegree P y ≤ 17
  · obtain ⟨x, hx, y, hy, hxy, hdx, hdy⟩ := hlow
    let L := lineBlock P x y
    let Q := P \ L
    have hLconn : L ∈ connectingLines P := lineBlock_mem_connectingLines hx hy hxy
    have hLcard : L.card ≤ P.card - 6 := hmax L hLconn
    have hQcard : Q.card = P.card - L.card := by
      dsimp [Q]
      rw [Finset.card_sdiff_of_subset (lineBlock_subset P x y)]
    have hsumcard : P.card = L.card + Q.card := by omega
    have hQdegree : Q.card ≤
        (pointDegree P x - 1) * (pointDegree P y - 1) :=
      card_off_line_le_degree_product hx hy hxy rfl
    have hdx16 : pointDegree P x - 1 ≤ 16 := by omega
    have hdy16 : pointDegree P y - 1 ≤ 16 := by omega
    have hQ256 : Q.card ≤ 256 :=
      hQdegree.trans (by simpa using Nat.mul_le_mul hdx16 hdy16)
    have hQ6 : 6 ≤ Q.card := by omega
    have hnum : 6 * P.card - 50 ≤
        1 + Q.card * L.card - Nat.choose Q.card 2 :=
      six_mul_sub_fifty_le_line_expression hsumcard hN hQ6 hQ256
    have hlines : 6 * P.card - 50 ≤ (connectingLines P).card :=
      hnum.trans (connectingLines_lower_of_lineBlock hx hy hxy rfl)
    omega
  · have hinc : ∑ p ∈ P, pointDegree P p ≤
        P.card - 1 + 3 * (connectingLines P).card := by
      rw [sum_pointDegree]
      exact sum_line_card_le_card_add_three_mul_lines hP
    have hsum : 18 * P.card - 16 ≤ ∑ p ∈ P, pointDegree P p := by
      by_cases hex : ∃ p ∈ P, pointDegree P p ≤ 17
      · obtain ⟨p, hp, hdp⟩ := hex
        have hother : ∀ q ∈ P.erase p, 18 ≤ pointDegree P q := by
          intro q hq
          have hqP := (Finset.mem_erase.mp hq).2
          have hqp := (Finset.mem_erase.mp hq).1
          by_contra hdeg
          have hdeg' : pointDegree P q ≤ 17 := by omega
          exact hlow ⟨p, hp, q, hqP, Ne.symm hqp, hdp, hdeg'⟩
        have herase : 18 * (P.erase p).card ≤
            ∑ q ∈ P.erase p, pointDegree P q := by
          calc
            _ = ∑ _q ∈ P.erase p, 18 := by simp [mul_comm]
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro q hq
              exact hother q hq
        have hpdeg := two_le_pointDegree_of_not_contained hP hp
        have hdecomp := P.sum_erase_add (fun q ↦ pointDegree P q) hp
        have hcarderase := Finset.card_erase_of_mem hp
        omega
      · push_neg at hex
        have hall : ∀ p ∈ P, 18 ≤ pointDegree P p := by
          intro p hp
          have := hex p hp
          omega
        calc
          18 * P.card - 16 ≤ 18 * P.card := Nat.sub_le _ _
          _ = ∑ _p ∈ P, 18 := by simp [mul_comm]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro p hp
            exact hall p hp
    omega

/-- Connecting lines containing two or three inverted points, with membership
in the ambient connecting-line family retained in their subtype. -/
noncomputable def lowLineSubtypes (P : Finset Point) :
    Finset {L // L ∈ connectingLines P} := by
  classical
  exact (connectingLines P).attach.filter fun L ↦ L.1.card ≤ 3

/-- The low lines through the inversion center. -/
noncomputable def radialLowLines (P : Finset Point) (p : Point) :
    Finset {L // L ∈ connectingLines P} := by
  classical
  exact (lowLineSubtypes P).filter fun L ↦
    Collinear p (chosenLineFirst L) (chosenLineSecond L)

/-- The low lines avoiding the inversion center.  These are precisely the
lines that invert to proper circles through the center. -/
noncomputable def nonradialLowLines (P : Finset Point) (p : Point) :
    Finset {L // L ∈ connectingLines P} := by
  classical
  exact (lowLineSubtypes P).filter fun L ↦
    Noncollinear p (chosenLineFirst L) (chosenLineSecond L)

lemma mem_lowLineSubtypes {P : Finset Point}
    {L : {L // L ∈ connectingLines P}} :
    L ∈ lowLineSubtypes P ↔ L.1.card ≤ 3 := by
  classical
  simp [lowLineSubtypes]

lemma mem_radialLowLines {P : Finset Point} {p : Point}
    {L : {L // L ∈ connectingLines P}} :
    L ∈ radialLowLines P p ↔
      L.1.card ≤ 3 ∧ Collinear p (chosenLineFirst L) (chosenLineSecond L) := by
  classical
  simp [radialLowLines, mem_lowLineSubtypes]

lemma mem_nonradialLowLines {P : Finset Point} {p : Point}
    {L : {L // L ∈ connectingLines P}} :
    L ∈ nonradialLowLines P p ↔
      L.1.card ≤ 3 ∧ Noncollinear p (chosenLineFirst L) (chosenLineSecond L) := by
  classical
  simp [nonradialLowLines, mem_lowLineSubtypes]

lemma card_lowLineSubtypes (P : Finset Point) :
    (lowLineSubtypes P).card =
      (linesOfSize P 2).card + (linesOfSize P 3).card := by
  classical
  have hfilter :
      ((connectingLines P).filter fun L ↦ L.card ≤ 3) =
        linesOfSize P 2 ∪ linesOfSize P 3 := by
    apply Finset.ext
    intro L
    simp only [Finset.mem_filter, Finset.mem_union, mem_linesOfSize]
    constructor
    · rintro ⟨hL, hcard⟩
      have htwo := connectingLine_card_two_le hL
      have hcases : L.card = 2 ∨ L.card = 3 := by omega
      rcases hcases with hcases | hcases
      · exact Or.inl ⟨hL, hcases⟩
      · exact Or.inr ⟨hL, hcases⟩
    · rintro (⟨hL, hcard⟩ | ⟨hL, hcard⟩) <;> exact ⟨hL, by omega⟩
  have hdisj : Disjoint (linesOfSize P 2) (linesOfSize P 3) := by
    rw [Finset.disjoint_left]
    intro L hL2 hL3
    rw [mem_linesOfSize] at hL2 hL3
    omega
  calc
    (lowLineSubtypes P).card =
        ((connectingLines P).filter fun L ↦ L.card ≤ 3).card := by
      rw [lowLineSubtypes]
      have h := congrArg Finset.card
        (Finset.filter_attach (fun L : Finset Point ↦ L.card ≤ 3)
          (connectingLines P))
      simpa using h
    _ = (linesOfSize P 2 ∪ linesOfSize P 3).card := by rw [hfilter]
    _ = _ := Finset.card_union_of_disjoint hdisj

lemma card_radial_add_card_nonradial {P : Finset Point} {p : Point} :
    (radialLowLines P p).card + (nonradialLowLines P p).card =
      (lowLineSubtypes P).card := by
  classical
  rw [radialLowLines, nonradialLowLines]
  have hsecond :
      (lowLineSubtypes P).filter (fun L ↦
        Noncollinear p (chosenLineFirst L) (chosenLineSecond L)) =
      (lowLineSubtypes P).filter (fun L ↦
        ¬ Collinear p (chosenLineFirst L) (chosenLineSecond L)) := by
    apply Finset.ext
    intro L
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ ↦ ?_
    simp only [Noncollinear, Collinear]
  rw [hsecond]
  exact Finset.card_filter_add_card_filter_not
    (s := lowLineSubtypes P)
    (fun L ↦ Collinear p (chosenLineFirst L) (chosenLineSecond L))

lemma mem_radialLine_iff {P : Finset Point} {p x y : Point}
    (hp : p ∉ P) (L : {L // L ∈ connectingLines P})
    (hrad : Collinear p (chosenLineFirst L) (chosenLineSecond L))
    (hx : x ∈ L.1) :
    y ∈ L.1 ↔ y ∈ P ∧ Collinear p x y := by
  have hxP : x ∈ P := connectingLine_subset L.2 hx
  have hpx : p ≠ x := fun h ↦ hp (h.symm ▸ hxP)
  have hline :
      Collinear (chosenLineFirst L) (chosenLineSecond L) y ↔
        Collinear p x y := by
    exact collinear_line_unique (chosenLineFirst_ne_second L) hpx
      (collinear_rotate.mp hrad) (chosenLine_collinear_of_mem L hx)
  rw [← lineBlock_chosenLine_eq L, mem_lineBlock]
  exact and_congr_right fun _ ↦ hline

lemma radialLowLines_pairwiseDisjoint {P : Finset Point} {p : Point}
    (hp : p ∉ P) :
    (((radialLowLines P p : Finset {L // L ∈ connectingLines P}) :
      Set {L // L ∈ connectingLines P}).PairwiseDisjoint fun L ↦ L.1) := by
  classical
  intro L hL M hM hLM
  change Disjoint L.1 M.1
  rw [Finset.disjoint_left]
  intro x hxL hxM
  have hradL := (mem_radialLowLines.mp hL).2
  have hradM := (mem_radialLowLines.mp hM).2
  apply hLM
  apply Subtype.ext
  apply Finset.ext
  intro y
  rw [mem_radialLine_iff hp L hradL hxL,
    mem_radialLine_iff hp M hradM hxM]

lemma two_mul_card_radialLowLines_le {P : Finset Point} {p : Point}
    (hp : p ∉ P) : 2 * (radialLowLines P p).card ≤ P.card := by
  classical
  let R := radialLowLines P p
  have hdisj : (((R : Finset {L // L ∈ connectingLines P}) :
      Set {L // L ∈ connectingLines P}).PairwiseDisjoint fun L ↦ L.1) := by
    dsimp [R]
    exact radialLowLines_pairwiseDisjoint hp
  have hsum : ∑ L ∈ R, L.1.card = (R.biUnion fun L ↦ L.1).card := by
    exact (Finset.card_biUnion hdisj).symm
  have hunion : (R.biUnion fun L ↦ L.1) ⊆ P := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨L, hLR, hxL⟩ := hx
    exact connectingLine_subset L.2 hxL
  have hsmall : 2 * R.card ≤ ∑ L ∈ R, L.1.card := by
    calc
      2 * R.card = ∑ _L ∈ R, 2 := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro L hL
        exact connectingLine_card_two_le L.2
  rw [hsum] at hsmall
  exact hsmall.trans (Finset.card_le_card hunion)

/-- Connecting lines with at most four points.  The affine sweep loses two
units of projective defect, and this one-extra-point cutoff recovers more
than enough margin for Elliott's final constant. -/
noncomputable def mediumLineSubtypes (P : Finset Point) :
    Finset {L // L ∈ connectingLines P} := by
  classical
  exact (connectingLines P).attach.filter fun L ↦ L.1.card ≤ 4

noncomputable def radialMediumLines (P : Finset Point) (p : Point) :
    Finset {L // L ∈ connectingLines P} := by
  classical
  exact (mediumLineSubtypes P).filter fun L ↦
    Collinear p (chosenLineFirst L) (chosenLineSecond L)

noncomputable def nonradialMediumLines (P : Finset Point) (p : Point) :
    Finset {L // L ∈ connectingLines P} := by
  classical
  exact (mediumLineSubtypes P).filter fun L ↦
    Noncollinear p (chosenLineFirst L) (chosenLineSecond L)

lemma mem_mediumLineSubtypes {P : Finset Point}
    {L : {L // L ∈ connectingLines P}} :
    L ∈ mediumLineSubtypes P ↔ L.1.card ≤ 4 := by
  classical
  simp [mediumLineSubtypes]

lemma mem_radialMediumLines {P : Finset Point} {p : Point}
    {L : {L // L ∈ connectingLines P}} :
    L ∈ radialMediumLines P p ↔
      L.1.card ≤ 4 ∧ Collinear p (chosenLineFirst L) (chosenLineSecond L) := by
  classical
  simp [radialMediumLines, mem_mediumLineSubtypes]

lemma mem_nonradialMediumLines {P : Finset Point} {p : Point}
    {L : {L // L ∈ connectingLines P}} :
    L ∈ nonradialMediumLines P p ↔
      L.1.card ≤ 4 ∧ Noncollinear p (chosenLineFirst L) (chosenLineSecond L) := by
  classical
  simp [nonradialMediumLines, mem_mediumLineSubtypes]

lemma card_mediumLineSubtypes_eq_filter (P : Finset Point) :
    (mediumLineSubtypes P).card =
      ((connectingLines P).filter fun L ↦ L.card ≤ 4).card := by
  classical
  rw [mediumLineSubtypes]
  have h := congrArg Finset.card
    (Finset.filter_attach (fun L : Finset Point ↦ L.card ≤ 4)
      (connectingLines P))
  simpa using h

lemma card_radialMedium_add_card_nonradial {P : Finset Point} {p : Point} :
    (radialMediumLines P p).card + (nonradialMediumLines P p).card =
      (mediumLineSubtypes P).card := by
  classical
  rw [radialMediumLines, nonradialMediumLines]
  have hsecond :
      (mediumLineSubtypes P).filter (fun L ↦
        Noncollinear p (chosenLineFirst L) (chosenLineSecond L)) =
      (mediumLineSubtypes P).filter (fun L ↦
        ¬ Collinear p (chosenLineFirst L) (chosenLineSecond L)) := by
    apply Finset.ext
    intro L
    simp only [Finset.mem_filter]
    refine and_congr_right fun _ ↦ ?_
    simp only [Noncollinear, Collinear]
  rw [hsecond]
  exact Finset.card_filter_add_card_filter_not
    (s := mediumLineSubtypes P)
    (fun L ↦ Collinear p (chosenLineFirst L) (chosenLineSecond L))

lemma radialMediumLines_pairwiseDisjoint {P : Finset Point} {p : Point}
    (hp : p ∉ P) :
    (((radialMediumLines P p : Finset {L // L ∈ connectingLines P}) :
      Set {L // L ∈ connectingLines P}).PairwiseDisjoint fun L ↦ L.1) := by
  classical
  intro L hL M hM hLM
  change Disjoint L.1 M.1
  rw [Finset.disjoint_left]
  intro x hxL hxM
  have hradL := (mem_radialMediumLines.mp hL).2
  have hradM := (mem_radialMediumLines.mp hM).2
  apply hLM
  apply Subtype.ext
  apply Finset.ext
  intro y
  rw [mem_radialLine_iff hp L hradL hxL,
    mem_radialLine_iff hp M hradM hxM]

lemma two_mul_card_radialMediumLines_le {P : Finset Point} {p : Point}
    (hp : p ∉ P) : 2 * (radialMediumLines P p).card ≤ P.card := by
  classical
  let R := radialMediumLines P p
  have hdisj : (((R : Finset {L // L ∈ connectingLines P}) :
      Set {L // L ∈ connectingLines P}).PairwiseDisjoint fun L ↦ L.1) := by
    dsimp [R]
    exact radialMediumLines_pairwiseDisjoint hp
  have hsum : ∑ L ∈ R, L.1.card = (R.biUnion fun L ↦ L.1).card :=
    (Finset.card_biUnion hdisj).symm
  have hunion : (R.biUnion fun L ↦ L.1) ⊆ P := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨L, hLR, hxL⟩ := hx
    exact connectingLine_subset L.2 hxL
  have htwo : 2 * R.card ≤ ∑ L ∈ R, L.1.card := by
    calc
      2 * R.card = ∑ _L ∈ R, 2 := by simp [mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro L hL
        exact connectingLine_card_two_le L.2
  rw [hsum] at htwo
  exact htwo.trans (Finset.card_le_card hunion)

lemma five_mul_lines_le_three_mul_medium_add_incidence (P : Finset Point) :
    5 * (connectingLines P).card ≤
      3 * (mediumLineSubtypes P).card +
        ∑ L ∈ connectingLines P, L.card := by
  classical
  have hmedium : (mediumLineSubtypes P).card =
      ∑ L ∈ connectingLines P, if L.card ≤ 4 then 1 else 0 := by
    rw [card_mediumLineSubtypes_eq_filter]
    exact (Finset.sum_boole (fun L : Finset Point ↦ L.card ≤ 4)
      (connectingLines P)).symm
  calc
    5 * (connectingLines P).card = ∑ _L ∈ connectingLines P, 5 := by
      simp [mul_comm]
    _ ≤ ∑ L ∈ connectingLines P,
        (3 * (if L.card ≤ 4 then 1 else 0) + L.card) := by
      apply Finset.sum_le_sum
      intro L hL
      have htwo := connectingLine_card_two_le hL
      by_cases hfour : L.card ≤ 4
      · simp [hfour]
        omega
      · simp [hfour]
        omega
    _ = 3 * (mediumLineSubtypes P).card +
        ∑ L ∈ connectingLines P, L.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hmedium]

lemma nine_mul_medium_lines_large
    {P : Finset Point} (hN : 393 ≤ P.card)
    (hP : ¬ ContainedInLine P)
    (hmax : ∀ L ∈ connectingLines P, L.card ≤ P.card - 6) :
    31 * P.card - 27 ≤ 9 * (mediumLineSubtypes P).card := by
  have hlines := seventeen_mul_card_sub_fifteen_le_three_mul_lines hN hP hmax
  have hmedium := five_mul_lines_le_three_mul_medium_add_incidence P
  have hinc := sum_line_card_le_card_add_three_mul_lines hP
  omega

lemma eighteen_mul_nonradialMedium_large
    {P : Finset Point} {p : Point} (hN : 393 ≤ P.card)
    (hP : ¬ ContainedInLine P)
    (hmax : ∀ L ∈ connectingLines P, L.card ≤ P.card - 6)
    (hp : p ∉ P) :
    53 * P.card - 54 ≤ 18 * (nonradialMediumLines P p).card := by
  have hmedium := nine_mul_medium_lines_large hN hP hmax
  have hpartition := card_radialMedium_add_card_nonradial (P := P) (p := p)
  have hradial := two_mul_card_radialMediumLines_le hp
  omega

lemma chosenLineFirst_ne_center {P : Finset Point} {p : Point}
    (hp : p ∉ P) (L : {L // L ∈ connectingLines P}) :
    chosenLineFirst L ≠ p := by
  intro h
  exact hp (h ▸ chosenLineFirst_mem_points L)

lemma chosenLineSecond_ne_center {P : Finset Point} {p : Point}
    (hp : p ∉ P) (L : {L // L ∈ connectingLines P}) :
    chosenLineSecond L ≠ p := by
  intro h
  exact hp (h ▸ chosenLineSecond_mem_points L)

/-- The circle obtained by inverting a connecting line; it is a proper circle
when the line is nonradial. -/
noncomputable def circleOfInvertedLine {P : Finset Point} (p : Point)
    (L : {L // L ∈ connectingLines P}) : Circle :=
  circleThrough p (pointInversion p (chosenLineFirst L))
    (pointInversion p (chosenLineSecond L))

lemma circleOfInvertedLine_noncollinear {P : Finset Point} {p : Point}
    (hp : p ∉ P) (L : {L // L ∈ connectingLines P})
    (hnonrad : Noncollinear p (chosenLineFirst L) (chosenLineSecond L)) :
    Noncollinear p (pointInversion p (chosenLineFirst L))
      (pointInversion p (chosenLineSecond L)) := by
  exact (noncollinear_center_inversions_iff
    (chosenLineFirst_ne_center hp L) (chosenLineSecond_ne_center hp L)).2 hnonrad

lemma circleOfInvertedLine_on_center {P : Finset Point} {p : Point}
    (L : {L // L ∈ connectingLines P}) :
    OnCircle (circleOfInvertedLine p L) p :=
  circleThrough_on_left _ _ _

lemma mem_line_iff_inverse_on_circle {P : Finset Point} {p z : Point}
    (hp : p ∉ P) (L : {L // L ∈ connectingLines P})
    (hnonrad : Noncollinear p (chosenLineFirst L) (chosenLineSecond L))
    (hzP : z ∈ P) :
    z ∈ L.1 ↔ OnCircle (circleOfInvertedLine p L) (pointInversion p z) := by
  have haz : chosenLineFirst L ≠ p := chosenLineFirst_ne_center hp L
  have hbz : chosenLineSecond L ≠ p := chosenLineSecond_ne_center hp L
  have hzp : z ≠ p := by
    intro h
    exact hp (h ▸ hzP)
  have hiap : pointInversion p (chosenLineFirst L) ≠ p :=
    pointInversion_ne_center haz
  have hibp : pointInversion p (chosenLineSecond L) ≠ p :=
    pointInversion_ne_center hbz
  have hizp : pointInversion p z ≠ p := pointInversion_ne_center hzp
  have hnc := circleOfInvertedLine_noncollinear hp L hnonrad
  have hkey := collinear_inversions_iff_onCircle hiap hibp hizp hnc
  rw [pointInversion_involutive haz, pointInversion_involutive hbz,
    pointInversion_involutive hzp] at hkey
  rw [← lineBlock_chosenLine_eq L, mem_lineBlock]
  exact ⟨fun hz ↦ hkey.mp hz.2, fun hz ↦ ⟨hzP, hkey.mpr hz⟩⟩

lemma circleOfInvertedLine_injOn {P : Finset Point} {p : Point}
    (hp : p ∉ P) :
    Set.InjOn (circleOfInvertedLine p)
      (nonradialLowLines P p : Set {L // L ∈ connectingLines P}) := by
  intro L hL M hM hcircle
  apply Subtype.ext
  apply Finset.ext
  intro z
  have hnonradL := (mem_nonradialLowLines.mp hL).2
  have hnonradM := (mem_nonradialLowLines.mp hM).2
  constructor
  · intro hzL
    have hzP : z ∈ P := connectingLine_subset L.2 hzL
    apply (mem_line_iff_inverse_on_circle hp M hnonradM hzP).2
    rw [← hcircle]
    exact (mem_line_iff_inverse_on_circle hp L hnonradL hzP).1 hzL
  · intro hzM
    have hzP : z ∈ P := connectingLine_subset M.2 hzM
    apply (mem_line_iff_inverse_on_circle hp L hnonradL hzP).2
    rw [hcircle]
    exact (mem_line_iff_inverse_on_circle hp M hnonradM hzP).1 hzM

/-- The finite family of circles obtained from nonradial low lines after
inversion about `p`. -/
noncomputable def inversionCircles (P : Finset Point) (p : Point) : Finset Circle := by
  classical
  exact (nonradialLowLines (invertedPoints P p) p).image
    (circleOfInvertedLine p)

lemma card_inversionCircles (P : Finset Point) (p : Point) :
    (inversionCircles P p).card =
      (nonradialLowLines (invertedPoints P p) p).card := by
  classical
  rw [inversionCircles, Finset.card_image_iff.mpr]
  exact (circleOfInvertedLine_injOn center_not_mem_invertedPoints)

lemma inversionCircles_subset_determined {P : Finset Point} {p : Point}
    (hp : p ∈ P) : inversionCircles P p ⊆ determinedCircles P := by
  classical
  intro C hC
  rw [inversionCircles, Finset.mem_image] at hC
  obtain ⟨L, hL, rfl⟩ := hC
  have hnonrad := (mem_nonradialLowLines.mp hL).2
  have haX : chosenLineFirst L ∈ invertedPoints P p := chosenLineFirst_mem_points L
  have hbX : chosenLineSecond L ∈ invertedPoints P p := chosenLineSecond_mem_points L
  have ha := pointInversion_mem_original_of_mem_inverted haX
  have hb := pointInversion_mem_original_of_mem_inverted hbX
  have hnc := circleOfInvertedLine_noncollinear
    (P := invertedPoints P p) center_not_mem_invertedPoints L hnonrad
  exact mem_determinedCircles.mpr
    ⟨p, hp,
      pointInversion p (chosenLineFirst L), ha.1,
      pointInversion p (chosenLineSecond L), hb.1,
      hnc, circleThrough_on_left _ _ _,
      circleThrough_on_middle hnc, circleThrough_on_right hnc⟩

lemma circleTrace_circleOfInvertedLine_le_four {P : Finset Point} {p : Point}
    (L : {L // L ∈ connectingLines (invertedPoints P p)})
    (hLlow : L ∈ nonradialLowLines (invertedPoints P p) p) :
    (circleTrace P (circleOfInvertedLine p L)).card ≤ 4 := by
  classical
  have hnonrad := (mem_nonradialLowLines.mp hLlow).2
  let I := L.1.image (pointInversion p)
  have hsub : circleTrace P (circleOfInvertedLine p L) ⊆ insert p I := by
    intro z hz
    rw [mem_circleTrace] at hz
    by_cases hzp : z = p
    · rw [hzp]
      exact Finset.mem_insert_self _ _
    · have hyX : pointInversion p z ∈ invertedPoints P p := by
        rw [mem_invertedPoints]
        exact ⟨z, hz.1, hzp, rfl⟩
      have hyL : pointInversion p z ∈ L.1 := by
        apply (mem_line_iff_inverse_on_circle center_not_mem_invertedPoints
          L hnonrad hyX).2
        rw [pointInversion_involutive hzp]
        exact hz.2
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨pointInversion p z, hyL, pointInversion_involutive hzp⟩)
  have hcardI : I.card ≤ L.1.card := by
    exact Finset.card_image_le
  have hcardInsert : (insert p I).card ≤ I.card + 1 := by
    by_cases hpI : p ∈ I
    · rw [Finset.insert_eq_of_mem hpI]
      omega
    · rw [Finset.card_insert_of_notMem hpI]
  have hLcard : L.1.card ≤ 3 := (mem_nonradialLowLines.mp hLlow).1
  exact (Finset.card_le_card hsub).trans (by omega)

/-- Determined circles containing at most four points of the configuration. -/
noncomputable def smallDeterminedCircles (P : Finset Point) : Finset Circle := by
  classical
  exact (determinedCircles P).filter fun C ↦ (circleTrace P C).card ≤ 4

lemma mem_smallDeterminedCircles {P : Finset Point} {C : Circle} :
    C ∈ smallDeterminedCircles P ↔
      C ∈ determinedCircles P ∧ (circleTrace P C).card ≤ 4 := by
  classical
  simp [smallDeterminedCircles]

lemma inversionCircles_subset_smallDetermined {P : Finset Point} {p : Point}
    (hp : p ∈ P) : inversionCircles P p ⊆ smallDeterminedCircles P := by
  classical
  intro C hC
  rw [inversionCircles, Finset.mem_image] at hC
  obtain ⟨L, hL, rfl⟩ := hC
  rw [mem_smallDeterminedCircles]
  refine ⟨inversionCircles_subset_determined hp ?_, ?_⟩
  · rw [inversionCircles, Finset.mem_image]
    exact ⟨L, hL, rfl⟩
  · exact circleTrace_circleOfInvertedLine_le_four L hL

lemma inversionCircles_on_center {P : Finset Point} {p : Point}
    {C : Circle} (hC : C ∈ inversionCircles P p) : OnCircle C p := by
  classical
  rw [inversionCircles, Finset.mem_image] at hC
  obtain ⟨L, hL, rfl⟩ := hC
  exact circleOfInvertedLine_on_center L

lemma circleOfInvertedLine_injOn_medium {P : Finset Point} {p : Point}
    (hp : p ∉ P) :
    Set.InjOn (circleOfInvertedLine p)
      (nonradialMediumLines P p : Set {L // L ∈ connectingLines P}) := by
  intro L hL M hM hcircle
  apply Subtype.ext
  apply Finset.ext
  intro z
  have hnonradL := (mem_nonradialMediumLines.mp hL).2
  have hnonradM := (mem_nonradialMediumLines.mp hM).2
  constructor
  · intro hzL
    have hzP : z ∈ P := connectingLine_subset L.2 hzL
    apply (mem_line_iff_inverse_on_circle hp M hnonradM hzP).2
    rw [← hcircle]
    exact (mem_line_iff_inverse_on_circle hp L hnonradL hzP).1 hzL
  · intro hzM
    have hzP : z ∈ P := connectingLine_subset M.2 hzM
    apply (mem_line_iff_inverse_on_circle hp L hnonradL hzP).2
    rw [hcircle]
    exact (mem_line_iff_inverse_on_circle hp M hnonradM hzP).1 hzM

/-- Circles obtained by inverting nonradial connecting lines with at most
four inverted points. -/
noncomputable def mediumInversionCircles (P : Finset Point) (p : Point) :
    Finset Circle := by
  classical
  exact (nonradialMediumLines (invertedPoints P p) p).image
    (circleOfInvertedLine p)

lemma card_mediumInversionCircles (P : Finset Point) (p : Point) :
    (mediumInversionCircles P p).card =
      (nonradialMediumLines (invertedPoints P p) p).card := by
  classical
  rw [mediumInversionCircles, Finset.card_image_iff.mpr]
  exact circleOfInvertedLine_injOn_medium center_not_mem_invertedPoints

lemma mediumInversionCircles_subset_determined {P : Finset Point} {p : Point}
    (hp : p ∈ P) : mediumInversionCircles P p ⊆ determinedCircles P := by
  classical
  intro C hC
  rw [mediumInversionCircles, Finset.mem_image] at hC
  obtain ⟨L, hL, rfl⟩ := hC
  have hnonrad := (mem_nonradialMediumLines.mp hL).2
  have haX : chosenLineFirst L ∈ invertedPoints P p := chosenLineFirst_mem_points L
  have hbX : chosenLineSecond L ∈ invertedPoints P p := chosenLineSecond_mem_points L
  have ha := pointInversion_mem_original_of_mem_inverted haX
  have hb := pointInversion_mem_original_of_mem_inverted hbX
  have hnc := circleOfInvertedLine_noncollinear
    (P := invertedPoints P p) center_not_mem_invertedPoints L hnonrad
  exact mem_determinedCircles.mpr
    ⟨p, hp,
      pointInversion p (chosenLineFirst L), ha.1,
      pointInversion p (chosenLineSecond L), hb.1,
      hnc, circleThrough_on_left _ _ _,
      circleThrough_on_middle hnc, circleThrough_on_right hnc⟩

lemma circleTrace_circleOfInvertedLine_le_five {P : Finset Point} {p : Point}
    (L : {L // L ∈ connectingLines (invertedPoints P p)})
    (hLmedium : L ∈ nonradialMediumLines (invertedPoints P p) p) :
    (circleTrace P (circleOfInvertedLine p L)).card ≤ 5 := by
  classical
  have hnonrad := (mem_nonradialMediumLines.mp hLmedium).2
  let I := L.1.image (pointInversion p)
  have hsub : circleTrace P (circleOfInvertedLine p L) ⊆ insert p I := by
    intro z hz
    rw [mem_circleTrace] at hz
    by_cases hzp : z = p
    · rw [hzp]
      exact Finset.mem_insert_self _ _
    · have hyX : pointInversion p z ∈ invertedPoints P p := by
        rw [mem_invertedPoints]
        exact ⟨z, hz.1, hzp, rfl⟩
      have hyL : pointInversion p z ∈ L.1 := by
        apply (mem_line_iff_inverse_on_circle center_not_mem_invertedPoints
          L hnonrad hyX).2
        rw [pointInversion_involutive hzp]
        exact hz.2
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨pointInversion p z, hyL, pointInversion_involutive hzp⟩)
  have hcardI : I.card ≤ L.1.card := Finset.card_image_le
  have hcardInsert : (insert p I).card ≤ I.card + 1 := by
    by_cases hpI : p ∈ I
    · rw [Finset.insert_eq_of_mem hpI]
      omega
    · rw [Finset.card_insert_of_notMem hpI]
  have hLcard : L.1.card ≤ 4 := (mem_nonradialMediumLines.mp hLmedium).1
  exact (Finset.card_le_card hsub).trans (by omega)

/-- Determined circles containing at most five points of the configuration. -/
noncomputable def mediumDeterminedCircles (P : Finset Point) : Finset Circle := by
  classical
  exact (determinedCircles P).filter fun C ↦ (circleTrace P C).card ≤ 5

lemma mem_mediumDeterminedCircles {P : Finset Point} {C : Circle} :
    C ∈ mediumDeterminedCircles P ↔
      C ∈ determinedCircles P ∧ (circleTrace P C).card ≤ 5 := by
  classical
  simp [mediumDeterminedCircles]

lemma mediumInversionCircles_subset_mediumDetermined
    {P : Finset Point} {p : Point} (hp : p ∈ P) :
    mediumInversionCircles P p ⊆ mediumDeterminedCircles P := by
  classical
  intro C hC
  rw [mediumInversionCircles, Finset.mem_image] at hC
  obtain ⟨L, hL, rfl⟩ := hC
  rw [mem_mediumDeterminedCircles]
  refine ⟨mediumInversionCircles_subset_determined hp ?_, ?_⟩
  · rw [mediumInversionCircles, Finset.mem_image]
    exact ⟨L, hL, rfl⟩
  · exact circleTrace_circleOfInvertedLine_le_five L hL

lemma mediumInversionCircles_on_center {P : Finset Point} {p : Point}
    {C : Circle} (hC : C ∈ mediumInversionCircles P p) : OnCircle C p := by
  classical
  rw [mediumInversionCircles, Finset.mem_image] at hC
  obtain ⟨L, hL, rfl⟩ := hC
  exact circleOfInvertedLine_on_center L

/-- The inverse images in the original configuration of the points of an
inverted connecting line. -/
noncomputable def inverseLinePoints {P : Finset Point} (p : Point)
    (L : {L // L ∈ connectingLines (invertedPoints P p)}) : Finset Point := by
  classical
  exact L.1.image (pointInversion p)

lemma card_inverseLinePoints {P : Finset Point} {p : Point}
    (L : {L // L ∈ connectingLines (invertedPoints P p)}) :
    (inverseLinePoints p L).card = L.1.card := by
  classical
  rw [inverseLinePoints, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact pointInversion_injective_off p
    (fun h ↦ center_not_mem_invertedPoints (h ▸
      connectingLine_subset L.2 hx))
    (fun h ↦ center_not_mem_invertedPoints (h ▸
      connectingLine_subset L.2 hy)) hxy

lemma center_not_mem_inverseLinePoints {P : Finset Point} {p : Point}
    (L : {L // L ∈ connectingLines (invertedPoints P p)}) :
    p ∉ inverseLinePoints p L := by
  classical
  intro hp
  rw [inverseLinePoints, Finset.mem_image] at hp
  obtain ⟨x, hx, hxp⟩ := hp
  have hxne : x ≠ p := fun h ↦ center_not_mem_invertedPoints
    (h ▸ connectingLine_subset L.2 hx)
  exact pointInversion_ne_center hxne hxp

lemma inverseLinePoints_subset_original {P : Finset Point} {p : Point}
    (L : {L // L ∈ connectingLines (invertedPoints P p)}) :
    inverseLinePoints p L ⊆ P := by
  classical
  intro x hx
  rw [inverseLinePoints, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (pointInversion_mem_original_of_mem_inverted
    (connectingLine_subset L.2 hy)).1

/-- The generic case: no connecting line and no circle contains all but at
most five points. -/
def NoLargeLineOrCircle (P : Finset Point) : Prop :=
  (∀ L ∈ connectingLines P, L.card ≤ P.card - 6) ∧
  (∀ C : Circle, (circleTrace P C).card ≤ P.card - 6)

lemma inverted_connectingLine_card_le {P : Finset Point} {p : Point}
    (hpP : p ∈ P) (hgeneric : NoLargeLineOrCircle P)
    (L : {L // L ∈ connectingLines (invertedPoints P p)}) :
    L.1.card ≤ (invertedPoints P p).card - 6 := by
  classical
  have hXcard := card_invertedPoints hpP
  have hInvCard := card_inverseLinePoints L
  have hpInv := center_not_mem_inverseLinePoints L
  by_cases hrad : Collinear p (chosenLineFirst L) (chosenLineSecond L)
  · let a := pointInversion p (chosenLineFirst L)
    have haP : a ∈ P := (pointInversion_mem_original_of_mem_inverted
      (chosenLineFirst_mem_points L)).1
    have hap : a ≠ p := (pointInversion_mem_original_of_mem_inverted
      (chosenLineFirst_mem_points L)).2
    have hblock : lineBlock P p a ∈ connectingLines P :=
      lineBlock_mem_connectingLines hpP haP (Ne.symm hap)
    have hsub : insert p (inverseLinePoints p L) ⊆ lineBlock P p a := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact left_mem_lineBlock hpP
      · rw [inverseLinePoints, Finset.mem_image] at hz
        obtain ⟨y, hyL, rfl⟩ := hz
        have hyX : y ∈ invertedPoints P p := connectingLine_subset L.2 hyL
        have hyne : y ≠ p := fun h ↦ center_not_mem_invertedPoints (h ▸ hyX)
        have hfirstne := chosenLineFirst_ne_center
          (P := invertedPoints P p) center_not_mem_invertedPoints L
        have hcol : Collinear p (chosenLineFirst L) y :=
          (mem_radialLine_iff center_not_mem_invertedPoints L hrad
            (chosenLineFirst_mem L)).1 hyL |>.2
        rw [mem_lineBlock]
        refine ⟨(pointInversion_mem_original_of_mem_inverted hyX).1, ?_⟩
        exact (collinear_center_inversions_iff hfirstne hyne).2 hcol
    have hcardSub := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hpInv, hInvCard] at hcardSub
    have hmax := hgeneric.1 _ hblock
    omega
  · have hnonrad : Noncollinear p (chosenLineFirst L) (chosenLineSecond L) := by
      exact hrad
    let C := circleOfInvertedLine p L
    have hsub : insert p (inverseLinePoints p L) ⊆ circleTrace P C := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact mem_circleTrace.mpr ⟨hpP, circleOfInvertedLine_on_center L⟩
      · rw [inverseLinePoints, Finset.mem_image] at hz
        obtain ⟨y, hyL, rfl⟩ := hz
        have hyX : y ∈ invertedPoints P p := connectingLine_subset L.2 hyL
        exact mem_circleTrace.mpr
          ⟨(pointInversion_mem_original_of_mem_inverted hyX).1,
            (mem_line_iff_inverse_on_circle center_not_mem_invertedPoints
              L hnonrad hyX).1 hyL⟩
    have hcardSub := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hpInv, hInvCard] at hcardSub
    have hmax := hgeneric.2 C
    omega

lemma invertedPoints_not_containedInLine {P : Finset Point} {p : Point}
    (hcard : 3 ≤ P.card) (hpP : p ∈ P)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P) :
    ¬ ContainedInLine (invertedPoints P p) := by
  classical
  intro hXline
  obtain ⟨a, b, hab, hline⟩ := hXline
  have hXcard := card_invertedPoints hpP
  have hXtwo : 1 < (invertedPoints P p).card := by omega
  obtain ⟨x, hxX, y, hyX, hxy⟩ := Finset.one_lt_card.mp hXtwo
  have hxyLine : ∀ z ∈ invertedPoints P p, Collinear x y z := by
    intro z hzX
    exact (collinear_line_unique hab hxy (hline x hxX) (hline y hyX)).mp
      (hline z hzX)
  have hxp : x ≠ p := fun h ↦ center_not_mem_invertedPoints (h ▸ hxX)
  have hyp : y ≠ p := fun h ↦ center_not_mem_invertedPoints (h ▸ hyX)
  by_cases hrad : Collinear p x y
  · apply hPline
    refine ⟨p, pointInversion p x, Ne.symm (pointInversion_ne_center hxp), ?_⟩
    intro z hzP
    by_cases hzp : z = p
    · rw [hzp]
      exact collinear_left _ _
    · have hizX : pointInversion p z ∈ invertedPoints P p := by
        rw [mem_invertedPoints]
        exact ⟨z, hzP, hzp, rfl⟩
      have hpxiz : Collinear p x (pointInversion p z) := by
        have hlinep : Collinear x y p := collinear_rotate.mp hrad
        exact (collinear_line_unique hxy (Ne.symm hxp) hlinep
          (collinear_left x y)).mp
          (hxyLine _ hizX)
      have hizp := pointInversion_ne_center hzp
      have hinv := (collinear_center_inversions_iff hxp hizp).2 hpxiz
      rw [pointInversion_involutive hzp] at hinv
      exact hinv
  · apply hPcircle
    let C := circleThrough p (pointInversion p x) (pointInversion p y)
    refine ⟨C, ?_⟩
    intro z hzP
    by_cases hzp : z = p
    · rw [hzp]
      exact circleThrough_on_left _ _ _
    · have hizX : pointInversion p z ∈ invertedPoints P p := by
        rw [mem_invertedPoints]
        exact ⟨z, hzP, hzp, rfl⟩
      have hncxy : Noncollinear p x y := hrad
      have hnc : Noncollinear p (pointInversion p x) (pointInversion p y) :=
        (noncollinear_center_inversions_iff hxp hyp).2 hncxy
      have hixp := pointInversion_ne_center hxp
      have hiyp := pointInversion_ne_center hyp
      have hkey := collinear_inversions_iff_onCircle hixp hiyp hzp hnc
      rw [pointInversion_involutive hxp, pointInversion_involutive hyp] at hkey
      exact hkey.mp (hxyLine _ hizX)

lemma inversionCircles_many_of_lineDefect {P : Finset Point} {p : Point}
    (hN : 394 ≤ P.card) (hpP : p ∈ P)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P)
    (hgeneric : NoLargeLineOrCircle P)
    (hM : (3 : ℤ) ≤ lineDefect (invertedPoints P p)) :
    5 * P.card - 52 ≤ 2 * (inversionCircles P p).card := by
  classical
  let X := invertedPoints P p
  have hXcard : X.card = P.card - 1 := card_invertedPoints hpP
  have hXlarge : 393 ≤ X.card := by omega
  have hXline : ¬ ContainedInLine X :=
    invertedPoints_not_containedInLine (by omega) hpP hPline hPcircle
  have hmax : ∀ L ∈ connectingLines X, L.card ≤ X.card - 6 := by
    intro L hL
    exact inverted_connectingLine_card_le hpP hgeneric ⟨L, hL⟩
  have hlines : 6 * X.card - 50 ≤ (connectingLines X).card :=
    kellyMoser_six_of_lineDefect hXlarge hXline hmax hM
  have hsmall := small_lines_of_lineDefect X hM
  have hlowcard := card_lowLineSubtypes X
  have hpartition := card_radial_add_card_nonradial (P := X) (p := p)
  have hradial := two_mul_card_radialLowLines_le
    (P := X) (p := p) center_not_mem_invertedPoints
  have hcirclecard := card_inversionCircles P p
  change (inversionCircles P p).card = (nonradialLowLines X p).card at hcirclecard
  have hthree : 6 * X.card - 47 ≤
      2 * (linesOfSize X 2).card + (linesOfSize X 3).card := by
    omega
  have htwolow :
      2 * (linesOfSize X 2).card + (linesOfSize X 3).card ≤
        2 * ((linesOfSize X 2).card + (linesOfSize X 3).card) := by omega
  omega

lemma mediumInversionCircles_many {P : Finset Point} {p : Point}
    (hN : 394 ≤ P.card) (hpP : p ∈ P)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P)
    (hgeneric : NoLargeLineOrCircle P) :
    53 * P.card - 107 ≤ 18 * (mediumInversionCircles P p).card := by
  let X := invertedPoints P p
  have hXcard : X.card = P.card - 1 := card_invertedPoints hpP
  have hXlarge : 393 ≤ X.card := by omega
  have hXline : ¬ ContainedInLine X :=
    invertedPoints_not_containedInLine (by omega) hpP hPline hPcircle
  have hmax : ∀ L ∈ connectingLines X, L.card ≤ X.card - 6 := by
    intro L hL
    exact inverted_connectingLine_card_le hpP hgeneric ⟨L, hL⟩
  have hmany := eighteen_mul_nonradialMedium_large hXlarge hXline hmax
    center_not_mem_invertedPoints
  have hcard := card_mediumInversionCircles P p
  change (mediumInversionCircles P p).card =
    (nonradialMediumLines X p).card at hcard
  omega

/-- Small determined circles incident with one point. -/
noncomputable def smallCirclesThrough (P : Finset Point) (p : Point) :
    Finset Circle := by
  classical
  exact (smallDeterminedCircles P).filter fun C ↦ OnCircle C p

lemma inversionCircles_subset_smallCirclesThrough {P : Finset Point} {p : Point}
    (hp : p ∈ P) : inversionCircles P p ⊆ smallCirclesThrough P p := by
  classical
  intro C hC
  rw [smallCirclesThrough, Finset.mem_filter]
  exact ⟨inversionCircles_subset_smallDetermined hp hC,
    inversionCircles_on_center hC⟩

lemma sum_card_smallCirclesThrough (P : Finset Point) :
    ∑ p ∈ P, (smallCirclesThrough P p).card =
      ∑ C ∈ smallDeterminedCircles P, (circleTrace P C).card := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ C ∈ smallDeterminedCircles P,
        if OnCircle C p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [smallCirclesThrough]
      exact (Finset.sum_boole (fun C : Circle ↦ OnCircle C p)
        (smallDeterminedCircles P)).symm
    _ = ∑ C ∈ smallDeterminedCircles P, ∑ p ∈ P,
        if OnCircle C p then 1 else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [circleTrace]
      exact Finset.sum_boole (OnCircle C) P

lemma sum_circleTrace_small_le (P : Finset Point) :
    ∑ C ∈ smallDeterminedCircles P, (circleTrace P C).card ≤
      4 * (smallDeterminedCircles P).card := by
  classical
  calc
    _ ≤ ∑ _C ∈ smallDeterminedCircles P, 4 := by
      apply Finset.sum_le_sum
      intro C hC
      exact (mem_smallDeterminedCircles.mp hC).2
    _ = _ := by simp [mul_comm]

lemma eight_mul_smallDetermined_ge_of_lineDefect
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P)
    (hgeneric : NoLargeLineOrCircle P)
    (hM : ∀ p ∈ P, (3 : ℤ) ≤ lineDefect (invertedPoints P p)) :
    P.card * (5 * P.card - 52) ≤
      8 * (smallDeterminedCircles P).card := by
  classical
  have hpoint : ∀ p ∈ P,
      5 * P.card - 52 ≤ 2 * (smallCirclesThrough P p).card := by
    intro p hp
    have hinv := inversionCircles_many_of_lineDefect hN hp hPline hPcircle
      hgeneric (hM p hp)
    exact hinv.trans (Nat.mul_le_mul_left 2
      (Finset.card_le_card (inversionCircles_subset_smallCirclesThrough hp)))
  have hsum : P.card * (5 * P.card - 52) ≤
      2 * ∑ p ∈ P, (smallCirclesThrough P p).card := by
    calc
      _ = ∑ _p ∈ P, (5 * P.card - 52) := by simp [mul_comm]
      _ ≤ ∑ p ∈ P, 2 * (smallCirclesThrough P p).card := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p hp
      _ = _ := by rw [Finset.mul_sum]
  rw [sum_card_smallCirclesThrough] at hsum
  have hupp : 2 * ∑ C ∈ smallDeterminedCircles P, (circleTrace P C).card ≤
      2 * (4 * (smallDeterminedCircles P).card) :=
    Nat.mul_le_mul_left 2 (sum_circleTrace_small_le P)
  exact hsum.trans (by
    calc
      _ ≤ 2 * (4 * (smallDeterminedCircles P).card) := hupp
      _ = _ := by ring)

lemma correctedBound_le_of_eight_circle_estimate {n c : ℕ}
    (hn : 394 ≤ n) (hest : n * (5 * n - 52) ≤ 8 * c) :
    correctedBound n ≤ c := by
  have hchoose := two_mul_choose_two (n - 1)
  have hnsub : n - 1 - 1 = n - 2 := by omega
  rw [hnsub] at hchoose
  have hsubfive : 5 * n - 52 + 52 = 5 * n := by omega
  have hsubone : n - 1 + 1 = n := by omega
  have hsubtwo : n - 2 + 2 = n := by omega
  have hquad : 40 * n + 16 ≤ n * n := by
    have hmul : 41 * n ≤ n * n := by
      exact Nat.mul_le_mul_right n (by omega)
    have hlin : 40 * n + 16 ≤ 41 * n := by omega
    exact hlin.trans hmul
  have hpoly : 8 * (Nat.choose (n - 1) 2 + 1) ≤ n * (5 * n - 52) := by
    nlinarith
  have hbound : correctedBound n ≤ Nat.choose (n - 1) 2 + 1 := by
    rw [correctedBound]
    omega
  have heighth := Nat.mul_le_mul_left 8 hbound
  omega

lemma correctedBound_le_determined_of_generic_of_lineDefect
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P)
    (hgeneric : NoLargeLineOrCircle P)
    (hM : ∀ p ∈ P, (3 : ℤ) ≤ lineDefect (invertedPoints P p)) :
    correctedBound P.card ≤ (determinedCircles P).card := by
  have hsmall := eight_mul_smallDetermined_ge_of_lineDefect hN hPline hPcircle
    hgeneric hM
  have hnum : correctedBound P.card ≤ (smallDeterminedCircles P).card :=
    correctedBound_le_of_eight_circle_estimate hN hsmall
  exact hnum.trans (Finset.card_le_card (Finset.filter_subset _ _))

/-- Five-point-bounded determined circles incident with one point. -/
noncomputable def mediumCirclesThrough (P : Finset Point) (p : Point) :
    Finset Circle := by
  classical
  exact (mediumDeterminedCircles P).filter fun C ↦ OnCircle C p

lemma mediumInversionCircles_subset_mediumCirclesThrough
    {P : Finset Point} {p : Point} (hp : p ∈ P) :
    mediumInversionCircles P p ⊆ mediumCirclesThrough P p := by
  classical
  intro C hC
  rw [mediumCirclesThrough, Finset.mem_filter]
  exact ⟨mediumInversionCircles_subset_mediumDetermined hp hC,
    mediumInversionCircles_on_center hC⟩

lemma sum_card_mediumCirclesThrough (P : Finset Point) :
    ∑ p ∈ P, (mediumCirclesThrough P p).card =
      ∑ C ∈ mediumDeterminedCircles P, (circleTrace P C).card := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ C ∈ mediumDeterminedCircles P,
        if OnCircle C p then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [mediumCirclesThrough]
      exact (Finset.sum_boole (fun C : Circle ↦ OnCircle C p)
        (mediumDeterminedCircles P)).symm
    _ = ∑ C ∈ mediumDeterminedCircles P, ∑ p ∈ P,
        if OnCircle C p then 1 else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [circleTrace]
      exact Finset.sum_boole (OnCircle C) P

lemma sum_circleTrace_medium_le (P : Finset Point) :
    ∑ C ∈ mediumDeterminedCircles P, (circleTrace P C).card ≤
      5 * (mediumDeterminedCircles P).card := by
  classical
  calc
    _ ≤ ∑ _C ∈ mediumDeterminedCircles P, 5 := by
      apply Finset.sum_le_sum
      intro C hC
      exact (mem_mediumDeterminedCircles.mp hC).2
    _ = _ := by simp [mul_comm]

lemma ninety_mul_mediumDetermined_ge
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P)
    (hgeneric : NoLargeLineOrCircle P) :
    P.card * (53 * P.card - 107) ≤
      90 * (mediumDeterminedCircles P).card := by
  classical
  have hpoint : ∀ p ∈ P,
      53 * P.card - 107 ≤ 18 * (mediumCirclesThrough P p).card := by
    intro p hp
    have hinv := mediumInversionCircles_many hN hp hPline hPcircle hgeneric
    exact hinv.trans (Nat.mul_le_mul_left 18
      (Finset.card_le_card
        (mediumInversionCircles_subset_mediumCirclesThrough hp)))
  have hsum : P.card * (53 * P.card - 107) ≤
      18 * ∑ p ∈ P, (mediumCirclesThrough P p).card := by
    calc
      _ = ∑ _p ∈ P, (53 * P.card - 107) := by simp [mul_comm]
      _ ≤ ∑ p ∈ P, 18 * (mediumCirclesThrough P p).card := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p hp
      _ = _ := by rw [Finset.mul_sum]
  rw [sum_card_mediumCirclesThrough] at hsum
  have hupp : 18 * ∑ C ∈ mediumDeterminedCircles P,
        (circleTrace P C).card ≤
      18 * (5 * (mediumDeterminedCircles P).card) :=
    Nat.mul_le_mul_left 18 (sum_circleTrace_medium_le P)
  exact hsum.trans (by
    calc
      _ ≤ 18 * (5 * (mediumDeterminedCircles P).card) := hupp
      _ = _ := by ring)

lemma correctedBound_le_of_ninety_circle_estimate {n c : ℕ}
    (hn : 394 ≤ n) (hest : n * (53 * n - 107) ≤ 90 * c) :
    correctedBound n ≤ c := by
  have hchoose := two_mul_choose_two (n - 1)
  have hnsub : n - 1 - 1 = n - 2 := by omega
  rw [hnsub] at hchoose
  have hsub : 53 * n - 107 + 107 = 53 * n := by omega
  have hsubone : n - 1 + 1 = n := by omega
  have hsubtwo : n - 2 + 2 = n := by omega
  have hpoly : 90 * (Nat.choose (n - 1) 2 + 1) ≤
      n * (53 * n - 107) := by
    nlinarith
  have hbound : correctedBound n ≤ Nat.choose (n - 1) 2 + 1 := by
    rw [correctedBound]
    omega
  have hninetyp := Nat.mul_le_mul_left 90 hbound
  omega

lemma correctedBound_le_determined_of_generic
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P)
    (hgeneric : NoLargeLineOrCircle P) :
    correctedBound P.card ≤ (determinedCircles P).card := by
  have hmedium := ninety_mul_mediumDetermined_ge hN hPline hPcircle hgeneric
  have hnum : correctedBound P.card ≤ (mediumDeterminedCircles P).card :=
    correctedBound_le_of_ninety_circle_estimate hN hmedium
  exact hnum.trans (Finset.card_le_card (Finset.filter_subset _ _))

/-! ## Circle-family Bonferroni estimates -/

/-- The denominator-free Bonferroni estimate for the large-line case. -/
lemma large_line_circle_union_bound
    {Q A : Finset Point} {a b : Point}
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hQ : ∀ p ∈ Q, Noncollinear a b p) :
    2 * (Q.card * Nat.choose A.card 2) ≤
      2 * (circleUnionFromPairs Q A).card +
        Q.card * (Q.card - 1) * (A.card / 2) := by
  classical
  have hinter : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q →
      (circlesFromPairs p A ∩ circlesFromPairs q A).card ≤ A.card / 2 := by
    intro p hp q hq hpq
    have htwo := card_inter_circlesFromPairs_common_line
      hab hA (hQ p hp) (hQ q hq) hpq
    change 2 * (circlesFromPairs p A ∩ circlesFromPairs q A).card ≤ A.card at htwo
    omega
  have hbon := two_mul_sum_card_le_two_mul_union_add_pair_bound
    Q (fun p ↦ circlesFromPairs p A) (A.card / 2) hinter
  have hsum : ∑ p ∈ Q, (circlesFromPairs p A).card =
      Q.card * Nat.choose A.card 2 := by
    calc
      _ = ∑ _p ∈ Q, Nat.choose A.card 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact card_circlesFromPairs_common_line hab hA (hQ p hp)
      _ = _ := by simp
  simpa only [hsum, circleUnionFromPairs] using hbon

/-- The elementary numerical comparison needed after the large-line
Bonferroni estimate. -/
lemma correctedBound_le_of_large_line_estimate
    {n k m c : ℕ} (hn : 394 ≤ n) (hk : 1 ≤ k) (hk5 : k ≤ 5)
    (hm : m = n - k)
    (hest : 2 * (k * Nat.choose m 2) ≤
      2 * c + k * (k - 1) * (m / 2)) :
    correctedBound n ≤ c := by
  interval_cases k <;> norm_num at hk hk5 hest ⊢
  · have hmn : m = n - 1 := hm
    have hc : Nat.choose m 2 ≤ c := by omega
    rw [correctedBound, ← hmn]
    have : 1 ≤ m / 2 := by omega
    omega
  · have hmn : n - 1 = m + 1 := by omega
    have hmlarge : 392 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        2 * m + 2 * (Nat.choose (n - 1) 2 + 1) ≤
          2 * (2 * Nat.choose m 2) := by
      rw [hmn] at hnchoose
      rw [hmn]
      simp only [Nat.add_sub_cancel] at hnchoose
      nlinarith
    rw [correctedBound]
    omega

  · have hmn : n - 1 = m + 2 := by omega
    have hmlarge : 391 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        6 * m + 2 * (Nat.choose (n - 1) 2 + 1) ≤
          2 * (3 * Nat.choose m 2) := by
      rw [hmn] at hnchoose
      rw [hmn]
      have hs : m + 2 - 1 = m + 1 := by omega
      rw [hs] at hnchoose
      nlinarith
    rw [correctedBound]
    omega

  · have hmn : n - 1 = m + 3 := by omega
    have hmlarge : 390 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        12 * m + 2 * (Nat.choose (n - 1) 2 + 1) ≤
          2 * (4 * Nat.choose m 2) := by
      rw [hmn] at hnchoose
      rw [hmn]
      have hs : m + 3 - 1 = m + 2 := by omega
      rw [hs] at hnchoose
      nlinarith
    rw [correctedBound]
    omega
  · have hmn : n - 1 = m + 4 := by omega
    have hmlarge : 389 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        20 * m + 2 * (Nat.choose (n - 1) 2 + 1) ≤
          2 * (5 * Nat.choose m 2) := by
      rw [hmn] at hnchoose
      rw [hmn]
      have hs : m + 4 - 1 = m + 3 := by omega
      rw [hs] at hnchoose
      nlinarith
    rw [correctedBound]
    omega

/-- Complete large-line branch: if `n-k` ambient points lie on a line and
the remaining indexed points are off it, with `1 ≤ k ≤ 5`, then the
corrected Elliott bound follows. -/
lemma correctedBound_le_determined_of_large_line
    {P A Q : Finset Point} {a b : Point} {n k : ℕ}
    (hn : 394 ≤ n) (hk : 1 ≤ k) (hk5 : k ≤ 5)
    (hab : a ≠ b) (hA : ∀ x ∈ A, Collinear a b x)
    (hQ : ∀ p ∈ Q, Noncollinear a b p)
    (hAP : A ⊆ P) (hQP : Q ⊆ P)
    (hAcard : A.card = n - k) (hQcard : Q.card = k) :
    correctedBound n ≤ (determinedCircles P).card := by
  have hest := large_line_circle_union_bound hab hA hQ
  rw [hAcard, hQcard] at hest
  have hnum : correctedBound n ≤ (circleUnionFromPairs Q A).card :=
    correctedBound_le_of_large_line_estimate hn hk hk5 rfl hest
  exact hnum.trans (Finset.card_le_card
    (circleUnionFromPairs_subset_determined hab hA hQ hAP hQP))

/-! ## The large-circle branch -/

lemma large_circle_union_bound
    {Q A : Finset Point} {G : Circle}
    (hA : ∀ x ∈ A, OnCircle G x)
    (hQ : ∀ p ∈ Q, ¬ OnCircle G p) :
    2 * (Q.card * (Nat.choose A.card 2 - A.card / 2)) ≤
      2 * (circleUnionGoodPairs Q A).card +
        Q.card * (Q.card - 1) * (A.card / 2) := by
  classical
  have hinter : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q →
      (goodCircles p A ∩ goodCircles q A).card ≤ A.card / 2 := by
    intro p hp q hq hpq
    have h := card_inter_goodCircles_le_half hA (hQ p hp) (hQ q hq) hpq
    change (goodCircles p A ∩ goodCircles q A).card ≤ A.card / 2 at h
    exact h
  have hbon := two_mul_sum_card_le_two_mul_union_add_pair_bound
    Q (fun p ↦ goodCircles p A) (A.card / 2) hinter
  have hsum : Q.card * (Nat.choose A.card 2 - A.card / 2) ≤
      ∑ p ∈ Q, (goodCircles p A).card := by
    calc
      _ = ∑ _p ∈ Q, (Nat.choose A.card 2 - A.card / 2) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        exact choose_sub_half_le_card_goodCircles hA (hQ p hp)
  have htwosum := Nat.mul_le_mul_left 2 hsum
  exact htwosum.trans (by simpa only [circleUnionGoodPairs] using hbon)

lemma correctedBound_le_of_large_circle_estimate
    {n k m c : ℕ} (hn : 394 ≤ n) (hk : 1 ≤ k) (hk5 : k ≤ 5)
    (hm : m = n - k)
    (hest : 2 * (k * (Nat.choose m 2 - m / 2)) ≤
      2 * c + k * (k - 1) * (m / 2)) :
    correctedBound n ≤ c + 1 := by
  interval_cases k <;> norm_num at hk hk5 hest ⊢
  · have hmn : m = n - 1 := hm
    rw [correctedBound, ← hmn]
    omega
  · have hmn : n - 1 = m + 1 := by omega
    have hmlarge : 392 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        6 * m + 2 * Nat.choose (n - 1) 2 ≤
          2 * (2 * Nat.choose m 2) := by
      rw [hmn] at hnchoose ⊢
      simp only [Nat.add_sub_cancel] at hnchoose
      nlinarith
    rw [correctedBound]
    omega
  · have hmn : n - 1 = m + 2 := by omega
    have hmlarge : 391 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        12 * m + 2 * Nat.choose (n - 1) 2 ≤
          2 * (3 * Nat.choose m 2) := by
      rw [hmn] at hnchoose ⊢
      have hs : m + 2 - 1 = m + 1 := by omega
      rw [hs] at hnchoose
      nlinarith
    rw [correctedBound]
    omega
  · have hmn : n - 1 = m + 3 := by omega
    have hmlarge : 390 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        20 * m + 2 * Nat.choose (n - 1) 2 ≤
          2 * (4 * Nat.choose m 2) := by
      rw [hmn] at hnchoose ⊢
      have hs : m + 3 - 1 = m + 2 := by omega
      rw [hs] at hnchoose
      nlinarith
    rw [correctedBound]
    omega
  · have hmn : n - 1 = m + 4 := by omega
    have hmlarge : 389 ≤ m := by omega
    have hmdiv : m / 2 ≤ m := Nat.div_le_self m 2
    have hmchoose := two_mul_choose_two m
    have hnchoose := two_mul_choose_two (n - 1)
    have hmpred : m - 1 + 1 = m := by omega
    have hpoly :
        30 * m + 2 * Nat.choose (n - 1) 2 ≤
          2 * (5 * Nat.choose m 2) := by
      rw [hmn] at hnchoose ⊢
      have hs : m + 4 - 1 = m + 3 := by omega
      rw [hs] at hnchoose
      nlinarith
    rw [correctedBound]
    omega

/-- Complete large-proper-circle branch for `1 ≤ k ≤ 5`. -/
lemma correctedBound_le_determined_of_large_circle
    {P A Q : Finset Point} {G : Circle} {n k : ℕ}
    (hn : 394 ≤ n) (hk : 1 ≤ k) (hk5 : k ≤ 5)
    (hA : ∀ x ∈ A, OnCircle G x)
    (hQ : ∀ p ∈ Q, ¬ OnCircle G p)
    (hAP : A ⊆ P) (hQP : Q ⊆ P)
    (hAcard : A.card = n - k) (hQcard : Q.card = k) :
    correctedBound n ≤ (determinedCircles P).card := by
  classical
  have hest := large_circle_union_bound hA hQ
  rw [hAcard, hQcard] at hest
  have hnum : correctedBound n ≤ (circleUnionGoodPairs Q A).card + 1 :=
    correctedBound_le_of_large_circle_estimate hn hk hk5 rfl hest
  have hnot : G ∉ circleUnionGoodPairs Q A :=
    baseCircle_not_mem_circleUnionGoodPairs hQ
  have hbase : G ∈ determinedCircles P := by
    apply baseCircle_mem_determined hAP hA
    rw [hAcard]
    omega
  have hsub : insert G (circleUnionGoodPairs Q A) ⊆ determinedCircles P := by
    intro C hC
    rw [Finset.mem_insert] at hC
    rcases hC with rfl | hC
    · exact hbase
    · exact circleUnionGoodPairs_subset_determined hAP hQP hC
  rw [← Finset.card_insert_of_notMem hnot] at hnum
  exact hnum.trans (Finset.card_le_card hsub)

lemma correctedBound_le_determined_of_large_connectingLine
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPline : ¬ ContainedInLine P)
    {L : Finset Point} (hL : L ∈ connectingLines P)
    (hlarge : P.card - 6 < L.card) :
    correctedBound P.card ≤ (determinedCircles P).card := by
  classical
  let Q := P \ L
  let k := Q.card
  let S : {L // L ∈ connectingLines P} := ⟨L, hL⟩
  have hLP : L ⊆ P := connectingLine_subset hL
  have hLle : L.card ≤ P.card := Finset.card_le_card hLP
  have hQcard : Q.card = P.card - L.card := by
    dsimp [Q]
    rw [Finset.card_sdiff_of_subset hLP]
  have hkcard : k = P.card - L.card := by
    exact hQcard
  have hLcard : L.card = P.card - k := by
    omega
  have hk5 : k ≤ 5 := by
    dsimp [k]
    omega
  have hk : 1 ≤ k := by
    by_contra hkzero
    have hQempty : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    apply hPline
    refine ⟨chosenLineFirst S, chosenLineSecond S,
      chosenLineFirst_ne_second S, ?_⟩
    intro x hxP
    have hxL : x ∈ L := by
      by_contra hxnot
      have hxQ : x ∈ Q := by
        change x ∈ P \ L
        rw [Finset.mem_sdiff]
        exact ⟨hxP, hxnot⟩
      rw [hQempty] at hxQ
      exact Finset.notMem_empty x hxQ
    exact chosenLine_collinear_of_mem S hxL
  have hQoff : ∀ q ∈ Q,
      Noncollinear (chosenLineFirst S) (chosenLineSecond S) q := by
    intro q hq hcol
    have hq' := hq
    change q ∈ P \ L at hq'
    rw [Finset.mem_sdiff] at hq'
    apply hq'.2
    have hEq := lineBlock_chosenLine_eq S
    change lineBlock P (chosenLineFirst S) (chosenLineSecond S) = L at hEq
    rw [← hEq, mem_lineBlock]
    exact ⟨hq'.1, hcol⟩
  exact correctedBound_le_determined_of_large_line
    (P := P) (A := L) (Q := Q)
    (a := chosenLineFirst S) (b := chosenLineSecond S)
    (n := P.card) (k := k) hN hk hk5 (chosenLineFirst_ne_second S)
    (fun x hx ↦ chosenLine_collinear_of_mem S hx) hQoff hLP
    (by dsimp [Q]; exact Finset.sdiff_subset) hLcard rfl

lemma correctedBound_le_determined_of_large_circleTrace
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPcircle : ¬ ContainedInCircle P) {C : Circle}
    (hlarge : P.card - 6 < (circleTrace P C).card) :
    correctedBound P.card ≤ (determinedCircles P).card := by
  classical
  let A := circleTrace P C
  let Q := P \ A
  let k := Q.card
  change P.card - 6 < A.card at hlarge
  have hAP : A ⊆ P := circleTrace_subset P C
  have hAle : A.card ≤ P.card := Finset.card_le_card hAP
  have hQcard : Q.card = P.card - A.card := by
    dsimp [Q]
    rw [Finset.card_sdiff_of_subset hAP]
  have hkcard : k = P.card - A.card := by
    exact hQcard
  have hAcard : A.card = P.card - k := by
    omega
  have hk5 : k ≤ 5 := by
    omega
  have hk : 1 ≤ k := by
    by_contra hkzero
    have hQempty : Q = ∅ := Finset.card_eq_zero.mp (by omega)
    apply hPcircle
    refine ⟨C, ?_⟩
    intro x hxP
    have hxA : x ∈ A := by
      by_contra hxnot
      have hxQ : x ∈ Q := by
        change x ∈ P \ A
        rw [Finset.mem_sdiff]
        exact ⟨hxP, hxnot⟩
      rw [hQempty] at hxQ
      exact Finset.notMem_empty x hxQ
    exact (mem_circleTrace.mp hxA).2
  have hAon : ∀ x ∈ A, OnCircle C x := by
    intro x hx
    exact (mem_circleTrace.mp hx).2
  have hQoff : ∀ q ∈ Q, ¬ OnCircle C q := by
    intro q hq hqC
    have hq' := hq
    change q ∈ P \ A at hq'
    rw [Finset.mem_sdiff] at hq'
    exact hq'.2 (mem_circleTrace.mpr ⟨hq'.1, hqC⟩)
  exact correctedBound_le_determined_of_large_circle
    (P := P) (A := A) (Q := Q) (G := C)
    (n := P.card) (k := k) hN hk hk5 hAon hQoff hAP
    (by dsimp [Q]; exact Finset.sdiff_subset) hAcard rfl

lemma correctedBound_le_determined_of_not_generic
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P)
    (hgeneric : ¬ NoLargeLineOrCircle P) :
    correctedBound P.card ≤ (determinedCircles P).card := by
  classical
  by_cases hlines : ∀ L ∈ connectingLines P, L.card ≤ P.card - 6
  · have hcircles : ¬ ∀ C : Circle,
        (circleTrace P C).card ≤ P.card - 6 := by
      intro hc
      exact hgeneric ⟨hlines, hc⟩
    push_neg at hcircles
    obtain ⟨C, hlarge⟩ := hcircles
    exact correctedBound_le_determined_of_large_circleTrace
      hN hPcircle hlarge
  · push_neg at hlines
    obtain ⟨L, hL, hlarge⟩ := hlines
    exact correctedBound_le_determined_of_large_connectingLine
      hN hPline hL hlarge

lemma correctedBound_le_determined
    {P : Finset Point} (hN : 394 ≤ P.card)
    (hPline : ¬ ContainedInLine P) (hPcircle : ¬ ContainedInCircle P) :
    correctedBound P.card ≤ (determinedCircles P).card := by
  by_cases hgeneric : NoLargeLineOrCircle P
  · exact correctedBound_le_determined_of_generic hN hPline hPcircle hgeneric
  · exact correctedBound_le_determined_of_not_generic
      hN hPline hPcircle hgeneric

/-! ## Explicit sharpness configuration -/

def origin : Point := (0, 0)

def eastPoint : Point := (1, 0)

def unitCircle : Circle := ⟨0, 0, -1⟩

def negPoint (x : Point) : Point := (-x.1, -x.2)

noncomputable def unitParam (t : ℝ) : Point :=
  ((1 - t ^ 2) / (1 + t ^ 2), (2 * t) / (1 + t ^ 2))

@[simp] lemma negPoint_fst (x : Point) : (negPoint x).1 = -x.1 := rfl
@[simp] lemma negPoint_snd (x : Point) : (negPoint x).2 = -x.2 := rfl

lemma negPoint_injective : Function.Injective negPoint := by
  intro x y h
  apply Prod.ext
  · have := congrArg Prod.fst h
    simp only [negPoint_fst] at this
    linarith
  · have := congrArg Prod.snd h
    simp only [negPoint_snd] at this
    linarith

lemma unitParam_on_unitCircle (t : ℝ) : OnCircle unitCircle (unitParam t) := by
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  simp only [OnCircle, unitCircle, unitParam, normSq]
  field_simp [hd]
  ring

lemma unitParam_recover (t : ℝ) :
    (unitParam t).2 / (1 + (unitParam t).1) = t := by
  have hd : 1 + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  simp only [unitParam]
  field_simp [hd]
  ring

lemma unitParam_injective : Function.Injective unitParam := by
  intro s t h
  have h' := congrArg (fun x : Point ↦ x.2 / (1 + x.1)) h
  simpa only [unitParam_recover] using h'

lemma unitParam_snd_pos {t : ℝ} (ht : 0 < t) : 0 < (unitParam t).2 := by
  simp only [unitParam]
  positivity

lemma unitParam_ne_negPoint_unitParam {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    unitParam s ≠ negPoint (unitParam t) := by
  intro h
  have h' := congrArg Prod.snd h
  have hspos := unitParam_snd_pos hs
  have htpos := unitParam_snd_pos ht
  simp only [negPoint_snd] at h'
  linarith

lemma eastPoint_ne_unitParam {t : ℝ} (ht : 0 < t) : eastPoint ≠ unitParam t := by
  intro h
  have h' := congrArg Prod.snd h
  have htpos := unitParam_snd_pos ht
  simp only [eastPoint] at h'
  linarith

lemma eastPoint_ne_negPoint_unitParam {t : ℝ} (ht : 0 < t) :
    eastPoint ≠ negPoint (unitParam t) := by
  intro h
  have h' := congrArg Prod.snd h
  have htpos := unitParam_snd_pos ht
  simp only [eastPoint, negPoint_snd] at h'
  linarith

lemma negPoint_on_unitCircle {x : Point} (hx : OnCircle unitCircle x) :
    OnCircle unitCircle (negPoint x) := by
  simp only [OnCircle, unitCircle, normSq, negPoint]
  simp only [OnCircle, unitCircle, normSq] at hx
  nlinarith

lemma origin_not_on_unitCircle : ¬ OnCircle unitCircle origin := by
  norm_num [OnCircle, unitCircle, origin, normSq]

lemma eastPoint_on_unitCircle : OnCircle unitCircle eastPoint := by
  norm_num [OnCircle, unitCircle, eastPoint, normSq]

noncomputable def upperPoints (q : ℕ) : Finset Point := by
  classical
  exact (Finset.range q).image fun i ↦ unitParam ((i + 1 : ℕ) : ℝ)

noncomputable def lowerPoints (q : ℕ) : Finset Point := by
  classical
  exact (upperPoints q).image negPoint

noncomputable def pairedPoints (q : ℕ) : Finset Point := by
  classical
  exact upperPoints q ∪ lowerPoints q

lemma mem_upperPoints {q : ℕ} {x : Point} :
    x ∈ upperPoints q ↔ ∃ i < q, x = unitParam ((i + 1 : ℕ) : ℝ) := by
  classical
  simp [upperPoints, eq_comm]

lemma mem_lowerPoints {q : ℕ} {x : Point} :
    x ∈ lowerPoints q ↔ ∃ i < q, x = negPoint (unitParam ((i + 1 : ℕ) : ℝ)) := by
  classical
  simp only [lowerPoints, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_upperPoints] at hy
    rcases hy with ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨unitParam ((i + 1 : ℕ) : ℝ), mem_upperPoints.mpr ⟨i, hi, rfl⟩, rfl⟩

lemma card_upperPoints (q : ℕ) : (upperPoints q).card = q := by
  classical
  have hinj : Set.InjOn (fun i : ℕ ↦ unitParam ((i + 1 : ℕ) : ℝ))
      (Finset.range q) := by
    intro i hi j hj hij
    have hc : ((i + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) :=
      unitParam_injective hij
    have hc' : i + 1 = j + 1 := Nat.cast_injective hc
    omega
  rw [upperPoints, Finset.card_image_iff.mpr hinj, Finset.card_range]

lemma card_lowerPoints (q : ℕ) : (lowerPoints q).card = q := by
  classical
  rw [lowerPoints, Finset.card_image_iff.mpr negPoint_injective.injOn,
    card_upperPoints]

lemma upperPoints_disjoint_lowerPoints (q : ℕ) :
    Disjoint (upperPoints q) (lowerPoints q) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxU hxL
  rw [mem_upperPoints] at hxU
  rw [mem_lowerPoints] at hxL
  rcases hxU with ⟨i, hi, rfl⟩
  rcases hxL with ⟨j, hj, hbad⟩
  have hiPos : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
  have hjPos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  exact unitParam_ne_negPoint_unitParam hiPos hjPos hbad

lemma card_pairedPoints (q : ℕ) : (pairedPoints q).card = 2 * q := by
  classical
  rw [pairedPoints, Finset.card_union_of_disjoint (upperPoints_disjoint_lowerPoints q),
    card_upperPoints, card_lowerPoints]
  omega

lemma mem_pairedPoints {q : ℕ} {x : Point} :
    x ∈ pairedPoints q ↔ x ∈ upperPoints q ∨ x ∈ lowerPoints q := by
  classical
  simp [pairedPoints]

lemma pairedPoints_on_unitCircle {q : ℕ} {x : Point} (hx : x ∈ pairedPoints q) :
    OnCircle unitCircle x := by
  rw [mem_pairedPoints] at hx
  rcases hx with hx | hx
  · rw [mem_upperPoints] at hx
    rcases hx with ⟨i, hi, rfl⟩
    exact unitParam_on_unitCircle _
  · rw [mem_lowerPoints] at hx
    rcases hx with ⟨i, hi, rfl⟩
    exact negPoint_on_unitCircle (unitParam_on_unitCircle _)

lemma eastPoint_not_mem_pairedPoints (q : ℕ) : eastPoint ∉ pairedPoints q := by
  intro h
  rw [mem_pairedPoints] at h
  rcases h with h | h
  · rw [mem_upperPoints] at h
    rcases h with ⟨i, hi, h⟩
    exact eastPoint_ne_unitParam
      (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ)) h
  · rw [mem_lowerPoints] at h
    rcases h with ⟨i, hi, h⟩
    exact eastPoint_ne_negPoint_unitParam
      (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ)) h

/-- `m` explicit unit-circle points: antipodal pairs, plus one extra point
when `m` is odd. -/
noncomputable def sharpBase (m : ℕ) : Finset Point := by
  classical
  exact if m % 2 = 0 then pairedPoints (m / 2)
    else insert eastPoint (pairedPoints (m / 2))

lemma card_sharpBase (m : ℕ) : (sharpBase m).card = m := by
  classical
  rw [sharpBase]
  split_ifs with heven
  · rw [card_pairedPoints]
    omega
  · rw [Finset.card_insert_of_notMem (eastPoint_not_mem_pairedPoints _),
      card_pairedPoints]
    omega

lemma sharpBase_on_unitCircle {m : ℕ} {x : Point} (hx : x ∈ sharpBase m) :
    OnCircle unitCircle x := by
  classical
  rw [sharpBase] at hx
  split_ifs at hx with heven
  · exact pairedPoints_on_unitCircle hx
  · rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact eastPoint_on_unitCircle
    · exact pairedPoints_on_unitCircle hx

noncomputable def intendedBadPairs (q : ℕ) : Finset (Sym2 Point) := by
  classical
  exact (Finset.range q).image fun i ↦
    s(unitParam ((i + 1 : ℕ) : ℝ), negPoint (unitParam ((i + 1 : ℕ) : ℝ)))

lemma card_intendedBadPairs (q : ℕ) : (intendedBadPairs q).card = q := by
  classical
  let f : ℕ → Sym2 Point := fun i ↦
    s(unitParam ((i + 1 : ℕ) : ℝ), negPoint (unitParam ((i + 1 : ℕ) : ℝ)))
  have hinj : Set.InjOn f (Finset.range q) := by
    intro i hi j hj heq
    dsimp [f] at heq
    rw [Sym2.eq_iff] at heq
    rcases heq with heq | heq
    · have hc : ((i + 1 : ℕ) : ℝ) = ((j + 1 : ℕ) : ℝ) :=
        unitParam_injective heq.1
      have : i + 1 = j + 1 := Nat.cast_injective hc
      omega
    · exact (unitParam_ne_negPoint_unitParam
        (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ))
        (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ)) heq.1).elim
  change ((Finset.range q).image f).card = q
  rw [Finset.card_image_iff.mpr hinj, Finset.card_range]

lemma pairedPoints_half_subset_sharpBase (m : ℕ) :
    pairedPoints (m / 2) ⊆ sharpBase m := by
  classical
  intro x hx
  rw [sharpBase]
  split_ifs with h
  · exact hx
  · exact Finset.mem_insert_of_mem hx

lemma collinear_origin_negPoint (x : Point) : Collinear origin x (negPoint x) := by
  simp only [Collinear, det, origin, negPoint]
  ring

lemma intendedBadPairs_subset_badPairs (m : ℕ) :
    intendedBadPairs (m / 2) ⊆ badPairs origin (sharpBase m) := by
  classical
  intro z hz
  rw [intendedBadPairs, Finset.mem_image] at hz
  rcases hz with ⟨i, hi, rfl⟩
  rw [Finset.mem_range] at hi
  let u := unitParam ((i + 1 : ℕ) : ℝ)
  have huU : u ∈ upperPoints (m / 2) := by
    rw [upperPoints, Finset.mem_image]
    exact ⟨i, Finset.mem_range.mpr hi, rfl⟩
  have hnuL : negPoint u ∈ lowerPoints (m / 2) := by
    rw [lowerPoints, Finset.mem_image]
    exact ⟨u, huU, rfl⟩
  have huP : u ∈ pairedPoints (m / 2) :=
    mem_pairedPoints.mpr (Or.inl huU)
  have hnuP : negPoint u ∈ pairedPoints (m / 2) :=
    mem_pairedPoints.mpr (Or.inr hnuL)
  have hune : u ≠ negPoint u := unitParam_ne_negPoint_unitParam
    (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ))
    (by positivity : (0 : ℝ) < ((i + 1 : ℕ) : ℝ))
  exact mem_badPairs_mk.mpr
    ⟨pairedPoints_half_subset_sharpBase m huP,
      pairedPoints_half_subset_sharpBase m hnuP, hune,
      collinear_origin_negPoint u⟩

lemma card_badPairs_sharpBase (m : ℕ) :
    (badPairs origin (sharpBase m)).card = m / 2 := by
  have hlower : m / 2 ≤ (badPairs origin (sharpBase m)).card := by
    rw [← card_intendedBadPairs (m / 2)]
    exact Finset.card_le_card (intendedBadPairs_subset_badPairs m)
  have hupper := two_mul_card_badPairs_le
    (A := sharpBase m) (G := unitCircle) (p := origin)
    (fun x hx ↦ sharpBase_on_unitCircle hx) origin_not_on_unitCircle
  rw [card_sharpBase] at hupper
  omega

lemma admissible_insert_off_circle
    {A : Finset Point} {G : Circle} {p : Point}
    (hA : ∀ x ∈ A, OnCircle G x) (hp : ¬ OnCircle G p)
    (hcard : 3 ≤ A.card) :
    Admissible (A.card + 1) (insert p A) := by
  classical
  have hpA : p ∉ A := by
    intro hpA
    exact hp (hA p hpA)
  refine ⟨by rw [Finset.card_insert_of_notMem hpA], ?_, ?_⟩
  · rintro ⟨r, s, hrs, hline⟩
    have hthree : 2 < A.card := by omega
    rcases Finset.two_lt_card.mp hthree with
      ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
    have hnc : Noncollinear x y z := noncollinear_of_onCircle_of_pairwise
      hxy hxz hyz (hA x hx) (hA y hy) (hA z hz)
    have hrx := hline x (Finset.mem_insert_of_mem hx)
    have hry := hline y (Finset.mem_insert_of_mem hy)
    have hrz := hline z (Finset.mem_insert_of_mem hz)
    exact hnc ((collinear_line_unique hrs hxy hrx hry).mp hrz)
  · rintro ⟨D, hD⟩
    have hthree : 2 < A.card := by omega
    rcases Finset.two_lt_card.mp hthree with
      ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
    have hnc : Noncollinear x y z := noncollinear_of_onCircle_of_pairwise
      hxy hxz hyz (hA x hx) (hA y hy) (hA z hz)
    have hDG : D = G := circle_eq_of_three hnc
      (hD x (Finset.mem_insert_of_mem hx))
      (hD y (Finset.mem_insert_of_mem hy))
      (hD z (Finset.mem_insert_of_mem hz))
      (hA x hx) (hA y hy) (hA z hz)
    exact hp (hDG ▸ hD p (Finset.mem_insert_self p A))

noncomputable def sharpConfiguration (n : ℕ) : Finset Point :=
  insert origin (sharpBase (n - 1))

lemma sharpConfiguration_admissible {n : ℕ} (hn : 4 ≤ n) :
    Admissible n (sharpConfiguration n) := by
  have h := admissible_insert_off_circle
    (A := sharpBase (n - 1))
    (fun x hx ↦ sharpBase_on_unitCircle hx) origin_not_on_unitCircle
    (by rw [card_sharpBase]; omega)
  rw [card_sharpBase] at h
  have hnsub : n - 1 + 1 = n := by omega
  rw [hnsub] at h
  simpa [sharpConfiguration] using h

lemma card_determinedCircles_sharpConfiguration {n : ℕ} (hn : 4 ≤ n) :
    (determinedCircles (sharpConfiguration n)).card = correctedBound n := by
  rw [sharpConfiguration,
    card_determinedCircles_insert_off_circle
      (fun x hx ↦ sharpBase_on_unitCircle hx) origin_not_on_unitCircle
      (by rw [card_sharpBase]; omega),
    card_sharpBase, card_badPairs_sharpBase, correctedBound]
  omega

/-- Corrected resolution of Erdős Problem 506 (Elliott, with the
Purdy--Smith correction): for every `n > 393`, the minimum number of proper
circles determined by an `n`-point set contained in neither a line nor a
circle is

`choose (n - 1) 2 + 1 - floor ((n - 1) / 2)`.

The explicit sharp configuration consists of `n - 1` points on one circle,
paired antipodally as far as possible, together with its center. -/
theorem erdos_506 {n : ℕ} (hn : 393 < n) :
    IsLeast (circleCounts n) (correctedBound n) := by
  have hn394 : 394 ≤ n := by omega
  constructor
  · rw [circleCounts]
    refine ⟨sharpConfiguration n, sharpConfiguration_admissible (by omega), ?_⟩
    exact card_determinedCircles_sharpConfiguration (by omega)
  · intro m hm
    rw [circleCounts] at hm
    obtain ⟨P, hPadm, hPm⟩ := hm
    rcases hPadm with ⟨hPcard, hPline, hPcircle⟩
    have hlower := correctedBound_le_determined
      (P := P) (by omega) hPline hPcircle
    rw [hPcard, hPm] at hlower
    exact hlower

#print axioms erdos_506


end Erdos506
