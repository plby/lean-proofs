import ErdosProblems.Erdos215.Geometry

/-!
# Rational coordinates and rational rotations for Erdős Problem 215

This file isolates the elementary affine and finite-counting facts used in
the Jackson--Mauldin construction.  An `OrientedFrame` is an origin together
with a direct orthonormal frame, encoded by its cosine and sine.  Its rational
plane is the image of `ℚ²`; its integer lattice is the image of `ℤ²`.
-/

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos215

open Set
open scoped BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Rational coordinate pairs. -/
abbrev RatPoint : Type := Fin 2 → ℚ

/-- The standard embedding of `ℚ²` in the real Euclidean plane. -/
def ratPoint (q : RatPoint) : Point :=
  WithLp.toLp 2 fun i ↦ (q i : ℝ)

@[simp]
lemma ratPoint_apply (q : RatPoint) (i : Fin 2) : ratPoint q i = (q i : ℝ) := rfl

lemma ratPoint_injective : Function.Injective ratPoint := by
  intro q r h
  funext i
  exact Rat.cast_injective (congrArg (fun p : Point ↦ p i) h)

/-- An oriented orthonormal affine frame, represented by an origin and the
cosine and sine of its direction angle. -/
structure OrientedFrame where
  origin : Point
  c : ℝ
  s : ℝ
  unit : c ^ 2 + s ^ 2 = 1

namespace OrientedFrame

/-- Convert frame coordinates to ambient coordinates. -/
def fromCoords (L : OrientedFrame) (p : Point) : Point :=
  L.origin + rotate L.c L.s p

/-- Convert ambient coordinates to frame coordinates. -/
def toCoords (L : OrientedFrame) (p : Point) : Point :=
  rotate L.c (-L.s) (p - L.origin)

lemma fromCoords_toCoords (L : OrientedFrame) (p : Point) :
    L.fromCoords (L.toCoords p) = p := by
  simp [fromCoords, toCoords, rotate_inverse_right L.c L.s L.unit]

lemma toCoords_fromCoords (L : OrientedFrame) (p : Point) :
    L.toCoords (L.fromCoords p) = p := by
  simp [fromCoords, toCoords, rotate_inverse_left L.c L.s L.unit]

lemma fromCoords_injective (L : OrientedFrame) : Function.Injective L.fromCoords := by
  intro p q h
  simpa only [L.toCoords_fromCoords] using congrArg L.toCoords h

lemma toCoords_injective (L : OrientedFrame) : Function.Injective L.toCoords := by
  intro p q h
  simpa only [L.fromCoords_toCoords] using congrArg L.fromCoords h

lemma distSq_fromCoords (L : OrientedFrame) (p q : Point) :
    distSq (L.fromCoords p) (L.fromCoords q) = distSq p q := by
  simpa [fromCoords, motion] using distSq_motion L.origin L.c L.s L.unit p q

/-- The rational-coordinate plane of a frame. -/
def IsRational (L : OrientedFrame) (p : Point) : Prop :=
  ∃ q : RatPoint, p = L.fromCoords (ratPoint q)

/-- The integer lattice of a frame. -/
def IsLatticePoint (L : OrientedFrame) (p : Point) : Prop :=
  ∃ z : IntPoint, p = L.fromCoords (intPoint z)

/-- A rational translate of the integer lattice belonging to `L`. -/
def rationalTranslate (L : OrientedFrame) (q : RatPoint) : Set Point :=
  {p | ∃ z : IntPoint, p = L.fromCoords (ratPoint q + intPoint z)}

lemma isRational_iff_toCoords (L : OrientedFrame) (p : Point) :
    L.IsRational p ↔ ∃ q : RatPoint, L.toCoords p = ratPoint q := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, L.toCoords_fromCoords _⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, (L.fromCoords_toCoords p).symm.trans (congrArg L.fromCoords hq)⟩

lemma origin_isRational (L : OrientedFrame) : L.IsRational L.origin := by
  refine ⟨0, ?_⟩
  have hzero : ratPoint (0 : RatPoint) = 0 := by
    ext i
    simp [ratPoint]
  simp [fromCoords, hzero]

/-- Rational equivalence, in its coordinate-plane form.  For orthonormal
frames this is equivalent to a finite chain of rational translations and
rational rotations. -/
def RationallyEquivalent (L K : OrientedFrame) : Prop :=
  ∀ p : Point, L.IsRational p ↔ K.IsRational p

@[refl]
lemma rationallyEquivalent_refl (L : OrientedFrame) : L.RationallyEquivalent L := by
  intro p
  rfl

@[symm]
lemma rationallyEquivalent_symm {L K : OrientedFrame}
    (h : L.RationallyEquivalent K) : K.RationallyEquivalent L := by
  intro p
  exact (h p).symm

@[trans]
lemma rationallyEquivalent_trans {L K M : OrientedFrame}
    (hLK : L.RationallyEquivalent K) (hKM : K.RationallyEquivalent M) :
    L.RationallyEquivalent M := by
  intro p
  exact (hLK p).trans (hKM p)

/-- Cosine of the rotation taking `K`-coordinates to `L`-coordinates. -/
def relativeC (L K : OrientedFrame) : ℝ := L.c * K.c + L.s * K.s

/-- Sine of the rotation taking `K`-coordinates to `L`-coordinates. -/
def relativeS (L K : OrientedFrame) : ℝ := L.c * K.s - L.s * K.c

lemma relative_unit (L K : OrientedFrame) :
    (L.relativeC K) ^ 2 + (L.relativeS K) ^ 2 = 1 := by
  dsimp [relativeC, relativeS]
  nlinarith [L.unit, K.unit]

lemma toCoords_fromCoords_other (L K : OrientedFrame) (p : Point) :
    L.toCoords (K.fromCoords p) =
      L.toCoords K.origin + rotate (L.relativeC K) (L.relativeS K) p := by
  ext i
  fin_cases i <;>
    simp [toCoords, fromCoords, rotate, relativeC, relativeS] <;> ring

/-- A rational relative rotation is one whose relative cosine and sine are
rational numbers. -/
def IsRationalRotation (L K : OrientedFrame) : Prop :=
  ∃ a b : ℚ, L.relativeC K = (a : ℝ) ∧ L.relativeS K = (b : ℝ)

lemma rational_image_of_relative
    {L K : OrientedFrame} (ho : L.IsRational K.origin)
    (hr : L.IsRationalRotation K) {p : Point} (hp : K.IsRational p) :
    L.IsRational p := by
  obtain ⟨o, ho⟩ := (L.isRational_iff_toCoords K.origin).mp ho
  obtain ⟨a, b, ha, hb⟩ := hr
  obtain ⟨q, rfl⟩ := hp
  apply (L.isRational_iff_toCoords _).mpr
  let v : RatPoint := fun i ↦ if i = 0 then o 0 + a * q 0 - b * q 1
    else o 1 + b * q 0 + a * q 1
  refine ⟨v, ?_⟩
  rw [L.toCoords_fromCoords_other K, ho, ha, hb]
  ext i
  fin_cases i <;> simp [v, rotate, ratPoint] <;> ring

lemma rationallyEquivalent_of_relative
    {L K : OrientedFrame} (ho : L.IsRational K.origin)
    (hr : L.IsRationalRotation K) : L.RationallyEquivalent K := by
  intro p
  constructor
  · intro hp
    have hKLr : K.IsRationalRotation L := by
      obtain ⟨a, b, ha, hb⟩ := hr
      refine ⟨a, -b, ?_, ?_⟩
      · dsimp [relativeC, relativeS] at ha hb ⊢
        nlinarith
      · dsimp [relativeC, relativeS] at ha hb ⊢
        push_cast
        nlinarith
    have hKLo : K.IsRational L.origin := by
      obtain ⟨q, hq⟩ := ho
      apply (K.isRational_iff_toCoords _).mpr
      obtain ⟨a, b, ha, hb⟩ := hKLr
      let v : RatPoint := fun i ↦ if i = 0 then -(a * q 0 - b * q 1)
        else -(b * q 0 + a * q 1)
      refine ⟨v, ?_⟩
      simp only [toCoords]
      rw [hq]
      ext i
      fin_cases i <;>
        simp [v, fromCoords, rotate, relativeC, relativeS] at ha hb ⊢ <;>
        rw [← ha, ← hb] <;> ring
    exact rational_image_of_relative hKLo hKLr hp
  · exact rational_image_of_relative ho hr

/-- Two distinct points which are rational in both frames force the relative
rotation to have rational cosine and sine. -/
lemma rationalRotation_of_two_common
    {L K : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxL : L.IsRational x) (hxK : K.IsRational x)
    (hyL : L.IsRational y) (hyK : K.IsRational y) :
    L.IsRationalRotation K := by
  obtain ⟨qx, hqx⟩ := hxL
  obtain ⟨rx, hrx⟩ := hxK
  obtain ⟨qy, hqy⟩ := hyL
  obtain ⟨ry, hry⟩ := hyK
  have hxcoord : ratPoint qx =
      L.toCoords K.origin + rotate (L.relativeC K) (L.relativeS K) (ratPoint rx) := by
    calc
      ratPoint qx = L.toCoords x := by rw [hqx, L.toCoords_fromCoords]
      _ = L.toCoords (K.fromCoords (ratPoint rx)) := by rw [← hrx]
      _ = _ := L.toCoords_fromCoords_other K _
  have hycoord : ratPoint qy =
      L.toCoords K.origin + rotate (L.relativeC K) (L.relativeS K) (ratPoint ry) := by
    calc
      ratPoint qy = L.toCoords y := by rw [hqy, L.toCoords_fromCoords]
      _ = L.toCoords (K.fromCoords (ratPoint ry)) := by rw [← hry]
      _ = _ := L.toCoords_fromCoords_other K _
  let u : ℚ := rx 0 - ry 0
  let v : ℚ := rx 1 - ry 1
  let m : ℚ := qx 0 - qy 0
  let n : ℚ := qx 1 - qy 1
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push_neg at h
    have hr : rx = ry := by
      funext i
      fin_cases i
      · dsimp [u] at h
        exact sub_eq_zero.mp h.1
      · dsimp [v] at h
        exact sub_eq_zero.mp h.2
    apply hxy
    rw [hrx, hry, hr]
  have hD : u ^ 2 + v ^ 2 ≠ 0 := by
    rcases huv with hu | hv
    · positivity
    · positivity
  have h0 : (m : ℝ) = L.relativeC K * (u : ℝ) - L.relativeS K * (v : ℝ) := by
    have hx0 := congrArg (fun z : Point ↦ z 0) hxcoord
    have hy0 := congrArg (fun z : Point ↦ z 0) hycoord
    simp [ratPoint, rotate] at hx0 hy0
    dsimp [m, u, v]
    push_cast
    linarith
  have h1 : (n : ℝ) = L.relativeS K * (u : ℝ) + L.relativeC K * (v : ℝ) := by
    have hx1 := congrArg (fun z : Point ↦ z 1) hxcoord
    have hy1 := congrArg (fun z : Point ↦ z 1) hycoord
    simp [ratPoint, rotate] at hx1 hy1
    dsimp [n, u, v]
    push_cast
    linarith
  let a : ℚ := (m * u + n * v) / (u ^ 2 + v ^ 2)
  let b : ℚ := (-m * v + n * u) / (u ^ 2 + v ^ 2)
  refine ⟨a, b, ?_, ?_⟩
  · dsimp [a]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hD)).2
    push_cast
    calc
      L.relativeC K * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) =
          (L.relativeC K * (u : ℝ) - L.relativeS K * (v : ℝ)) * (u : ℝ) +
            (L.relativeS K * (u : ℝ) + L.relativeC K * (v : ℝ)) * (v : ℝ) := by ring
      _ = (m : ℝ) * (u : ℝ) + (n : ℝ) * (v : ℝ) := by rw [← h0, ← h1]
  · dsimp [b]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hD)).2
    push_cast
    calc
      L.relativeS K * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) =
          -(L.relativeC K * (u : ℝ) - L.relativeS K * (v : ℝ)) * (v : ℝ) +
            (L.relativeS K * (u : ℝ) + L.relativeC K * (v : ℝ)) * (u : ℝ) := by ring
      _ = -(m : ℝ) * (v : ℝ) + (n : ℝ) * (u : ℝ) := by rw [← h0, ← h1]

/-- Two distinct common rational points determine the rational-equivalence
class of an oriented lattice. -/
theorem rationallyEquivalent_of_two_common
    {L K : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxL : L.IsRational x) (hxK : K.IsRational x)
    (hyL : L.IsRational y) (hyK : K.IsRational y) :
    L.RationallyEquivalent K := by
  have hr := rationalRotation_of_two_common hxy hxL hxK hyL hyK
  have ho : L.IsRational K.origin := by
    obtain ⟨q, hq⟩ := hxL
    obtain ⟨r, hrx⟩ := hxK
    obtain ⟨a, b, ha, hb⟩ := hr
    apply (L.isRational_iff_toCoords _).mpr
    let o : RatPoint := fun i ↦ if i = 0 then q 0 - (a * r 0 - b * r 1)
      else q 1 - (b * r 0 + a * r 1)
    refine ⟨o, ?_⟩
    have hcoord : ratPoint q = L.toCoords K.origin +
        rotate (L.relativeC K) (L.relativeS K) (ratPoint r) := by
      calc
        ratPoint q = L.toCoords x := by rw [hq, L.toCoords_fromCoords]
        _ = L.toCoords (K.fromCoords (ratPoint r)) := by rw [← hrx]
        _ = _ := L.toCoords_fromCoords_other K _
    rw [ha, hb] at hcoord
    ext i
    fin_cases i
    · have h := congrArg (fun z : Point ↦ z 0) hcoord
      simp [o, ratPoint, rotate] at h ⊢
      linarith
    · have h := congrArg (fun z : Point ↦ z 1) hcoord
      simp [o, ratPoint, rotate] at h ⊢
      linarith
  exact rationallyEquivalent_of_relative ho hr

/-- If two frames are not rationally equivalent, their rational planes have
at most one common point. -/
theorem rat_inter_subsingleton {L K : OrientedFrame}
    (hLK : ¬L.RationallyEquivalent K) :
    ∀ ⦃x : Point⦄, L.IsRational x ∧ K.IsRational x →
      ∀ ⦃y : Point⦄, L.IsRational y ∧ K.IsRational y → x = y := by
  intro x hx y hy
  by_contra hxy
  exact hLK (rationallyEquivalent_of_two_common hxy hx.1 hx.2 hy.1 hy.2)

end OrientedFrame

/-- Standard rational points, used to state the affine-line lemma in
coordinates.  The framed version follows by applying `toCoords`. -/
def IsStandardRational (p : Point) : Prop := ∃ q : RatPoint, p = ratPoint q

/-- The determinant of two plane vectors. -/
def det₂ (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

/-- An affine line through `p` with direction `v`. -/
def affineLine (p v : Point) : Set Point := {x | ∃ t : ℝ, x = p + t • v}

/-- The rational points at rational squared distance from `z`. -/
def rationalDistanceSet (z : Point) : Set Point :=
  {w | IsStandardRational w ∧ ∃ r : ℚ, distSq w z = (r : ℝ)}

lemma rational_sqDist_triple_collinear {z w₁ w₂ w₃ : Point}
    (hz : ¬IsStandardRational z)
    (hw₁ : w₁ ∈ rationalDistanceSet z)
    (hw₂ : w₂ ∈ rationalDistanceSet z)
    (hw₃ : w₃ ∈ rationalDistanceSet z) :
    det₂ (w₂ - w₁) (w₃ - w₁) = 0 := by
  obtain ⟨q₁, rfl⟩ := hw₁.1
  obtain ⟨q₂, rfl⟩ := hw₂.1
  obtain ⟨q₃, rfl⟩ := hw₃.1
  obtain ⟨r₁, hr₁⟩ := hw₁.2
  obtain ⟨r₂, hr₂⟩ := hw₂.2
  obtain ⟨r₃, hr₃⟩ := hw₃.2
  let A : ℚ := q₂ 0 - q₁ 0
  let B : ℚ := q₂ 1 - q₁ 1
  let C : ℚ := ((q₂ 0) ^ 2 + (q₂ 1) ^ 2 - r₂ -
    ((q₁ 0) ^ 2 + (q₁ 1) ^ 2 - r₁)) / 2
  let D : ℚ := q₃ 0 - q₁ 0
  let E : ℚ := q₃ 1 - q₁ 1
  let F : ℚ := ((q₃ 0) ^ 2 + (q₃ 1) ^ 2 - r₃ -
    ((q₁ 0) ^ 2 + (q₁ 1) ^ 2 - r₁)) / 2
  have hAC : (A : ℝ) * z 0 + (B : ℝ) * z 1 = (C : ℝ) := by
    simp [distSq, Fin.sum_univ_two, ratPoint] at hr₁ hr₂
    dsimp [A, B, C]
    push_cast
    nlinarith
  have hDF : (D : ℝ) * z 0 + (E : ℝ) * z 1 = (F : ℝ) := by
    simp [distSq, Fin.sum_univ_two, ratPoint] at hr₁ hr₃
    dsimp [D, E, F]
    push_cast
    nlinarith
  by_contra hdet
  have hden : A * E - B * D ≠ 0 := by
    intro h
    apply hdet
    simp [det₂, A, B, D, E, ratPoint]
    exact_mod_cast h
  let x : ℚ := (C * E - B * F) / (A * E - B * D)
  let y : ℚ := (A * F - C * D) / (A * E - B * D)
  have hx : z 0 = (x : ℝ) := by
    dsimp [x]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hden)).2
    push_cast
    calc
      z 0 * ((A : ℝ) * (E : ℝ) - (B : ℝ) * (D : ℝ)) =
          ((A : ℝ) * z 0 + (B : ℝ) * z 1) * (E : ℝ) -
            (B : ℝ) * ((D : ℝ) * z 0 + (E : ℝ) * z 1) := by ring
      _ = (C : ℝ) * (E : ℝ) - (B : ℝ) * (F : ℝ) := by rw [hAC, hDF]
  have hy : z 1 = (y : ℝ) := by
    dsimp [y]
    rw [Rat.cast_div]
    apply (eq_div_iff (by exact_mod_cast hden)).2
    push_cast
    calc
      z 1 * ((A : ℝ) * (E : ℝ) - (B : ℝ) * (D : ℝ)) =
          (A : ℝ) * ((D : ℝ) * z 0 + (E : ℝ) * z 1) -
            ((A : ℝ) * z 0 + (B : ℝ) * z 1) * (D : ℝ) := by ring
      _ = (A : ℝ) * (F : ℝ) - (C : ℝ) * (D : ℝ) := by rw [hAC, hDF]
  apply hz
  let q : RatPoint := fun i ↦ if i = 0 then x else y
  refine ⟨q, ?_⟩
  ext i
  fin_cases i
  · simpa [q, ratPoint] using hx
  · simpa [q, ratPoint] using hy

/-- Rational points at rational squared distance from a fixed irrational
point lie on an affine line. -/
theorem rational_sqDist_subset_line {z : Point} (hz : ¬IsStandardRational z) :
    ∃ p v : Point, v ≠ 0 ∧ rationalDistanceSet z ⊆ affineLine p v := by
  let e₀ : Point := WithLp.toLp 2 fun i : Fin 2 ↦ if i = 0 then 1 else 0
  have he₀ : e₀ ≠ 0 := by
    intro h
    have h0 := congrArg (fun x : Point ↦ x 0) h
    simp [e₀] at h0
  by_cases hp : ∃ p, p ∈ rationalDistanceSet z
  · obtain ⟨p, hp⟩ := hp
    by_cases hq : ∃ q, q ∈ rationalDistanceSet z ∧ q ≠ p
    · obtain ⟨q, hq, hqp⟩ := hq
      refine ⟨p, q - p, sub_ne_zero.mpr hqp, ?_⟩
      intro w hw
      have hcol := rational_sqDist_triple_collinear hz hp hq hw
      by_cases h0 : (q - p) 0 = 0
      · have h1 : (q - p) 1 ≠ 0 := by
          intro hz1
          apply sub_ne_zero.mpr hqp
          ext i
          fin_cases i
          · simpa using h0
          · simpa using hz1
        refine ⟨(w 1 - p 1) / (q - p) 1, ?_⟩
        ext i
        fin_cases i
        · have hw0 : w 0 = p 0 := by
            simp [det₂, h0] at hcol
            rcases hcol with hbad | hgood
            · exact False.elim (h1 (by simpa using hbad))
            · exact sub_eq_zero.mp hgood
          simp [hw0, h0]
        · have h1' : q 1 - p 1 ≠ 0 := by simpa using h1
          simp
          field_simp [h1']
          <;> ring
      · refine ⟨(w 0 - p 0) / (q - p) 0, ?_⟩
        ext i
        fin_cases i
        · have h0' : q 0 - p 0 ≠ 0 := by simpa using h0
          simp
          field_simp [h0']
          <;> ring
        · simp [det₂] at hcol ⊢
          have h0' : q 0 - p 0 ≠ 0 := by simpa using h0
          field_simp [h0']
          nlinarith [hcol]
    · refine ⟨p, e₀, he₀, ?_⟩
      intro w hw
      have hwp : w = p := by
        by_contra hne
        exact hq ⟨w, hw, hne⟩
      exact ⟨0, by simp [hwp]⟩
  · refine ⟨0, e₀, he₀, ?_⟩
    intro w hw
    exact False.elim (hp ⟨w, hw⟩)

/-! ## The finite fundamental-domain count -/

/-- Integer coordinate pairs, written separately here to emphasize that the
following calculation takes place in the scaled integer plane. -/
abbrev ZPair : Type := Fin 2 → ℤ

/-- The integral matrix with columns `(a,b)` and `(-b,a)`. -/
def rotIntLinear (a b : ℤ) : ZPair →ₗ[ℤ] ZPair where
  toFun z := fun i ↦ if i = 0 then a * z 0 - b * z 1 else b * z 0 + a * z 1
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' n x := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
lemma rotIntLinear_apply_zero (a b : ℤ) (z : ZPair) :
    rotIntLinear a b z 0 = a * z 0 - b * z 1 := by simp [rotIntLinear]

@[simp]
lemma rotIntLinear_apply_one (a b : ℤ) (z : ZPair) :
    rotIntLinear a b z 1 = b * z 0 + a * z 1 := by simp [rotIntLinear]

lemma rotIntLinear_injective {a b d : ℤ} (hd : d ≠ 0)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) : Function.Injective (rotIntLinear a b) := by
  rw [← LinearMap.ker_eq_bot]
  ext z
  constructor
  · intro hz
    have h0 : a * z 0 - b * z 1 = 0 := by
      simpa using congrArg (fun x : ZPair ↦ x 0) hz
    have h1 : b * z 0 + a * z 1 = 0 := by
      simpa using congrArg (fun x : ZPair ↦ x 1) hz
    have hx : (a ^ 2 + b ^ 2) * z 0 = 0 := by
      linear_combination a * h0 + b * h1
    have hy : (a ^ 2 + b ^ 2) * z 1 = 0 := by
      linear_combination -(b * h0) + a * h1
    have hab0 : a ^ 2 + b ^ 2 ≠ 0 := by
      rw [hab]
      exact pow_ne_zero 2 hd
    have hz0 : z 0 = 0 := (mul_eq_zero.mp hx).resolve_left hab0
    have hz1 : z 1 = 0 := (mul_eq_zero.mp hy).resolve_left hab0
    ext i
    fin_cases i <;> simp [hz0, hz1]
  · rintro rfl
    simp [rotIntLinear]

/-- The full-rank sublattice generated by `(a,b)` and `(-b,a)`. -/
def rotatedIntLattice (a b : ℤ) : AddSubgroup ZPair :=
  (LinearMap.range (rotIntLinear a b)).toAddSubgroup

/-- The scalar sublattice `n ℤ²`. -/
def scalarIntLattice (n : ℤ) : AddSubgroup ZPair :=
  rotatedIntLattice n 0

lemma rotIntLinear_det (a b : ℤ) : LinearMap.det (rotIntLinear a b) = a ^ 2 + b ^ 2 := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := fun i j ↦
    if i = 0 then (if j = 0 then a else -b) else (if j = 0 then b else a)
  have hmap : rotIntLinear a b = Matrix.toLin' M := by
    apply LinearMap.ext
    intro z
    funext i
    fin_cases i <;>
      rw [Matrix.toLin'_apply] <;>
      simp [rotIntLinear, M, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [hmap, LinearMap.det_toLin']
  rw [Matrix.det_fin_two]
  simp [M]
  ring

/-- The determinant-index computation for the rotated integral lattice. -/
lemma rotatedIntLattice_index {a b d : ℤ} (hd : d ≠ 0)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    (rotatedIntLattice a b).index = d.natAbs ^ 2 := by
  let N : Submodule ℤ ZPair := LinearMap.range (rotIntLinear a b)
  let e : ZPair ≃ₗ[ℤ] N :=
    LinearEquiv.ofInjective (rotIntLinear a b) (rotIntLinear_injective hd hab)
  have hcard := Submodule.natAbs_det_equiv N e
  change Nat.card (ZPair ⧸ N) = _
  rw [← hcard]
  change (LinearMap.det (rotIntLinear a b)).natAbs = _
  rw [rotIntLinear_det, hab, Int.natAbs_pow]

/-- If `d ∣ e`, then `(de)ℤ²` lies in the lattice generated by the rational
rotation numerator vectors. -/
lemma scalarIntLattice_le_rotated {a b d e : ℤ} (hde : d ∣ e)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    scalarIntLattice (d * e) ≤ rotatedIntLattice a b := by
  obtain ⟨k, rfl⟩ := hde
  rintro _ ⟨z, rfl⟩
  let w : ZPair := fun i ↦ if i = 0 then a * k * z 0 + b * k * z 1
    else -(b * k) * z 0 + a * k * z 1
  refine ⟨w, ?_⟩
  ext i
  fin_cases i
  · simp [scalarIntLattice, rotatedIntLattice, w, rotIntLinear]
    linear_combination k * z 0 * hab
  · simp [scalarIntLattice, rotatedIntLattice, w, rotIntLinear]
    linear_combination k * z 1 * hab

/-- Exact finite fundamental-domain count.  The relative index is the number
of classes of the numerator lattice modulo `(de)ℤ²`, equivalently the number
of points of `e⁻¹R(ℤ²)` in a half-open unit square. -/
theorem scaled_rot_card_fundamental {a b d e : ℤ} (hd : 0 < d) (he : 0 < e)
    (hde : d ∣ e) (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    (scalarIntLattice (d * e)).relIndex (rotatedIntLattice a b) = e.natAbs ^ 2 := by
  have hle := scalarIntLattice_le_rotated hde hab
  have hrot := rotatedIntLattice_index (ne_of_gt hd) hab
  have hscalar : (scalarIntLattice (d * e)).index = (d * e).natAbs ^ 2 := by
    apply rotatedIntLattice_index (mul_ne_zero (ne_of_gt hd) (ne_of_gt he))
    ring
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [hrot, hscalar, Int.natAbs_mul] at hmul
  have hdabs : 0 < d.natAbs ^ 2 := by positivity
  nlinarith

lemma rotatedIntLattice_multiple_le (a b d : ℤ) :
    rotatedIntLattice (d * a) (d * b) ≤ rotatedIntLattice a b := by
  rintro _ ⟨z, rfl⟩
  let w : ZPair := fun i ↦ d * z i
  refine ⟨w, ?_⟩
  ext i
  fin_cases i <;> simp [w, rotIntLinear] <;> ring

lemma rotatedIntLattice_multiple_relIndex {a b d : ℤ} (hd : 0 < d)
    (hab : a ^ 2 + b ^ 2 = d ^ 2) :
    (rotatedIntLattice (d * a) (d * b)).relIndex (rotatedIntLattice a b) =
      d.natAbs ^ 2 := by
  have hle := rotatedIntLattice_multiple_le a b d
  have hsmall : (rotatedIntLattice (d * a) (d * b)).index =
      (d * d).natAbs ^ 2 := by
    apply rotatedIntLattice_index (mul_ne_zero (ne_of_gt hd) (ne_of_gt hd))
    nlinarith
  have hlarge := rotatedIntLattice_index (ne_of_gt hd) hab
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [hsmall, hlarge, Int.natAbs_mul] at hmul
  have hpos : 0 < d.natAbs ^ 2 := by positivity
  nlinarith

/-! ## Finite transfer between commensurable lattices -/

/-- `A` meets every additive coset of `H`. -/
def HitsCosets {G : Type*} [AddCommGroup G] (A : Set G) (H : AddSubgroup G) : Prop :=
  ∀ x : G, ∃ a ∈ A, a - x ∈ H

/-- No two distinct points of `A` lie in the same coset of `H`. -/
def SeparatedMod {G : Type*} [AddCommGroup G] (A : Set G) (H : AddSubgroup G) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → a - b ∈ H → a = b

/-- The finite pigeonhole argument underlying rational-rotation transfer.
If two sublattices have the same finite index in a common superlattice, a
transversal for the first which is separated modulo the second is also a
transversal for the second. -/
theorem hitsCosets_of_equal_relIndex
    {G : Type*} [AddCommGroup G] (A : Set G) (H K M : AddSubgroup G)
    (hH : H ≤ M) (hK : K ≤ M)
    [Fintype (M ⧸ H.comap M.subtype)] [Fintype (M ⧸ K.comap M.subtype)]
    (hcard : Fintype.card (M ⧸ H.comap M.subtype) =
      Fintype.card (M ⧸ K.comap M.subtype))
    (hhit : HitsCosets A H) (hsep : SeparatedMod A K) : HitsCosets A K := by
  intro x
  let QH := M ⧸ H.comap M.subtype
  let QK := M ⧸ K.comap M.subtype
  let center (q : QH) : G := x + (Quotient.out q : M)
  let pick (q : QH) : G := Classical.choose (hhit (center q))
  have pick_mem (q : QH) : pick q ∈ A := (Classical.choose_spec (hhit (center q))).1
  have pick_res (q : QH) : pick q - center q ∈ H :=
    (Classical.choose_spec (hhit (center q))).2
  have pick_delta_mem (q : QH) : pick q - x ∈ M := by
    have hr : ((Quotient.out q : M) : G) ∈ M := (Quotient.out q : M).property
    have hs : pick q - center q ∈ M := hH (pick_res q)
    convert M.add_mem hs hr using 1 <;> simp [center] <;> abel
  let delta (q : QH) : M := ⟨pick q - x, pick_delta_mem q⟩
  let f (q : QH) : QK := QuotientAddGroup.mk (delta q)
  have hf_inj : Function.Injective f := by
    intro q r hqr
    have hkr : pick r - pick q ∈ K := by
      have hk0 : -delta q + delta r ∈ K.comap M.subtype :=
        QuotientAddGroup.eq.mp hqr
      change -(pick q - x) + (pick r - x) ∈ K at hk0
      convert hk0 using 1 <;> abel
    have hpick : pick q = pick r :=
      (hsep (pick_mem r) (pick_mem q) hkr).symm
    rw [← Quotient.out_eq' q, ← Quotient.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    change -((Quotient.out q : M) : G) + ((Quotient.out r : M) : G) ∈ H
    have hs := H.sub_mem (pick_res q) (pick_res r)
    rw [hpick] at hs
    convert hs using 1 <;> simp [center] <;> abel
  have hf_surj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩ |>.2
  obtain ⟨q, hq⟩ := hf_surj (0 : QK)
  refine ⟨pick q, pick_mem q, ?_⟩
  have hk0 : -delta q + 0 ∈ K.comap M.subtype := QuotientAddGroup.eq.mp hq
  have hkneg' : (-delta q : M) ∈ K.comap M.subtype := by simpa using hk0
  have hkneg : -(pick q - x) ∈ K := hkneg'
  simpa using K.neg_mem hkneg

/-- The special case of `hitsCosets_of_equal_relIndex` in which the common
supergroup is the whole ambient group. -/
theorem hitsCosets_of_equal_index
    {G : Type*} [AddCommGroup G] (A : Set G) (H K : AddSubgroup G)
    [Fintype (G ⧸ H)] [Fintype (G ⧸ K)]
    (hcard : Fintype.card (G ⧸ H) = Fintype.card (G ⧸ K))
    (hhit : HitsCosets A H) (hsep : SeparatedMod A K) : HitsCosets A K := by
  intro x
  let pick (q : G ⧸ H) : G := Classical.choose (hhit (x + Quotient.out q))
  have pick_mem (q : G ⧸ H) : pick q ∈ A :=
    (Classical.choose_spec (hhit (x + Quotient.out q))).1
  have pick_res (q : G ⧸ H) : pick q - (x + Quotient.out q) ∈ H :=
    (Classical.choose_spec (hhit (x + Quotient.out q))).2
  let f (q : G ⧸ H) : G ⧸ K := QuotientAddGroup.mk (pick q - x)
  have hf_inj : Function.Injective f := by
    intro q r hqr
    have hkr : pick r - pick q ∈ K := by
      have hk0 : -(pick q - x) + (pick r - x) ∈ K := QuotientAddGroup.eq.mp hqr
      convert hk0 using 1 <;> abel
    have hpick : pick q = pick r :=
      (hsep (pick_mem r) (pick_mem q) hkr).symm
    rw [← Quotient.out_eq' q, ← Quotient.out_eq' r]
    apply QuotientAddGroup.eq.mpr
    have hs := H.sub_mem (pick_res q) (pick_res r)
    rw [hpick] at hs
    convert hs using 1 <;> abel
  have hf_surj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩ |>.2
  obtain ⟨q, hq⟩ := hf_surj (0 : G ⧸ K)
  refine ⟨pick q, pick_mem q, ?_⟩
  have hk0 : -(pick q - x) ∈ K := by simpa using QuotientAddGroup.eq.mp hq
  simpa using K.neg_mem hk0

/-- Rational-rotation transfer in its exact finite form.  In the application,
`M = e⁻¹R(ℤ²)`, `H = ℤ²`, and `K = R(ℤ²)`; the equality of the two finite
indices is `scaled_rot_card_fundamental`. -/
theorem hits_rational_rotations
    {G : Type*} [AddCommGroup G] (A : Set G) (H K M : AddSubgroup G)
    (hH : H ≤ M) (hK : K ≤ M)
    [Fintype (M ⧸ H.comap M.subtype)] [Fintype (M ⧸ K.comap M.subtype)]
    (hcard : Fintype.card (M ⧸ H.comap M.subtype) =
      Fintype.card (M ⧸ K.comap M.subtype))
    (hhit : HitsCosets A H) (hsep : SeparatedMod A K) : HitsCosets A K :=
  hitsCosets_of_equal_relIndex A H K M hH hK hcard hhit hsep

/-! ## Rational-equivalence classes -/

namespace OrientedFrame

/-- The setoid of oriented frames having the same rational-coordinate plane. -/
def rationalSetoid : Setoid OrientedFrame where
  r := RationallyEquivalent
  iseqv := ⟨rationallyEquivalent_refl, rationallyEquivalent_symm,
    rationallyEquivalent_trans⟩

/-- A rational-equivalence class of oriented lattices. -/
abbrev RationalClass : Type := Quotient rationalSetoid

/-- The class of a concrete oriented frame. -/
def classOf (L : OrientedFrame) : RationalClass := Quotient.mk rationalSetoid L

/-- A classical representative of a rational-equivalence class. -/
noncomputable def representative (C : RationalClass) : OrientedFrame := Quotient.out C

@[simp]
lemma classOf_representative (C : RationalClass) : classOf (representative C) = C :=
  Quotient.out_eq C

lemma classOf_eq_iff (L K : OrientedFrame) :
    classOf L = classOf K ↔ L.RationallyEquivalent K :=
  Quotient.eq

/-- Two distinct common rational points recover equality of the quotient
classes, the interface used by the global Davies recursion. -/
theorem class_eq_of_two_common {L K : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxL : L.IsRational x) (hxK : K.IsRational x)
    (hyL : L.IsRational y) (hyK : K.IsRational y) : classOf L = classOf K :=
  (classOf_eq_iff L K).2
    (rationallyEquivalent_of_two_common hxy hxL hxK hyL hyK)

lemma rationalRotation_of_equivalent {L K : OrientedFrame}
    (hKL : K.RationallyEquivalent L) : L.IsRationalRotation K := by
  let e₀ : RatPoint := fun i ↦ if i = 0 then 1 else 0
  have he₀ : ratPoint e₀ ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : Point ↦ p 0) h
    simp [e₀, ratPoint] at h0
  have hxy : K.origin ≠ K.fromCoords (ratPoint e₀) := by
    intro h
    apply he₀
    apply K.fromCoords_injective
    calc
      K.fromCoords (ratPoint e₀) = K.origin := h.symm
      _ = K.fromCoords 0 := by simp [fromCoords]
  have hxK : K.IsRational K.origin := K.origin_isRational
  have hyK : K.IsRational (K.fromCoords (ratPoint e₀)) := ⟨e₀, rfl⟩
  have hxL : L.IsRational K.origin := (hKL K.origin).mp hxK
  have hyL : L.IsRational (K.fromCoords (ratPoint e₀)) :=
    (hKL (K.fromCoords (ratPoint e₀))).mp hyK
  exact rationalRotation_of_two_common hxy hxL hxK hyL hyK

end OrientedFrame

/-- Clear the two rational denominators of a rational point on the unit
circle.  This supplies the integral Pythagorean triple used by the finite
fundamental-domain calculation. -/
lemma clear_rational_unit_denominators {A B : ℝ} {α β : ℚ}
    (hA : A = (α : ℝ)) (hB : B = (β : ℝ)) (hunit : A ^ 2 + B ^ 2 = 1) :
    ∃ a b d : ℤ, 0 < d ∧ A = (a : ℝ) / d ∧ B = (b : ℝ) / d ∧
      a ^ 2 + b ^ 2 = d ^ 2 := by
  let d : ℤ := (α.den * β.den : ℕ)
  let a : ℤ := α.num * β.den
  let b : ℤ := β.num * α.den
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Nat.mul_pos α.pos β.pos
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have ha : A = (a : ℝ) / d := by
    rw [hA]
    dsimp [a, d]
    push_cast
    rw [show (α : ℝ) = (α.num : ℝ) / α.den by exact_mod_cast α.num_div_den.symm]
    field_simp
  have hb : B = (b : ℝ) / d := by
    rw [hB]
    dsimp [b, d]
    push_cast
    rw [show (β : ℝ) = (β.num : ℝ) / β.den by exact_mod_cast β.num_div_den.symm]
    field_simp
  refine ⟨a, b, d, hd, ha, hb, ?_⟩
  have hint : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = (d : ℝ) ^ 2 := by
    rw [ha, hb] at hunit
    field_simp [hd0] at hunit
    nlinarith
  exact_mod_cast hint

/-- An integer vector divided by a nonzero integer, regarded as a rational
coordinate vector. -/
def scaledRatPoint (n : ℤ) (z : ZPair) : RatPoint := fun i ↦ (z i : ℚ) / n

/-- Concrete rational-translate hitting predicate, kept in this foundational
module so the transfer theorem does not depend on the global recursion file. -/
def HitsFrameRationalTranslates (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ q : RatPoint, (S ∩ L.rationalTranslate q).Nonempty

/-- Concrete rational-class hitting predicate. -/
def HitsFrameRationalClass (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ K : OrientedFrame, K.RationallyEquivalent L →
    ∃ p : Point, p ∈ S ∧ K.IsLatticePoint p

/-- Rational-rotation transfer for actual oriented frames. -/
theorem RationalRotationTransferTheorem
    (S : Set Point) (L : OrientedFrame) (hpartial : IsPartialSteinhaus S)
    (hhit : HitsFrameRationalTranslates S L) : HitsFrameRationalClass S L := by
  intro K hKL
  have hrot := OrientedFrame.rationalRotation_of_equivalent hKL
  obtain ⟨α, β, hα, hβ⟩ := hrot
  obtain ⟨a, b, d, hd, hA, hB, hab⟩ :=
    clear_rational_unit_denominators hα hβ (L.relative_unit K)
  have hd0 : d ≠ 0 := ne_of_gt hd
  have horigin : L.IsRational K.origin := (hKL K.origin).mp K.origin_isRational
  obtain ⟨o, ho⟩ := (L.isRational_iff_toCoords K.origin).mp horigin
  let Λ : AddSubgroup ZPair := rotatedIntLattice a b
  let H₀ : AddSubgroup ZPair := scalarIntLattice (d * d)
  let K₀ : AddSubgroup ZPair := rotatedIntLattice (d * a) (d * b)
  have hHle : H₀ ≤ Λ := by
    exact scalarIntLattice_le_rotated (dvd_refl d) hab
  have hKle : K₀ ≤ Λ := rotatedIntLattice_multiple_le a b d
  let H : AddSubgroup Λ := H₀.comap Λ.subtype
  let J : AddSubgroup Λ := K₀.comap Λ.subtype
  have hHindex : H.index = d.natAbs ^ 2 := by
    exact scaled_rot_card_fundamental hd hd (dvd_refl d) hab
  have hJindex : J.index = d.natAbs ^ 2 := by
    exact rotatedIntLattice_multiple_relIndex hd hab
  letI : H.FiniteIndex := ⟨by rw [hHindex]; positivity⟩
  letI : J.FiniteIndex := ⟨by rw [hJindex]; positivity⟩
  letI : Fintype (Λ ⧸ H) := AddSubgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Λ ⧸ J) := AddSubgroup.fintypeQuotientOfFiniteIndex
  have hcard : Fintype.card (Λ ⧸ H) = Fintype.card (Λ ⧸ J) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hHindex.trans hJindex.symm
  let A : Set Λ := {u | L.fromCoords (ratPoint (o + scaledRatPoint (d * d) u)) ∈ S}
  have hAHit : HitsCosets A H := by
    intro x
    obtain ⟨p, hpS, z, hpz⟩ := hhit (o + scaledRatPoint (d * d) x)
    let δ : ZPair := fun i ↦ x.1 i + (d * d) * z i
    have hδ : δ ∈ Λ := by
      apply Λ.add_mem x.2
      apply hHle
      refine ⟨z, ?_⟩
      ext i
      fin_cases i <;> simp [H₀, scalarIntLattice, rotIntLinear, δ]
    let y : Λ := ⟨δ, hδ⟩
    refine ⟨y, ?_, ?_⟩
    · change L.fromCoords (ratPoint (o + scaledRatPoint (d * d) y)) ∈ S
      rw [show L.fromCoords (ratPoint (o + scaledRatPoint (d * d) y)) = p by
        rw [hpz]
        apply congrArg L.fromCoords
        ext i
        fin_cases i <;> simp [y, δ, scaledRatPoint, ratPoint]
        · field_simp
          ring
        · field_simp
          ring]
      exact hpS
    · change y.1 - x.1 ∈ H₀
      refine ⟨z, ?_⟩
      ext i
      fin_cases i <;> simp [y, δ, H₀, scalarIntLattice, rotIntLinear]
  have hASep : SeparatedMod A J := by
    intro u hu v hv huv
    change u.1 - v.1 ∈ K₀ at huv
    obtain ⟨z, hz⟩ := huv
    let pu := L.fromCoords (ratPoint (o + scaledRatPoint (d * d) u))
    let pv := L.fromCoords (ratPoint (o + scaledRatPoint (d * d) v))
    have hdist : distSq pu pv = ((z 0) ^ 2 + (z 1) ^ 2 : ℤ) := by
      rw [L.distSq_fromCoords]
      simp [pu, pv, distSq, Fin.sum_univ_two, scaledRatPoint, ratPoint]
      have hz0 := congrArg (fun w : ZPair ↦ w 0) hz
      have hz1 := congrArg (fun w : ZPair ↦ w 1) hz
      simp [K₀, rotIntLinear] at hz0 hz1
      have hz0R : (d : ℝ) * (a : ℝ) * (z 0 : ℝ) -
          (d : ℝ) * (b : ℝ) * (z 1 : ℝ) = (u.1 0 : ℝ) - (v.1 0 : ℝ) := by
        exact_mod_cast hz0
      have hz1R : (d : ℝ) * (b : ℝ) * (z 0 : ℝ) +
          (d : ℝ) * (a : ℝ) * (z 1 : ℝ) = (u.1 1 : ℝ) - (v.1 1 : ℝ) := by
        exact_mod_cast hz1
      push_cast at ⊢
      field_simp [hd0]
      rw [← hz0R, ← hz1R]
      have habR : (a : ℝ) ^ 2 + (b : ℝ) ^ 2 = (d : ℝ) ^ 2 := by exact_mod_cast hab
      calc
        ((d : ℝ) * (a : ℝ) * (z 0 : ℝ) - (d : ℝ) * (b : ℝ) * (z 1 : ℝ)) ^ 2 +
            ((d : ℝ) * (b : ℝ) * (z 0 : ℝ) + (d : ℝ) * (a : ℝ) * (z 1 : ℝ)) ^ 2 =
            (d : ℝ) ^ 2 * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) *
              ((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) := by ring
        _ = (d : ℝ) ^ 4 * ((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) := by rw [habR]; ring
    have hpq : pu = pv := by
      by_contra hpq
      exact hpartial hu hv hpq ((z 0) ^ 2 + (z 1) ^ 2) hdist
    apply Subtype.ext
    apply funext
    intro i
    have hc := congrArg (fun p : Point ↦ (L.toCoords p) i) hpq
    simp [pu, pv, L.toCoords_fromCoords, scaledRatPoint, ratPoint] at hc
    have hdr : (d : ℝ) * (d : ℝ) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hd0) (by exact_mod_cast hd0)
    have hc' : ((u.1 i : ℤ) : ℝ) = ((v.1 i : ℤ) : ℝ) :=
      (div_left_inj' hdr).mp hc
    exact_mod_cast hc'
  have hAJ : HitsCosets A J := hitsCosets_of_equal_index A H J hcard hAHit hASep
  obtain ⟨u, huA, huJ⟩ := hAJ 0
  have huJ' : u ∈ J := by simpa using huJ
  change u.1 ∈ K₀ at huJ'
  obtain ⟨z, hz⟩ := huJ'
  let p := L.fromCoords (ratPoint (o + scaledRatPoint (d * d) u))
  refine ⟨p, huA, z, ?_⟩
  apply L.toCoords_injective
  rw [L.toCoords_fromCoords, L.toCoords_fromCoords_other K, ho]
  ext i
  fin_cases i
  · have hz0 := congrArg (fun w : ZPair ↦ w 0) hz
    simp [p, scaledRatPoint, K₀, rotIntLinear, hA, hB, ratPoint] at hz0 ⊢
    have hz0R : (d : ℝ) * (a : ℝ) * (z 0 : ℝ) -
        (d : ℝ) * (b : ℝ) * (z 1 : ℝ) = (u.1 0 : ℝ) := by exact_mod_cast hz0
    push_cast at ⊢
    field_simp [hd0]
    nlinarith [hz0R]
  · have hz1 := congrArg (fun w : ZPair ↦ w 1) hz
    simp [p, scaledRatPoint, K₀, rotIntLinear, hA, hB, ratPoint] at hz1 ⊢
    have hz1R : (d : ℝ) * (b : ℝ) * (z 0 : ℝ) +
        (d : ℝ) * (a : ℝ) * (z 1 : ℝ) = (u.1 1 : ℝ) := by exact_mod_cast hz1
    push_cast at ⊢
    field_simp [hd0]
    nlinarith [hz1R]

end

end Erdos215
