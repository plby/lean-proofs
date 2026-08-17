import ErdosProblems.Erdos215.Geometry
import ErdosProblems.Erdos215.Circle

/-!
# Coordinate wrapper for the three-circle finiteness theorem

`Circle.circle_congruent_finite` proves the normalized algebraic-orientation
case.  This file performs the similarity normalization and splits an arbitrary
labelled congruent triangle into its two possible orientations.
-/

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos215

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace CircleWrapper

abbrev Pair : Type := ℝ × ℝ

def pairDistSq (p q : Pair) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

def toPair (p : Point) : Pair := (p 0, p 1)

def ofPair (p : Pair) : Point :=
  WithLp.toLp 2 fun i ↦ if i = 0 then p.1 else p.2

@[simp] lemma ofPair_apply_zero (p : Pair) : ofPair p 0 = p.1 := by simp [ofPair]
@[simp] lemma ofPair_apply_one (p : Pair) : ofPair p 1 = p.2 := by simp [ofPair]

@[simp] lemma toPair_ofPair (p : Pair) : toPair (ofPair p) = p := by
  ext <;> simp [toPair]

@[simp] lemma ofPair_toPair (p : Point) : ofPair (toPair p) = p := by
  ext i
  fin_cases i <;> simp [toPair]

lemma pairDistSq_toPair (p q : Point) : pairDistSq (toPair p) (toPair q) = distSq p q := by
  simp [pairDistSq, toPair, distSq, Fin.sum_univ_two]

def baselineLength (p q : Point) : ℝ := Real.sqrt (distSq p q)

lemma baselineLength_pos {p q : Point} (hpq : p ≠ q) : 0 < baselineLength p q := by
  rw [baselineLength, Real.sqrt_pos]
  rw [distSq_eq_dist_sq]
  have hdist : 0 < dist p q := dist_pos.mpr hpq
  positivity

lemma baselineLength_sq (p q : Point) : baselineLength p q ^ 2 = distSq p q := by
  rw [baselineLength, Real.sq_sqrt]
  rw [distSq_eq_dist_sq]
  positivity

lemma baseline_components_sq (p q : Point) :
    (q 0 - p 0) ^ 2 + (q 1 - p 1) ^ 2 = baselineLength p q ^ 2 := by
  rw [baselineLength_sq]
  simp [distSq, Fin.sum_univ_two]
  ring

/-- Direct similarity taking `p` to the origin and `q` to the positive
horizontal axis, with an additional division by `ρ`. -/
def normalize (p q : Point) (ρ : ℝ) (x : Point) : Pair :=
  let D := baselineLength p q
  let dx := q 0 - p 0
  let dy := q 1 - p 1
  ((dx * (x 0 - p 0) + dy * (x 1 - p 1)) / (D * ρ),
    (-dy * (x 0 - p 0) + dx * (x 1 - p 1)) / (D * ρ))

/-- Inverse to `normalize` when the baseline and scale are nonzero. -/
def denormalize (p q : Point) (ρ : ℝ) (x : Pair) : Point :=
  let D := baselineLength p q
  let dx := q 0 - p 0
  let dy := q 1 - p 1
  WithLp.toLp 2 fun i ↦
    if i = 0 then p 0 + ρ / D * (dx * x.1 - dy * x.2)
    else p 1 + ρ / D * (dy * x.1 + dx * x.2)

lemma normalize_self (p q : Point) {ρ : ℝ} (_hρ : ρ ≠ 0) :
    normalize p q ρ p = (0, 0) := by
  simp [normalize]

lemma normalize_second {p q : Point} (hpq : p ≠ q) {ρ : ℝ} (hρ : ρ ≠ 0) :
    normalize p q ρ q = (baselineLength p q / ρ, 0) := by
  have hD := baselineLength_pos hpq
  have hDsq := baselineLength_sq p q
  have hcomp := baseline_components_sq p q
  ext <;> simp [normalize]
  · field_simp [ne_of_gt hD, hρ]
    nlinarith
  · exact Or.inl (by ring)

lemma pairDistSq_normalize {p q : Point} (hpq : p ≠ q) {ρ : ℝ} (hρ : ρ ≠ 0)
    (x y : Point) :
    pairDistSq (normalize p q ρ x) (normalize p q ρ y) = distSq x y / ρ ^ 2 := by
  have hD := baselineLength_pos hpq
  have hcomp := baseline_components_sq p q
  simp [pairDistSq, normalize, distSq, Fin.sum_univ_two]
  field_simp [ne_of_gt hD, hρ]
  linear_combination
    ((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) * hcomp

lemma denormalize_normalize {p q : Point} (hpq : p ≠ q) {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : Point) : denormalize p q ρ (normalize p q ρ x) = x := by
  have hD := baselineLength_pos hpq
  have hcomp := baseline_components_sq p q
  ext i
  fin_cases i <;> simp [denormalize, normalize]
  · field_simp [ne_of_gt hD, hρ]
    linear_combination (x 0 - p 0) * hcomp
  · field_simp [ne_of_gt hD, hρ]
    linear_combination (x 1 - p 1) * hcomp

/-- The two possible orientations of a triangle with prescribed three side
lengths, after its first edge has been represented as `d(X,Y)`. -/
lemma triangle_two_orientations {d u v : ℝ} (hd : 0 < d)
    (p₀ p₁ p₂ : Pair)
    (h01 : pairDistSq p₀ p₁ = d ^ 2)
    (h02 : pairDistSq p₀ p₂ = u ^ 2 + v ^ 2)
    (h12 : pairDistSq p₁ p₂ = (u - d) ^ 2 + v ^ 2) :
    ∃ X Y : ℝ,
      X ^ 2 + Y ^ 2 = 1 ∧
      p₁ = (p₀.1 + d * X, p₀.2 + d * Y) ∧
      (p₂ = (p₀.1 + u * X - v * Y, p₀.2 + v * X + u * Y) ∨
       p₂ = (p₀.1 + u * X + v * Y, p₀.2 - v * X + u * Y)) := by
  let X := (p₁.1 - p₀.1) / d
  let Y := (p₁.2 - p₀.2) / d
  let a := p₂.1 - p₀.1
  let b := p₂.2 - p₀.2
  let P := a * X + b * Y
  let Q := -a * Y + b * X
  have hd0 : d ≠ 0 := ne_of_gt hd
  have h01' : (p₁.1 - p₀.1) ^ 2 + (p₁.2 - p₀.2) ^ 2 = d ^ 2 := by
    calc
      _ = pairDistSq p₀ p₁ := by simp [pairDistSq]; ring
      _ = d ^ 2 := h01
  have h02' : a ^ 2 + b ^ 2 = u ^ 2 + v ^ 2 := by
    dsimp [a, b]
    calc
      _ = pairDistSq p₀ p₂ := by simp [pairDistSq]; ring
      _ = u ^ 2 + v ^ 2 := h02
  have h12' : (p₂.1 - p₁.1) ^ 2 + (p₂.2 - p₁.2) ^ 2 =
      (u - d) ^ 2 + v ^ 2 := by
    calc
      _ = pairDistSq p₁ p₂ := by simp [pairDistSq]; ring
      _ = (u - d) ^ 2 + v ^ 2 := h12
  have hunit : X ^ 2 + Y ^ 2 = 1 := by
    dsimp [X, Y]
    field_simp [hd0]
    nlinarith [h01']
  have hP : P = u := by
    dsimp [P, a, b, X, Y]
    field_simp [hd0]
    ring_nf at h01' h02' h12' ⊢
    nlinarith
  have hPQ : P ^ 2 + Q ^ 2 = u ^ 2 + v ^ 2 := by
    dsimp [P, Q]
    calc
      (a * X + b * Y) ^ 2 + (-a * Y + b * X) ^ 2 =
          (a ^ 2 + b ^ 2) * (X ^ 2 + Y ^ 2) := by ring
      _ = a ^ 2 + b ^ 2 := by rw [hunit, mul_one]
      _ = u ^ 2 + v ^ 2 := h02'
  have hQ : Q = v ∨ Q = -v := by
    have hsq : Q ^ 2 = v ^ 2 := by rw [hP] at hPQ; nlinarith
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  refine ⟨X, Y, hunit, ?_, ?_⟩
  · ext <;> simp [X, Y] <;> field_simp [hd0] <;> ring
  · have ha : a = P * X - Q * Y := by
      calc
        a = a * (X ^ 2 + Y ^ 2) := by rw [hunit, mul_one]
        _ = P * X - Q * Y := by dsimp [P, Q]; ring
    have hb : b = Q * X + P * Y := by
      calc
        b = b * (X ^ 2 + Y ^ 2) := by rw [hunit, mul_one]
        _ = Q * X + P * Y := by dsimp [P, Q]; ring
    rcases hQ with hQ | hQ
    · left
      rw [hP, hQ] at ha hb
      ext <;> simp [a, b] at ha hb ⊢ <;> linarith
    · right
      rw [hP, hQ] at ha hb
      ext <;> simp [a, b] at ha hb ⊢ <;> linarith

end CircleWrapper

open CircleWrapper

private lemma fin3_distances_of_three (f g : Fin 3 → Point)
    (h01 : distSq (f 0) (f 1) = distSq (g 0) (g 1))
    (h02 : distSq (f 0) (f 2) = distSq (g 0) (g 2))
    (h12 : distSq (f 1) (f 2) = distSq (g 1) (g 2)) :
    ∀ i j, distSq (f i) (f j) = distSq (g i) (g j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · simp [distSq_self]
  · exact h01
  · exact h02
  · norm_num
    rw [distSq_comm (f 1) (f 0), distSq_comm (g 1) (g 0)]
    exact h01
  · simp [distSq_self]
  · exact h12
  · norm_num
    convert (show distSq (f 2) (f 0) = distSq (g 2) (g 0) by
      rw [distSq_comm (f 2) (f 0), distSq_comm (g 2) (g 0)]
      exact h02) using 1 <;> congr 2
  · norm_num
    convert (show distSq (f 2) (f 1) = distSq (g 2) (g 1) by
      rw [distSq_comm (f 2) (f 1), distSq_comm (g 2) (g 1)]
      exact h12) using 1 <;> congr 2
  · simp [distSq_self]

private lemma fin3_values_of_zero (r : Fin 3 → ℝ)
    (h1 : r 1 = r 0) (h2 : r 2 = r 0) : ∀ i j, r i = r j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all

/-- The coordinate-free three-circle finiteness statement used in the global
construction.  The two alternatives are exactly the two exceptional rigid
coincidences excluded by the normalized algebraic theorem. -/
theorem threeCircleFiniteness :
    ∀ (center target : Fin 3 → Point) (radiusSq : Fin 3 → ℝ),
      Function.Injective center →
      Function.Injective target →
      (∀ i, 0 < radiusSq i) →
      Set.Finite {z : Fin 3 → Point |
        (∀ i, distSq (center i) (z i) = radiusSq i) ∧
        ∀ i j, distSq (z i) (z j) = distSq (target i) (target j)} ∨
      ((∀ i j, radiusSq i = radiusSq j) ∧
        ∀ i j, distSq (center i) (center j) = distSq (target i) (target j)) := by
  intro center target radiusSq hcenter htarget hradius
  classical
  let Flexible : Prop :=
    (∀ i j, radiusSq i = radiusSq j) ∧
      ∀ i j, distSq (center i) (center j) = distSq (target i) (target j)
  by_cases hflex : Flexible
  · exact Or.inr hflex
  left
  have hc01 : center 0 ≠ center 1 := by
    intro h; have := hcenter h; omega
  have ht01 : target 0 ≠ target 1 := by
    intro h; have := htarget h; omega
  let ρ := Real.sqrt (radiusSq 0)
  have hρ : 0 < ρ := by dsimp [ρ]; exact Real.sqrt_pos.2 (hradius 0)
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hρsq : ρ ^ 2 = radiusSq 0 := by
    dsimp [ρ]
    exact Real.sq_sqrt (le_of_lt (hradius 0))
  let wc : Fin 3 → Pair := fun i ↦ normalize (center 0) (center 1) ρ (center i)
  let wt : Fin 3 → Pair := fun i ↦ normalize (target 0) (target 1) ρ (target i)
  let A := baselineLength (center 0) (center 1) / ρ
  let B := (wc 2).1
  let C := (wc 2).2
  let d := baselineLength (target 0) (target 1) / ρ
  let u := (wt 2).1
  let v := (wt 2).2
  let R := Real.sqrt (radiusSq 1) / ρ
  let S := Real.sqrt (radiusSq 2) / ρ
  have hA : 0 < A := div_pos (baselineLength_pos hc01) hρ
  have hd : 0 < d := div_pos (baselineLength_pos ht01) hρ
  have hwc0 : wc 0 = (0, 0) := by
    dsimp [wc]
    exact normalize_self _ _ hρ0
  have hwc1 : wc 1 = (A, 0) := by
    dsimp [wc, A]
    exact normalize_second hc01 hρ0
  have hwt0 : wt 0 = (0, 0) := by
    dsimp [wt]
    exact normalize_self _ _ hρ0
  have hwt1 : wt 1 = (d, 0) := by
    dsimp [wt, d]
    exact normalize_second ht01 hρ0
  have hc02 : center 0 ≠ center 2 := by
    intro h; have := hcenter h; omega
  have hc12 : center 1 ≠ center 2 := by
    intro h; have := hcenter h; omega
  have ht02 : target 0 ≠ target 2 := by
    intro h; have := htarget h; omega
  have ht12 : target 1 ≠ target 2 := by
    intro h; have := htarget h; omega
  have hc13 : 0 < B ^ 2 + C ^ 2 := by
    have hdist : 0 < distSq (center 0) (center 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (center 0) (center 2) := dist_pos.mpr hc02
      positivity
    have hn := pairDistSq_normalize hc01 hρ0 (center 0) (center 2)
    change pairDistSq (wc 0) (wc 2) = _ at hn
    rw [hwc0] at hn
    have heq : B ^ 2 + C ^ 2 = distSq (center 0) (center 2) / ρ ^ 2 := by
      simpa [pairDistSq, B, C] using hn
    rw [heq]
    positivity
  have hc23 : 0 < (A - B) ^ 2 + C ^ 2 := by
    have hdist : 0 < distSq (center 1) (center 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (center 1) (center 2) := dist_pos.mpr hc12
      positivity
    have hn := pairDistSq_normalize hc01 hρ0 (center 1) (center 2)
    change pairDistSq (wc 1) (wc 2) = _ at hn
    rw [hwc1] at hn
    have heq : (A - B) ^ 2 + C ^ 2 = distSq (center 1) (center 2) / ρ ^ 2 := by
      simpa [pairDistSq, B, C] using hn
    rw [heq]
    positivity
  have ht13 : 0 < u ^ 2 + v ^ 2 := by
    have hdist : 0 < distSq (target 0) (target 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (target 0) (target 2) := dist_pos.mpr ht02
      positivity
    have hn := pairDistSq_normalize ht01 hρ0 (target 0) (target 2)
    change pairDistSq (wt 0) (wt 2) = _ at hn
    rw [hwt0] at hn
    have heq : u ^ 2 + v ^ 2 = distSq (target 0) (target 2) / ρ ^ 2 := by
      simpa [pairDistSq, u, v] using hn
    rw [heq]
    positivity
  have ht23 : 0 < (u - d) ^ 2 + v ^ 2 := by
    have hdist : 0 < distSq (target 1) (target 2) := by
      rw [distSq_eq_dist_sq]
      have : 0 < dist (target 1) (target 2) := dist_pos.mpr ht12
      positivity
    have hn := pairDistSq_normalize ht01 hρ0 (target 1) (target 2)
    change pairDistSq (wt 1) (wt 2) = _ at hn
    rw [hwt1] at hn
    have heq : (u - d) ^ 2 + v ^ 2 = distSq (target 1) (target 2) / ρ ^ 2 := by
      have heq' : (d - u) ^ 2 + v ^ 2 = distSq (target 1) (target 2) / ρ ^ 2 := by
        simpa [pairDistSq, u, v] using hn
      nlinarith
    rw [heq]
    positivity
  have hRsqrt : (Real.sqrt (radiusSq 1)) ^ 2 = radiusSq 1 :=
    Real.sq_sqrt (le_of_lt (hradius 1))
  have hSsqrt : (Real.sqrt (radiusSq 2)) ^ 2 = radiusSq 2 :=
    Real.sq_sqrt (le_of_lt (hradius 2))
  have exceptional_flexible
      (hAd : A = d) (hBu : B = u) (hCv : C ^ 2 = v ^ 2)
      (hR : R ^ 2 = 1) (hS : S ^ 2 = 1) : Flexible := by
    have hr1 : radiusSq 1 = radiusSq 0 := by
      dsimp [R] at hR
      field_simp [hρ0] at hR
      nlinarith [hRsqrt, hρsq]
    have hr2 : radiusSq 2 = radiusSq 0 := by
      dsimp [S] at hS
      field_simp [hρ0] at hS
      nlinarith [hSsqrt, hρsq]
    have hd01 : distSq (center 0) (center 1) = distSq (target 0) (target 1) := by
      have hc := baselineLength_sq (center 0) (center 1)
      have ht := baselineLength_sq (target 0) (target 1)
      dsimp [A, d] at hAd
      field_simp [hρ0] at hAd
      nlinarith [congrArg (fun x : ℝ ↦ x ^ 2) hAd]
    have hd02 : distSq (center 0) (center 2) = distSq (target 0) (target 2) := by
      have hc := pairDistSq_normalize hc01 hρ0 (center 0) (center 2)
      have ht := pairDistSq_normalize ht01 hρ0 (target 0) (target 2)
      change pairDistSq (wc 0) (wc 2) = _ at hc
      change pairDistSq (wt 0) (wt 2) = _ at ht
      rw [hwc0] at hc
      rw [hwt0] at ht
      have hc' : B ^ 2 + C ^ 2 = distSq (center 0) (center 2) / ρ ^ 2 := by
        simpa [pairDistSq, B, C] using hc
      have ht' : u ^ 2 + v ^ 2 = distSq (target 0) (target 2) / ρ ^ 2 := by
        simpa [pairDistSq, u, v] using ht
      field_simp [hρ0] at hc' ht'
      rw [hBu, hCv] at hc'
      rw [← hc', ← ht']
      ring
    have hd12 : distSq (center 1) (center 2) = distSq (target 1) (target 2) := by
      have hc := pairDistSq_normalize hc01 hρ0 (center 1) (center 2)
      have ht := pairDistSq_normalize ht01 hρ0 (target 1) (target 2)
      change pairDistSq (wc 1) (wc 2) = _ at hc
      change pairDistSq (wt 1) (wt 2) = _ at ht
      rw [hwc1] at hc
      rw [hwt1] at ht
      have hc' : (A - B) ^ 2 + C ^ 2 = distSq (center 1) (center 2) / ρ ^ 2 := by
        simpa [pairDistSq, B, C] using hc
      have ht' : (d - u) ^ 2 + v ^ 2 = distSq (target 1) (target 2) / ρ ^ 2 := by
        simpa [pairDistSq, u, v] using ht
      field_simp [hρ0] at hc' ht'
      rw [hAd, hBu, hCv] at hc'
      rw [← hc', ← ht']
      ring
    constructor
    · exact fin3_values_of_zero radiusSq hr1 hr2
    · exact fin3_distances_of_three center target hd01 hd02 hd12
  have hnotPlus :
      ¬ (A = d ∧ B = u ∧ C = v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1) := by
    rintro ⟨hAd, hBu, hCv, hR, hS⟩
    apply hflex
    apply exceptional_flexible hAd hBu (by rw [hCv]) hR hS
  have hnotMinus :
      ¬ (A = d ∧ B = u ∧ C = -v ∧ R ^ 2 = 1 ∧ S ^ 2 = 1) := by
    rintro ⟨hAd, hBu, hCv, hR, hS⟩
    apply hflex
    apply exceptional_flexible hAd hBu (by rw [hCv]; ring) hR hS
  have hfinitePlus := Circle.circle_congruent_finite hA hd hc13 hc23 ht13 ht23 hnotPlus
  have hfiniteMinus := Circle.circle_congruent_finite hA hd hc13 hc23
    (by simpa using ht13) (by simpa using ht23) hnotMinus
  let Quad := ℝ × ℝ × ℝ × ℝ
  let placePlus : Quad → Fin 3 → Pair := fun q i ↦
    if i = 0 then (q.1, q.2.1)
    else if i = 1 then (q.1 + d * q.2.2.1, q.2.1 + d * q.2.2.2)
    else (q.1 + u * q.2.2.1 - v * q.2.2.2,
      q.2.1 + v * q.2.2.1 + u * q.2.2.2)
  let placeMinus : Quad → Fin 3 → Pair := fun q i ↦
    if i = 0 then (q.1, q.2.1)
    else if i = 1 then (q.1 + d * q.2.2.1, q.2.1 + d * q.2.2.2)
    else (q.1 + u * q.2.2.1 + v * q.2.2.2,
      q.2.1 - v * q.2.2.1 + u * q.2.2.2)
  let decodePlus : Quad → Fin 3 → Point := fun q i ↦
    denormalize (center 0) (center 1) ρ (placePlus q i)
  let decodeMinus : Quad → Fin 3 → Point := fun q i ↦
    denormalize (center 0) (center 1) ρ (placeMinus q i)
  apply Set.Finite.subset
    ((hfinitePlus.image decodePlus).union (hfiniteMinus.image decodeMinus))
  intro z hz
  let w : Fin 3 → Pair := fun i ↦ normalize (center 0) (center 1) ρ (z i)
  have hw01 : pairDistSq (w 0) (w 1) = d ^ 2 := by
    calc
      _ = distSq (z 0) (z 1) / ρ ^ 2 :=
        pairDistSq_normalize hc01 hρ0 (z 0) (z 1)
      _ = distSq (target 0) (target 1) / ρ ^ 2 := by rw [hz.2 0 1]
      _ = pairDistSq (wt 0) (wt 1) :=
        (pairDistSq_normalize ht01 hρ0 (target 0) (target 1)).symm
      _ = d ^ 2 := by rw [hwt0, hwt1]; simp [pairDistSq]
  have hw02 : pairDistSq (w 0) (w 2) = u ^ 2 + v ^ 2 := by
    calc
      _ = distSq (z 0) (z 2) / ρ ^ 2 :=
        pairDistSq_normalize hc01 hρ0 (z 0) (z 2)
      _ = distSq (target 0) (target 2) / ρ ^ 2 := by rw [hz.2 0 2]
      _ = pairDistSq (wt 0) (wt 2) :=
        (pairDistSq_normalize ht01 hρ0 (target 0) (target 2)).symm
      _ = u ^ 2 + v ^ 2 := by rw [hwt0]; simp [pairDistSq, u, v]
  have hw12 : pairDistSq (w 1) (w 2) = (u - d) ^ 2 + v ^ 2 := by
    calc
      _ = distSq (z 1) (z 2) / ρ ^ 2 :=
        pairDistSq_normalize hc01 hρ0 (z 1) (z 2)
      _ = distSq (target 1) (target 2) / ρ ^ 2 := by rw [hz.2 1 2]
      _ = pairDistSq (wt 1) (wt 2) :=
        (pairDistSq_normalize ht01 hρ0 (target 1) (target 2)).symm
      _ = (u - d) ^ 2 + v ^ 2 := by
        rw [hwt1]
        simp [pairDistSq, u, v]
        ring
  obtain ⟨X, Y, hXY, hw1, hw2 | hw2⟩ :=
    triangle_two_orientations hd (w 0) (w 1) (w 2) hw01 hw02 hw12
  · let q : Quad := ((w 0).1, (w 0).2, X, Y)
    have hrad0 : (w 0).1 ^ 2 + (w 0).2 ^ 2 = 1 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 0) (z 0)
      change pairDistSq (wc 0) (w 0) = _ at hn
      rw [hwc0, hz.1 0, hρsq] at hn
      simpa [pairDistSq, ne_of_gt (hradius 0)] using hn
    have hrad1 :
        ((w 0).1 + d * X - A) ^ 2 + ((w 0).2 + d * Y) ^ 2 = R ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 1) (z 1)
      change pairDistSq (wc 1) (w 1) = _ at hn
      rw [hwc1, hw1, hz.1 1] at hn
      dsimp [R]
      rw [div_pow, hRsqrt]
      dsimp [pairDistSq] at hn
      convert hn using 1 <;> ring
    have hrad2 :
        ((w 0).1 + u * X - v * Y - B) ^ 2 +
          ((w 0).2 + v * X + u * Y - C) ^ 2 = S ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 2) (z 2)
      change pairDistSq (wc 2) (w 2) = _ at hn
      rw [hw2, hz.1 2] at hn
      dsimp [S]
      rw [div_pow, hSsqrt]
      dsimp [pairDistSq, B, C] at hn
      convert hn using 1 <;> ring
    have hq : Circle.NormalizedSolution A B C R S d u v q := by
      exact ⟨hrad0, hXY, hrad1, hrad2⟩
    refine Set.mem_union_left _ ⟨q, hq, ?_⟩
    funext i
    fin_cases i
    · dsimp [decodePlus, placePlus, q, w]
      simpa only [Prod.eta] using denormalize_normalize hc01 hρ0 (z 0)
    · dsimp [decodePlus, placePlus, q]
      rw [← hw1]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 1)
    · dsimp [decodePlus, placePlus, q]
      rw [← hw2]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 2)
  · let q : Quad := ((w 0).1, (w 0).2, X, Y)
    have hrad0 : (w 0).1 ^ 2 + (w 0).2 ^ 2 = 1 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 0) (z 0)
      change pairDistSq (wc 0) (w 0) = _ at hn
      rw [hwc0, hz.1 0, hρsq] at hn
      simpa [pairDistSq, ne_of_gt (hradius 0)] using hn
    have hrad1 :
        ((w 0).1 + d * X - A) ^ 2 + ((w 0).2 + d * Y) ^ 2 = R ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 1) (z 1)
      change pairDistSq (wc 1) (w 1) = _ at hn
      rw [hwc1, hw1, hz.1 1] at hn
      dsimp [R]
      rw [div_pow, hRsqrt]
      dsimp [pairDistSq] at hn
      convert hn using 1 <;> ring
    have hrad2 :
        ((w 0).1 + u * X + v * Y - B) ^ 2 +
          ((w 0).2 - v * X + u * Y - C) ^ 2 = S ^ 2 := by
      have hn := pairDistSq_normalize hc01 hρ0 (center 2) (z 2)
      change pairDistSq (wc 2) (w 2) = _ at hn
      rw [hw2, hz.1 2] at hn
      dsimp [S]
      rw [div_pow, hSsqrt]
      dsimp [pairDistSq, B, C] at hn
      convert hn using 1 <;> ring
    have hq : Circle.NormalizedSolution A B C R S d u (-v) q := by
      dsimp [Circle.NormalizedSolution, q]
      refine ⟨hrad0, hXY, hrad1, ?_⟩
      convert hrad2 using 1 <;> ring
    refine Set.mem_union_right _ ⟨q, hq, ?_⟩
    funext i
    fin_cases i
    · dsimp [decodeMinus, placeMinus, q, w]
      simpa only [Prod.eta] using denormalize_normalize hc01 hρ0 (z 0)
    · dsimp [decodeMinus, placeMinus, q]
      rw [← hw1]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 1)
    · dsimp [decodeMinus, placeMinus, q]
      rw [← hw2]
      dsimp [w]
      exact denormalize_normalize hc01 hρ0 (z 2)

end


end Erdos215
