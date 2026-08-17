/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license.
-/

import Mathlib
import ErdosProblems.Erdos465.Analytic.Asymptotic
import ErdosProblems.Erdos465.Analytic.Separator

/-!
# Erdős Problem 465

For a real number `x`, let `distToInt x` be its distance to the nearest integer.  We define
`N X δ` to be the largest cardinality of a finite subset of the closed Euclidean disk of
radius `X` whose distinct mutual distances have `distToInt` at least `δ`.

The main theorem below is Konyagin's resolution of the problem:

`N X δ = Oδ(√X)` for every `0 < δ < 1 / 2`.

In particular `N X δ = o(X)`, and the proposed `X^(1/2+o(1))` upper bound follows.
The accompanying mathematical proof and a correspondence between its steps and the declarations
in this file are in `tex/465.tex`.
-/

open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
open Filter Metric Set

namespace Erdos465

noncomputable section

/-- The Euclidean plane, represented by the complex numbers with their usual Euclidean norm. -/
abbrev Plane := ℂ

/-- The distance from `x` to the nearest integer. -/
def distToInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

lemma distToInt_eq_norm_addCircle (x : ℝ) :
    distToInt x = ‖(x : AddCircle (1 : ℝ))‖ := by
  simp [distToInt, AddCircle.norm_eq]

lemma distToInt_nonneg (x : ℝ) : 0 ≤ distToInt x := abs_nonneg _

/-- The selected nearest integer is no farther away than any prescribed integer. -/
lemma distToInt_le_int (x : ℝ) (z : ℤ) : distToInt x ≤ |x - (z : ℝ)| := by
  exact round_le x z

lemma distToInt_le_self {x : ℝ} (hx : 0 ≤ x) : distToInt x ≤ x := by
  simpa [abs_of_nonneg hx] using distToInt_le_int x 0

/-- A finite set is admissible when it lies in the closed disk and avoids the prescribed
neighbourhood of every integer distance. -/
def Admissible (X δ : ℝ) (P : Finset Plane) : Prop :=
  (∀ p ∈ P, ‖p‖ ≤ X) ∧
    (P : Set Plane).Pairwise fun p q ↦ δ ≤ distToInt ‖p - q‖

lemma Admissible.subset_closedBall {X δ : ℝ} {P : Finset Plane}
    (hP : Admissible X δ P) : (P : Set Plane) ⊆ closedBall 0 X := by
  intro p hp
  simpa [mem_closedBall, dist_zero_right] using hP.1 p hp

lemma Admissible.mono_radius {X Y δ : ℝ} {P : Finset Plane}
    (hP : Admissible X δ P) (hXY : X ≤ Y) : Admissible Y δ P := by
  exact ⟨fun p hp ↦ (hP.1 p hp).trans hXY, hP.2⟩

lemma Admissible.mono_delta {X δ η : ℝ} {P : Finset Plane}
    (hP : Admissible X δ P) (hηδ : η ≤ δ) : Admissible X η P := by
  refine ⟨hP.1, ?_⟩
  intro p hp q hq hpq
  exact hηδ.trans (hP.2 hp hq hpq)

/-- Admissibility implies ordinary Euclidean `δ`-separation. -/
lemma Admissible.separated {X δ : ℝ} {P : Finset Plane}
    (hP : Admissible X δ P) :
    (P : Set Plane).Pairwise fun p q ↦ δ ≤ dist p q := by
  intro p hp q hq hpq
  have havoid := hP.2 hp hq hpq
  have hnorm : 0 ≤ ‖p - q‖ := norm_nonneg _
  calc
    δ ≤ distToInt ‖p - q‖ := havoid
    _ ≤ ‖p - q‖ := distToInt_le_self hnorm
    _ = dist p q := by rw [dist_eq_norm]

/-- The set of all cardinalities achieved by admissible finite configurations. -/
def admissibleCardinalities (X δ : ℝ) : Set ℕ :=
  {n | ∃ P : Finset Plane, Admissible X δ P ∧ P.card = n}

/-- The extremal number in Erdős Problem 465.  Finiteness and attainment are proved below. -/
def N (X δ : ℝ) : ℕ := sSup (admissibleCardinalities X δ)

lemma zero_mem_admissibleCardinalities (X δ : ℝ) :
    0 ∈ admissibleCardinalities X δ := by
  refine ⟨∅, ?_, rfl⟩
  simp [Admissible]

lemma admissibleCardinalities_nonempty (X δ : ℝ) :
    (admissibleCardinalities X δ).Nonempty :=
  ⟨0, zero_mem_admissibleCardinalities X δ⟩

/-- Compactness of the disk gives a finite (deliberately non-explicit) packing bound. -/
lemma admissibleCardinalities_bddAbove {X δ : ℝ} (hδ : 0 < δ) :
    BddAbove (admissibleCardinalities X δ) := by
  let ε : ℝ≥0 := ⟨δ / 4, by positivity⟩
  have hε : ε ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast (show 0 < δ / 4 by positivity)
  obtain ⟨C, hCsub, hCfin, hCcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hε (isCompact_closedBall (0 : Plane) X)
  obtain ⟨M, hCM⟩ := hCfin.exists_encard_eq_coe
  refine ⟨M, ?_⟩
  intro n hn
  obtain ⟨P, hP, rfl⟩ := hn
  have hPsep : Metric.IsSeparated (2 * ε) (P : Set Plane) := by
    intro p hp q hq hpq
    rw [edist_dist]
    have hlt : (2 * (ε : ℝ)) < dist p q := by
      have hbase : δ / 2 < dist p q :=
        (half_lt_self hδ).trans_le (hP.separated hp hq hpq)
      have heq : 2 * (ε : ℝ) = δ / 2 := by
        change 2 * (δ / 4) = δ / 2
        ring
      rw [heq]
      exact hbase
    have hlt' : (↑(2 * ε) : ℝ≥0∞) < ENNReal.ofReal (dist p q) := by
      rw [ENNReal.coe_lt_ofReal]
      simpa using hlt
    simpa using hlt'
  have hcardE : (P : Set Plane).encard ≤ C.encard := calc
    (P : Set Plane).encard
        ≤ Metric.packingNumber (2 * ε) (closedBall (0 : Plane) X) :=
      hPsep.encard_le_packingNumber hP.subset_closedBall
    _ ≤ Metric.externalCoveringNumber ε (closedBall (0 : Plane) X) :=
      Metric.packingNumber_two_mul_le_externalCoveringNumber ε _
    _ ≤ C.encard := hCcover.externalCoveringNumber_le_encard
  rw [Set.encard_coe_eq_coe_finsetCard, hCM] at hcardE
  exact_mod_cast hcardE

lemma N_mem_admissibleCardinalities {X δ : ℝ} (hδ : 0 < δ) :
    N X δ ∈ admissibleCardinalities X δ := by
  exact Nat.sSup_mem (admissibleCardinalities_nonempty X δ)
    (admissibleCardinalities_bddAbove hδ)

lemma exists_extremal_configuration {X δ : ℝ} (hδ : 0 < δ) :
    ∃ P : Finset Plane, Admissible X δ P ∧ P.card = N X δ :=
  N_mem_admissibleCardinalities hδ

lemma card_le_N {X δ : ℝ} (hδ : 0 < δ) {P : Finset Plane}
    (hP : Admissible X δ P) : P.card ≤ N X δ := by
  apply le_csSup (admissibleCardinalities_bddAbove hδ)
  exact ⟨P, hP, rfl⟩

lemma N_le_of_forall_card_le {X δ : ℝ} {m : ℕ}
    (h : ∀ P : Finset Plane, Admissible X δ P → P.card ≤ m) : N X δ ≤ m := by
  apply csSup_le (admissibleCardinalities_nonempty X δ)
  rintro n ⟨P, hP, rfl⟩
  exact h P hP

/-- A translate of the neighbors of one point inside a fixed distance is itself an admissible
configuration in the fixed disk. -/
lemma short_neighbors_card_le_N {X δ R : ℝ} {P : Finset Plane}
    (hδ : 0 < δ) (hP : Admissible X δ P) {p : Plane} (hp : p ∈ P) :
    (P.filter fun q ↦ ‖p - q‖ < R).card ≤ N R δ := by
  classical
  let Q : Finset Plane := (P.filter fun q ↦ ‖p - q‖ < R).image fun q ↦ q - p
  have hcard : Q.card = (P.filter fun q ↦ ‖p - q‖ < R).card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have := congrArg (fun z : Plane ↦ z + p) hab
    simpa using this
  have hQ : Admissible R δ Q := by
    constructor
    · intro z hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_filter] at hq
      simpa [norm_sub_rev] using hq.2.le
    · intro a ha b hb hab
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp hb
      subst hsp
      rw [Finset.mem_filter] at hq hs
      have hqs : q ≠ s := by
        intro h
        apply hab
        simpa [h]
      have := hP.2 hq.1 hs.1 hqs
      simpa [sub_sub_sub_cancel_right] using this
  rw [← hcard]
  exact card_le_N hδ hQ

/-! ## The circular Fourier kernel -/

/-- The normalized Fourier transform of arclength measure on the unit circle. -/
def circleKernel (t : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ ↦ Real.cos (t * z.re)) 0 1

@[simp] lemma circleKernel_zero : circleKernel 0 = 1 := by
  simp [circleKernel, Real.circleAverage_const]

/-- The circle kernel is the order-zero Bessel function whose stationary-phase expansion is
proved in `Erdos465Analytic.Asymptotic`. -/
lemma circleKernel_eq_besselJ0 (t : ℝ) : circleKernel t = Q776.besselJ0 t := by
  let G : ℝ → ℝ := fun θ ↦ Real.cos (t * Real.sin θ)
  have hG : Function.Periodic G (2 * Real.pi) := by
    intro θ
    simp [G, Real.sin_add_two_pi]
  have hpoint (u : ℝ) : Real.cos (t * Real.cos u) = G (u - Real.pi / 2) := by
    simp [G, Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
  rw [circleKernel, Real.circleAverage_def, Q776.besselJ0]
  simp only [smul_eq_mul]
  rw [inv_eq_one_div]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun u ↦ G (u - Real.pi / 2)) (fun u _ ↦ by
    rw [circleMap_zero_re]
    norm_num
    exact hpoint u)]
  rw [intervalIntegral.integral_comp_sub_right G (Real.pi / 2)]
  convert Q776.periodic_shift hG (-Real.pi / 2) using 1 <;> ring

/-- A one-term consequence of the checked two-term stationary-phase expansion. -/
lemma circleKernel_asymptotic_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, 2 ≤ y →
      |circleKernel y - Real.sqrt (2 / (Real.pi * y)) *
        Real.cos (y - Real.pi / 4)| ≤ D / (y * Real.sqrt y) := by
  obtain ⟨C, hC, hmain⟩ := Q776.besselJ0_expansion
  refine ⟨C + 1, by positivity, ?_⟩
  intro y hy
  have hy0 : 0 < y := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : Real.sqrt (2 / (Real.pi * y)) ≤ 2 / Real.sqrt y := by
    have hA : 0 ≤ 2 / (Real.pi * y) := by positivity
    have hsqA := Real.sq_sqrt hA
    have hsqy := Real.sq_sqrt hy0.le
    have hpi3 := Real.pi_gt_three
    have hprodSq :
        (Real.sqrt (2 / (Real.pi * y)) * Real.sqrt y) ^ 2 = 2 / Real.pi := by
      rw [mul_pow, hsqA, hsqy]
      field_simp
    have hfrac : 2 / Real.pi < 1 := by
      rw [div_lt_one hpi]
      linarith
    apply (le_div_iff₀ hsy).2
    have hprod0 : 0 ≤ Real.sqrt (2 / (Real.pi * y)) * Real.sqrt y := mul_nonneg
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith
  have hsin : |Real.sin (y - Real.pi / 4)| ≤ 1 := Real.abs_sin_le_one _
  have hcorr :
      |Real.sqrt (2 / (Real.pi * y)) *
          (Real.sin (y - Real.pi / 4) / (8 * y))| ≤
        1 / (y * Real.sqrt y) := by
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8), abs_of_pos hy0,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hmul : Real.sqrt (2 / (Real.pi * y)) * |Real.sin (y - Real.pi / 4)| ≤
        2 / Real.sqrt y := by
      simpa using mul_le_mul hsqrt hsin (abs_nonneg _) (by positivity)
    calc
      Real.sqrt (2 / (Real.pi * y)) * (|Real.sin (y - Real.pi / 4)| / (8 * y)) =
          (Real.sqrt (2 / (Real.pi * y)) * |Real.sin (y - Real.pi / 4)|) / (8 * y) := by ring
      _ ≤ (2 / Real.sqrt y) / (8 * y) :=
        div_le_div_of_nonneg_right hmul (by positivity)
      _ ≤ 1 / (y * Real.sqrt y) := by
        field_simp
        nlinarith
  have hrem := hmain y hy
  have hsplit :
      circleKernel y - Real.sqrt (2 / (Real.pi * y)) * Real.cos (y - Real.pi / 4) =
        (Q776.besselJ0 y - Real.sqrt (2 / (Real.pi * y)) *
          (Real.cos (y - Real.pi / 4) + Real.sin (y - Real.pi / 4) / (8 * y))) +
        Real.sqrt (2 / (Real.pi * y)) *
          (Real.sin (y - Real.pi / 4) / (8 * y)) := by
    rw [circleKernel_eq_besselJ0]
    ring
  rw [hsplit]
  calc
    |(Q776.besselJ0 y - Real.sqrt (2 / (Real.pi * y)) *
          (Real.cos (y - Real.pi / 4) + Real.sin (y - Real.pi / 4) / (8 * y))) +
        Real.sqrt (2 / (Real.pi * y)) *
          (Real.sin (y - Real.pi / 4) / (8 * y))|
        ≤ |Q776.besselJ0 y - Real.sqrt (2 / (Real.pi * y)) *
          (Real.cos (y - Real.pi / 4) + Real.sin (y - Real.pi / 4) / (8 * y))| +
          |Real.sqrt (2 / (Real.pi * y)) *
            (Real.sin (y - Real.pi / 4) / (8 * y))| := abs_add_le _ _
    _ ≤ C / (y ^ 2 * Real.sqrt y) + 1 / (y * Real.sqrt y) := add_le_add hrem hcorr
    _ ≤ (C + 1) / (y * Real.sqrt y) := by
      have hden : 0 < y * Real.sqrt y := mul_pos hy0 hsy
      have hden2 : 0 < y ^ 2 * Real.sqrt y := by positivity
      have hdenle : y * Real.sqrt y ≤ y ^ 2 * Real.sqrt y := by
        nlinarith [Real.sqrt_nonneg y]
      have hfirst : C / (y ^ 2 * Real.sqrt y) ≤ C / (y * Real.sqrt y) :=
        div_le_div_of_nonneg_left hC hden hdenle
      calc
        C / (y ^ 2 * Real.sqrt y) + 1 / (y * Real.sqrt y) ≤
            C / (y * Real.sqrt y) + 1 / (y * Real.sqrt y) := add_le_add hfirst le_rfl
        _ = (C + 1) / (y * Real.sqrt y) := by ring

lemma scaled_circleKernel_main_term (k : ℕ) (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    Real.sqrt k * (Real.sqrt (2 / (Real.pi * (2 * Real.pi * k * r))) *
      Real.cos (2 * Real.pi * k * r - Real.pi / 4)) =
      (Real.cos (2 * Real.pi * k * r) + Real.sin (2 * Real.pi * k * r)) /
        (Real.pi * Real.sqrt 2 * Real.sqrt r) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkR
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  let a : ℝ := Real.sqrt k * Real.sqrt (2 / (Real.pi * (2 * Real.pi * k * r))) *
    (Real.sqrt 2 / 2)
  let b : ℝ := 1 / (Real.pi * Real.sqrt 2 * Real.sqrt r)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hA : 0 ≤ 2 / (Real.pi * (2 * Real.pi * k * r)) := by positivity
  have haSq : a ^ 2 = b ^ 2 := by
    dsimp [a, b]
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hkR.le, Real.sq_sqrt hA,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    rw [Real.sq_sqrt hr.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hab : a = b := by nlinarith
  rw [Real.cos_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  calc
    Real.sqrt k *
        (Real.sqrt (2 / (Real.pi * (2 * Real.pi * k * r))) *
          (Real.cos (2 * Real.pi * k * r) * (Real.sqrt 2 / 2) +
           Real.sin (2 * Real.pi * k * r) * (Real.sqrt 2 / 2))) =
        a * (Real.cos (2 * Real.pi * k * r) + Real.sin (2 * Real.pi * k * r)) := by
      dsimp [a]
      ring
    _ = b * (Real.cos (2 * Real.pi * k * r) + Real.sin (2 * Real.pi * k * r)) := by rw [hab]
    _ = (Real.cos (2 * Real.pi * k * r) + Real.sin (2 * Real.pi * k * r)) /
        (Real.pi * Real.sqrt 2 * Real.sqrt r) := by dsimp [b]; ring

lemma FourierSeparator.separates_real {δ : ℝ} (S : FourierSeparator δ) (r : ℝ)
    (hr : δ ≤ distToInt r) :
    (∑ i, S.coefficient i *
      (Real.cos (2 * Real.pi * S.frequency i * r) +
       Real.sin (2 * Real.pi * S.frequency i * r))) ≤ -(1 / 4 : ℝ) := by
  have hsep := S.separates (r : AddCircle (1 : ℝ)) (by
    simpa [distToInt_eq_norm_addCircle] using hr)
  have heq :
      (∑ i, S.coefficient i *
        (((AddCircle.toCircle (r : AddCircle (1 : ℝ)) : ℂ) ^ S.frequency i).re +
         ((AddCircle.toCircle (r : AddCircle (1 : ℝ)) : ℂ) ^ S.frequency i).im)) =
      ∑ i, S.coefficient i *
        (Real.cos (2 * Real.pi * S.frequency i * r) +
         Real.sin (2 * Real.pi * S.frequency i * r)) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hpow :
        ((AddCircle.toCircle (r : AddCircle (1 : ℝ)) : ℂ) ^ S.frequency i) =
          Complex.exp (((2 * Real.pi * S.frequency i * r : ℝ) : ℂ) * Complex.I) := by
      rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
      rw [← Complex.exp_nsmul]
      congr 1
      push_cast
      field_simp
      ring
    rw [hpow, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [heq] at hsep
  exact hsep

/-- The finite positive combination of circle kernels attached to a separator. -/
def FourierSeparator.kernel {δ : ℝ} (S : FourierSeparator δ) (r : ℝ) : ℝ :=
  ∑ i, S.coefficient i * Real.sqrt (S.frequency i) *
    circleKernel (2 * Real.pi * S.frequency i * r)

def FourierSeparator.totalWeight {δ : ℝ} (S : FourierSeparator δ) : ℝ :=
  ∑ i, S.coefficient i * Real.sqrt (S.frequency i)

lemma FourierSeparator.totalWeight_nonneg {δ : ℝ} (S : FourierSeparator δ) :
    0 ≤ S.totalWeight := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (S.coefficient_nonneg i) (Real.sqrt_nonneg _)

/-- Beyond a fixed radius, every forbidden distance makes the separator kernel uniformly
negative on the natural `r⁻¹²` scale. -/
lemma FourierSeparator.kernel_long_upper {δ : ℝ} (S : FourierSeparator δ) :
    ∃ R A : ℝ, 1 ≤ R ∧ 0 < A ∧ ∀ r : ℝ, R ≤ r → δ ≤ distToInt r →
      S.kernel r ≤ -A / Real.sqrt r := by
  obtain ⟨D, hD, hBessel⟩ := circleKernel_asymptotic_bound
  let W := S.totalWeight
  let A : ℝ := 1 / (8 * Real.pi * Real.sqrt 2)
  let R : ℝ := 8 * Real.pi * Real.sqrt 2 * D * W + 1
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hW : 0 ≤ W := S.totalWeight_nonneg
  have hA : 0 < A := by
    dsimp [A]
    exact one_div_pos.mpr (mul_pos (mul_pos (by positivity) hpi) hs2)
  have hR : 1 ≤ R := by
    dsimp [R]
    have : 0 ≤ 8 * Real.pi * Real.sqrt 2 * D * W := by positivity
    linarith
  refine ⟨R, A, hR, hA, ?_⟩
  intro r hr havoid
  have hr1 : 1 ≤ r := hR.trans hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hsep := S.separates_real r havoid
  have hterm (i : Fin S.size) :
      S.coefficient i * Real.sqrt (S.frequency i) *
          circleKernel (2 * Real.pi * S.frequency i * r) ≤
        S.coefficient i * Real.sqrt (S.frequency i) *
          (Real.sqrt (2 / (Real.pi * (2 * Real.pi * S.frequency i * r))) *
            Real.cos (2 * Real.pi * S.frequency i * r - Real.pi / 4)) +
        S.coefficient i * Real.sqrt (S.frequency i) * D / (r * Real.sqrt r) := by
    let y : ℝ := 2 * Real.pi * S.frequency i * r
    have hk : 0 < S.frequency i := S.frequency_pos i
    have hkR : (0 : ℝ) < S.frequency i := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ S.frequency i := by exact_mod_cast hk
    have hfac2 : 2 ≤ 2 * Real.pi * S.frequency i := calc
      (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      _ ≤ (2 * Real.pi) * S.frequency i :=
        le_mul_of_one_le_right (by positivity) hk1
    have hfac1 : 1 ≤ 2 * Real.pi * S.frequency i := by linarith
    have hy : 2 ≤ y := by
      dsimp [y]
      calc
        (2 : ℝ) ≤ 2 * Real.pi * S.frequency i := hfac2
        _ ≤ (2 * Real.pi * S.frequency i) * r :=
          le_mul_of_one_le_right (by positivity) hr1
    have hyr : r ≤ y := by
      dsimp [y]
      nth_rewrite 1 [← one_mul r]
      exact mul_le_mul_of_nonneg_right hfac1 hr0.le
    have hsy : Real.sqrt r ≤ Real.sqrt y := Real.sqrt_le_sqrt hyr
    have hden : 0 < r * Real.sqrt r := mul_pos hr0 hsr
    have hy0 : 0 < y := by linarith
    have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
    have hdenY : 0 < y * Real.sqrt y := mul_pos hy0 hsy0
    have hdenle : r * Real.sqrt r ≤ y * Real.sqrt y :=
      mul_le_mul hyr hsy (Real.sqrt_nonneg _) hy0.le
    have hremle : D / (y * Real.sqrt y) ≤ D / (r * Real.sqrt r) :=
      div_le_div_of_nonneg_left hD hden hdenle
    have hb := hBessel y hy
    have habs :
        |circleKernel y - Real.sqrt (2 / (Real.pi * y)) * Real.cos (y - Real.pi / 4)| ≤
          D / (r * Real.sqrt r) := hb.trans hremle
    have hone := (abs_le.mp habs).2
    have hw : 0 ≤ S.coefficient i * Real.sqrt (S.frequency i) :=
      mul_nonneg (S.coefficient_nonneg i) (Real.sqrt_nonneg _)
    dsimp [y] at hone ⊢
    let w := S.coefficient i * Real.sqrt (S.frequency i)
    have hmul := mul_le_mul_of_nonneg_left hone hw
    change w * circleKernel (2 * Real.pi * S.frequency i * r) ≤ _
    calc
      w * circleKernel (2 * Real.pi * S.frequency i * r) =
          w * (circleKernel (2 * Real.pi * S.frequency i * r) -
            Real.sqrt (2 / (Real.pi * (2 * Real.pi * S.frequency i * r))) *
              Real.cos (2 * Real.pi * S.frequency i * r - Real.pi / 4)) +
          w * (Real.sqrt (2 / (Real.pi * (2 * Real.pi * S.frequency i * r))) *
              Real.cos (2 * Real.pi * S.frequency i * r - Real.pi / 4)) := by ring
      _ ≤ w * (D / (r * Real.sqrt r)) +
          w * (Real.sqrt (2 / (Real.pi * (2 * Real.pi * S.frequency i * r))) *
              Real.cos (2 * Real.pi * S.frequency i * r - Real.pi / 4)) :=
        add_le_add hmul le_rfl
      _ = _ := by dsimp [w]; ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i hi ↦ hterm i
  have hmainEq :
      (∑ i, S.coefficient i * Real.sqrt (S.frequency i) *
        (Real.sqrt (2 / (Real.pi * (2 * Real.pi * S.frequency i * r))) *
          Real.cos (2 * Real.pi * S.frequency i * r - Real.pi / 4))) =
      (∑ i, S.coefficient i *
        (Real.cos (2 * Real.pi * S.frequency i * r) +
         Real.sin (2 * Real.pi * S.frequency i * r))) /
        (Real.pi * Real.sqrt 2 * Real.sqrt r) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc]
    rw [scaled_circleKernel_main_term (S.frequency i) (S.frequency_pos i) hr0]
    ring
  have hmainLe :
      (∑ i, S.coefficient i * Real.sqrt (S.frequency i) *
        (Real.sqrt (2 / (Real.pi * (2 * Real.pi * S.frequency i * r))) *
          Real.cos (2 * Real.pi * S.frequency i * r - Real.pi / 4))) ≤
        -(1 / 4) / (Real.pi * Real.sqrt 2 * Real.sqrt r) := by
    rw [hmainEq]
    exact div_le_div_of_nonneg_right hsep (by positivity)
  have herrorEq :
      (∑ i, S.coefficient i * Real.sqrt (S.frequency i) * D / (r * Real.sqrt r)) =
        D * W / (r * Real.sqrt r) := by
    dsimp [W, FourierSeparator.totalWeight]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have herrorLe : D * W / r ≤ A := by
    have hrpos : 0 < r := hr0
    apply (div_le_iff₀ hrpos).2
    dsimp [R, A] at hr ⊢
    have hprod : 0 ≤ D * W := mul_nonneg hD hW
    field_simp
    nlinarith
  change (∑ i, S.coefficient i * Real.sqrt (S.frequency i) *
    circleKernel (2 * Real.pi * S.frequency i * r)) ≤ _
  rw [Finset.sum_add_distrib, herrorEq] at hsum
  have hcombine := hsum.trans (add_le_add hmainLe le_rfl)
  have herrScaled : D * W / (r * Real.sqrt r) ≤ A / Real.sqrt r := by
    calc
      D * W / (r * Real.sqrt r) = (D * W / r) / Real.sqrt r := by ring
      _ ≤ A / Real.sqrt r := div_le_div_of_nonneg_right herrorLe hsr.le
  calc
    ∑ i, S.coefficient i * Real.sqrt (S.frequency i) *
        circleKernel (2 * Real.pi * S.frequency i * r) ≤
        -(1 / 4) / (Real.pi * Real.sqrt 2 * Real.sqrt r) +
          D * W / (r * Real.sqrt r) := hcombine
    _ ≤ -(1 / 4) / (Real.pi * Real.sqrt 2 * Real.sqrt r) + A / Real.sqrt r :=
      add_le_add le_rfl herrScaled
    _ = -A / Real.sqrt r := by
      dsimp [A]
      field_simp
      ring

lemma circleKernel_neg (t : ℝ) : circleKernel (-t) = circleKernel t := by
  apply Real.circleAverage_congr_sphere
  intro z hz
  simp only [neg_mul, Real.cos_neg]

lemma circleKernel_abs_le_one (t : ℝ) : |circleKernel t| ≤ 1 := by
  have hf : CircleIntegrable (fun z : ℂ ↦ Real.cos (t * z.re)) 0 1 := by
    exact (by fun_prop : Continuous (fun z : ℂ ↦ Real.cos (t * z.re))).continuousOn
      |>.circleIntegrable (by norm_num)
  calc
    |circleKernel t| ≤
        Real.circleAverage (fun z : ℂ ↦ |Real.cos (t * z.re)|) 0 1 := by
      rw [circleKernel]
      let f : ℂ → ℝ := fun z ↦ Real.cos (t * z.re)
      have h := Real.abs_circleAverage_le_circleAverage_abs
        (f := f) (c := 0) (R := 1)
      change |Real.circleAverage f 0 1| ≤
        Real.circleAverage (fun z ↦ |f z|) 0 1
      exact h
    _ ≤ Real.circleAverage (fun _ : ℂ ↦ (1 : ℝ)) 0 1 := by
      apply Real.circleAverage_mono hf.abs (continuousOn_const.circleIntegrable (by norm_num))
      intro z hz
      exact Real.abs_cos_le_one _
    _ = 1 := Real.circleAverage_const 1 0 1

lemma FourierSeparator.kernel_le_totalWeight {δ : ℝ} (S : FourierSeparator δ) (r : ℝ) :
    S.kernel r ≤ S.totalWeight := by
  apply Finset.sum_le_sum
  intro i hi
  have hk : circleKernel (2 * Real.pi * S.frequency i * r) ≤ 1 :=
    (le_abs_self _).trans (circleKernel_abs_le_one _)
  exact mul_le_of_le_one_right
    (mul_nonneg (S.coefficient_nonneg i) (Real.sqrt_nonneg _)) hk

/-- Rotation invariance identifies the Fourier transform in a vector direction with the radial
kernel `circleKernel`. -/
lemma circleAverage_cos_projection (t : ℝ) (y : ℂ) :
    Real.circleAverage (fun z : ℂ ↦ Real.cos (t * (y * conj z).re)) 0 1 =
      circleKernel (t * ‖y‖) := by
  rw [circleKernel, Real.circleAverage_eq_integral_add (f := fun z : ℂ ↦
    Real.cos ((t * ‖y‖) * z.re)) (c := 0) (R := 1) (-Complex.arg y)]
  rw [Real.circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ
  intro hθ
  have hy : y = circleMap 0 ‖y‖ (Complex.arg y) := by
    rw [circleMap_zero, ← Complex.norm_mul_exp_arg_mul_I y]
    norm_num
  nth_rewrite 1 [hy]
  dsimp only
  rw [conj_circleMap_zero, circleMap_zero_mul, circleMap_zero_re,
    circleMap_zero_re]
  have hangle : Complex.arg y + -θ = -(θ + -Complex.arg y) := by ring
  rw [hangle, Real.cos_neg]
  ring

lemma doubleSum_cos_projection_nonneg (t : ℝ) (P : Finset ℂ) (z : ℂ) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, Real.cos (t * ((p - q) * conj z).re) := by
  classical
  let a : ℂ → ℝ := fun p ↦ t * (p * conj z).re
  have hphase (p q : ℂ) : t * ((p - q) * conj z).re = a p - a q := by
    simp only [a, sub_mul, Complex.sub_re]
    ring
  simp_rw [hphase, Real.cos_sub, Finset.sum_add_distrib]
  have hcos :
      (∑ p ∈ P, ∑ q ∈ P, Real.cos (a p) * Real.cos (a q)) =
        (∑ p ∈ P, Real.cos (a p)) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
  have hsin :
      (∑ p ∈ P, ∑ q ∈ P, Real.sin (a p) * Real.sin (a q)) =
        (∑ p ∈ P, Real.sin (a p)) ^ 2 := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
  rw [hcos, hsin]
  positivity

/-- Positive definiteness of normalized arclength measure on the circle. -/
lemma sum_circleKernel_nonneg (t : ℝ) (P : Finset ℂ) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, circleKernel (t * ‖p - q‖) := by
  classical
  have hint (p q : ℂ) : CircleIntegrable
      (fun z : ℂ ↦ Real.cos (t * ((p - q) * conj z).re)) 0 1 := by
    exact (by fun_prop : Continuous (fun z : ℂ ↦
      Real.cos (t * ((p - q) * conj z).re))).continuousOn.circleIntegrable (by norm_num)
  calc
    0 ≤ Real.circleAverage
        (fun z : ℂ ↦ ∑ p ∈ P, ∑ q ∈ P,
          Real.cos (t * ((p - q) * conj z).re)) 0 1 := by
      apply Real.circleAverage_nonneg_of_nonneg
      intro z hz
      exact doubleSum_cos_projection_nonneg t P z
    _ = ∑ p ∈ P, ∑ q ∈ P,
          Real.circleAverage
            (fun z : ℂ ↦ Real.cos (t * ((p - q) * conj z).re)) 0 1 := by
      rw [Real.circleAverage_fun_sum]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Real.circleAverage_fun_sum]
        intro q hq
        exact hint p q
      · intro p hp
        rw [show (fun z : ℂ ↦ ∑ q ∈ P,
            Real.cos (t * ((p - q) * conj z).re)) =
            ∑ q ∈ P, fun z : ℂ ↦ Real.cos (t * ((p - q) * conj z).re) by
          funext z
          simp]
        exact CircleIntegrable.sum P fun q hq ↦ hint p q
    _ = ∑ p ∈ P, ∑ q ∈ P, circleKernel (t * ‖p - q‖) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact circleAverage_cos_projection t (p - q)

/-- Positive definiteness is preserved by the positive separator weights. -/
lemma FourierSeparator.kernel_energy_nonneg {δ : ℝ} (S : FourierSeparator δ)
    (P : Finset Plane) :
    0 ≤ ∑ p ∈ P, ∑ q ∈ P, S.kernel ‖p - q‖ := by
  classical
  have hi (i : Fin S.size) :
      0 ≤ ∑ p ∈ P, ∑ q ∈ P,
        circleKernel ((2 * Real.pi * S.frequency i) * ‖p - q‖) :=
    sum_circleKernel_nonneg (2 * Real.pi * S.frequency i) P
  have hreorder :
      (∑ p ∈ P, ∑ q ∈ P, S.kernel ‖p - q‖) =
        ∑ i, S.coefficient i * Real.sqrt (S.frequency i) *
          (∑ p ∈ P, ∑ q ∈ P,
            circleKernel ((2 * Real.pi * S.frequency i) * ‖p - q‖)) := by
    simp only [FourierSeparator.kernel]
    calc
      (∑ p ∈ P, ∑ q ∈ P, ∑ i,
          S.coefficient i * Real.sqrt (S.frequency i) *
            circleKernel (2 * Real.pi * S.frequency i * ‖p - q‖)) =
          ∑ p ∈ P, ∑ i, ∑ q ∈ P,
            S.coefficient i * Real.sqrt (S.frequency i) *
              circleKernel (2 * Real.pi * S.frequency i * ‖p - q‖) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_comm
      _ = ∑ i, ∑ p ∈ P, ∑ q ∈ P,
            S.coefficient i * Real.sqrt (S.frequency i) *
              circleKernel (2 * Real.pi * S.frequency i * ‖p - q‖) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
  rw [hreorder]
  apply Finset.sum_nonneg
  intro i hi_mem
  exact mul_nonneg (mul_nonneg (S.coefficient_nonneg i) (Real.sqrt_nonneg _)) (hi i)

lemma Admissible.pair_distance_le_two_mul {X δ : ℝ} {P : Finset Plane}
    (hP : Admissible X δ P) {p q : Plane} (hp : p ∈ P) (hq : q ∈ P) :
    ‖p - q‖ ≤ 2 * X := by
  calc
    ‖p - q‖ ≤ ‖p‖ + ‖q‖ := norm_sub_le _ _
    _ ≤ X + X := add_le_add (hP.1 p hp) (hP.1 q hq)
    _ = 2 * X := by ring

/-- One row of the energy matrix: at most `N R δ` entries are short, and every other entry
has the uniform negative tail bound. -/
lemma FourierSeparator.row_energy_upper {δ X R A : ℝ} (S : FourierSeparator δ)
    (hR : 1 ≤ R) (hA : 0 < A)
    (htail : ∀ r : ℝ, R ≤ r → δ ≤ distToInt r → S.kernel r ≤ -A / Real.sqrt r)
    {P : Finset Plane} (hP : Admissible X δ P) (hX : 1 ≤ X)
    (hδ : 0 < δ) {p : Plane} (hp : p ∈ P) (hlarge : N R δ < P.card) :
    (∑ q ∈ P, S.kernel ‖p - q‖) ≤
      (N R δ : ℝ) * S.totalWeight -
        ((P.card : ℝ) - N R δ) * (A / Real.sqrt (2 * X)) := by
  classical
  let T := P.filter fun q ↦ ‖p - q‖ < R
  let L := P.filter fun q ↦ ¬ ‖p - q‖ < R
  have hTcard : T.card ≤ N R δ := by
    simpa [T] using short_neighbors_card_le_N hδ hP hp
  have hpartition : T.card + L.card = P.card := by
    dsimp [T, L]
    exact P.card_filter_add_card_filter_not (fun q ↦ ‖p - q‖ < R)
  have hW : 0 ≤ S.totalWeight := S.totalWeight_nonneg
  have htwoX : 0 < 2 * X := by positivity
  have hs2X : 0 < Real.sqrt (2 * X) := Real.sqrt_pos.2 htwoX
  have hshort :
      (∑ q ∈ T, S.kernel ‖p - q‖) ≤ (T.card : ℝ) * S.totalWeight := by
    simpa [nsmul_eq_mul] using
      T.sum_le_card_nsmul (fun q ↦ S.kernel ‖p - q‖) S.totalWeight
        (fun q hq ↦ S.kernel_le_totalWeight ‖p - q‖)
  have hlongPoint (q : Plane) (hq : q ∈ L) :
      S.kernel ‖p - q‖ ≤ -A / Real.sqrt (2 * X) := by
    rw [Finset.mem_filter] at hq
    have hdistR : R ≤ ‖p - q‖ := le_of_not_gt hq.2
    have hpq : p ≠ q := by
      intro heq
      subst q
      simp at hdistR
      linarith
    have havoid := hP.2 hp hq.1 hpq
    have htailpq := htail ‖p - q‖ hdistR havoid
    have hdist0 : 0 < ‖p - q‖ := lt_of_lt_of_le zero_lt_one (hR.trans hdistR)
    have hsdist : 0 < Real.sqrt ‖p - q‖ := Real.sqrt_pos.2 hdist0
    have hdistX := hP.pair_distance_le_two_mul hp hq.1
    have hsle : Real.sqrt ‖p - q‖ ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt hdistX
    have hfrac : A / Real.sqrt (2 * X) ≤ A / Real.sqrt ‖p - q‖ :=
      div_le_div_of_nonneg_left hA.le hsdist hsle
    exact htailpq.trans (by simpa [neg_div] using neg_le_neg hfrac)
  have hlong :
      (∑ q ∈ L, S.kernel ‖p - q‖) ≤ (L.card : ℝ) * (-A / Real.sqrt (2 * X)) := by
    simpa [nsmul_eq_mul] using
      L.sum_le_card_nsmul (fun q ↦ S.kernel ‖p - q‖) (-A / Real.sqrt (2 * X)) hlongPoint
  have hsplit := Finset.sum_filter_add_sum_filter_not P (fun q ↦ ‖p - q‖ < R)
    (fun q ↦ S.kernel ‖p - q‖)
  have hrow :
      (∑ q ∈ P, S.kernel ‖p - q‖) =
        (∑ q ∈ T, S.kernel ‖p - q‖) +
        (∑ q ∈ L, S.kernel ‖p - q‖) := by
    simpa [T, L] using hsplit.symm
  rw [hrow]
  have hTcardR : (T.card : ℝ) ≤ N R δ := by exact_mod_cast hTcard
  have hpartR : (T.card : ℝ) + (L.card : ℝ) = P.card := by exact_mod_cast hpartition
  have hB : 0 < A / Real.sqrt (2 * X) := div_pos hA hs2X
  calc
    (∑ q ∈ T, S.kernel ‖p - q‖) + (∑ q ∈ L, S.kernel ‖p - q‖) ≤
        (T.card : ℝ) * S.totalWeight +
          (L.card : ℝ) * (-A / Real.sqrt (2 * X)) := add_le_add hshort hlong
    _ ≤ (N R δ : ℝ) * S.totalWeight +
          ((P.card : ℝ) - N R δ) * (-A / Real.sqrt (2 * X)) := by
      have hLcardR : (P.card : ℝ) - N R δ ≤ L.card := by linarith
      exact add_le_add
        (mul_le_mul_of_nonneg_right hTcardR hW)
        (mul_le_mul_of_nonpos_right hLcardR (by
          simpa [neg_div] using neg_nonpos.mpr hB.le))
    _ = (N R δ : ℝ) * S.totalWeight -
          ((P.card : ℝ) - N R δ) * (A / Real.sqrt (2 * X)) := by ring

/-! ## Konyagin's square-root estimate -/

/-- The energy inequality bounds every admissible configuration by a constant (depending only
on `δ`) times `√X`. -/
theorem configuration_card_le_sqrt {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ P : Finset Plane,
      Admissible X δ P → (P.card : ℝ) ≤ C * Real.sqrt X := by
  obtain ⟨S⟩ := exists_fourierSeparator hδ hδhalf
  obtain ⟨R, A, hR, hA, htail⟩ := S.kernel_long_upper
  let M : ℕ := N R δ
  let C : ℝ := ((M : ℝ) + 1) *
    (1 + S.totalWeight * Real.sqrt 2 / A)
  have hW : 0 ≤ S.totalWeight := S.totalWeight_nonneg
  have hsqrtTwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro X hX P hP
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hsXone : 1 ≤ Real.sqrt X := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hX
  by_cases hsmall : P.card ≤ M
  · have hcardR : (P.card : ℝ) ≤ M := by exact_mod_cast hsmall
    dsimp [C]
    have hratio : 0 ≤ S.totalWeight * Real.sqrt 2 / A := by
      exact div_nonneg (mul_nonneg hW hsqrtTwo.le) hA.le
    have hfactor : 1 ≤ 1 + S.totalWeight * Real.sqrt 2 / A := by linarith
    have hM : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
    calc
      (P.card : ℝ) ≤ M := hcardR
      _ ≤ ((M : ℝ) + 1) * 1 := by simpa using hM
      _ ≤ ((M : ℝ) + 1) *
          (1 + S.totalWeight * Real.sqrt 2 / A) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ ≤ ((M : ℝ) + 1) *
          (1 + S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X :=
        le_mul_of_one_le_right (by positivity) hsXone
  · have hlarge : M < P.card := Nat.lt_of_not_ge hsmall
    have henergy := S.kernel_energy_nonneg P
    have hrow (p : Plane) (hp : p ∈ P) :=
      S.row_energy_upper hR hA htail hP hX hδ hp hlarge
    have hsumUpper :
        (∑ p ∈ P, ∑ q ∈ P, S.kernel ‖p - q‖) ≤
          (P.card : ℝ) *
            ((M : ℝ) * S.totalWeight -
              ((P.card : ℝ) - M) * (A / Real.sqrt (2 * X))) := by
      simpa [M, nsmul_eq_mul] using
        P.sum_le_card_nsmul
          (fun p ↦ ∑ q ∈ P, S.kernel ‖p - q‖)
          ((M : ℝ) * S.totalWeight -
            ((P.card : ℝ) - M) * (A / Real.sqrt (2 * X))) hrow
    have hcardPosNat : 0 < P.card := lt_of_le_of_lt (Nat.zero_le M) hlarge
    have hcardPos : 0 < (P.card : ℝ) := by exact_mod_cast hcardPosNat
    have hs2X : 0 < Real.sqrt (2 * X) := Real.sqrt_pos.2 (by positivity)
    have hbracket :
        0 ≤ (M : ℝ) * S.totalWeight -
          ((P.card : ℝ) - M) * (A / Real.sqrt (2 * X)) := by
      nlinarith
    have hbase :
        ((P.card : ℝ) - M) * (A / Real.sqrt (2 * X)) ≤
          (M : ℝ) * S.totalWeight := by linarith
    have hB : 0 < A / Real.sqrt (2 * X) := div_pos hA hs2X
    have hquot :
        (P.card : ℝ) - M ≤
          ((M : ℝ) * S.totalWeight) / (A / Real.sqrt (2 * X)) :=
      (le_div_iff₀ hB).2 hbase
    have hquot' :
        (P.card : ℝ) - M ≤
          (M : ℝ) * S.totalWeight * Real.sqrt (2 * X) / A := by
      calc
        (P.card : ℝ) - M ≤
            ((M : ℝ) * S.totalWeight) / (A / Real.sqrt (2 * X)) := hquot
        _ = (M : ℝ) * S.totalWeight * Real.sqrt (2 * X) / A := by
          field_simp
    have hs2 : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hs2] at hquot'
    dsimp [C]
    have hMnonneg : 0 ≤ (M : ℝ) := by positivity
    have htargetBase :
        (P.card : ℝ) ≤ (M : ℝ) +
          (M : ℝ) * (S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X := by
      calc
        (P.card : ℝ) ≤ (M : ℝ) +
            (M : ℝ) * S.totalWeight * (Real.sqrt 2 * Real.sqrt X) / A := by
          linarith
        _ = (M : ℝ) +
            (M : ℝ) * (S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X := by
          field_simp
          <;> ring
    calc
      (P.card : ℝ) ≤ (M : ℝ) +
          (M : ℝ) * (S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X := htargetBase
      _ ≤ (M : ℝ) * Real.sqrt X +
          (M : ℝ) * (S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X := by
        simpa using add_le_add_right
          (mul_le_mul_of_nonneg_left hsXone hMnonneg)
          ((M : ℝ) * (S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X)
      _ ≤ ((M : ℝ) + 1) *
          (1 + S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X := by
        have hratio : 0 ≤ S.totalWeight * Real.sqrt 2 / A := by positivity
        have hextra : 0 ≤
            (1 + S.totalWeight * Real.sqrt 2 / A) * Real.sqrt X := by positivity
        nlinarith

/-- Increasing the forbidden neighbourhood of the integers can only decrease the extremal
cardinality. -/
lemma N_anti_delta {X η δ : ℝ} (hη : 0 < η) (hηδ : η ≤ δ) :
    N X δ ≤ N X η := by
  apply N_le_of_forall_card_le
  intro P hP
  exact card_le_N hη (hP.mono_delta hηδ)

/-- Konyagin's bound, in the exact uniform form `N(X,δ) ≤ Cδ √X`.  The reduction to
`min δ (1/4)` also covers `δ ≥ 1/2`, where the question is only easier. -/
theorem konyagin_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      (N X δ : ℝ) ≤ C * Real.sqrt X := by
  let η : ℝ := min δ (1 / 4)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min hδ (by norm_num)
  have hηhalf : η < 1 / 2 := by
    dsimp [η]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C, hC, hconfig⟩ := configuration_card_le_sqrt hη hηhalf
  refine ⟨C, hC, ?_⟩
  intro X hX
  obtain ⟨P, hP, hPcard⟩ := exists_extremal_configuration (X := X) hη
  have hηbound : (N X η : ℝ) ≤ C * Real.sqrt X := by
    rw [← hPcard]
    exact hconfig X hX P hP
  have hmono : N X δ ≤ N X η := N_anti_delta hη (min_le_left _ _)
  exact (by exact_mod_cast hmono : (N X δ : ℝ) ≤ N X η).trans hηbound

/-- The first question in Erdős 465 has an affirmative answer: `N(X,δ) = o(X)`. -/
theorem N_isLittleO_id {δ : ℝ} (hδ : 0 < δ) :
    (fun X : ℝ ↦ (N X δ : ℝ)) =o[atTop] (fun X : ℝ ↦ X) := by
  obtain ⟨C, hC, hbound⟩ := konyagin_bound hδ
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  filter_upwards [eventually_ge_atTop (max 1 ((C / c) ^ 2))] with X hX
  have hXone : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hsX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hsXsq : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX0.le
  have hratio0 : 0 ≤ C / c := div_nonneg hC.le hc.le
  have hratioSq : (C / c) ^ 2 ≤ X := le_trans (le_max_right _ _) hX
  have hratio : C / c ≤ Real.sqrt X := by nlinarith
  have hCsqrt : C ≤ c * Real.sqrt X := by
    calc
      C = (C / c) * c := by field_simp
      _ ≤ Real.sqrt X * c := mul_le_mul_of_nonneg_right hratio hc.le
      _ = c * Real.sqrt X := mul_comm _ _
  have hmain : (N X δ : ℝ) ≤ c * X := calc
    (N X δ : ℝ) ≤ C * Real.sqrt X := hbound X hXone
    _ ≤ (c * Real.sqrt X) * Real.sqrt X :=
      mul_le_mul_of_nonneg_right hCsqrt hsX0
    _ = c * X := by
      calc
        c * Real.sqrt X * Real.sqrt X = c * (Real.sqrt X) ^ 2 := by ring
        _ = c * X := by rw [hsXsq]
  have hNnonneg : 0 ≤ (N X δ : ℝ) := by positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hNnonneg, abs_of_pos hX0] using hmain

/-- The conventional precise meaning of the proposed `X^(1/2+o(1))` upper bound: for every
positive `ε`, eventually `N(X,δ) < X^(1/2+ε)`. -/
theorem N_eventually_lt_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      (N X δ : ℝ) < X ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨C, hC, hbound⟩ := konyagin_bound hδ
  intro ε hε
  have hgrow : ∀ᶠ X : ℝ in atTop, C < X ^ ε :=
    (tendsto_rpow_atTop hε).eventually (eventually_gt_atTop C)
  filter_upwards [eventually_ge_atTop 1, hgrow] with X hX hCX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
  calc
    (N X δ : ℝ) ≤ C * Real.sqrt X := hbound X hX
    _ < X ^ ε * Real.sqrt X := mul_lt_mul_of_pos_right hCX hsX
    _ = X ^ ((1 : ℝ) / 2 + ε) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hX0]
      ring

/-- Complete formal resolution of Erdős Problem 465: Konyagin's square-root estimate, its
little-`o` consequence, and the asserted `1/2+o(1)` exponent formulation. -/
theorem erdos_465 {δ : ℝ} (hδ : 0 < δ) :
    (∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
        (N X δ : ℝ) ≤ C * Real.sqrt X) ∧
      (fun X : ℝ ↦ (N X δ : ℝ)) =o[atTop] (fun X : ℝ ↦ X) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
        (N X δ : ℝ) < X ^ ((1 : ℝ) / 2 + ε)) :=
  ⟨konyagin_bound hδ, N_isLittleO_id hδ, N_eventually_lt_rpow hδ⟩

end

end Erdos465

#print axioms Erdos465.erdos_465
