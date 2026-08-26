/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
MIT License

Copyright (c) 2026 Axiom Math.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

This file has been modified for Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 209. Informal author: Juan García Escudero.
Formal author: AxiomProver. Published by Axiom Math.
Source: https://www.erdosproblems.com/forum/thread/209#post-7065
https://github.com/AxiomMath/erdos-public/blob/3ccf48c78b9df4aa26e1b2f90058bdd3f61da1ab/Erdos/Erdos209/solution.lean
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos209

/-
# Problem Description

Disproof of Erdos Problem 209: For every integer $d \geq 4$, there exists a finite
arrangement of $d$ pairwise non-parallel lines in $\mathbb{R}^2$ such that no point
lies on four or more lines and the arrangement contains no Gallai triangle (ordinary
triangle).

A Gallai triangle (or ordinary triangle) in a line arrangement is a triple of lines
whose three pairwise intersection points each have multiplicity exactly 2 (i.e., no
other line of the arrangement passes through any of the three vertices).

The construction is due to Escudero (2016), who defines arrangements $A_{d,k}$ in the
complex plane $\mathbb{C} \cong \mathbb{R}^2$ using complex exponentials, and shows that
for appropriate choice of $k$ these arrangements have no Gallai triangles.
-/

-- We identify the Euclidean plane $\mathbb{R}^2$ with $\mathbb{C}$ viewed as a
-- 2-dimensional real vector space ($\dim_{\mathbb{R}} \mathbb{C} = 2$).
abbrev PlanePoint := ℂ
abbrev PlaneLine := AffineSubspace ℝ PlanePoint

-- Definition 1 (Line): A line in the plane is a 1-dimensional real affine subspace
-- of $\mathbb{C}$.
def IsLine (L : PlaneLine) : Prop :=
  Module.finrank ℝ L.direction = 1

-- Definition 1 (Line arrangement): A finite set of lines in the plane.
structure LineArrangement where
  lines : Set PlaneLine
  finite : lines.Finite
  all_lines : ∀ L ∈ lines, IsLine L

-- The number of lines in the arrangement.
noncomputable def LineArrangement.card (A : LineArrangement) : ℕ :=
  A.lines.ncard

-- Definition 2 (Multiplicity of a point): The number of lines in the arrangement
-- passing through a given point $p$.
noncomputable def LineArrangement.pointMultiplicity
    (A : LineArrangement) (p : PlanePoint) : ℕ :=
  Set.ncard {L ∈ A.lines | p ∈ (L : Set PlanePoint)}

-- Two lines are parallel if they have the same direction subspace.
def LinesParallel (L₁ L₂ : PlaneLine) : Prop :=
  L₁.direction = L₂.direction

-- Pairwise non-parallel: no two distinct lines in the arrangement are parallel.
def LineArrangement.pairwiseNonParallel (A : LineArrangement) : Prop :=
  ∀ L₁ ∈ A.lines, ∀ L₂ ∈ A.lines, L₁ ≠ L₂ → ¬LinesParallel L₁ L₂

-- Definition 3 (Gallai triangle / ordinary triangle): Three distinct lines from the
-- arrangement whose three pairwise intersection points are distinct and each has
-- multiplicity exactly 2 (i.e., no other line passes through any vertex).
def LineArrangement.IsGallaiTriangle
    (A : LineArrangement) (L₁ L₂ L₃ : PlaneLine) : Prop :=
  L₁ ∈ A.lines ∧ L₂ ∈ A.lines ∧ L₃ ∈ A.lines ∧
  L₁ ≠ L₂ ∧ L₁ ≠ L₃ ∧ L₂ ≠ L₃ ∧
  ∃ p₁₂ p₁₃ p₂₃ : PlanePoint,
    -- $p_{12} = \ell_1 \cap \ell_2$, $p_{13} = \ell_1 \cap \ell_3$,
    -- $p_{23} = \ell_2 \cap \ell_3$
    p₁₂ ∈ (L₁ : Set PlanePoint) ∧ p₁₂ ∈ (L₂ : Set PlanePoint) ∧
    p₁₃ ∈ (L₁ : Set PlanePoint) ∧ p₁₃ ∈ (L₃ : Set PlanePoint) ∧
    p₂₃ ∈ (L₂ : Set PlanePoint) ∧ p₂₃ ∈ (L₃ : Set PlanePoint) ∧
    -- The three intersection points are distinct (lines not concurrent)
    p₁₂ ≠ p₁₃ ∧ p₁₂ ≠ p₂₃ ∧ p₁₃ ≠ p₂₃ ∧
    -- Each vertex has multiplicity exactly 2
    A.pointMultiplicity p₁₂ = 2 ∧
    A.pointMultiplicity p₁₃ = 2 ∧
    A.pointMultiplicity p₂₃ = 2

-- The arrangement has a Gallai triangle if some triple of lines forms one.
def LineArrangement.hasGallaiTriangle (A : LineArrangement) : Prop :=
  ∃ L₁ L₂ L₃, A.IsGallaiTriangle L₁ L₂ L₃

-- Definition 4 (Hypothesis of Erdos Problem 209): An arrangement satisfies the
-- hypothesis if it has $d \geq 4$ pairwise non-parallel lines with no point of
-- multiplicity $\geq 4$.
def LineArrangement.satisfiesErdosHypothesis (A : LineArrangement) : Prop :=
  4 ≤ A.card ∧
  A.pairwiseNonParallel ∧
  ∀ p : PlanePoint, A.pointMultiplicity p ≤ 3

-- Definition 5 (Parametric line in $\mathbb{C}$): The real affine line through
-- $a \in \mathbb{C}$ with direction $b \in \mathbb{C}$, i.e.,
-- $\{a + t \cdot b : t \in \mathbb{R}\}$.
noncomputable def complexParametricLine (a b : ℂ) : PlaneLine :=
  AffineSubspace.mk' a (Submodule.span ℝ {b})

-- Correctness: the direction of a parametric line is $\mathrm{span}_{\mathbb{R}}\{b\}$.
theorem complexParametricLine_direction (a b : ℂ) :
    (complexParametricLine a b).direction = Submodule.span ℝ {b} := by
  unfold complexParametricLine
  exact AffineSubspace.direction_mk' a (Submodule.span ℝ {b})

-- Correctness: complexParametricLine gives a line when $b \neq 0$.
theorem complexParametricLine_isLine (a b : ℂ) (hb : b ≠ 0) :
    IsLine (complexParametricLine a b) := by
  unfold IsLine
  rw [complexParametricLine_direction]
  exact finrank_span_singleton hb

-- Correctness: membership characterization.
-- $p \in \mathrm{complexParametricLine}(a, b) \iff \exists t \in \mathbb{R},\, p = a + t \cdot b$.
theorem mem_complexParametricLine_iff (a b p : ℂ) :
    p ∈ (complexParametricLine a b : Set PlanePoint) ↔ ∃ t : ℝ, p = a + t • b := by
  simp only [SetLike.mem_coe, complexParametricLine, AffineSubspace.mem_mk',
    Submodule.mem_span_singleton, vsub_eq_sub]
  constructor
  · rintro ⟨t, ht⟩
    have h := ht.symm
    rw [sub_eq_iff_eq_add] at h
    exact ⟨t, by rw [h, add_comm]⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, by rw [ht, add_sub_cancel_left]⟩

-- Definition 5 (Escudero's parameter): $u_\nu = (3\nu - k - 1) / (3d)$.
noncomputable def escuderoU (d : ℕ) (k : ℤ) (ν : ℤ) : ℝ :=
  ((3 * ν - k - 1 : ℤ) : ℝ) / ((3 * (d : ℤ)) : ℝ)

-- Definition 5 (Escudero's line): $L_{d,k,\nu}$ given parametrically
-- (identifying $\mathbb{R}^2 \cong \mathbb{C}$) by
-- $z(t) = e^{-i \cdot 2\pi u_\nu} + t \cdot e^{i\pi u_\nu}$, $t \in \mathbb{R}$.
noncomputable def escuderoLine (d : ℕ) (k : ℤ) (ν : ℤ) : PlaneLine :=
  let u := escuderoU d k ν
  let basePoint := Complex.exp (-Complex.I * ↑(2 * Real.pi * u))
  let direction := Complex.exp (Complex.I * ↑(Real.pi * u))
  complexParametricLine basePoint direction

-- Definition 5 (Index set $S$): Depends on the parity of $d$.
-- If $d = 2m+1$, then $S = \{-m+1, \ldots, m+1\}$.
-- If $d = 2m$, then $S = \{-m+1, \ldots, m\}$.
-- In both cases $|S| = d$.
def escuderoIndexSet (d : ℕ) : Set ℤ :=
  if d % 2 = 1 then
    let m := (d - 1) / 2
    {ν : ℤ | -(m : ℤ) + 1 ≤ ν ∧ ν ≤ (m : ℤ) + 1}
  else
    let m := d / 2
    {ν : ℤ | -(m : ℤ) + 1 ≤ ν ∧ ν ≤ (m : ℤ)}

-- Correctness: the index set is finite.
theorem escuderoIndexSet_finite (d : ℕ) :
    Set.Finite (escuderoIndexSet d) := by
  unfold escuderoIndexSet
  split
  · exact Set.Finite.subset (Set.finite_Icc _ _) (fun ν ⟨h1, h2⟩ => ⟨h1, h2⟩)
  · exact Set.Finite.subset (Set.finite_Icc _ _) (fun ν ⟨h1, h2⟩ => ⟨h1, h2⟩)

-- Correctness: the index set has exactly $d$ elements.
theorem escuderoIndexSet_ncard (d : ℕ) :
    Set.ncard (escuderoIndexSet d) = d := by
  simp only [escuderoIndexSet]
  split
  · -- odd case: d = 2m+1, S = {-m+1, ..., m+1}, |S| = 2m+1 = d
    have : {ν : ℤ | -(((d - 1) / 2 : ℕ) : ℤ) + 1 ≤ ν ∧ ν ≤ (((d - 1) / 2 : ℕ) : ℤ) + 1} =
           Set.Icc (-(((d - 1) / 2 : ℕ) : ℤ) + 1) ((((d - 1) / 2 : ℕ) : ℤ) + 1) := by
      ext; simp [Set.mem_Icc]
    rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Icc, Int.card_Icc]
    omega
  · -- even case
    have : {ν : ℤ | -(((d / 2 : ℕ) : ℤ)) + 1 ≤ ν ∧ ν ≤ ((d / 2 : ℕ) : ℤ)} =
           Set.Icc (-((d / 2 : ℕ) : ℤ) + 1) (((d / 2 : ℕ) : ℤ)) := by
      ext; simp [Set.mem_Icc]
    rw [this, Set.ncard_eq_toFinset_card', Set.toFinset_Icc, Int.card_Icc]
    omega

-- Definition 5 (Choice of $k$): $k \in \{0, 1, 2\}$ depends on $d \bmod 9$:
-- $k = 0$ if $d \not\equiv 0 \pmod{3}$, or $d \equiv 0 \pmod{9}$;
-- $k = 2$ if $d \equiv 3$ or $6 \pmod{9}$.
def escuderoK (d : ℕ) : ℤ :=
  if d % 3 ≠ 0 then 0
  else if d % 9 = 0 then 0
  else 2

-- Definition 5 (Escudero's arrangement): $A_{d,k} = \{L_{d,k,\nu} : \nu \in S\}$.
noncomputable def escuderoArrangementLines (d : ℕ) (k : ℤ) : Set PlaneLine :=
  escuderoLine d k '' escuderoIndexSet d

-- Helper: for d ≥ 1 consecutive integers [a, a+d-1], there exists n in the range with d | n - r.
private lemma exists_in_Icc_dvd_sub (a : ℤ) (d : ℕ) (hd : 1 ≤ d) (r : ℤ) :
    ∃ ν, a ≤ ν ∧ ν ≤ a + d - 1 ∧ (d : ℤ) ∣ (ν - r) := by
  refine ⟨a + (r - a) % (d : ℤ), ?_, ?_, ?_⟩
  · linarith [Int.emod_nonneg (r - a) (by omega : (d : ℤ) ≠ 0)]
  · linarith [Int.emod_lt_of_pos (r - a) (by omega : 0 < (d : ℤ))]
  · exact ⟨-((r - a) / d), by linarith [Int.mul_ediv_add_emod (r - a) (d : ℤ)]⟩

-- The escuderoIndexSet is a complete residue system mod d.
lemma escuderoIndexSet_complete_residue (d : ℕ) (hd : 1 ≤ d) (r : ℤ) :
    ∃ ν ∈ escuderoIndexSet d, (d : ℤ) ∣ (ν - r) := by
  unfold escuderoIndexSet
  by_cases hodd : d % 2 = 1
  · simp only [hodd, ↓reduceIte, Set.mem_ofPred_eq]
    set m := (d - 1) / 2
    obtain ⟨ν, hν_lo, hν_hi, hν_dvd⟩ := exists_in_Icc_dvd_sub (-(m : ℤ) + 1) d hd r
    exact ⟨ν, ⟨hν_lo, by omega⟩, hν_dvd⟩
  · simp only [hodd, ↓reduceIte, Set.mem_ofPred_eq]
    set m := d / 2
    obtain ⟨ν, hν_lo, hν_hi, hν_dvd⟩ := exists_in_Icc_dvd_sub (-(m : ℤ) + 1) d hd r
    exact ⟨ν, ⟨hν_lo, by omega⟩, hν_dvd⟩

-- Helper: the index set has bounded width < d.
private lemma escuderoIndexSet_bound (d : ℕ) (hd : 1 ≤ d) (ν₁ ν₂ : ℤ)
    (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d) :
    |ν₁ - ν₂| < d := by
  unfold escuderoIndexSet at h₁ h₂
  rw [abs_lt]
  by_cases hodd : d % 2 = 1
  · simp only [hodd, ↓reduceIte, Set.mem_ofPred_eq] at h₁ h₂
    have key : 2 * (((d - 1) / 2 : ℕ) : ℤ) + 1 ≤ (d : ℤ) := by
      have h := Nat.div_mul_le_self (d - 1) 2; zify [Nat.sub_le] at h ⊢; omega
    constructor <;> omega
  · simp only [hodd, ↓reduceIte, Set.mem_ofPred_eq] at h₁ h₂
    have key : 2 * (((d / 2 : ℕ) : ℤ)) ≤ (d : ℤ) := by
      have h := Nat.div_mul_le_self d 2; zify at h ⊢; omega
    constructor <;> omega

-- Helper: if r (unit) • exp(iθ₁) = exp(iθ₂), then θ₂ - θ₁ ∈ πℤ.
private lemma unit_smul_exp_eq_exp_imp (θ₁ θ₂ : ℝ) (r : ℝˣ)
    (h : r • Complex.exp (↑θ₁ * Complex.I) = Complex.exp (↑θ₂ * Complex.I)) :
    ∃ n : ℤ, θ₂ - θ₁ = n * Real.pi := by
  have h' : (↑(r : ℝ) : ℂ) * Complex.exp (↑θ₁ * Complex.I) =
            Complex.exp (↑θ₂ * Complex.I) := by rwa [← Complex.real_smul]
  have hr_abs : |r.val| = 1 := by
    have h1 := congr_arg (‖·‖) h'
    simp only [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one] at h1
    exact h1
  have hr_val : r.val = 1 ∨ r.val = -1 := by
    cases le_or_gt 0 r.val with
    | inl hr => left; rwa [abs_of_nonneg hr] at hr_abs
    | inr hr => right; rwa [abs_of_neg hr, neg_eq_iff_eq_neg] at hr_abs
  rcases hr_val with hr1 | hr_neg1
  · -- Case r = 1: exp(iθ₁) = exp(iθ₂)
    simp only [hr1, Complex.ofReal_one, one_mul] at h'
    rw [Complex.exp_eq_exp_iff_exists_int] at h'
    obtain ⟨n, hn⟩ := h'
    exact ⟨-2 * n, by
      have h3 : θ₁ = θ₂ + ↑n * 2 * Real.pi := by
        have h1 : (↑θ₁ : ℂ) * Complex.I = (↑θ₂ + ↑n * 2 * ↑Real.pi) * Complex.I := by
          rw [hn]; ring
        exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
      subst h3; push_cast; ring⟩
  · -- Case r = -1: -exp(iθ₁) = exp(iθ₂)
    simp only [hr_neg1, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul] at h'
    have key : Complex.exp (↑θ₂ * Complex.I) =
               Complex.exp (↑(θ₁ + Real.pi) * Complex.I) := by
      rw [← h', Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring
    rw [Complex.exp_eq_exp_iff_exists_int] at key
    obtain ⟨n, hn⟩ := key
    exact ⟨2 * n + 1, by
      have h3 : θ₂ = θ₁ + Real.pi + ↑n * 2 * Real.pi := by
        have h1 : (↑θ₂ : ℂ) * Complex.I = (↑(θ₁ + Real.pi) + ↑n * 2 * ↑Real.pi) * Complex.I := by
          rw [hn]; ring
        exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h1
      subst h3; push_cast; ring⟩

-- Lemma: The escuderoLine map is injective on escuderoIndexSet d when d ≥ 1.
-- (Distinct indices give distinct lines because they have different directions.)
theorem escuderoLine_injective (d : ℕ) (k : ℤ) (hd : 1 ≤ d)
    (ν₁ ν₂ : ℤ) (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d)
    (heq : escuderoLine d k ν₁ = escuderoLine d k ν₂) :
    ν₁ = ν₂ := by
  -- Step 1: Extract direction equality from equal lines
  have hdir : Submodule.span ℝ ({Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₁))} : Set ℂ) =
              Submodule.span ℝ {Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₂))} := by
    have h := congrArg AffineSubspace.direction heq
    simp only [escuderoLine, complexParametricLine, AffineSubspace.direction_mk'] at h
    exact h
  -- Step 2: From equal spans of nonzero vectors, get a unit scalar
  rw [show Submodule.span ℝ ({Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₁))} : Set ℂ) =
        ℝ ∙ Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₁)) from rfl,
      show Submodule.span ℝ ({Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₂))} : Set ℂ) =
        ℝ ∙ Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₂)) from rfl] at hdir
  rw [Submodule.span_singleton_eq_span_singleton] at hdir
  obtain ⟨r, hr⟩ := hdir
  -- Step 3: Apply the key lemma to get πu₂ - πu₁ ∈ πℤ
  have hr' : r • Complex.exp (↑(Real.pi * escuderoU d k ν₁) * Complex.I) =
             Complex.exp (↑(Real.pi * escuderoU d k ν₂) * Complex.I) := by
    rwa [show Complex.I * ↑(Real.pi * escuderoU d k ν₁) =
         ↑(Real.pi * escuderoU d k ν₁) * Complex.I from mul_comm _ _,
         show Complex.I * ↑(Real.pi * escuderoU d k ν₂) =
         ↑(Real.pi * escuderoU d k ν₂) * Complex.I from mul_comm _ _] at hr
  obtain ⟨n, hn⟩ := unit_smul_exp_eq_exp_imp _ _ r hr'
  -- Step 4: Deduce u₂ - u₁ = n (cancel π)
  have hu_diff : escuderoU d k ν₂ - escuderoU d k ν₁ = n := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    exact mul_left_cancel₀ hpi (by rw [mul_sub]; linarith : Real.pi * _ = Real.pi * _)
  -- Step 5: From u₂ - u₁ = n and u = (3ν-k-1)/(3d), deduce ν₂ - ν₁ = n * d
  have hdiv : ν₂ - ν₁ = n * d := by
    unfold escuderoU at hu_diff
    have h3d_ne : (3 * (d : ℤ) : ℝ) ≠ 0 := by positivity
    field_simp at hu_diff
    have key : (3 : ℤ) * (ν₂ - ν₁) = 3 * (n * d) := by
      exact_mod_cast show (3 : ℝ) * ((ν₂ : ℝ) - ν₁) = 3 * (↑n * ↑d) from by
        push_cast at hu_diff ⊢; linarith
    linarith
  -- Step 6: |ν₁ - ν₂| < d and d | (ν₁ - ν₂) implies ν₁ = ν₂
  have hbound := escuderoIndexSet_bound d hd ν₁ ν₂ h₁ h₂
  by_contra hne
  have hne' : ν₁ - ν₂ ≠ 0 := sub_ne_zero.mpr hne
  have h_dvd : (d : ℤ) ∣ (ν₁ - ν₂) := ⟨-n, by linarith [hdiv]⟩
  have h_le := Int.le_of_dvd (abs_pos.mpr hne') ((dvd_abs (d : ℤ) _).mpr h_dvd)
  linarith

-- Lemma: The Escudero arrangement lines form a finite set.
theorem escuderoArrangementLines_finite (d : ℕ) (k : ℤ) :
    Set.Finite (escuderoArrangementLines d k) := by
  exact Set.Finite.image _ (escuderoIndexSet_finite d)

-- Lemma: The Escudero arrangement has exactly d lines.
theorem escuderoArrangementLines_ncard (d : ℕ) (k : ℤ) (hd : 1 ≤ d) :
    Set.ncard (escuderoArrangementLines d k) = d := by
  unfold escuderoArrangementLines
  rw [Set.InjOn.ncard_image
    (fun a ha b hb hab => escuderoLine_injective d k hd a b ha hb hab)]
  exact escuderoIndexSet_ncard d

-- Lemma: Every line in the Escudero arrangement is a line (1-dim affine subspace).
-- This follows because the direction of each line is exp(iπu_ν) ≠ 0.
theorem escuderoArrangementLines_all_lines (d : ℕ) (k : ℤ) :
    ∀ L ∈ escuderoArrangementLines d k, IsLine L := by
  intro L hL
  obtain ⟨ν, _, rfl⟩ := hL
  unfold escuderoLine
  apply complexParametricLine_isLine
  exact Complex.exp_ne_zero _

-- The Escudero arrangement as a LineArrangement structure.
noncomputable def escuderoArrangement (d : ℕ) (k : ℤ) : LineArrangement where
  lines := escuderoArrangementLines d k
  finite := escuderoArrangementLines_finite d k
  all_lines := escuderoArrangementLines_all_lines d k

-- Lemma: Pairwise non-parallel.
-- Two Escudero lines L_{d,k,ν₁} and L_{d,k,ν₂} have directions
-- exp(iπu_{ν₁}) and exp(iπu_{ν₂}). They are parallel iff these span the same
-- 1-d subspace, which (for nonzero complex numbers) happens iff the ratio is real,
-- i.e. exp(iπ(u_{ν₁} - u_{ν₂})) ∈ ℝ, i.e. π(u_{ν₁} - u_{ν₂}) ∈ πℤ,
-- i.e. u_{ν₁} - u_{ν₂} ∈ ℤ. We have u_{ν₁} - u_{ν₂} = (ν₁ - ν₂)/d.
-- For distinct ν₁, ν₂ ∈ S with |S| = d, we have 0 < |ν₁ - ν₂| < d,
-- so (ν₁ - ν₂)/d is not an integer.
theorem escuderoArrangement_pairwiseNonParallel (d : ℕ) (k : ℤ) (hd : 1 ≤ d) :
    (escuderoArrangement d k).pairwiseNonParallel := by
  intro L₁ hL₁ L₂ hL₂ hne hpar
  obtain ⟨ν₁, hν₁, rfl⟩ := hL₁
  obtain ⟨ν₂, hν₂, rfl⟩ := hL₂
  unfold LinesParallel at hpar
  simp only [escuderoLine, complexParametricLine, AffineSubspace.direction_mk'] at hpar
  rw [show Submodule.span ℝ ({Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₁))} : Set ℂ) =
        ℝ ∙ Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₁)) from rfl,
      show Submodule.span ℝ ({Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₂))} : Set ℂ) =
        ℝ ∙ Complex.exp (Complex.I * ↑(Real.pi * escuderoU d k ν₂)) from rfl] at hpar
  rw [Submodule.span_singleton_eq_span_singleton] at hpar
  obtain ⟨r, hr⟩ := hpar
  have hr' : r • Complex.exp (↑(Real.pi * escuderoU d k ν₁) * Complex.I) =
             Complex.exp (↑(Real.pi * escuderoU d k ν₂) * Complex.I) := by
    rwa [show Complex.I * ↑(Real.pi * escuderoU d k ν₁) =
         ↑(Real.pi * escuderoU d k ν₁) * Complex.I from mul_comm _ _,
         show Complex.I * ↑(Real.pi * escuderoU d k ν₂) =
         ↑(Real.pi * escuderoU d k ν₂) * Complex.I from mul_comm _ _] at hr
  obtain ⟨n, hn⟩ := unit_smul_exp_eq_exp_imp _ _ r hr'
  have hu_diff : escuderoU d k ν₂ - escuderoU d k ν₁ = n := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    exact mul_left_cancel₀ hpi (by rw [mul_sub]; linarith : Real.pi * _ = Real.pi * _)
  have hdiv : ν₂ - ν₁ = n * d := by
    unfold escuderoU at hu_diff
    have h3d_ne : (3 * (d : ℤ) : ℝ) ≠ 0 := by positivity
    field_simp at hu_diff
    have key : (3 : ℤ) * (ν₂ - ν₁) = 3 * (n * d) := by
      exact_mod_cast show (3 : ℝ) * ((ν₂ : ℝ) - ν₁) = 3 * (↑n * ↑d) from by
        push_cast at hu_diff ⊢; linarith
    linarith
  have hbound := escuderoIndexSet_bound d hd ν₁ ν₂ hν₁ hν₂
  have heq_idx : ν₁ = ν₂ := by
    by_contra hne'
    have hne'' : ν₁ - ν₂ ≠ 0 := sub_ne_zero.mpr hne'
    have h_dvd : (d : ℤ) ∣ (ν₁ - ν₂) := ⟨-n, by linarith [hdiv]⟩
    have h_le := Int.le_of_dvd (abs_pos.mpr hne'') ((dvd_abs (d : ℤ) _).mpr h_dvd)
    linarith
  exact hne (by rw [heq_idx])

private lemma escuderoLine_mem_iff_im_eq_zero (d : ℕ) (k : ℤ) (ν : ℤ) (p : PlanePoint) :
    p ∈ (escuderoLine d k ν : Set PlanePoint) ↔
    (p * Complex.exp (-Complex.I * ↑(Real.pi * escuderoU d k ν)) -
     Complex.exp (-Complex.I * ↑(3 * Real.pi * escuderoU d k ν))).im = 0 := by
  set u := escuderoU d k ν with hu_def
  set ω := Complex.exp (Complex.I * ↑(Real.pi * u)) with hω_def
  set ωinv := Complex.exp (-Complex.I * ↑(Real.pi * u)) with hωinv_def
  have hω_mul_ωinv : ω * ωinv = 1 := by
    rw [hω_def, hωinv_def, ← Complex.exp_add]; simp
  have hωinv_mul_ω : ωinv * ω = 1 := by rw [mul_comm]; exact hω_mul_ωinv
  have hbase_mul_ωinv : Complex.exp (-Complex.I * ↑(2 * Real.pi * u)) * ωinv =
      Complex.exp (-Complex.I * ↑(3 * Real.pi * u)) := by
    rw [hωinv_def, ← Complex.exp_add]; congr 1; push_cast; ring
  have hωinv3_mul_ω : Complex.exp (-Complex.I * ↑(3 * Real.pi * u)) * ω =
      Complex.exp (-Complex.I * ↑(2 * Real.pi * u)) := by
    rw [hω_def, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [show (escuderoLine d k ν : Set PlanePoint) =
    (complexParametricLine (Complex.exp (-Complex.I * ↑(2 * Real.pi * u))) ω : Set PlanePoint) from by
    simp [escuderoLine, hu_def, hω_def]]
  rw [mem_complexParametricLine_iff]
  constructor
  · rintro ⟨t, ht⟩
    suffices h : p * ωinv - Complex.exp (-Complex.I * ↑(3 * Real.pi * u)) = ↑t by
      rw [h]; simp [Complex.ofReal_im]
    rw [ht, show t • ω = (↑t : ℂ) * ω from Complex.real_smul, add_mul]
    have h1 : (↑t : ℂ) * ω * ωinv = ↑t := by
      rw [mul_assoc, hω_mul_ωinv, mul_one]
    rw [hbase_mul_ωinv, h1, add_sub_cancel_left]
  · intro him
    set z := p * ωinv - Complex.exp (-Complex.I * ↑(3 * Real.pi * u)) with hz_def
    have hz_eq : (z : ℂ) = ↑z.re := by
      apply Complex.ext
      · simp
      · simp [him]
    have hp_eq : p = (z + Complex.exp (-Complex.I * ↑(3 * Real.pi * u))) * ω := by
      have h1 : p * ωinv = z + Complex.exp (-Complex.I * ↑(3 * Real.pi * u)) := by
        rw [hz_def]; ring
      calc p = p * (ωinv * ω) := by rw [hωinv_mul_ω, mul_one]
        _ = (z + Complex.exp (-Complex.I * ↑(3 * Real.pi * u))) * ω := by
            rw [← mul_assoc, h1]
    refine ⟨z.re, ?_⟩
    rw [show z.re • ω = (↑z.re : ℂ) * ω from Complex.real_smul]
    rw [hp_eq, hz_eq, add_mul, hωinv3_mul_ω, add_comm]
    simp [Complex.ofReal_re]

-- Helper: sin(π(ν₁-ν₂)/d) ≠ 0 for distinct indices in the index set
private lemma escuderoU_sin_diff_ne_zero (d : ℕ) (k : ℤ) (hd : 1 ≤ d) (ν₁ ν₂ : ℤ)
    (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d) (hne : ν₁ ≠ ν₂) :
    Real.sin (Real.pi * (escuderoU d k ν₁ - escuderoU d k ν₂)) ≠ 0 := by
  unfold escuderoU
  have hd_ne : (3 * (d : ℤ) : ℝ) ≠ 0 := by positivity
  have hsimpl : Real.pi * (((3 * ν₁ - k - 1 : ℤ) : ℝ) / ((3 * (d : ℤ)) : ℝ) -
    ((3 * ν₂ - k - 1 : ℤ) : ℝ) / ((3 * (d : ℤ)) : ℝ)) = Real.pi * ↑(ν₁ - ν₂) / ↑d := by
    field_simp; push_cast; ring
  rw [hsimpl]; intro h_eq; rw [Real.sin_eq_zero_iff] at h_eq
  obtain ⟨n, hn⟩ := h_eq
  have hd_ne2 : (d : ℝ) ≠ 0 := by positivity
  have hnd' : n * (d : ℤ) = ν₁ - ν₂ := by
    exact_mod_cast show (n : ℝ) * ↑d = ↑(ν₁ - ν₂) from by field_simp at hn; linarith
  have h_dvd : (d : ℤ) ∣ (ν₁ - ν₂) := ⟨n, by linarith⟩
  linarith [escuderoIndexSet_bound d hd ν₁ ν₂ h₁ h₂,
    Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr hne)) ((dvd_abs _ _).mpr h_dvd)]

-- Helper: sin(2α₁+αⱼ) - sin(3αⱼ) = 2sin(α₁-αⱼ)cos(α₁+2αⱼ)
private lemma sin_diff_identity (α₁ αⱼ : ℝ) :
    Real.sin (2*α₁+αⱼ) - Real.sin (3*αⱼ) = 2 * Real.sin (α₁-αⱼ) * Real.cos (α₁+2*αⱼ) := by
  have h := Real.sin_sub_sin (2*α₁+αⱼ) (3*αⱼ)
  rw [show (2*α₁+αⱼ - 3*αⱼ) / 2 = α₁-αⱼ from by ring,
      show (2*α₁+αⱼ + 3*αⱼ) / 2 = α₁+2*αⱼ from by ring] at h
  linarith

private lemma cos_eq_iff_sin_sum_eq_zero (α₁ α₂ α₃ : ℝ)
    (hsin23 : Real.sin (α₂ - α₃) ≠ 0) :
    Real.cos (α₁+2*α₂) = Real.cos (α₁+2*α₃) ↔ Real.sin (α₁+α₂+α₃) = 0 := by
  -- Convert equality to subtraction form
  have key : Real.cos (α₁+2*α₂) - Real.cos (α₁+2*α₃) =
    -2 * Real.sin ((α₁+2*α₂ + (α₁+2*α₃)) / 2) * Real.sin ((α₁+2*α₂ - (α₁+2*α₃)) / 2) :=
    Real.cos_sub_cos _ _
  rw [show (α₁+2*α₂ + (α₁+2*α₃)) / 2 = α₁+α₂+α₃ from by ring,
      show (α₁+2*α₂ - (α₁+2*α₃)) / 2 = α₂-α₃ from by ring] at key
  constructor
  · intro h
    have h' : -2 * Real.sin (α₁+α₂+α₃) * Real.sin (α₂-α₃) = 0 := by linarith
    rcases mul_eq_zero.mp h' with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact h2
    · exact absurd h1 hsin23
  · intro h
    have : -2 * Real.sin (α₁+α₂+α₃) * Real.sin (α₂-α₃) = 0 := by rw [h]; ring
    linarith

private lemma im_param_subst (α β t₁ : ℝ) :
    ((Complex.exp (-Complex.I * ↑(2 * α)) + (↑t₁ : ℂ) * Complex.exp (Complex.I * ↑α)) *
     Complex.exp (-Complex.I * ↑β) -
     Complex.exp (-Complex.I * ↑(3 * β))).im =
    Real.sin (α - β) * (t₁ - 2 * Real.cos (α + 2 * β)) := by
  have h1 : Complex.exp (-Complex.I * ↑(2 * α)) * Complex.exp (-Complex.I * ↑β) =
    Complex.exp (↑(-(2 * α + β)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : (↑t₁ : ℂ) * Complex.exp (Complex.I * ↑α) * Complex.exp (-Complex.I * ↑β) =
    (↑t₁ : ℂ) * Complex.exp (↑(α - β) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]; congr 1; push_cast; ring_nf
  have h3 : Complex.exp (-Complex.I * ↑(3 * β)) = Complex.exp (↑(-(3 * β)) * Complex.I) := by
    congr 1; push_cast; ring
  have h4 : (↑t₁ * Complex.exp (↑(α - β) * Complex.I)).im = t₁ * Real.sin (α - β) := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]; ring
  rw [add_mul, h1, h2, Complex.sub_im, Complex.add_im, h3,
      Complex.exp_ofReal_mul_I_im, h4, Complex.exp_ofReal_mul_I_im,
      Real.sin_neg, Real.sin_neg]
  nlinarith [sin_diff_identity α β]

private lemma escuderoLines_concurrent_iff_sin_eq_zero (d : ℕ) (k : ℤ) (hd : 1 ≤ d)
    (ν₁ ν₂ ν₃ : ℤ)
    (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d) (h₃ : ν₃ ∈ escuderoIndexSet d)
    (hne12 : ν₁ ≠ ν₂) (hne13 : ν₁ ≠ ν₃) (hne23 : ν₂ ≠ ν₃) :
    (∃ p : PlanePoint,
      p ∈ (escuderoLine d k ν₁ : Set PlanePoint) ∧
      p ∈ (escuderoLine d k ν₂ : Set PlanePoint) ∧
      p ∈ (escuderoLine d k ν₃ : Set PlanePoint)) ↔
    Real.sin (Real.pi * ↑(ν₁ + ν₂ + ν₃ - (k + 1)) / ↑d) = 0 := by
  -- Abbreviations for angles α_j = π · u_j
  set u₁ := escuderoU d k ν₁
  set u₂ := escuderoU d k ν₂
  set u₃ := escuderoU d k ν₃
  -- The RHS argument simplifies to π·u₁ + π·u₂ + π·u₃
  have hsum : Real.pi * ↑(ν₁ + ν₂ + ν₃ - (k + 1)) / ↑d = Real.pi * u₁ + Real.pi * u₂ + Real.pi * u₃ := by
    simp only [u₁, u₂, u₃, escuderoU]
    have hd_ne : (3 * (d : ℤ) : ℝ) ≠ 0 := by positivity
    have hd_ne2 : (d : ℝ) ≠ 0 := by positivity
    field_simp; push_cast; ring
  rw [hsum]
  -- sin(π(u₁-u₂)) ≠ 0 (non-parallel)
  have hsin12 : Real.sin (Real.pi * u₁ - Real.pi * u₂) ≠ 0 := by
    rw [show Real.pi * u₁ - Real.pi * u₂ = Real.pi * (u₁ - u₂) from by ring]
    exact escuderoU_sin_diff_ne_zero d k hd ν₁ ν₂ h₁ h₂ hne12
  have hsin13 : Real.sin (Real.pi * u₁ - Real.pi * u₃) ≠ 0 := by
    rw [show Real.pi * u₁ - Real.pi * u₃ = Real.pi * (u₁ - u₃) from by ring]
    exact escuderoU_sin_diff_ne_zero d k hd ν₁ ν₃ h₁ h₃ hne13
  have hsin23 : Real.sin (Real.pi * u₂ - Real.pi * u₃) ≠ 0 := by
    rw [show Real.pi * u₂ - Real.pi * u₃ = Real.pi * (u₂ - u₃) from by ring]
    exact escuderoU_sin_diff_ne_zero d k hd ν₂ ν₃ h₂ h₃ hne23
  -- Use parametric form: p on line ν iff ∃ t, p = exp(-2iπu) + t·exp(iπu)
  -- Forward direction: ∃ p on all 3 lines → sin(sum) = 0
  -- Backward direction: sin(sum) = 0 → ∃ p on all 3 lines
  constructor
  · -- Forward: from p on all 3 lines, derive sin = 0
    rintro ⟨p, hp₁, hp₂, hp₃⟩
    -- Get parametric form from line 1: p = exp(-2iπu₁) + t₁·exp(iπu₁)
    rw [show (escuderoLine d k ν₁ : Set PlanePoint) =
      (complexParametricLine (Complex.exp (-Complex.I * ↑(2 * Real.pi * u₁)))
        (Complex.exp (Complex.I * ↑(Real.pi * u₁))) : Set PlanePoint) from by
      simp [escuderoLine, u₁]] at hp₁
    obtain ⟨t₁, ht₁⟩ := (mem_complexParametricLine_iff _ _ p).mp hp₁
    -- Convert line 2,3 membership to Im conditions
    rw [escuderoLine_mem_iff_im_eq_zero] at hp₂ hp₃
    -- Substitute p = base₁ + t₁ • dir₁ into hp₂ and hp₃
    simp only [show escuderoU d k ν₂ = u₂ from rfl, show escuderoU d k ν₃ = u₃ from rfl] at hp₂ hp₃
    rw [ht₁, show t₁ • Complex.exp (Complex.I * ↑(Real.pi * u₁)) =
      (↑t₁ : ℂ) * Complex.exp (Complex.I * ↑(Real.pi * u₁)) from Complex.real_smul,
      show 3 * Real.pi * u₂ = 3 * (Real.pi * u₂) from by ring,
      show 2 * Real.pi * u₁ = 2 * (Real.pi * u₁) from by ring,
      im_param_subst] at hp₂
    rw [ht₁, show t₁ • Complex.exp (Complex.I * ↑(Real.pi * u₁)) =
      (↑t₁ : ℂ) * Complex.exp (Complex.I * ↑(Real.pi * u₁)) from Complex.real_smul,
      show 3 * Real.pi * u₃ = 3 * (Real.pi * u₃) from by ring,
      show 2 * Real.pi * u₁ = 2 * (Real.pi * u₁) from by ring,
      im_param_subst] at hp₃
    -- hp₂ : sin(πu₁ - πu₂) * (t₁ - 2cos(πu₁ + 2πu₂)) = 0
    -- hp₃ : sin(πu₁ - πu₃) * (t₁ - 2cos(πu₁ + 2πu₃)) = 0
    have ht₂ : t₁ = 2 * Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₂)) := by
      rcases mul_eq_zero.mp hp₂ with h | h
      · exact absurd h hsin12
      · linarith
    have ht₃ : t₁ = 2 * Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₃)) := by
      rcases mul_eq_zero.mp hp₃ with h | h
      · exact absurd h hsin13
      · linarith
    -- cos(πu₁+2πu₂) = cos(πu₁+2πu₃)
    have hcos_eq : Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₂)) =
        Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₃)) := by linarith
    -- Apply cos_eq_iff_sin_sum_eq_zero
    have key := (cos_eq_iff_sin_sum_eq_zero (Real.pi * u₁) (Real.pi * u₂) (Real.pi * u₃) hsin23).mp hcos_eq
    exact key
  · -- Backward: sin(sum) = 0 → construct p on all 3 lines
    intro hsin
    -- sin(πu₁+πu₂+πu₃) = 0 → cos(πu₁+2πu₂) = cos(πu₁+2πu₃)
    have hcos_eq : Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₂)) =
        Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₃)) := by
      apply (cos_eq_iff_sin_sum_eq_zero (Real.pi * u₁) (Real.pi * u₂) (Real.pi * u₃) hsin23).mpr
      exact hsin
    -- Construct p as a point on line 1 with parameter t₁ = 2cos(πu₁+2πu₂)
    set t₁ := 2 * Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₂))
    set p := Complex.exp (-Complex.I * ↑(2 * Real.pi * u₁)) +
             t₁ • Complex.exp (Complex.I * ↑(Real.pi * u₁))
    refine ⟨p, ?_, ?_, ?_⟩
    · -- p ∈ line 1 by construction
      rw [show (escuderoLine d k ν₁ : Set PlanePoint) =
        (complexParametricLine (Complex.exp (-Complex.I * ↑(2 * Real.pi * u₁)))
          (Complex.exp (Complex.I * ↑(Real.pi * u₁))) : Set PlanePoint) from by
        simp [escuderoLine, u₁]]
      exact (mem_complexParametricLine_iff _ _ p).mpr ⟨t₁, rfl⟩
    · -- p ∈ line 2: Im condition = 0
      rw [escuderoLine_mem_iff_im_eq_zero]
      show (p * Complex.exp (-Complex.I * ↑(Real.pi * u₂)) -
            Complex.exp (-Complex.I * ↑(3 * Real.pi * u₂))).im = 0
      rw [show p = Complex.exp (-Complex.I * ↑(2 * Real.pi * u₁)) +
        (↑t₁ : ℂ) * Complex.exp (Complex.I * ↑(Real.pi * u₁)) from by
        simp [p, Complex.real_smul]]
      rw [show 3 * Real.pi * u₂ = 3 * (Real.pi * u₂) from by ring,
          show 2 * Real.pi * u₁ = 2 * (Real.pi * u₁) from by ring,
          im_param_subst]
      simp [t₁, sub_self]
    · -- p ∈ line 3: Im condition = 0, using cos equality
      rw [escuderoLine_mem_iff_im_eq_zero]
      show (p * Complex.exp (-Complex.I * ↑(Real.pi * u₃)) -
            Complex.exp (-Complex.I * ↑(3 * Real.pi * u₃))).im = 0
      rw [show p = Complex.exp (-Complex.I * ↑(2 * Real.pi * u₁)) +
        (↑t₁ : ℂ) * Complex.exp (Complex.I * ↑(Real.pi * u₁)) from by
        simp [p, Complex.real_smul]]
      rw [show 3 * Real.pi * u₃ = 3 * (Real.pi * u₃) from by ring,
          show 2 * Real.pi * u₁ = 2 * (Real.pi * u₁) from by ring,
          im_param_subst]
      -- sin(πu₁ - πu₃) * (t₁ - 2cos(πu₁+2πu₃)) = 0
      -- Since t₁ = 2cos(πu₁+2πu₂) = 2cos(πu₁+2πu₃)
      have : t₁ - 2 * Real.cos (Real.pi * u₁ + 2 * (Real.pi * u₃)) = 0 := by
        simp [t₁]; linarith [hcos_eq]
      rw [this, mul_zero]

private lemma sin_pi_int_div_nat_eq_zero_iff (n : ℤ) (d : ℕ) (hd : 1 ≤ d) :
    Real.sin (Real.pi * ↑n / ↑d) = 0 ↔ (d : ℤ) ∣ n := by
  have hd_ne : ((d : ℤ) : ℝ) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    have key : (m : ℤ) * (d : ℤ) = n := by
      have h1 : ((m : ℤ) : ℝ) * ((d : ℤ) : ℝ) = (n : ℝ) := by
        field_simp at hm; push_cast at hm ⊢; linarith
      exact_mod_cast h1
    exact ⟨m, by linarith⟩
  · intro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]; push_cast; field_simp

theorem escuderoLines_concurrent_iff (d : ℕ) (k : ℤ) (hd : 1 ≤ d)
    (ν₁ ν₂ ν₃ : ℤ) (h₁ : ν₁ ∈ escuderoIndexSet d)
    (h₂ : ν₂ ∈ escuderoIndexSet d) (h₃ : ν₃ ∈ escuderoIndexSet d)
    (hne12 : ν₁ ≠ ν₂) (hne13 : ν₁ ≠ ν₃) (hne23 : ν₂ ≠ ν₃) :
    (∃ p : PlanePoint,
      p ∈ (escuderoLine d k ν₁ : Set PlanePoint) ∧
      p ∈ (escuderoLine d k ν₂ : Set PlanePoint) ∧
      p ∈ (escuderoLine d k ν₃ : Set PlanePoint)) ↔
    (d : ℤ) ∣ (ν₁ + ν₂ + ν₃ - (k + 1)) := by
  rw [escuderoLines_concurrent_iff_sin_eq_zero d k hd ν₁ ν₂ ν₃ h₁ h₂ h₃ hne12 hne13 hne23]
  exact sin_pi_int_div_nat_eq_zero_iff (ν₁ + ν₂ + ν₃ - (k + 1)) d hd

-- Helper: two 1-dim affine subspaces with different directions intersect in at most one point.
private lemma isLine_inter_unique {L₁ L₂ : PlaneLine}
    (h1 : IsLine L₁) (h2 : IsLine L₂) (hne : L₁.direction ≠ L₂.direction)
    {p q : PlanePoint} (hp1 : p ∈ (L₁ : Set PlanePoint)) (hp2 : p ∈ (L₂ : Set PlanePoint))
    (hq1 : q ∈ (L₁ : Set PlanePoint)) (hq2 : q ∈ (L₂ : Set PlanePoint)) :
    p = q := by
  by_contra hpq
  have hv1 : (p -ᵥ q : ℂ) ∈ L₁.direction := AffineSubspace.vsub_mem_direction hp1 hq1
  have hv2 : (p -ᵥ q : ℂ) ∈ L₂.direction := AffineSubspace.vsub_mem_direction hp2 hq2
  have hvne : (p -ᵥ q : ℂ) ≠ 0 := vsub_ne_zero.mpr hpq
  have hmem : (p -ᵥ q : ℂ) ∈ L₁.direction ⊓ L₂.direction :=
    Submodule.mem_inf.mpr ⟨hv1, hv2⟩
  have : 0 < Module.finrank ℝ ↥(L₁.direction ⊓ L₂.direction) := by
    have : Nontrivial ↥(L₁.direction ⊓ L₂.direction) :=
      nontrivial_of_ne ⟨p -ᵥ q, hmem⟩ ⟨0, (L₁.direction ⊓ L₂.direction).zero_mem⟩
        (fun h => hvne (congrArg Subtype.val h))
    exact Module.finrank_pos
  exact hne ((Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [h1]; omega)).symm.trans
    (Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [h2]; omega)))

-- Helper: extract 4 distinct elements from a finite set with ncard ≥ 4.
private lemma extract_four_from_ncard {α : Type*} {S : Set α}
    (hfin : S.Finite) (h4 : 4 ≤ S.ncard) :
    ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hne : S.Nonempty := (Set.ncard_pos hfin).mp (by omega)
  obtain ⟨a, ha⟩ := hne
  have hS1_fin : (S \ {a}).Finite := hfin.subset Set.sdiff_subset
  have h3 : 3 ≤ (S \ {a}).ncard := by rw [Set.ncard_sdiff_singleton_of_mem ha]; omega
  obtain ⟨b, hb⟩ := (Set.ncard_pos hS1_fin).mp (by omega)
  have hbS : b ∈ S := Set.sdiff_subset hb
  have hab : a ≠ b := fun h => by subst h; exact (Set.mem_sdiff_singleton.mp hb).2 rfl
  have hS2_fin : (S \ {a, b}).Finite := hfin.subset Set.sdiff_subset
  have h2 : 2 ≤ (S \ {a, b}).ncard := by
    have hconv : S \ {a, b} = (S \ {a}) \ {b} := by ext; simp [and_assoc]
    rw [hconv, Set.ncard_sdiff_singleton_of_mem hb]; omega
  obtain ⟨c, hc⟩ := (Set.ncard_pos hS2_fin).mp (by omega)
  have hcS : c ∈ S := Set.sdiff_subset hc
  have hc_diff : c ∈ S \ {a, b} := hc
  have hac : a ≠ c := fun h => by subst h; simp at hc_diff
  have hbc : b ≠ c := fun h => by subst h; simp at hc_diff
  have hS3_fin : (S \ {a, b, c}).Finite := hfin.subset Set.sdiff_subset
  have h1 : 1 ≤ (S \ {a, b, c}).ncard := by
    have hconv : S \ {a, b, c} = (S \ {a, b}) \ {c} := by ext; simp [and_assoc]
    rw [hconv, Set.ncard_sdiff_singleton_of_mem hc]; omega
  obtain ⟨d, hd⟩ := (Set.ncard_pos hS3_fin).mp (by omega)
  have hdS : d ∈ S := Set.sdiff_subset hd
  have hd_diff : d ∈ S \ {a, b, c} := hd
  have had : a ≠ d := fun h => by subst h; simp at hd_diff
  have hbd : b ≠ d := fun h => by subst h; simp at hd_diff
  have hcd : c ≠ d := fun h => by subst h; simp at hd_diff
  exact ⟨a, ha, b, hbS, c, hcS, d, hdS, hab, hac, had, hbc, hbd, hcd⟩

-- Helper: derive contradiction from d | (νᵢ - νⱼ) when both are in the index set and distinct
private lemma index_diff_not_dvd (d : ℕ) (hd : 1 ≤ d) (ν₁ ν₂ : ℤ)
    (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d)
    (hne : ν₁ ≠ ν₂) (hdvd : (d : ℤ) ∣ (ν₁ - ν₂)) : False := by
  have hbound := escuderoIndexSet_bound d hd ν₁ ν₂ h₁ h₂
  have hne' : ν₁ - ν₂ ≠ 0 := sub_ne_zero.mpr hne
  linarith [Int.le_of_dvd (abs_pos.mpr hne') ((dvd_abs _ _).mpr hdvd)]

theorem escuderoArrangement_no_four_concurrent (d : ℕ) (k : ℤ) (hd : 1 ≤ d) :
    ∀ p : PlanePoint, (escuderoArrangement d k).pointMultiplicity p ≤ 3 := by
  intro p
  by_contra h_ge4
  push Not at h_ge4
  set A := escuderoArrangement d k
  set S_p := {L ∈ A.lines | p ∈ (L : Set PlanePoint)}
  have hS_p_fin : S_p.Finite := A.finite.subset (fun L hL => hL.1)
  -- Extract 4 distinct lines from S_p
  obtain ⟨L₁, hL₁, L₂, hL₂, L₃, hL₃, L₄, hL₄, hne12, hne13, hne14, hne23, hne24, hne34⟩ :=
    extract_four_from_ncard hS_p_fin h_ge4
  -- Each line is in A.lines and p is on it
  -- Each line comes from an index in escuderoIndexSet d
  obtain ⟨ν₁, hν₁, rfl⟩ : ∃ ν ∈ escuderoIndexSet d, escuderoLine d k ν = L₁ := by
    obtain ⟨ν, hν, hνeq⟩ := hL₁.1; exact ⟨ν, hν, hνeq⟩
  obtain ⟨ν₂, hν₂, rfl⟩ : ∃ ν ∈ escuderoIndexSet d, escuderoLine d k ν = L₂ := by
    obtain ⟨ν, hν, hνeq⟩ := hL₂.1; exact ⟨ν, hν, hνeq⟩
  obtain ⟨ν₃, hν₃, rfl⟩ : ∃ ν ∈ escuderoIndexSet d, escuderoLine d k ν = L₃ := by
    obtain ⟨ν, hν, hνeq⟩ := hL₃.1; exact ⟨ν, hν, hνeq⟩
  obtain ⟨ν₄, hν₄, rfl⟩ : ∃ ν ∈ escuderoIndexSet d, escuderoLine d k ν = L₄ := by
    obtain ⟨ν, hν, hνeq⟩ := hL₄.1; exact ⟨ν, hν, hνeq⟩
  -- Indices are distinct (by injectivity of escuderoLine)
  have hne_ν12 : ν₁ ≠ ν₂ := fun h => hne12 (congrArg (escuderoLine d k) h)
  have hne_ν13 : ν₁ ≠ ν₃ := fun h => hne13 (congrArg (escuderoLine d k) h)
  have hne_ν23 : ν₂ ≠ ν₃ := fun h => hne23 (congrArg (escuderoLine d k) h)
  have hne_ν14 : ν₁ ≠ ν₄ := fun h => hne14 (congrArg (escuderoLine d k) h)
  have hne_ν24 : ν₂ ≠ ν₄ := fun h => hne24 (congrArg (escuderoLine d k) h)
  have hne_ν34 : ν₃ ≠ ν₄ := fun h => hne34 (congrArg (escuderoLine d k) h)
  -- p is on lines ν₁, ν₂, ν₃ → concurrent → d | (ν₁+ν₂+ν₃-(k+1))
  have hconc123 : (d : ℤ) ∣ (ν₁ + ν₂ + ν₃ - (k + 1)) :=
    (escuderoLines_concurrent_iff d k hd ν₁ ν₂ ν₃ hν₁ hν₂ hν₃ hne_ν12 hne_ν13 hne_ν23).mp
      ⟨p, hL₁.2, hL₂.2, hL₃.2⟩
  -- p is on lines ν₁, ν₂, ν₄ → concurrent → d | (ν₁+ν₂+ν₄-(k+1))
  have hconc124 : (d : ℤ) ∣ (ν₁ + ν₂ + ν₄ - (k + 1)) :=
    (escuderoLines_concurrent_iff d k hd ν₁ ν₂ ν₄ hν₁ hν₂ hν₄ hne_ν12 hne_ν14 hne_ν24).mp
      ⟨p, hL₁.2, hL₂.2, hL₄.2⟩
  -- Subtracting: d | (ν₃ - ν₄)
  have hdvd34 : (d : ℤ) ∣ (ν₃ - ν₄) := by
    obtain ⟨c₁, hc₁⟩ := hconc123; obtain ⟨c₂, hc₂⟩ := hconc124
    exact ⟨c₁ - c₂, by linarith⟩
  -- But ν₃ ≠ ν₄ and both are in the index set, so |ν₃ - ν₄| < d, contradiction
  exact index_diff_not_dvd d hd ν₃ ν₄ hν₃ hν₄ hne_ν34 hdvd34

-- Lemma: Two non-parallel Escudero lines intersect.
-- (Since the arrangement is pairwise non-parallel and we are in ℝ², any two
-- non-parallel lines meet in exactly one point.)
theorem escuderoLines_intersect (d : ℕ) (k : ℤ) (hd : 1 ≤ d)
    (ν₁ ν₂ : ℤ) (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d)
    (hne : ν₁ ≠ ν₂) :
    ∃ p : PlanePoint,
      p ∈ (escuderoLine d k ν₁ : Set PlanePoint) ∧
      p ∈ (escuderoLine d k ν₂ : Set PlanePoint) := by
  -- Both lines are nonempty (they are mk' affine subspaces)
  have hne1 : ((escuderoLine d k ν₁ : Set PlanePoint)).Nonempty := by
    unfold escuderoLine complexParametricLine; exact AffineSubspace.mk'_nonempty _ _
  have hne2 : ((escuderoLine d k ν₂ : Set PlanePoint)).Nonempty := by
    unfold escuderoLine complexParametricLine; exact AffineSubspace.mk'_nonempty _ _
  -- The lines are in the arrangement and distinct
  have hlines_ne : escuderoLine d k ν₁ ≠ escuderoLine d k ν₂ :=
    fun heq => hne (escuderoLine_injective d k hd ν₁ ν₂ h₁ h₂ heq)
  have hmem₁ : escuderoLine d k ν₁ ∈ (escuderoArrangement d k).lines :=
    Set.mem_image_of_mem _ h₁
  have hmem₂ : escuderoLine d k ν₂ ∈ (escuderoArrangement d k).lines :=
    Set.mem_image_of_mem _ h₂
  -- By pairwise non-parallel, the directions differ
  have hdir_ne : (escuderoLine d k ν₁).direction ≠ (escuderoLine d k ν₂).direction :=
    escuderoArrangement_pairwiseNonParallel d k hd _ hmem₁ _ hmem₂ hlines_ne
  -- Both directions are 1-dimensional (IsLine)
  set dir₁ := (escuderoLine d k ν₁).direction with dir₁_def
  set dir₂ := (escuderoLine d k ν₂).direction with dir₂_def
  have hd₁ : Module.finrank ℝ ↥dir₁ = 1 :=
    escuderoArrangementLines_all_lines d k _ hmem₁
  have hd₂ : Module.finrank ℝ ↥dir₂ = 1 :=
    escuderoArrangementLines_all_lines d k _ hmem₂
  -- Dimension counting: dir₁ ⊔ dir₂ = ⊤ (since ℂ has ℝ-dimension 2)
  have hdir_sup : dir₁ ⊔ dir₂ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq dir₁ dir₂
    have hinf_le : Module.finrank ℝ ↥(dir₁ ⊓ dir₂) ≤ 1 :=
      le_trans (Submodule.finrank_mono inf_le_left) (le_of_eq hd₁)
    have hinf_zero : Module.finrank ℝ ↥(dir₁ ⊓ dir₂) = 0 := by
      by_contra h; push Not at h
      have hinf1 : Module.finrank ℝ ↥(dir₁ ⊓ dir₂) = 1 := by omega
      have h_eq1 : dir₁ ⊓ dir₂ = dir₁ :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have h_eq2 : dir₁ ⊓ dir₂ = dir₂ :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hdir_ne (h_eq1.symm.trans h_eq2)
    rw [Complex.finrank_real_complex]; omega
  -- Apply the affine subspace intersection theorem
  obtain ⟨p, hp₁, hp₂⟩ := AffineSubspace.inter_nonempty_of_nonempty_of_sup_direction_eq_top
    hne1 hne2 (by rw [dir₁_def, dir₂_def] at hdir_sup; exact hdir_sup)
  exact ⟨p, hp₁, hp₂⟩

-- Lemma (Gallai triangle implies non-concurrency via distinct intersection points):
-- If three lines L₁, L₂, L₃ form a Gallai triangle, the three vertices p₁₂, p₁₃, p₂₃
-- are distinct, so the lines cannot be concurrent. Via the concurrency criterion,
-- this means ν₁ + ν₂ + ν₃ ≢ k+1 (mod d).
theorem gallai_implies_not_concurrent (d : ℕ) (k : ℤ) (hd : 4 ≤ d)
    (ν₁ ν₂ ν₃ : ℤ) (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d)
    (h₃ : ν₃ ∈ escuderoIndexSet d)
    (hne12 : ν₁ ≠ ν₂) (hne13 : ν₁ ≠ ν₃) (hne23 : ν₂ ≠ ν₃)
    (hGT : (escuderoArrangement d k).IsGallaiTriangle
      (escuderoLine d k ν₁) (escuderoLine d k ν₂) (escuderoLine d k ν₃)) :
    ¬((d : ℤ) ∣ (ν₁ + ν₂ + ν₃ - (k + 1))) := by
  -- The Gallai triangle has three distinct intersection points p₁₂, p₁₃, p₂₃.
  -- If the three lines were concurrent, all three intersection points would coincide,
  -- contradicting distinctness. By escuderoLines_concurrent_iff, concurrency is
  -- equivalent to d ∣ (ν₁ + ν₂ + ν₃ - (k + 1)).
  intro hdvd
  -- Get the three distinct intersection points from the Gallai triangle
  obtain ⟨_, _, _, _, _, _, ⟨p₁₂, p₁₃, _, hp₁₂L₁, hp₁₂L₂, hp₁₃L₁, hp₁₃L₃,
    _, _, hp_ne12_13, _, _, _, _, _⟩⟩ := hGT
  -- By concurrent_iff, there is a point p on all three lines
  have hconc := (escuderoLines_concurrent_iff d k (by omega) ν₁ ν₂ ν₃ h₁ h₂ h₃
    hne12 hne13 hne23).mpr hdvd
  obtain ⟨p, hpL₁, hpL₂, hpL₃⟩ := hconc
  -- The lines are IsLine (1-dimensional)
  have hd1 : 1 ≤ d := by omega
  have hisL₁ := escuderoArrangementLines_all_lines d k _ (Set.mem_image_of_mem _ h₁)
  have hisL₃ := escuderoArrangementLines_all_lines d k _ (Set.mem_image_of_mem _ h₃)
  -- Lines are non-parallel
  have hL_ne12 : escuderoLine d k ν₁ ≠ escuderoLine d k ν₂ :=
    fun h => hne12 (escuderoLine_injective d k hd1 ν₁ ν₂ h₁ h₂ h)
  have hL_ne13 : escuderoLine d k ν₁ ≠ escuderoLine d k ν₃ :=
    fun h => hne13 (escuderoLine_injective d k hd1 ν₁ ν₃ h₁ h₃ h)
  have hisL₂ := escuderoArrangementLines_all_lines d k _ (Set.mem_image_of_mem _ h₂)
  have hdir12 : (escuderoLine d k ν₁).direction ≠ (escuderoLine d k ν₂).direction :=
    fun heq => escuderoArrangement_pairwiseNonParallel d k hd1
      _ (Set.mem_image_of_mem _ h₁) _ (Set.mem_image_of_mem _ h₂) hL_ne12 heq
  have hdir13 : (escuderoLine d k ν₁).direction ≠ (escuderoLine d k ν₃).direction :=
    fun heq => escuderoArrangement_pairwiseNonParallel d k hd1
      _ (Set.mem_image_of_mem _ h₁) _ (Set.mem_image_of_mem _ h₃) hL_ne13 heq
  -- Unique intersection: p₁₂ = p and p₁₃ = p
  have h_p12_eq : p₁₂ = p :=
    isLine_inter_unique hisL₁ hisL₂ hdir12 hp₁₂L₁ hp₁₂L₂ hpL₁ hpL₂
  have h_p13_eq : p₁₃ = p :=
    isLine_inter_unique hisL₁ hisL₃ hdir13 hp₁₃L₁ hp₁₃L₃ hpL₁ hpL₃
  -- But p₁₂ ≠ p₁₃, contradiction
  exact hp_ne12_13 (h_p12_eq.trans h_p13_eq.symm)

-- Lemma (Multiplicity-2 at a vertex forces no third line through it):
-- If vertex p = L_{ν₁} ∩ L_{ν₂} has multiplicity 2, then for every ν₃ ∈ S
-- distinct from ν₁ and ν₂, the line L_{ν₃} does not pass through p.
-- By the concurrency criterion, this means:
-- for all ν₃ ∈ S \ {ν₁, ν₂}, ν₁ + ν₂ + ν₃ ≢ k+1 (mod d).
theorem gallai_vertex_mult2_no_third_line (d : ℕ) (k : ℤ) (hd : 4 ≤ d)
    (ν₁ ν₂ : ℤ) (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d)
    (hne : ν₁ ≠ ν₂)
    (p : PlanePoint) (hp₁ : p ∈ (escuderoLine d k ν₁ : Set PlanePoint))
    (hp₂ : p ∈ (escuderoLine d k ν₂ : Set PlanePoint))
    (hmult : (escuderoArrangement d k).pointMultiplicity p = 2) :
    ∀ ν₃ ∈ escuderoIndexSet d, ν₃ ≠ ν₁ → ν₃ ≠ ν₂ →
      ¬((d : ℤ) ∣ (ν₁ + ν₂ + ν₃ - (k + 1))) := by
  intro ν₃ h₃ hne31 hne32 hdvd
  have hd1 : 1 ≤ d := by omega
  -- By concurrent_iff, there exists q on all 3 lines
  have hconc := (escuderoLines_concurrent_iff d k hd1 ν₁ ν₂ ν₃ h₁ h₂ h₃
    hne (Ne.symm hne31) (Ne.symm hne32)).mpr hdvd
  obtain ⟨q, hqL₁, hqL₂, hqL₃⟩ := hconc
  -- Lines are in the arrangement
  set A := escuderoArrangement d k
  have hmult' : A.pointMultiplicity p = 2 := hmult
  have hL₁_mem : escuderoLine d k ν₁ ∈ A.lines := Set.mem_image_of_mem _ h₁
  have hL₂_mem : escuderoLine d k ν₂ ∈ A.lines := Set.mem_image_of_mem _ h₂
  have hL₃_mem : escuderoLine d k ν₃ ∈ A.lines := Set.mem_image_of_mem _ h₃
  -- Lines L₁, L₂ are IsLine
  have hisL₁ := A.all_lines _ hL₁_mem
  have hisL₂ := A.all_lines _ hL₂_mem
  -- L₁ ≠ L₂ and non-parallel
  have hL_ne : escuderoLine d k ν₁ ≠ escuderoLine d k ν₂ :=
    fun h => hne (escuderoLine_injective d k hd1 ν₁ ν₂ h₁ h₂ h)
  have hdir_ne : (escuderoLine d k ν₁).direction ≠ (escuderoLine d k ν₂).direction :=
    fun h => escuderoArrangement_pairwiseNonParallel d k hd1 _ hL₁_mem _ hL₂_mem hL_ne h
  -- Unique intersection: p = q (both on L₁ ∩ L₂)
  have hpq : p = q := isLine_inter_unique hisL₁ hisL₂ hdir_ne hp₁ hp₂ hqL₁ hqL₂
  -- Therefore p ∈ L₃
  have hp₃ : p ∈ (escuderoLine d k ν₃ : Set PlanePoint) := hpq ▸ hqL₃
  -- Lines L₁, L₂, L₃ are distinct
  have hL₃_ne1 : escuderoLine d k ν₃ ≠ escuderoLine d k ν₁ :=
    fun h => hne31 (escuderoLine_injective d k hd1 ν₃ ν₁ h₃ h₁ h)
  have hL₃_ne2 : escuderoLine d k ν₃ ≠ escuderoLine d k ν₂ :=
    fun h => hne32 (escuderoLine_injective d k hd1 ν₃ ν₂ h₃ h₂ h)
  -- {L₁, L₂} ⊆ {L ∈ A.lines | p ∈ L} with ncard 2, so the set equals {L₁, L₂}
  -- But L₃ is also in this set and L₃ ∉ {L₁, L₂}, contradiction
  have hS_fin : Set.Finite {L ∈ A.lines | p ∈ (L : Set PlanePoint)} :=
    A.finite.subset (fun L hL => hL.1)
  have hab_sub : ({escuderoLine d k ν₁, escuderoLine d k ν₂} : Set PlaneLine) ⊆
      {L ∈ A.lines | p ∈ (L : Set PlanePoint)} :=
    Set.insert_subset ⟨hL₁_mem, hp₁⟩ (Set.singleton_subset_iff.mpr ⟨hL₂_mem, hp₂⟩)
  have hab_card : ({escuderoLine d k ν₁, escuderoLine d k ν₂} : Set PlaneLine).ncard = 2 :=
    Set.ncard_pair hL_ne
  have hS_eq : {L ∈ A.lines | p ∈ (L : Set PlanePoint)} =
      {escuderoLine d k ν₁, escuderoLine d k ν₂} :=
    (Set.eq_of_subset_of_ncard_le hab_sub (by rw [hab_card]; unfold LineArrangement.pointMultiplicity at hmult'; omega) hS_fin).symm
  have hL₃_in : escuderoLine d k ν₃ ∈ ({escuderoLine d k ν₁, escuderoLine d k ν₂} : Set PlaneLine) :=
    hS_eq ▸ (⟨hL₃_mem, hp₃⟩ : escuderoLine d k ν₃ ∈ {L ∈ A.lines | p ∈ (L : Set PlanePoint)})
  simp at hL₃_in
  rcases hL₃_in with h | h
  · exact hne31 (escuderoLine_injective d k hd1 ν₃ ν₁ h₃ h₁ h)
  · exact hne32 (escuderoLine_injective d k hd1 ν₃ ν₂ h₃ h₂ h)

theorem gallai_forces_9nu_equiv (d : ℕ) (k : ℤ) (hd : 4 ≤ d)
    (ν₁ ν₂ ν₃ : ℤ) (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d)
    (h₃ : ν₃ ∈ escuderoIndexSet d)
    (hne12 : ν₁ ≠ ν₂) (hne13 : ν₁ ≠ ν₃) (hne23 : ν₂ ≠ ν₃)
    -- For each pair, no third line from S passes through the vertex
    (h12 : ∀ ν ∈ escuderoIndexSet d, ν ≠ ν₁ → ν ≠ ν₂ →
      ¬((d : ℤ) ∣ (ν₁ + ν₂ + ν - (k + 1))))
    (h13 : ∀ ν ∈ escuderoIndexSet d, ν ≠ ν₁ → ν ≠ ν₃ →
      ¬((d : ℤ) ∣ (ν₁ + ν₃ + ν - (k + 1))))
    (h23 : ∀ ν ∈ escuderoIndexSet d, ν ≠ ν₂ → ν ≠ ν₃ →
      ¬((d : ℤ) ∣ (ν₂ + ν₃ + ν - (k + 1)))) :
    (d : ℤ) ∣ (9 * ν₁ - 3 * (k + 1)) ∧
    (d : ℤ) ∣ (9 * ν₂ - 3 * (k + 1)) ∧
    (d : ℤ) ∣ (9 * ν₃ - 3 * (k + 1)) := by
  -- Find complementary indices for each pair
  obtain ⟨ν₁₂, hν₁₂_mem, hν₁₂_dvd⟩ := escuderoIndexSet_complete_residue d (by omega) (k + 1 - ν₁ - ν₂)
  have hν₁₂_dvd' : (d : ℤ) ∣ (ν₁ + ν₂ + ν₁₂ - (k + 1)) := by
    obtain ⟨c, hc⟩ := hν₁₂_dvd; exact ⟨c, by linarith⟩
  have hν₁₂_choice : ν₁₂ = ν₁ ∨ ν₁₂ = ν₂ := by
    by_contra h; push Not at h; exact h12 ν₁₂ hν₁₂_mem h.1 h.2 hν₁₂_dvd'
  obtain ⟨ν₁₃, hν₁₃_mem, hν₁₃_dvd⟩ := escuderoIndexSet_complete_residue d (by omega) (k + 1 - ν₁ - ν₃)
  have hν₁₃_dvd' : (d : ℤ) ∣ (ν₁ + ν₃ + ν₁₃ - (k + 1)) := by
    obtain ⟨c, hc⟩ := hν₁₃_dvd; exact ⟨c, by linarith⟩
  have hν₁₃_choice : ν₁₃ = ν₁ ∨ ν₁₃ = ν₃ := by
    by_contra h; push Not at h; exact h13 ν₁₃ hν₁₃_mem h.1 h.2 hν₁₃_dvd'
  obtain ⟨ν₂₃, hν₂₃_mem, hν₂₃_dvd⟩ := escuderoIndexSet_complete_residue d (by omega) (k + 1 - ν₂ - ν₃)
  have hν₂₃_dvd' : (d : ℤ) ∣ (ν₂ + ν₃ + ν₂₃ - (k + 1)) := by
    obtain ⟨c, hc⟩ := hν₂₃_dvd; exact ⟨c, by linarith⟩
  have hν₂₃_choice : ν₂₃ = ν₂ ∨ ν₂₃ = ν₃ := by
    by_contra h; push Not at h; exact h23 ν₂₃ hν₂₃_mem h.1 h.2 hν₂₃_dvd'
  -- Case split on 8 possibilities. Only (A,B,A) and (B,A,B) are consistent.
  -- A = ν₁₂=ν₁ means d | (2ν₁+ν₂-(k+1)); B = ν₁₂=ν₂ means d | (ν₁+2ν₂-(k+1))
  -- Similarly for the other pairs.
  -- In 6 of 8 cases, subtracting two equations yields d | (νᵢ-νⱼ), contradicting the
  -- index set bound. The remaining 2 cases admit integer linear combinations.
  rcases hν₁₂_choice with h12eq | h12eq <;>
  rcases hν₁₃_choice with h13eq | h13eq <;>
  rcases hν₂₃_choice with h23eq | h23eq
  -- (A,A,A): d | (ν₂-ν₃)
  · exfalso; apply index_diff_not_dvd d (by omega) ν₂ ν₃ h₂ h₃ hne23
    have ⟨c1, hc1⟩ := hν₁₂_dvd'; have ⟨c2, hc2⟩ := hν₁₃_dvd'
    rw [h12eq] at hc1; rw [h13eq] at hc2; exact ⟨c1 - c2, by linarith⟩
  -- (A,A,B): d | (ν₂-ν₃)
  · exfalso; apply index_diff_not_dvd d (by omega) ν₂ ν₃ h₂ h₃ hne23
    have ⟨c1, hc1⟩ := hν₁₂_dvd'; have ⟨c2, hc2⟩ := hν₁₃_dvd'
    rw [h12eq] at hc1; rw [h13eq] at hc2; exact ⟨c1 - c2, by linarith⟩
  -- (A,B,A): VALID — 9νᵢ-3(k+1) = integer linear combo of 3 divisible expressions
  · have ⟨c12, hc12⟩ := hν₁₂_dvd'; have ⟨c13, hc13⟩ := hν₁₃_dvd'; have ⟨c23, hc23⟩ := hν₂₃_dvd'
    rw [h12eq] at hc12; rw [h13eq] at hc13; rw [h23eq] at hc23
    exact ⟨⟨4*c12 + c13 - 2*c23, by linarith⟩,
           ⟨c12 - 2*c13 + 4*c23, by linarith⟩,
           ⟨-2*c12 + 4*c13 + c23, by linarith⟩⟩
  -- (A,B,B): d | (ν₁-ν₂)
  · exfalso; apply index_diff_not_dvd d (by omega) ν₁ ν₂ h₁ h₂ hne12
    have ⟨c1, hc1⟩ := hν₁₃_dvd'; have ⟨c2, hc2⟩ := hν₂₃_dvd'
    rw [h13eq] at hc1; rw [h23eq] at hc2; exact ⟨c1 - c2, by linarith⟩
  -- (B,A,A): d | (ν₁-ν₃)
  · exfalso; apply index_diff_not_dvd d (by omega) ν₁ ν₃ h₁ h₃ hne13
    have ⟨c1, hc1⟩ := hν₁₂_dvd'; have ⟨c2, hc2⟩ := hν₂₃_dvd'
    rw [h12eq] at hc1; rw [h23eq] at hc2; exact ⟨c1 - c2, by linarith⟩
  -- (B,A,B): VALID — 9νᵢ-3(k+1) = integer linear combo of 3 divisible expressions
  · have ⟨c12, hc12⟩ := hν₁₂_dvd'; have ⟨c13, hc13⟩ := hν₁₃_dvd'; have ⟨c23, hc23⟩ := hν₂₃_dvd'
    rw [h12eq] at hc12; rw [h13eq] at hc13; rw [h23eq] at hc23
    exact ⟨⟨c12 + 4*c13 - 2*c23, by linarith⟩,
           ⟨4*c12 - 2*c13 + c23, by linarith⟩,
           ⟨-2*c12 + c13 + 4*c23, by linarith⟩⟩
  -- (B,B,A): d | (ν₁-ν₃)
  · exfalso; apply index_diff_not_dvd d (by omega) ν₁ ν₃ h₁ h₃ hne13
    have ⟨c1, hc1⟩ := hν₁₂_dvd'; have ⟨c2, hc2⟩ := hν₂₃_dvd'
    rw [h12eq] at hc1; rw [h23eq] at hc2; exact ⟨c1 - c2, by linarith⟩
  -- (B,B,B): d | (ν₁-ν₂)
  · exfalso; apply index_diff_not_dvd d (by omega) ν₁ ν₂ h₁ h₂ hne12
    have ⟨c1, hc1⟩ := hν₁₃_dvd'; have ⟨c2, hc2⟩ := hν₂₃_dvd'
    rw [h13eq] at hc1; rw [h23eq] at hc2; exact ⟨c1 - c2, by linarith⟩

-- Helper: 3 distinct integers with |aᵢ - aⱼ| < 3 have sum divisible by 3
-- (they must be a permutation of {n, n+1, n+2} for some n, so sum = 3n+3)
private lemma three_distinct_close_sum_div3 (a₁ a₂ a₃ : ℤ)
    (hne12 : a₁ ≠ a₂) (hne13 : a₁ ≠ a₃) (hne23 : a₂ ≠ a₃)
    (h12 : |a₁ - a₂| < 3) (h13 : |a₁ - a₃| < 3) (h23 : |a₂ - a₃| < 3) :
    (3 : ℤ) ∣ (a₁ + a₂ + a₃) := by
  rw [abs_lt] at h12 h13 h23
  suffices h : (3 : ℤ) ∣ ((a₂ - a₁) + (a₃ - a₁)) by
    obtain ⟨k, hk⟩ := h; exact ⟨a₁ + k, by linarith⟩
  omega

theorem no_gallai_number_theory (d : ℕ) (k : ℤ) (hd : 4 ≤ d)
    (hk : k = escuderoK d)
    (ν₁ ν₂ ν₃ : ℤ) (h₁ : ν₁ ∈ escuderoIndexSet d) (h₂ : ν₂ ∈ escuderoIndexSet d)
    (h₃ : ν₃ ∈ escuderoIndexSet d)
    (hne12 : ν₁ ≠ ν₂) (hne13 : ν₁ ≠ ν₃) (hne23 : ν₂ ≠ ν₃)
    (h_not_concurrent : ¬((d : ℤ) ∣ (ν₁ + ν₂ + ν₃ - (k + 1))))
    (h9₁ : (d : ℤ) ∣ (9 * ν₁ - 3 * (k + 1)))
    (h9₂ : (d : ℤ) ∣ (9 * ν₂ - 3 * (k + 1)))
    (h9₃ : (d : ℤ) ∣ (9 * ν₃ - 3 * (k + 1))) :
    False := by
  -- Sum: d | 9(ν₁ + ν₂ + ν₃ - (k+1))
  have hsum : (d : ℤ) ∣ 9 * (ν₁ + ν₂ + ν₃ - (k + 1)) := by
    obtain ⟨c₁, hc₁⟩ := h9₁; obtain ⟨c₂, hc₂⟩ := h9₂; obtain ⟨c₃, hc₃⟩ := h9₃
    exact ⟨c₁ + c₂ + c₃, by linarith⟩
  -- Differences
  have hdiff12 : (d : ℤ) ∣ 9 * (ν₁ - ν₂) := by
    obtain ⟨c₁, hc₁⟩ := h9₁; obtain ⟨c₂, hc₂⟩ := h9₂; exact ⟨c₁ - c₂, by linarith⟩
  have hdiff13 : (d : ℤ) ∣ 9 * (ν₁ - ν₃) := by
    obtain ⟨c₁, hc₁⟩ := h9₁; obtain ⟨c₃, hc₃⟩ := h9₃; exact ⟨c₁ - c₃, by linarith⟩
  -- Case 1: d % 3 ≠ 0 (gcd(d,9) = 1, so d | 9·X → d | X)
  by_cases h3 : d % 3 ≠ 0
  · have hcop : IsCoprime (d : ℤ) 9 := by
      have h3' : ¬ (3 : ℕ) ∣ d := fun hd' => h3 (Nat.mod_eq_zero_of_dvd hd')
      have hc := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3').symm
      have hc9 : Nat.Coprime d (3^2) := hc.pow_right _
      rw [show (3:ℕ)^2 = 9 from by norm_num] at hc9
      rwa [Int.isCoprime_iff_gcd_eq_one]
    apply h_not_concurrent
    exact hcop.dvd_of_dvd_mul_right (show (d : ℤ) ∣ (ν₁ + ν₂ + ν₃ - (k + 1)) * 9 from by
      rw [show (ν₁ + ν₂ + ν₃ - (k + 1)) * 9 =
        9 * (ν₁ + ν₂ + ν₃ - (k + 1)) from by ring]; exact hsum)
  · push Not at h3
    by_cases h9 : d % 9 = 0
    · -- Case 2: 9 | d, k = 0. Then 9 | (9ν₁ - 3), so 9 | 3, contradiction.
      have hk0 : k = 0 := by
        rw [hk]; unfold escuderoK; simp [show ¬(d % 3 ≠ 0) from by omega, h9]
      obtain ⟨c₁, hc₁⟩ := h9₁
      have h9d : (9 : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mod_eq_zero h9
      have h_9_dvd : (9 : ℤ) ∣ (9 * ν₁ - 3 * (k + 1)) :=
        dvd_trans h9d ⟨c₁, hc₁⟩
      rw [hk0] at h_9_dvd
      have h93 : (9 : ℤ) ∣ 3 := by
        have h1 : (9 : ℤ) ∣ (9 * ν₁) := dvd_mul_right 9 ν₁
        exact (show 9 * ν₁ - (9 * ν₁ - 3 * (0 + 1)) = (3 : ℤ) from by ring) ▸
          dvd_sub h1 h_9_dvd
      omega
    · -- Case 3: 3 | d, 9 ∤ d, k = 2. Write d = 3e with gcd(e,3) = 1.
      have hk2 : k = 2 := by
        rw [hk]; unfold escuderoK
        simp only [show ¬(d % 3 ≠ 0) from by omega,
          ↓reduceIte, show ¬(d % 9 = 0) from h9]
      subst hk2
      obtain ⟨e, he⟩ : (3 : ℕ) ∣ d := Nat.dvd_of_mod_eq_zero (by omega)
      have he_pos : 1 ≤ e := by omega
      have h3ne : e % 3 ≠ 0 := by omega
      have hcop_e3 : IsCoprime (e : ℤ) 3 := by
        have h3' : ¬ (3 : ℕ) ∣ e :=
          fun hd' => h3ne (Nat.mod_eq_zero_of_dvd hd')
        have hc := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3').symm
        rwa [Int.isCoprime_iff_gcd_eq_one]
      -- From d | 9(x-y): 3e | 9(x-y) → e | 3(x-y) → e | (x-y)
      have he_dvd_diff : ∀ x y : ℤ,
          (d : ℤ) ∣ 9 * (x - y) → (e : ℤ) ∣ (x - y) := by
        intro x y hdvd
        have h1 : (↑(3 * e) : ℤ) ∣ 9 * (x - y) := by
          rwa [show (↑(3 * e) : ℤ) = (d : ℤ) from by push_cast; omega]
        have h2 : (e : ℤ) ∣ 3 * (x - y) := by
          obtain ⟨c, hc⟩ := h1; push_cast at hc
          exact ⟨c, by linarith⟩
        exact hcop_e3.dvd_of_dvd_mul_right
          (show (e : ℤ) ∣ (x - y) * 3 from by
            rw [show (x - y) * 3 = 3 * (x - y) from by ring]
            exact h2)
      have he_dvd12 := he_dvd_diff ν₁ ν₂ hdiff12
      have he_dvd13 := he_dvd_diff ν₁ ν₃ hdiff13
      -- e | (νᵢ - 1) since d | 9(νᵢ - 1) (because 3(k+1) = 9)
      have he_dvd1 : (e : ℤ) ∣ (ν₁ - 1) := by
        apply he_dvd_diff
        obtain ⟨c, hc⟩ := h9₁; exact ⟨c, by linarith⟩
      have he_dvd2 : (e : ℤ) ∣ (ν₂ - 1) := by
        have : ν₂ - 1 = -(ν₁ - ν₂) + (ν₁ - 1) := by ring
        rw [this]; exact dvd_add (dvd_neg.mpr he_dvd12) he_dvd1
      have he_dvd3 : (e : ℤ) ∣ (ν₃ - 1) := by
        have : ν₃ - 1 = -(ν₁ - ν₃) + (ν₁ - 1) := by ring
        rw [this]; exact dvd_add (dvd_neg.mpr he_dvd13) he_dvd1
      -- Write νᵢ = 1 + e·aᵢ
      obtain ⟨a₁, ha₁⟩ := he_dvd1
      obtain ⟨a₂, ha₂⟩ := he_dvd2
      obtain ⟨a₃, ha₃⟩ := he_dvd3
      -- aᵢ are distinct
      have hane12 : a₁ ≠ a₂ := fun h => hne12 (by nlinarith)
      have hane13 : a₁ ≠ a₃ := fun h => hne13 (by nlinarith)
      have hane23 : a₂ ≠ a₃ := fun h => hne23 (by nlinarith)
      -- |aᵢ - aⱼ| < 3 (since |νᵢ-νⱼ| < d = 3e and νᵢ-νⱼ = e(aᵢ-aⱼ))
      have hbd12 := escuderoIndexSet_bound d (by omega) ν₁ ν₂ h₁ h₂
      have hbd13 := escuderoIndexSet_bound d (by omega) ν₁ ν₃ h₁ h₃
      have hbd23 := escuderoIndexSet_bound d (by omega) ν₂ ν₃ h₂ h₃
      have he_nn : (0 : ℤ) ≤ ↑e := by omega
      have hab12 : |a₁ - a₂| < 3 := by
        have : |ν₁ - ν₂| = ↑e * |a₁ - a₂| := by
          rw [show ν₁ - ν₂ = ↑e * (a₁ - a₂) from by linarith,
              abs_mul, abs_of_nonneg he_nn]
        rw [he] at hbd12; push_cast at hbd12; nlinarith
      have hab13 : |a₁ - a₃| < 3 := by
        have : |ν₁ - ν₃| = ↑e * |a₁ - a₃| := by
          rw [show ν₁ - ν₃ = ↑e * (a₁ - a₃) from by linarith,
              abs_mul, abs_of_nonneg he_nn]
        rw [he] at hbd13; push_cast at hbd13; nlinarith
      have hab23 : |a₂ - a₃| < 3 := by
        have : |ν₂ - ν₃| = ↑e * |a₂ - a₃| := by
          rw [show ν₂ - ν₃ = ↑e * (a₂ - a₃) from by linarith,
              abs_mul, abs_of_nonneg he_nn]
        rw [he] at hbd23; push_cast at hbd23; nlinarith
      -- ν₁+ν₂+ν₃ - 3 = e(a₁+a₂+a₃), and 3 | (a₁+a₂+a₃)
      have hS_eq : ν₁ + ν₂ + ν₃ - (2 + 1) = ↑e * (a₁ + a₂ + a₃) := by
        linarith
      have h3_sum : (3 : ℤ) ∣ (a₁ + a₂ + a₃) :=
        three_distinct_close_sum_div3 a₁ a₂ a₃
          hane12 hane13 hane23 hab12 hab13 hab23
      -- d = 3e divides e(a₁+a₂+a₃) since 3 | (a₁+a₂+a₃)
      apply h_not_concurrent
      rw [hS_eq]
      obtain ⟨m, hm⟩ := h3_sum
      rw [hm,
          show ↑e * (3 * m) = ↑(3 * e) * m from by push_cast; ring,
          show (d : ℤ) = ↑(3 * e) from by push_cast; omega]
      exact dvd_mul_right _ _

-- The main no-Gallai-triangle theorem, assembled from the lemmas above.
theorem escuderoArrangement_no_gallai_triangle (d : ℕ) (k : ℤ) (hd : 4 ≤ d)
    (hk : k = escuderoK d) :
    ¬(escuderoArrangement d k).hasGallaiTriangle := by
  -- Assume for contradiction that there is a Gallai triangle.
  intro ⟨L₁, L₂, L₃, hGT⟩
  -- Since L₁, L₂, L₃ ∈ escuderoArrangementLines, they come from indices ν₁, ν₂, ν₃ ∈ S.
  have hL₁ := hGT.1
  have hL₂ := hGT.2.1
  have hL₃ := hGT.2.2.1
  -- Obtain the indices
  have ⟨ν₁, hν₁S, hν₁eq⟩ : ∃ ν ∈ escuderoIndexSet d, escuderoLine d k ν = L₁ := by
    simp [escuderoArrangement, escuderoArrangementLines] at hL₁; exact hL₁
  have ⟨ν₂, hν₂S, hν₂eq⟩ : ∃ ν ∈ escuderoIndexSet d, escuderoLine d k ν = L₂ := by
    simp [escuderoArrangement, escuderoArrangementLines] at hL₂; exact hL₂
  have ⟨ν₃, hν₃S, hν₃eq⟩ : ∃ ν ∈ escuderoIndexSet d, escuderoLine d k ν = L₃ := by
    simp [escuderoArrangement, escuderoArrangementLines] at hL₃; exact hL₃
  -- The three indices are distinct (by injectivity of escuderoLine on S)
  have hne12 : ν₁ ≠ ν₂ := by
    intro heq; exact hGT.2.2.2.1 (by rw [← hν₁eq, ← hν₂eq, heq])
  have hne13 : ν₁ ≠ ν₃ := by
    intro heq; exact hGT.2.2.2.2.1 (by rw [← hν₁eq, ← hν₃eq, heq])
  have hne23 : ν₂ ≠ ν₃ := by
    intro heq; exact hGT.2.2.2.2.2.1 (by rw [← hν₂eq, ← hν₃eq, heq])
  -- Rewrite the Gallai triangle in terms of indices
  rw [← hν₁eq, ← hν₂eq, ← hν₃eq] at hGT
  have h_nc := gallai_implies_not_concurrent d k hd ν₁ ν₂ ν₃
    hν₁S hν₂S hν₃S hne12 hne13 hne23 hGT
  obtain ⟨p₁₂, p₁₃, p₂₃, hp₁₂L₁, hp₁₂L₂, hp₁₃L₁, hp₁₃L₃,
    hp₂₃L₂, hp₂₃L₃, _, _, _, hmult₁₂, hmult₁₃, hmult₂₃⟩ := hGT.2.2.2.2.2.2
  have h12 := gallai_vertex_mult2_no_third_line d k hd ν₁ ν₂
    hν₁S hν₂S hne12 p₁₂ hp₁₂L₁ hp₁₂L₂ hmult₁₂
  have h13 := gallai_vertex_mult2_no_third_line d k hd ν₁ ν₃
    hν₁S hν₃S hne13 p₁₃ hp₁₃L₁ hp₁₃L₃ hmult₁₃
  have h23 := gallai_vertex_mult2_no_third_line d k hd ν₂ ν₃
    hν₂S hν₃S hne23 p₂₃ hp₂₃L₂ hp₂₃L₃ hmult₂₃
  have ⟨h9₁, h9₂, h9₃⟩ := gallai_forces_9nu_equiv d k hd ν₁ ν₂ ν₃
    hν₁S hν₂S hν₃S hne12 hne13 hne23 h12 h13 h23
  exact no_gallai_number_theory d k hd hk ν₁ ν₂ ν₃
    hν₁S hν₂S hν₃S hne12 hne13 hne23 h_nc h9₁ h9₂ h9₃

-- The Escudero arrangement satisfies all required properties.
noncomputable def escuderoArrangementForD (d : ℕ) : LineArrangement :=
  escuderoArrangement d (escuderoK d)

theorem escuderoArrangementForD_card (d : ℕ) (hd : 4 ≤ d) :
    (escuderoArrangementForD d).card = d := by
  unfold escuderoArrangementForD
  unfold LineArrangement.card escuderoArrangement
  simp only
  exact escuderoArrangementLines_ncard d (escuderoK d) (by omega)

theorem escuderoArrangementForD_pairwiseNonParallel (d : ℕ) (hd : 4 ≤ d) :
    (escuderoArrangementForD d).pairwiseNonParallel := by
  unfold escuderoArrangementForD
  exact escuderoArrangement_pairwiseNonParallel d (escuderoK d) (by omega)

theorem escuderoArrangementForD_mult_le_3 (d : ℕ) (hd : 4 ≤ d) :
    ∀ p : PlanePoint, (escuderoArrangementForD d).pointMultiplicity p ≤ 3 := by
  unfold escuderoArrangementForD
  exact escuderoArrangement_no_four_concurrent d (escuderoK d) (by omega)

theorem escuderoArrangementForD_no_gallai (d : ℕ) (hd : 4 ≤ d) :
    ¬(escuderoArrangementForD d).hasGallaiTriangle := by
  unfold escuderoArrangementForD
  exact escuderoArrangement_no_gallai_triangle d (escuderoK d) hd rfl

-- Theorem (Disproof of Erdos Problem 209): For every $d \geq 4$, there exists a
-- line arrangement of $d$ pairwise non-parallel lines in $\mathbb{R}^2$ with no
-- point of multiplicity $\geq 4$ and no Gallai triangle.
-- Equivalently: the answer to Erdos Problem 209 is **no**.
theorem erdos_problem_209_disproof :
    ∀ d : ℕ, 4 ≤ d →
    ∃ A : LineArrangement,
      A.card = d ∧
      A.pairwiseNonParallel ∧
      (∀ p : PlanePoint, A.pointMultiplicity p ≤ 3) ∧
      ¬A.hasGallaiTriangle := by
  intro d hd
  exact ⟨escuderoArrangementForD d,
    escuderoArrangementForD_card d hd,
    escuderoArrangementForD_pairwiseNonParallel d hd,
    escuderoArrangementForD_mult_le_3 d hd,
    escuderoArrangementForD_no_gallai d hd⟩

end Erdos209
