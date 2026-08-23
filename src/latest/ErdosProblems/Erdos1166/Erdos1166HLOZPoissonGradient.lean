import ErdosProblems.Erdos1166.Erdos1166HLOZPoissonCanonical
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixATwoPointSource
import ErdosProblems.Erdos1166.Erdos1166HLOZNormalResolvent
import ErdosProblems.Erdos1166.Erdos1166HLOZSquareLazyKernel

namespace Erdos1166.KilledGreen

open scoped BigOperators ENNReal
open HLOZAppendixATwoPointSource
open HLOZAppendixAFirstMoment
open HLOZPropositionA7

/-! # Localized Poisson-kernel gradients

The source Harnack estimate is local in the starting point.  The lemmas in
this file isolate the sharp analytic input in that form: an `O(R⁻²)` edge
gradient for the exit kernel and an `Omega(R⁻¹)` lower bound for the reference
exit mass.  Telescoping along an inner path then gives the required relative
`O(r / R)` estimate, without taking a global range over the outer boundary.
-/

/-- Telescoping an edge estimate along a finite path. -/
theorem abs_sub_le_pathLength_mul_of_edge
    {f : Site → ℝ} {path : ℕ → Site} {pathLength : ℕ} {edgeBound : ℝ}
    (hedge : ∀ k < pathLength,
      |f (path (k + 1)) - f (path k)| ≤ edgeBound) :
    |f (path pathLength) - f (path 0)| ≤
      (pathLength : ℝ) * edgeBound := by
  induction pathLength with
  | zero => simp
  | succ n ih =>
      have hlast := hedge n (by omega)
      have hprev : ∀ k < n,
          |f (path (k + 1)) - f (path k)| ≤ edgeBound := by
        intro k hk
        exact hedge k (by omega)
      have htel := ih hprev
      rw [show f (path (n + 1)) - f (path 0) =
          (f (path (n + 1)) - f (path n)) +
            (f (path n) - f (path 0)) by ring]
      calc
        |(f (path (n + 1)) - f (path n)) +
            (f (path n) - f (path 0))| ≤
            |f (path (n + 1)) - f (path n)| +
              |f (path n) - f (path 0)| := abs_add_le _ _
        _ ≤ edgeBound + (n : ℝ) * edgeBound := add_le_add hlast htel
        _ = ((n + 1 : ℕ) : ℝ) * edgeBound := by
          push_cast
          ring

/-- The sharp localized analytic premise for one square exit site.  Unlike a
global boundary oscillation, this controls only gradients traversed by the
inner path and the mass at its reference endpoint. -/
def HasLocalizedSquareExitKernelBounds
    (R : ℕ) (path : ℕ → Site) (pathLength : ℕ) (y : Site)
    (gradientConstant denominatorConstant : ℝ) : Prop :=
  (∀ k < pathLength,
      |squareGreenExitKernel R (path (k + 1)) y -
          squareGreenExitKernel R (path k) y| ≤
        gradientConstant / (R : ℝ) ^ 2) ∧
    denominatorConstant / (R : ℝ) ≤
      squareGreenExitKernel R (path 0) y

/-- The uniform inner-edge formulation of the remaining analytic estimate.
It is the discrete fixed-exit-site gradient bound used in the proofs of
Rosen's Lemma 6.1 and HLOZ Lemma A.2. -/
def HasUniformInnerSquareExitKernelGradient
    (r R : ℕ) (referenceStart y : Site)
    (gradientConstant denominatorConstant : ℝ) : Prop :=
  (∀ x ∈ squareDisk r, ∀ d : Direction,
      x + directionStep d ∈ squareDisk r →
        |squareGreenExitKernel R (x + directionStep d) y -
            squareGreenExitKernel R x y| ≤
          gradientConstant / (R : ℝ) ^ 2) ∧
    denominatorConstant / (R : ℝ) ≤
      squareGreenExitKernel R referenceStart y

/-- A nearest-neighbor path inside the inner square converts the uniform
gradient estimate into the localized premise used below. -/
theorem hasLocalizedSquareExitKernelBounds_of_uniformInnerGradient
    {r R pathLength : ℕ} {referenceStart y : Site}
    {path : ℕ → Site} {direction : ℕ → Direction}
    {gradientConstant denominatorConstant : ℝ}
    (hstart : path 0 = referenceStart)
    (hstep : ∀ k < pathLength,
      path (k + 1) = path k + directionStep (direction k))
    (hinner : ∀ k ≤ pathLength, path k ∈ squareDisk r)
    (huniform : HasUniformInnerSquareExitKernelGradient
      r R referenceStart y gradientConstant denominatorConstant) :
    HasLocalizedSquareExitKernelBounds R path pathLength y
      gradientConstant denominatorConstant := by
  constructor
  · intro k hk
    rw [hstep k hk]
    exact huniform.1 (path k) (hinner k (Nat.le_of_lt hk)) (direction k)
      (by rw [← hstep k hk]; exact hinner (k + 1) (by omega))
  · simpa [hstart] using huniform.2

/-- Corner-robust localized form of the sharp Poisson-kernel estimate.  Its
edge error is normalized by the reference exit mass itself, so it remains
meaningful for boundary sites whose harmonic measure is smaller than order
`R⁻¹`. -/
def HasLocalizedSquareExitKernelRelativeGradient
    (R : ℕ) (path : ℕ → Site) (pathLength : ℕ) (y : Site)
    (relativeConstant : ℝ) : Prop :=
  0 < squareGreenExitKernel R (path 0) y ∧
    ∀ k < pathLength,
      |squareGreenExitKernel R (path (k + 1)) y -
          squareGreenExitKernel R (path k) y| ≤
        (relativeConstant / (R : ℝ)) *
          squareGreenExitKernel R (path 0) y

/-- Uniform inner-edge version of the corner-robust relative gradient.  This
is the exact remaining Lawler--Rosen discrete harmonic-measure premise. -/
def HasUniformInnerSquareExitKernelRelativeGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  0 < squareGreenExitKernel R referenceStart y ∧
    ∀ x ∈ squareDisk r, ∀ d : Direction,
      x + directionStep d ∈ squareDisk r →
        |squareGreenExitKernel R (x + directionStep d) y -
            squareGreenExitKernel R x y| ≤
          (relativeConstant / (R : ℝ)) *
            squareGreenExitKernel R referenceStart y

/-- Zero-safe, cross-multiplied form of the uniform inner edge estimate.
Unlike `HasUniformInnerSquareExitKernelRelativeGradient`, this formulation
does not assume that the reference exit mass is positive.  If that mass is
zero, the estimate forces every traversed edge difference to vanish, which
is exactly what the one-sided exit-word comparison needs. -/
def HasUniformInnerSquareExitKernelScaledEdgeGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ x ∈ squareDisk r, ∀ d : Direction,
    x + directionStep d ∈ squareDisk r →
      (R : ℝ) *
          |squareGreenExitKernel R (x + directionStep d) y -
            squareGreenExitKernel R x y| ≤
        relativeConstant * squareGreenExitKernel R referenceStart y

theorem hasLocalizedSquareExitKernelRelativeGradient_of_uniformInner
    {r R pathLength : ℕ} {referenceStart y : Site}
    {path : ℕ → Site} {direction : ℕ → Direction}
    {relativeConstant : ℝ}
    (hstart : path 0 = referenceStart)
    (hstep : ∀ k < pathLength,
      path (k + 1) = path k + directionStep (direction k))
    (hinner : ∀ k ≤ pathLength, path k ∈ squareDisk r)
    (huniform : HasUniformInnerSquareExitKernelRelativeGradient
      r R referenceStart y relativeConstant) :
    HasLocalizedSquareExitKernelRelativeGradient
      R path pathLength y relativeConstant := by
  constructor
  · simpa [hstart] using huniform.1
  · intro k hk
    rw [hstep k hk, hstart]
    exact huniform.2 (path k) (hinner k (Nat.le_of_lt hk)) (direction k)
      (by rw [← hstep k hk]; exact hinner (k + 1) (by omega))

/-- Telescoping the corner-robust relative edge gradient gives the sharp
`O(pathLength / R)` relative exit-kernel estimate directly, with no separate
boundary-mass lower bound. -/
theorem squareGreenExitKernel_ratio_path_le_of_relativeGradient
    {R pathLength : ℕ} {path : ℕ → Site} {y : Site}
    {relativeConstant : ℝ} (hR : 0 < R)
    (hrelative : HasLocalizedSquareExitKernelRelativeGradient
      R path pathLength y relativeConstant) :
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
      relativeConstant * ((pathLength : ℝ) / (R : ℝ)) := by
  have hdiff :
      |squareGreenExitKernel R (path pathLength) y -
          squareGreenExitKernel R (path 0) y| ≤
        (pathLength : ℝ) *
          ((relativeConstant / (R : ℝ)) *
            squareGreenExitKernel R (path 0) y) := by
    exact abs_sub_le_pathLength_mul_of_edge
      (f := fun x ↦ squareGreenExitKernel R x y)
      (path := path) (pathLength := pathLength)
      (edgeBound := (relativeConstant / (R : ℝ)) *
        squareGreenExitKernel R (path 0) y) hrelative.2
  have hratio := ratio_sub_one_abs_le_of_abs_sub_le
    hrelative.1 (le_refl _) hdiff
  have hrefNe : squareGreenExitKernel R (path 0) y ≠ 0 := ne_of_gt hrelative.1
  have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  calc
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
        ((pathLength : ℝ) *
          ((relativeConstant / (R : ℝ)) *
            squareGreenExitKernel R (path 0) y)) /
              squareGreenExitKernel R (path 0) y := hratio
    _ = relativeConstant * ((pathLength : ℝ) / (R : ℝ)) := by
      field_simp

theorem squareGreenExitKernel_ratio_path_le_cubicScale_of_relativeGradient
    {n r R pathLength : ℕ} {path : ℕ → Site} {y : Site}
    {relativeConstant : ℝ}
    (hn : 0 < n) (hR : 0 < R) (hr : pathLength ≤ r)
    (hscale : n ^ 3 * r ≤ R) (hconstant : 0 ≤ relativeConstant)
    (hrelative : HasLocalizedSquareExitKernelRelativeGradient
      R path pathLength y relativeConstant) :
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
      relativeConstant / (n : ℝ) ^ 3 := by
  have hbase := squareGreenExitKernel_ratio_path_le_of_relativeGradient
    hR hrelative
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hmulNat : pathLength * n ^ 3 ≤ R := by
    calc
      pathLength * n ^ 3 ≤ r * n ^ 3 := Nat.mul_le_mul_right _ hr
      _ = n ^ 3 * r := Nat.mul_comm _ _
      _ ≤ R := hscale
  have hmul : (pathLength : ℝ) * (n : ℝ) ^ 3 ≤ (R : ℝ) := by
    exact_mod_cast hmulNat
  have hratio : (pathLength : ℝ) / (R : ℝ) ≤
      1 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hRreal (pow_pos hnreal 3)]
    simpa [mul_comm] using hmul
  calc
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
        relativeConstant * ((pathLength : ℝ) / (R : ℝ)) := hbase
    _ ≤ relativeConstant * (1 / (n : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hratio hconstant
    _ = relativeConstant / (n : ℝ) ^ 3 := by ring

/-- The cross-multiplied edge estimate telescopes without dividing by the
reference exit mass.  Consequently this one-sided source-scale comparison
also covers the zero-mass case. -/
theorem squareGreenExitKernel_path_le_cubicScale_of_scaledEdgeGradient
    {n r R pathLength : ℕ} {path : ℕ → Site}
    {referenceStart y : Site} {direction : ℕ → Direction}
    {relativeConstant : ℝ}
    (hn : 0 < n) (hR : 0 < R) (hr : pathLength ≤ r)
    (hscale : n ^ 3 * r ≤ R) (hconstant : 0 ≤ relativeConstant)
    (hstart : path 0 = referenceStart)
    (hstep : ∀ k < pathLength,
      path (k + 1) = path k + directionStep (direction k))
    (hinner : ∀ k ≤ pathLength, path k ∈ squareDisk r)
    (hscaled : HasUniformInnerSquareExitKernelScaledEdgeGradient
      r R referenceStart y relativeConstant) :
    squareGreenExitKernel R (path pathLength) y ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) *
        squareGreenExitKernel R referenceStart y := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have href0 : 0 ≤ squareGreenExitKernel R referenceStart y := by
    unfold squareGreenExitKernel
    positivity
  have hedge : ∀ k < pathLength,
      |squareGreenExitKernel R (path (k + 1)) y -
          squareGreenExitKernel R (path k) y| ≤
        (relativeConstant / (R : ℝ)) *
          squareGreenExitKernel R referenceStart y := by
    intro k hk
    have hs := hscaled (path k) (hinner k (Nat.le_of_lt hk))
      (direction k) (by
        rw [← hstep k hk]
        exact hinner (k + 1) (by omega))
    rw [← hstep k hk] at hs
    calc
      |squareGreenExitKernel R (path (k + 1)) y -
          squareGreenExitKernel R (path k) y| ≤
          (relativeConstant *
            squareGreenExitKernel R referenceStart y) / (R : ℝ) := by
        apply (le_div_iff₀ hRreal).2
        simpa [mul_comm] using hs
      _ = (relativeConstant / (R : ℝ)) *
          squareGreenExitKernel R referenceStart y := by ring
  have hdiff :
      |squareGreenExitKernel R (path pathLength) y -
          squareGreenExitKernel R (path 0) y| ≤
        (pathLength : ℝ) *
          ((relativeConstant / (R : ℝ)) *
            squareGreenExitKernel R referenceStart y) :=
    abs_sub_le_pathLength_mul_of_edge
      (f := fun x ↦ squareGreenExitKernel R x y)
      (path := path) (pathLength := pathLength)
      (edgeBound := (relativeConstant / (R : ℝ)) *
        squareGreenExitKernel R referenceStart y) hedge
  rw [hstart] at hdiff
  have hmulNat : pathLength * n ^ 3 ≤ R := by
    calc
      pathLength * n ^ 3 ≤ r * n ^ 3 := Nat.mul_le_mul_right _ hr
      _ = n ^ 3 * r := Nat.mul_comm _ _
      _ ≤ R := hscale
  have hmul : (pathLength : ℝ) * (n : ℝ) ^ 3 ≤ (R : ℝ) := by
    exact_mod_cast hmulNat
  have hratio : (pathLength : ℝ) / (R : ℝ) ≤
      1 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hRreal (pow_pos hnreal 3)]
    simpa [mul_comm] using hmul
  have hcoeff : 0 ≤
      relativeConstant * squareGreenExitKernel R referenceStart y :=
    mul_nonneg hconstant href0
  have herror := mul_le_mul_of_nonneg_left hratio hcoeff
  have herror' :
      (pathLength : ℝ) *
          ((relativeConstant / (R : ℝ)) *
            squareGreenExitKernel R referenceStart y) ≤
        (relativeConstant / (n : ℝ) ^ 3) *
          squareGreenExitKernel R referenceStart y := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm]
      using herror
  have hupper :
      squareGreenExitKernel R (path pathLength) y -
          squareGreenExitKernel R referenceStart y ≤
        (relativeConstant / (n : ℝ) ^ 3) *
          squareGreenExitKernel R referenceStart y := by
    exact (le_abs_self _).trans (hdiff.trans herror')
  nlinarith

/-- An `O(R⁻²)` localized edge gradient divided by an `Omega(R⁻¹)`
reference mass yields the sharp relative `O(pathLength / R)` comparison. -/
theorem squareGreenExitKernel_ratio_path_le
    {R pathLength : ℕ} {path : ℕ → Site} {y : Site}
    {gradientConstant denominatorConstant : ℝ}
    (hR : 0 < R) (_hgradient : 0 ≤ gradientConstant)
    (hdenominator : 0 < denominatorConstant)
    (hlocalized : HasLocalizedSquareExitKernelBounds R path pathLength y
      gradientConstant denominatorConstant) :
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
      (gradientConstant / denominatorConstant) *
        ((pathLength : ℝ) / (R : ℝ)) := by
  rcases hlocalized with ⟨hedge, hden⟩
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hlower : 0 < denominatorConstant / (R : ℝ) :=
    div_pos hdenominator hRreal
  have hdiff :
      |squareGreenExitKernel R (path pathLength) y -
          squareGreenExitKernel R (path 0) y| ≤
        (pathLength : ℝ) * (gradientConstant / (R : ℝ) ^ 2) := by
    exact abs_sub_le_pathLength_mul_of_edge
      (f := fun x ↦ squareGreenExitKernel R x y)
      (path := path) (pathLength := pathLength)
      (edgeBound := gradientConstant / (R : ℝ) ^ 2) hedge
  have hratio := ratio_sub_one_abs_le_of_abs_sub_le hlower hden hdiff
  calc
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
        ((pathLength : ℝ) * (gradientConstant / (R : ℝ) ^ 2)) /
          (denominatorConstant / (R : ℝ)) := hratio
    _ = (gradientConstant / denominatorConstant) *
          ((pathLength : ℝ) / (R : ℝ)) := by
      field_simp

/-- Event-level version of the localized square exit-kernel comparison. -/
theorem firstExitAtWeight_square_ratio_path_le
    {R pathLength : ℕ} {path : ℕ → Site} {y : Site}
    {gradientConstant denominatorConstant : ℝ}
    (hy : y ∉ squareDisk R) (hR : 0 < R)
    (hgradient : 0 ≤ gradientConstant)
    (hdenominator : 0 < denominatorConstant)
    (hlocalized : HasLocalizedSquareExitKernelBounds R path pathLength y
      gradientConstant denominatorConstant) :
    |(firstExitAtWeight (squareDisk R : Set Site) (path pathLength) y).toReal /
          (firstExitAtWeight (squareDisk R : Set Site) (path 0) y).toReal - 1| ≤
      (gradientConstant / denominatorConstant) *
        ((pathLength : ℝ) / (R : ℝ)) := by
  rw [firstExitAtWeight_square_eq_kernel R (path pathLength) y hy,
    firstExitAtWeight_square_eq_kernel R (path 0) y hy,
    squareGreenExitKernelENNReal_toReal,
    squareGreenExitKernelENNReal_toReal]
  exact squareGreenExitKernel_ratio_path_le hR hgradient hdenominator hlocalized

/-- At the Appendix-A scale `R ≥ n³ r`, a path of length at most `r`
has relative exit-kernel error at most `(gradientConstant / denominatorConstant) / n³`.
This is the exact source scale used before multiplying the excursion factors. -/
theorem squareGreenExitKernel_ratio_path_le_cubicScale
    {n r R pathLength : ℕ} {path : ℕ → Site} {y : Site}
    {gradientConstant denominatorConstant : ℝ}
    (hn : 0 < n) (hR : 0 < R)
    (hr : pathLength ≤ r) (hscale : n ^ 3 * r ≤ R)
    (hgradient : 0 ≤ gradientConstant)
    (hdenominator : 0 < denominatorConstant)
    (hlocalized : HasLocalizedSquareExitKernelBounds R path pathLength y
      gradientConstant denominatorConstant) :
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
      (gradientConstant / denominatorConstant) / (n : ℝ) ^ 3 := by
  have hbase := squareGreenExitKernel_ratio_path_le hR hgradient hdenominator hlocalized
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hmulNat : pathLength * n ^ 3 ≤ R := by
    calc
      pathLength * n ^ 3 ≤ r * n ^ 3 := Nat.mul_le_mul_right _ hr
      _ = n ^ 3 * r := Nat.mul_comm _ _
      _ ≤ R := hscale
  have hmul : (pathLength : ℝ) * (n : ℝ) ^ 3 ≤ (R : ℝ) := by
    exact_mod_cast hmulNat
  have hratio : (pathLength : ℝ) / (R : ℝ) ≤
      1 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hRreal (pow_pos hnreal 3)]
    simpa [mul_comm] using hmul
  have hconstant : 0 ≤ gradientConstant / denominatorConstant :=
    div_nonneg hgradient hdenominator.le
  calc
    |squareGreenExitKernel R (path pathLength) y /
          squareGreenExitKernel R (path 0) y - 1| ≤
        (gradientConstant / denominatorConstant) *
          ((pathLength : ℝ) / (R : ℝ)) := hbase
    _ ≤ (gradientConstant / denominatorConstant) *
          (1 / (n : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left hratio hconstant
    _ = (gradientConstant / denominatorConstant) / (n : ℝ) ^ 3 := by
      ring

/-- A relative ratio estimate gives the one-sided comparison used when
multiplying the exact first-exit factors. -/
theorem le_one_add_mul_of_ratio_sub_one_abs_le
    {p q error : ℝ} (hq : 0 < q) (hratio : |p / q - 1| ≤ error) :
    p ≤ (1 + error) * q := by
  have hratioUpper : p / q ≤ 1 + error := by
    have hself : p / q - 1 ≤ |p / q - 1| := le_abs_self _
    linarith
  calc
    p = (p / q) * q := by field_simp
    _ ≤ (1 + error) * q := mul_le_mul_of_nonneg_right hratioUpper hq.le

theorem firstExitAtWeight_square_ratio_path_le_cubicScale_of_relativeGradient
    {n r R pathLength : ℕ} {path : ℕ → Site} {y : Site}
    {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hn : 0 < n) (hR : 0 < R)
    (hr : pathLength ≤ r) (hscale : n ^ 3 * r ≤ R)
    (hconstant : 0 ≤ relativeConstant)
    (hrelative : HasLocalizedSquareExitKernelRelativeGradient
      R path pathLength y relativeConstant) :
    |(firstExitAtWeight (squareDisk R : Set Site) (path pathLength) y).toReal /
          (firstExitAtWeight (squareDisk R : Set Site) (path 0) y).toReal - 1| ≤
      relativeConstant / (n : ℝ) ^ 3 := by
  rw [firstExitAtWeight_square_eq_kernel R (path pathLength) y hy,
    firstExitAtWeight_square_eq_kernel R (path 0) y hy,
    squareGreenExitKernelENNReal_toReal,
    squareGreenExitKernelENNReal_toReal]
  exact squareGreenExitKernel_ratio_path_le_cubicScale_of_relativeGradient
    hn hR hr hscale hconstant hrelative

/-- Corner-robust source word estimate.  It consumes the direct relative
inner-edge gradient and gives precisely the `(1 + C / n³)^m` multiplier. -/
theorem annularExitWordWeight_le_of_relativeGradient_cubicScale
    {m n : ℕ} (r radius pathLength : Fin m → ℕ)
    (path : Fin m → ℕ → Site) (exitSite : Fin m → Site)
    {relativeConstant : ℝ}
    (hn : 0 < n) (hexit : ∀ i, exitSite i ∉ squareDisk (radius i))
    (hR : ∀ i, 0 < radius i)
    (hpathLength : ∀ i, pathLength i ≤ r i)
    (hscale : ∀ i, n ^ 3 * r i ≤ radius i)
    (hconstant : 0 ≤ relativeConstant)
    (hrelative : ∀ i, HasLocalizedSquareExitKernelRelativeGradient
      (radius i) (path i) (pathLength i) (exitSite i) relativeConstant) :
    annularExitWordWeight radius (fun i ↦ path i (pathLength i)) exitSite ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        annularExitWordWeight radius (fun i ↦ path i 0) exitSite := by
  unfold annularExitWordWeight
  calc
    (∏ i : Fin m,
        (firstExitAtWeight (squareDisk (radius i) : Set Site)
          (path i (pathLength i)) (exitSite i)).toReal) ≤
        ∏ i : Fin m,
          ((1 + relativeConstant / (n : ℝ) ^ 3) *
            (firstExitAtWeight (squareDisk (radius i) : Set Site)
              (path i 0) (exitSite i)).toReal) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact ENNReal.toReal_nonneg
      · intro i hi
        apply le_one_add_mul_of_ratio_sub_one_abs_le
        · rw [firstExitAtWeight_square_eq_kernel
              (radius i) (path i 0) (exitSite i) (hexit i),
            squareGreenExitKernelENNReal_toReal]
          exact (hrelative i).1
        · exact firstExitAtWeight_square_ratio_path_le_cubicScale_of_relativeGradient
            (hexit i) hn (hR i) (hpathLength i) (hscale i) hconstant
            (hrelative i)
    _ = (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        ∏ i : Fin m,
          (firstExitAtWeight (squareDisk (radius i) : Set Site)
            (path i 0) (exitSite i)).toReal := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Corner-robust relative-gradient comparison after summing the exact exit
words and nonnegative continuation weights from the source expansion. -/
theorem annularProfileWordKernelMass_le_of_relativeGradient_cubicScale
    {β : Type*} {N m n : ℕ} {delta : ℝ} (hnProfile : 2 ≤ n)
    (Q : Finset (NatPath N)) (words : Finset β)
    (r radius pathLength : β → Fin m → ℕ)
    (path : β → Fin m → ℕ → Site)
    (exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ)
    {relativeConstant : ℝ}
    (hn : 0 < n)
    (hcontinuation : ∀ b ∈ words, ∀ q ∈ Q, 0 ≤ continuation b q)
    (hexit : ∀ b ∈ words, ∀ i,
      exitSite b i ∉ squareDisk (radius b i))
    (hR : ∀ b ∈ words, ∀ i, 0 < radius b i)
    (hpathLength : ∀ b ∈ words, ∀ i, pathLength b i ≤ r b i)
    (hscale : ∀ b ∈ words, ∀ i, n ^ 3 * r b i ≤ radius b i)
    (hconstant : 0 ≤ relativeConstant)
    (hrelative : ∀ b ∈ words, ∀ i,
      HasLocalizedSquareExitKernelRelativeGradient
        (radius b i) (path b i) (pathLength b i) (exitSite b i)
          relativeConstant) :
    annularProfileWordKernelMass n delta Q words radius
        (fun b i ↦ path b i (pathLength b i)) exitSite continuation ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        annularProfileWordKernelMass n delta Q words radius
          (fun b i ↦ path b i 0) exitSite continuation := by
  unfold annularProfileWordKernelMass
  calc
    (∑ b ∈ words,
        annularExitWordWeight (radius b)
            (fun i ↦ path b i (pathLength b i)) (exitSite b) *
          ∑ q ∈ Q, successfulProfileWeight n delta q * continuation b q) ≤
      ∑ b ∈ words,
        ((1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
          annularExitWordWeight (radius b) (fun i ↦ path b i 0) (exitSite b)) *
            ∑ q ∈ Q,
              successfulProfileWeight n delta q * continuation b q := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right
      · exact annularExitWordWeight_le_of_relativeGradient_cubicScale
          (r b) (radius b) (pathLength b) (path b) (exitSite b) hn
          (hexit b hb) (hR b hb) (hpathLength b hb) (hscale b hb)
          hconstant (hrelative b hb)
      · apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (successfulProfileWeight_nonneg delta hnProfile q)
          (hcontinuation b hb q hq)
    _ = (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        ∑ b ∈ words,
          annularExitWordWeight (radius b) (fun i ↦ path b i 0) (exitSite b) *
            ∑ q ∈ Q,
              successfulProfileWeight n delta q * continuation b q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- Event-level zero-safe comparison obtained from the cross-multiplied
inner-edge estimate. -/
theorem firstExitAtWeight_square_path_le_cubicScale_of_scaledEdgeGradient
    {n r R pathLength : ℕ} {path : ℕ → Site}
    {referenceStart y : Site} {direction : ℕ → Direction}
    {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hn : 0 < n) (hR : 0 < R)
    (hr : pathLength ≤ r) (hscale : n ^ 3 * r ≤ R)
    (hconstant : 0 ≤ relativeConstant)
    (hstart : path 0 = referenceStart)
    (hstep : ∀ k < pathLength,
      path (k + 1) = path k + directionStep (direction k))
    (hinner : ∀ k ≤ pathLength, path k ∈ squareDisk r)
    (hscaled : HasUniformInnerSquareExitKernelScaledEdgeGradient
      r R referenceStart y relativeConstant) :
    (firstExitAtWeight (squareDisk R : Set Site) (path pathLength) y).toReal ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) *
        (firstExitAtWeight (squareDisk R : Set Site) referenceStart y).toReal := by
  rw [firstExitAtWeight_square_eq_kernel R (path pathLength) y hy,
    firstExitAtWeight_square_eq_kernel R referenceStart y hy,
    squareGreenExitKernelENNReal_toReal,
    squareGreenExitKernelENNReal_toReal]
  exact squareGreenExitKernel_path_le_cubicScale_of_scaledEdgeGradient
    hn hR hr hscale hconstant hstart hstep hinner hscaled

/-- Multiplicative exit-word comparison from zero-safe edge estimates. -/
theorem annularExitWordWeight_le_of_scaledEdgeGradient_cubicScale
    {m n : ℕ} (r radius pathLength : Fin m → ℕ)
    (path : Fin m → ℕ → Site)
    (direction : Fin m → ℕ → Direction)
    (referenceStart exitSite : Fin m → Site)
    {relativeConstant : ℝ}
    (hn : 0 < n) (hexit : ∀ i, exitSite i ∉ squareDisk (radius i))
    (hR : ∀ i, 0 < radius i)
    (hpathLength : ∀ i, pathLength i ≤ r i)
    (hscale : ∀ i, n ^ 3 * r i ≤ radius i)
    (hconstant : 0 ≤ relativeConstant)
    (hstart : ∀ i, path i 0 = referenceStart i)
    (hstep : ∀ i, ∀ k < pathLength i,
      path i (k + 1) = path i k + directionStep (direction i k))
    (hinner : ∀ i, ∀ k ≤ pathLength i, path i k ∈ squareDisk (r i))
    (hscaled : ∀ i, HasUniformInnerSquareExitKernelScaledEdgeGradient
      (r i) (radius i) (referenceStart i) (exitSite i) relativeConstant) :
    annularExitWordWeight radius (fun i ↦ path i (pathLength i)) exitSite ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        annularExitWordWeight radius referenceStart exitSite := by
  unfold annularExitWordWeight
  calc
    (∏ i : Fin m,
        (firstExitAtWeight (squareDisk (radius i) : Set Site)
          (path i (pathLength i)) (exitSite i)).toReal) ≤
        ∏ i : Fin m,
          ((1 + relativeConstant / (n : ℝ) ^ 3) *
            (firstExitAtWeight (squareDisk (radius i) : Set Site)
              (referenceStart i) (exitSite i)).toReal) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact ENNReal.toReal_nonneg
      · intro i hi
        exact firstExitAtWeight_square_path_le_cubicScale_of_scaledEdgeGradient
          (hexit i) hn (hR i) (hpathLength i) (hscale i) hconstant
          (hstart i) (hstep i) (hinner i) (hscaled i)
    _ = (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        ∏ i : Fin m,
          (firstExitAtWeight (squareDisk (radius i) : Set Site)
            (referenceStart i) (exitSite i)).toReal := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Summed exit-word comparison from zero-safe edge estimates.  No separate
positivity hypothesis on the reference exit kernels is needed. -/
theorem annularProfileWordKernelMass_le_of_scaledEdgeGradient_cubicScale
    {β : Type*} {N m n : ℕ} {delta : ℝ} (hnProfile : 2 ≤ n)
    (Q : Finset (NatPath N)) (words : Finset β)
    (r radius pathLength : β → Fin m → ℕ)
    (path : β → Fin m → ℕ → Site)
    (direction : β → Fin m → ℕ → Direction)
    (referenceStart exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ)
    {relativeConstant : ℝ}
    (hn : 0 < n)
    (hcontinuation : ∀ b ∈ words, ∀ q ∈ Q, 0 ≤ continuation b q)
    (hexit : ∀ b ∈ words, ∀ i,
      exitSite b i ∉ squareDisk (radius b i))
    (hR : ∀ b ∈ words, ∀ i, 0 < radius b i)
    (hpathLength : ∀ b ∈ words, ∀ i, pathLength b i ≤ r b i)
    (hscale : ∀ b ∈ words, ∀ i, n ^ 3 * r b i ≤ radius b i)
    (hconstant : 0 ≤ relativeConstant)
    (hstart : ∀ b ∈ words, ∀ i, path b i 0 = referenceStart b i)
    (hstep : ∀ b ∈ words, ∀ i, ∀ k < pathLength b i,
      path b i (k + 1) = path b i k + directionStep (direction b i k))
    (hinner : ∀ b ∈ words, ∀ i, ∀ k ≤ pathLength b i,
      path b i k ∈ squareDisk (r b i))
    (hscaled : ∀ b ∈ words, ∀ i,
      HasUniformInnerSquareExitKernelScaledEdgeGradient
        (r b i) (radius b i) (referenceStart b i) (exitSite b i)
          relativeConstant) :
    annularProfileWordKernelMass n delta Q words radius
        (fun b i ↦ path b i (pathLength b i)) exitSite continuation ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        annularProfileWordKernelMass n delta Q words radius
          referenceStart exitSite continuation := by
  unfold annularProfileWordKernelMass
  calc
    (∑ b ∈ words,
        annularExitWordWeight (radius b)
            (fun i ↦ path b i (pathLength b i)) (exitSite b) *
          ∑ q ∈ Q, successfulProfileWeight n delta q * continuation b q) ≤
      ∑ b ∈ words,
        ((1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
          annularExitWordWeight (radius b) (referenceStart b) (exitSite b)) *
            ∑ q ∈ Q,
              successfulProfileWeight n delta q * continuation b q := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right
      · exact annularExitWordWeight_le_of_scaledEdgeGradient_cubicScale
          (r b) (radius b) (pathLength b) (path b) (direction b)
          (referenceStart b) (exitSite b) hn (hexit b hb) (hR b hb)
          (hpathLength b hb) (hscale b hb) hconstant (hstart b hb)
          (hstep b hb) (hinner b hb) (hscaled b hb)
      · apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (successfulProfileWeight_nonneg delta hnProfile q)
          (hcontinuation b hb q hq)
    _ = (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        ∑ b ∈ words,
          annularExitWordWeight (radius b) (referenceStart b) (exitSite b) *
            ∑ q ∈ Q,
              successfulProfileWeight n delta q * continuation b q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- Localized-gradient one-sided comparison for a single exact first-exit
factor.  The explicit `pathError` premise permits nonuniform radii and path
lengths in the later word product. -/
theorem firstExitAtWeight_square_le_of_localized_gradient
    {R pathLength : ℕ} {path : ℕ → Site} {y : Site}
    {gradientConstant denominatorConstant pathError : ℝ}
    (hy : y ∉ squareDisk R) (hR : 0 < R)
    (hgradient : 0 ≤ gradientConstant)
    (hdenominator : 0 < denominatorConstant)
    (hlocalized : HasLocalizedSquareExitKernelBounds R path pathLength y
      gradientConstant denominatorConstant)
    (herror : (gradientConstant / denominatorConstant) *
      ((pathLength : ℝ) / (R : ℝ)) ≤ pathError) :
    (firstExitAtWeight (squareDisk R : Set Site) (path pathLength) y).toReal ≤
      (1 + pathError) *
        (firstExitAtWeight (squareDisk R : Set Site) (path 0) y).toReal := by
  have hratio := firstExitAtWeight_square_ratio_path_le
    hy hR hgradient hdenominator hlocalized
  have hratio' :
      |(firstExitAtWeight (squareDisk R : Set Site) (path pathLength) y).toReal /
          (firstExitAtWeight (squareDisk R : Set Site) (path 0) y).toReal - 1| ≤
        pathError := hratio.trans herror
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hlower : 0 < denominatorConstant / (R : ℝ) :=
    div_pos hdenominator hRreal
  have href : 0 <
      (firstExitAtWeight (squareDisk R : Set Site) (path 0) y).toReal := by
    rw [firstExitAtWeight_square_eq_kernel R (path 0) y hy,
      squareGreenExitKernelENNReal_toReal]
    exact hlower.trans_le hlocalized.2
  exact le_one_add_mul_of_ratio_sub_one_abs_le href hratio'

/-- Multiplying localized single-exit comparisons yields the exact word-level
factor required in the Appendix-A strong-Markov expansion.  This theorem
replaces the too-coarse global boundary-potential range by path-local edge
gradients. -/
theorem annularExitWordWeight_le_of_localized_gradient
    {m : ℕ} (radius pathLength : Fin m → ℕ)
    (path : Fin m → ℕ → Site) (exitSite : Fin m → Site)
    {gradientConstant denominatorConstant error : ℝ}
    (hexit : ∀ i, exitSite i ∉ squareDisk (radius i))
    (hR : ∀ i, 0 < radius i)
    (hgradient : 0 ≤ gradientConstant)
    (hdenominator : 0 < denominatorConstant)
    (hlocalized : ∀ i, HasLocalizedSquareExitKernelBounds
      (radius i) (path i) (pathLength i) (exitSite i)
        gradientConstant denominatorConstant)
    (herror : ∀ i, (gradientConstant / denominatorConstant) *
      ((pathLength i : ℝ) / (radius i : ℝ)) ≤ error) :
    annularExitWordWeight radius (fun i ↦ path i (pathLength i)) exitSite ≤
      (1 + error) ^ m *
        annularExitWordWeight radius (fun i ↦ path i 0) exitSite := by
  unfold annularExitWordWeight
  calc
    (∏ i : Fin m,
        (firstExitAtWeight (squareDisk (radius i) : Set Site)
          (path i (pathLength i)) (exitSite i)).toReal) ≤
        ∏ i : Fin m,
          ((1 + error) *
            (firstExitAtWeight (squareDisk (radius i) : Set Site)
              (path i 0) (exitSite i)).toReal) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact ENNReal.toReal_nonneg
      · intro i hi
        exact firstExitAtWeight_square_le_of_localized_gradient
          (hexit i) (hR i) hgradient hdenominator (hlocalized i) (herror i)
    _ = (1 + error) ^ m *
        ∏ i : Fin m,
          (firstExitAtWeight (squareDisk (radius i) : Set Site)
            (path i 0) (exitSite i)).toReal := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Source-scale word comparison.  If every traversed path has length at most
`r i` and every square radius is at least `n³ * r i`, the exact `m`-factor
exit word changes by at most `(1 + (gradientConstant / denominatorConstant) /
n³)^m`. -/
theorem annularExitWordWeight_le_of_localized_gradient_cubicScale
    {m n : ℕ} (r radius pathLength : Fin m → ℕ)
    (path : Fin m → ℕ → Site) (exitSite : Fin m → Site)
    {gradientConstant denominatorConstant : ℝ}
    (hn : 0 < n) (hexit : ∀ i, exitSite i ∉ squareDisk (radius i))
    (hR : ∀ i, 0 < radius i)
    (hpathLength : ∀ i, pathLength i ≤ r i)
    (hscale : ∀ i, n ^ 3 * r i ≤ radius i)
    (hgradient : 0 ≤ gradientConstant)
    (hdenominator : 0 < denominatorConstant)
    (hlocalized : ∀ i, HasLocalizedSquareExitKernelBounds
      (radius i) (path i) (pathLength i) (exitSite i)
        gradientConstant denominatorConstant) :
    annularExitWordWeight radius (fun i ↦ path i (pathLength i)) exitSite ≤
      (1 + (gradientConstant / denominatorConstant) / (n : ℝ) ^ 3) ^ m *
        annularExitWordWeight radius (fun i ↦ path i 0) exitSite := by
  apply annularExitWordWeight_le_of_localized_gradient
    radius pathLength path exitSite hexit hR hgradient hdenominator hlocalized
  intro i
  have hRreal : 0 < (radius i : ℝ) := by exact_mod_cast hR i
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmulNat : pathLength i * n ^ 3 ≤ radius i := by
    calc
      pathLength i * n ^ 3 ≤ r i * n ^ 3 :=
        Nat.mul_le_mul_right _ (hpathLength i)
      _ = n ^ 3 * r i := Nat.mul_comm _ _
      _ ≤ radius i := hscale i
  have hmul : (pathLength i : ℝ) * (n : ℝ) ^ 3 ≤
      (radius i : ℝ) := by
    exact_mod_cast hmulNat
  have hratio : (pathLength i : ℝ) / (radius i : ℝ) ≤
      1 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hRreal (pow_pos hnreal 3)]
    simpa [mul_comm] using hmul
  have hconstant : 0 ≤ gradientConstant / denominatorConstant :=
    div_nonneg hgradient hdenominator.le
  calc
    (gradientConstant / denominatorConstant) *
        ((pathLength i : ℝ) / (radius i : ℝ)) ≤
      (gradientConstant / denominatorConstant) * (1 / (n : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hratio hconstant
    _ = (gradientConstant / denominatorConstant) / (n : ℝ) ^ 3 := by
      ring

/-- The cubic-scale localized-gradient comparison after summing over exact
boundary words and nonnegative profile continuations.  This is the direct
quantitative input consumed by the source strong-Markov expansion. -/
theorem annularProfileWordKernelMass_le_of_localized_gradient_cubicScale
    {β : Type*} {N m n : ℕ} {delta : ℝ} (hnProfile : 2 ≤ n)
    (Q : Finset (NatPath N)) (words : Finset β)
    (r radius pathLength : β → Fin m → ℕ)
    (path : β → Fin m → ℕ → Site)
    (exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ)
    {gradientConstant denominatorConstant : ℝ}
    (hn : 0 < n)
    (hcontinuation : ∀ b ∈ words, ∀ q ∈ Q, 0 ≤ continuation b q)
    (hexit : ∀ b ∈ words, ∀ i,
      exitSite b i ∉ squareDisk (radius b i))
    (hR : ∀ b ∈ words, ∀ i, 0 < radius b i)
    (hpathLength : ∀ b ∈ words, ∀ i, pathLength b i ≤ r b i)
    (hscale : ∀ b ∈ words, ∀ i, n ^ 3 * r b i ≤ radius b i)
    (hgradient : 0 ≤ gradientConstant)
    (hdenominator : 0 < denominatorConstant)
    (hlocalized : ∀ b ∈ words, ∀ i,
      HasLocalizedSquareExitKernelBounds
        (radius b i) (path b i) (pathLength b i) (exitSite b i)
          gradientConstant denominatorConstant) :
    annularProfileWordKernelMass n delta Q words radius
        (fun b i ↦ path b i (pathLength b i)) exitSite continuation ≤
      (1 + (gradientConstant / denominatorConstant) / (n : ℝ) ^ 3) ^ m *
        annularProfileWordKernelMass n delta Q words radius
          (fun b i ↦ path b i 0) exitSite continuation := by
  unfold annularProfileWordKernelMass
  calc
    (∑ b ∈ words,
        annularExitWordWeight (radius b)
            (fun i ↦ path b i (pathLength b i)) (exitSite b) *
          ∑ q ∈ Q, successfulProfileWeight n delta q * continuation b q) ≤
      ∑ b ∈ words,
        ((1 + (gradientConstant / denominatorConstant) / (n : ℝ) ^ 3) ^ m *
          annularExitWordWeight (radius b) (fun i ↦ path b i 0) (exitSite b)) *
            ∑ q ∈ Q,
              successfulProfileWeight n delta q * continuation b q := by
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right
      · exact annularExitWordWeight_le_of_localized_gradient_cubicScale
          (r b) (radius b) (pathLength b) (path b) (exitSite b) hn
          (hexit b hb) (hR b hb) (hpathLength b hb) (hscale b hb)
          hgradient hdenominator (hlocalized b hb)
      · apply Finset.sum_nonneg
        intro q hq
        exact mul_nonneg (successfulProfileWeight_nonneg delta hnProfile q)
          (hcontinuation b hb q hq)
    _ = (1 + (gradientConstant / denominatorConstant) / (n : ℝ) ^ 3) ^ m *
        ∑ b ∈ words,
          annularExitWordWeight (radius b) (fun i ↦ path b i 0) (exitSite b) *
            ∑ q ∈ Q,
              successfulProfileWeight n delta q * continuation b q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-! ## Corner-robust signed potential-kernel reduction -/

/-- Signed potential-kernel contribution to one exit-kernel difference. -/
noncomputable def squareExitSignedPotentialDifference
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Direction,
    if y - directionStep d ∈ squareDisk R then
      a (x - (y - directionStep d)) -
        a (x' - (y - directionStep d))
    else 0

/-- Signed harmonic-remainder contribution to one exit-kernel difference. -/
noncomputable def squareExitSignedRemainderDifference
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) : ℝ :=
  (1 / 4 : ℝ) * ∑ d : Direction,
    if y - directionStep d ∈ squareDisk R then
      diskGreenPotentialRemainder R a x (y - directionStep d) -
        diskGreenPotentialRemainder R a x' (y - directionStep d)
    else 0

/-- Exact signed potential-kernel decomposition.  Unlike the earlier
triangle-inequality bound, this retains the cancellation between the
potential term and its harmonic extension that is essential for corner exit
sites. -/
theorem squareGreenExitKernel_sub_eq_signedRemainder_sub_signedPotential
    (R : ℕ) (a : Site → ℝ) (x x' y : Site) :
    squareGreenExitKernel R x y - squareGreenExitKernel R x' y =
      squareExitSignedRemainderDifference R a x x' y -
        squareExitSignedPotentialDifference R a x x' y := by
  unfold squareGreenExitKernel squareExitSignedRemainderDifference
    squareExitSignedPotentialDifference
  calc
    (1 / 4 : ℝ) * (∑ d : Direction,
          if y - directionStep d ∈ squareDisk R then
            (diskGreen R x (y - directionStep d)).toReal else 0) -
        (1 / 4 : ℝ) * (∑ d : Direction,
          if y - directionStep d ∈ squareDisk R then
            (diskGreen R x' (y - directionStep d)).toReal else 0) =
        (1 / 4 : ℝ) * ∑ d : Direction,
          ((if y - directionStep d ∈ squareDisk R then
            (diskGreen R x (y - directionStep d)).toReal else 0) -
          (if y - directionStep d ∈ squareDisk R then
            (diskGreen R x' (y - directionStep d)).toReal else 0)) := by
      rw [Finset.sum_sub_distrib]
      ring
    _ = (1 / 4 : ℝ) * ∑ d : Direction,
          ((if y - directionStep d ∈ squareDisk R then
            diskGreenPotentialRemainder R a x (y - directionStep d) -
              diskGreenPotentialRemainder R a x' (y - directionStep d)
            else 0) -
          (if y - directionStep d ∈ squareDisk R then
            a (x - (y - directionStep d)) -
              a (x' - (y - directionStep d)) else 0)) := by
      apply congrArg (fun t : ℝ ↦ (1 / 4 : ℝ) * t)
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hpred : y - directionStep d ∈ squareDisk R
      · simp only [if_pos hpred]
        rw [diskGreen_difference_eq_remainder_sub_potential]
      · simp [hpred]
    _ = (1 / 4 : ℝ) * (∑ d : Direction,
          if y - directionStep d ∈ squareDisk R then
            diskGreenPotentialRemainder R a x (y - directionStep d) -
              diskGreenPotentialRemainder R a x' (y - directionStep d)
          else 0) -
        (1 / 4 : ℝ) * (∑ d : Direction,
          if y - directionStep d ∈ squareDisk R then
            a (x - (y - directionStep d)) -
              a (x' - (y - directionStep d)) else 0) := by
      rw [Finset.sum_sub_distrib]
      ring

/-- Event-level form of the exact signed decomposition.  Thus the signed
defect below is literally the difference of the two first-exit-at-`y`
probabilities, not an auxiliary Green-function surrogate. -/
theorem firstExitAtWeight_square_toReal_sub_eq_signedDefect
    {R : ℕ} {a : Site → ℝ} {x x' y : Site} (hy : y ∉ squareDisk R) :
    (firstExitAtWeight (squareDisk R : Set Site) x y).toReal -
        (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal =
      squareExitSignedRemainderDifference R a x x' y -
        squareExitSignedPotentialDifference R a x x' y := by
  rw [firstExitAtWeight_square_eq_kernel R x y hy,
    firstExitAtWeight_square_eq_kernel R x' y hy,
    squareGreenExitKernelENNReal_toReal,
    squareGreenExitKernelENNReal_toReal]
  exact squareGreenExitKernel_sub_eq_signedRemainder_sub_signedPotential
    R a x x' y

/-- Exact corner-robust reduction of the desired relative edge gradient to
the signed potential/remainder defect. -/
theorem hasUniformInnerSquareExitKernelRelativeGradient_iff_signedDefect
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (a : Site → ℝ) :
    HasUniformInnerSquareExitKernelRelativeGradient
        r R referenceStart y relativeConstant ↔
      0 < squareGreenExitKernel R referenceStart y ∧
        ∀ x ∈ squareDisk r, ∀ d : Direction,
          x + directionStep d ∈ squareDisk r →
            |squareExitSignedRemainderDifference R a
                (x + directionStep d) x y -
              squareExitSignedPotentialDifference R a
                (x + directionStep d) x y| ≤
              (relativeConstant / (R : ℝ)) *
                squareGreenExitKernel R referenceStart y := by
  constructor
  · rintro ⟨href, hedge⟩
    refine ⟨href, ?_⟩
    intro x hx d hxd
    rw [← squareGreenExitKernel_sub_eq_signedRemainder_sub_signedPotential]
    exact hedge x hx d hxd
  · rintro ⟨href, hedge⟩
    refine ⟨href, ?_⟩
    intro x hx d hxd
    rw [squareGreenExitKernel_sub_eq_signedRemainder_sub_signedPotential]
    exact hedge x hx d hxd

/-- Cross-multiplied canonical potential-kernel form of the remaining
Lawler--Rosen estimate.  It never divides by a boundary atom and therefore
continues to state the correct estimate at square corners. -/
def HasUniformInnerCanonicalSignedExitDefect
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  0 < squareGreenExitKernel R referenceStart y ∧
    ∀ x ∈ squareDisk r, ∀ d : Direction,
      x + directionStep d ∈ squareDisk r →
        (R : ℝ) *
            |squareExitSignedRemainderDifference R
                PotentialConvergence.planarPotentialKernel
                (x + directionStep d) x y -
              squareExitSignedPotentialDifference R
                PotentialConvergence.planarPotentialKernel
                (x + directionStep d) x y| ≤
          relativeConstant * squareGreenExitKernel R referenceStart y

/-- The desired corner-robust relative edge gradient is equivalent to one
finite, cross-multiplied signed potential-kernel defect estimate.  This is
the source-faithful quantitative input still required from the
Lawler--Rosen estimate; no uniform `c / R` lower bound is introduced. -/
theorem hasUniformInnerSquareExitKernelRelativeGradient_iff_canonicalSignedDefect
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hR : 0 < R) :
    HasUniformInnerSquareExitKernelRelativeGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerCanonicalSignedExitDefect
        r R referenceStart y relativeConstant := by
  rw [hasUniformInnerSquareExitKernelRelativeGradient_iff_signedDefect
    (a := PotentialConvergence.planarPotentialKernel)]
  unfold HasUniformInnerCanonicalSignedExitDefect
  apply and_congr Iff.rfl
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  constructor
  · intro hedge x hx d hxd
    have h := hedge x hx d hxd
    have h' :
        |squareExitSignedRemainderDifference R
              PotentialConvergence.planarPotentialKernel
              (x + directionStep d) x y -
            squareExitSignedPotentialDifference R
              PotentialConvergence.planarPotentialKernel
              (x + directionStep d) x y| ≤
          (relativeConstant * squareGreenExitKernel R referenceStart y) /
            (R : ℝ) := by
      convert h using 1 <;> ring
    have hm := (le_div_iff₀ hRreal).mp h'
    simpa [mul_comm] using hm
  · intro hedge x hx d hxd
    have h := hedge x hx d hxd
    have hm :
        |squareExitSignedRemainderDifference R
              PotentialConvergence.planarPotentialKernel
              (x + directionStep d) x y -
            squareExitSignedPotentialDifference R
              PotentialConvergence.planarPotentialKernel
              (x + directionStep d) x y| * (R : ℝ) ≤
          relativeConstant * squareGreenExitKernel R referenceStart y := by
      simpa [mul_comm] using h
    have hd := (le_div_iff₀ hRreal).mpr hm
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hd

/-! ## Finite predecessor-column summation -/

/-- Relative edge-gradient bounds for the at most four killed-Green columns
which contribute to exit at `y`.  Zero/non-predecessor columns are omitted.
This is strictly more local than an additive potential-kernel oscillation
bound and retains the cancellation inside each Green column. -/
def HasUniformInnerExitPredecessorGreenGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |(diskGreen R (x + directionStep e)
                (y - directionStep p)).toReal -
              (diskGreen R x (y - directionStep p)).toReal| ≤
          relativeConstant *
            (diskGreen R referenceStart (y - directionStep p)).toReal

/-- Self-adjoint target-variable form of the predecessor-column estimate.
After path reversal, the varying inner start becomes the target variable of
one Green column started at the boundary predecessor.  This is the form to
which the square Dirichlet sine basis applies. -/
def HasUniformInnerExitPredecessorTargetGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |(diskGreen R (y - directionStep p)
                (x + directionStep e)).toReal -
              (diskGreen R (y - directionStep p) x).toReal| ≤
          relativeConstant *
            (diskGreen R (y - directionStep p) referenceStart).toReal

/-- Exact path-reversal conversion to the target-variable gradient. -/
theorem hasUniformInnerExitPredecessorGreenGradient_iff_targetGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ} :
    HasUniformInnerExitPredecessorGreenGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorTargetGradient
        r R referenceStart y relativeConstant := by
  unfold HasUniformInnerExitPredecessorGreenGradient
  unfold HasUniformInnerExitPredecessorTargetGradient
  simp_rw [diskGreen_toReal_comm]

/-- The exact signed double-sine form of the predecessor-column estimate.
Unlike a termwise absolute-value bound, this predicate retains all Fourier
cancellation, including at square corners. -/
def HasUniformInnerExitPredecessorSignedSineGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |(4 / (2 * (R + 1 : ℝ)) ^ 2) *
              ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
                (squareSineMode R k l (y - directionStep p) /
                    squareSineEigenvalue R k l) *
                  (squareSineMode R k l (x + directionStep e) -
                    squareSineMode R k l x)| ≤
          relativeConstant *
            ((4 / (2 * (R + 1 : ℝ)) ^ 2) *
              ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
                (squareSineMode R k l (y - directionStep p) /
                    squareSineEigenvalue R k l) *
                  squareSineMode R k l referenceStart)

/-- Boundary-face form of the signed sine estimate.  The normal boundary
sine and the tangential mode are kept signed inside each complete double
sum; in particular this does not make the invalid termwise absolute-value
estimate at a corner. -/
def HasUniformInnerExitPredecessorBoundarySignedSineGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |(4 / (2 * (R + 1 : ℝ)) ^ 2) *
              ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
                ((squareSinePredecessorFactor R p k l *
                      squareSinePredecessorTangential R p k l
                        (y - directionStep p)) /
                    squareSineEigenvalue R k l) *
                  (squareSineMode R k l (x + directionStep e) -
                    squareSineMode R k l x)| ≤
          relativeConstant *
            ((4 / (2 * (R + 1 : ℝ)) ^ 2) *
              ∑ k : Fin (2 * R + 1), ∑ l : Fin (2 * R + 1),
                ((squareSinePredecessorFactor R p k l *
                      squareSinePredecessorTangential R p k l
                        (y - directionStep p)) /
                    squareSineEigenvalue R k l) *
                  squareSineMode R k l referenceStart)

/-- The same predecessor-column estimate after the normal frequency has
been summed exactly.  Each `exitPredecessorColumnProfile` is one signed
tangential sum, so corner cancellation is still present. -/
def HasUniformInnerExitPredecessorColumnProfileGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |(4 / (2 * (R + 1 : ℝ)) ^ 2) *
              (exitPredecessorColumnProfile R p y
                  (x + directionStep e) -
                exitPredecessorColumnProfile R p y x)| ≤
          relativeConstant *
            ((4 / (2 * (R + 1 : ℝ)) ^ 2) *
              exitPredecessorColumnProfile R p y referenceStart)

/-- Fully resolved one-dimensional version of the predecessor estimate.
The normal frequency has been evaluated by the hyperbolic Green formula and
the common positive spectral normalization has been cancelled.  Thus the
only remaining analytic assertion is an inequality between complete signed
tangential sums; in particular no termwise absolute value or uniform
boundary-atom denominator appears. -/
def HasUniformInnerExitPredecessorResolvedColumnGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |exitPredecessorResolvedColumnProfile R p y
                (x + directionStep e) -
              exitPredecessorResolvedColumnProfile R p y x| ≤
          relativeConstant *
            exitPredecessorResolvedColumnProfile R p y referenceStart

/-- Canonical single-face form of the remaining analytic estimate.  All
four predecessor faces are transported to the right face, and every edge is
the explicit signed sum `rightBoundaryResolvedEdgeProfile`. -/
def HasUniformInnerExitPredecessorCanonicalRightGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |rightBoundaryResolvedEdgeProfile R
              (canonicalRightFaceSite p (y - directionStep p))
              (canonicalRightFaceSite p x)
              (canonicalRightFaceDirection p e)| ≤
          relativeConstant *
            rightBoundaryResolvedColumnProfile R
              (canonicalRightFaceSite p (y - directionStep p))
              (canonicalRightFaceSite p referenceStart)

/-- Corner-normalized form of the canonical right-face estimate.  The
common first tangential sine has been divided out of both sides, so this
predicate no longer degenerates when the exit predecessor approaches a
corner. -/
def HasUniformInnerExitPredecessorCanonicalRightNormalizedGradient
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |rightBoundaryCornerNormalizedEdgeProfile R
              (canonicalRightFaceSite p (y - directionStep p))
              (canonicalRightFaceSite p x)
              (canonicalRightFaceDirection p e)| ≤
          relativeConstant *
            rightBoundaryCornerNormalizedColumnProfile R
              (canonicalRightFaceSite p (y - directionStep p))
              (canonicalRightFaceSite p referenceStart)

/-- The canonical estimate is exactly equivalent to its corner-normalized
version.  Positivity of the cancelled first mode follows just from the fact
that the last-step predecessor lies in the killed square. -/
theorem hasUniformInnerExitPredecessorCanonicalRightGradient_iff_normalized
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ} :
    HasUniformInnerExitPredecessorCanonicalRightGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorCanonicalRightNormalizedGradient
        r R referenceStart y relativeConstant := by
  unfold HasUniformInnerExitPredecessorCanonicalRightGradient
  unfold HasUniformInnerExitPredecessorCanonicalRightNormalizedGradient
  constructor <;> intro h p hp x hx e hxe
  · let z := canonicalRightFaceSite p (y - directionStep p)
    let x' := canonicalRightFaceSite p x
    let x₀ := canonicalRightFaceSite p referenceStart
    let e' := canonicalRightFaceDirection p e
    have hz : z ∈ squareDisk R :=
      (canonicalRightFaceSite_mem_squareDisk_iff R p
        (y - directionStep p)).2 hp
    have hc : 0 < rightBoundaryCornerFactor R z :=
      rightBoundaryCornerFactor_pos R hz
    have hb := h p hp x hx e hxe
    have hscaled :
        rightBoundaryCornerFactor R z *
            ((R : ℝ) * |rightBoundaryCornerNormalizedEdgeProfile R z x' e'|) ≤
          rightBoundaryCornerFactor R z *
            (relativeConstant *
              rightBoundaryCornerNormalizedColumnProfile R z x₀) := by
      calc
        rightBoundaryCornerFactor R z *
              ((R : ℝ) *
                |rightBoundaryCornerNormalizedEdgeProfile R z x' e'|) =
            (R : ℝ) *
              |rightBoundaryResolvedEdgeProfile R z x' e'| := by
                rw [← rightBoundaryCornerFactor_mul_normalizedEdge R e' hz,
                  abs_mul, abs_of_pos hc]
                ring
        _ ≤ relativeConstant *
              rightBoundaryResolvedColumnProfile R z x₀ := by
                simpa only [z, x', x₀, e'] using hb
        _ = rightBoundaryCornerFactor R z *
              (relativeConstant *
                rightBoundaryCornerNormalizedColumnProfile R z x₀) := by
                rw [← rightBoundaryCornerFactor_mul_normalizedColumn R hz]
                ring
    exact (mul_le_mul_iff_of_pos_left hc).mp hscaled
  · let z := canonicalRightFaceSite p (y - directionStep p)
    let x' := canonicalRightFaceSite p x
    let x₀ := canonicalRightFaceSite p referenceStart
    let e' := canonicalRightFaceDirection p e
    have hz : z ∈ squareDisk R :=
      (canonicalRightFaceSite_mem_squareDisk_iff R p
        (y - directionStep p)).2 hp
    have hc : 0 < rightBoundaryCornerFactor R z :=
      rightBoundaryCornerFactor_pos R hz
    have hb := h p hp x hx e hxe
    calc
      (R : ℝ) * |rightBoundaryResolvedEdgeProfile R z x' e'| =
          rightBoundaryCornerFactor R z *
            ((R : ℝ) *
              |rightBoundaryCornerNormalizedEdgeProfile R z x' e'|) := by
            rw [← rightBoundaryCornerFactor_mul_normalizedEdge R e' hz,
              abs_mul, abs_of_pos hc]
            ring
      _ ≤ rightBoundaryCornerFactor R z *
            (relativeConstant *
              rightBoundaryCornerNormalizedColumnProfile R z x₀) :=
          (mul_le_mul_iff_of_pos_left hc).2
            (by simpa only [z, x', x₀, e'] using hb)
      _ = relativeConstant *
            rightBoundaryResolvedColumnProfile R z x₀ := by
          rw [← rightBoundaryCornerFactor_mul_normalizedColumn R hz]
          ring

/-- Reciprocal lower bound for the single signed column remaining after
corner normalization.  The already-proved mode estimate controls every
edge numerator, so this is the sole quantitative spectral input needed for
the canonical right-face gradient. -/
def HasUniformInnerExitPredecessorCanonicalRightNormalizedColumnLower
    (R : ℕ) (referenceStart y : Site) (lowerConstant : ℝ) : Prop :=
  0 ≤ lowerConstant ∧
    ∀ p : Direction, y - directionStep p ∈ squareDisk R →
      (R : ℝ) ≤ lowerConstant *
        rightBoundaryCornerNormalizedColumnProfile R
          (canonicalRightFaceSite p (y - directionStep p))
          (canonicalRightFaceSite p referenceStart)

/-- The positive lazy-kernel window supplies the canonical normalized column
lower bound with a completely explicit universal constant. -/
theorem hasUniformInnerExitPredecessorCanonicalRightNormalizedColumnLower_of_lazyKernel
    {r R : ℕ} {referenceStart y : Site}
    (hy : y ∉ squareDisk R)
    (href : referenceStart ∈ squareDisk r)
    (hrR : 2 * r ≤ R) (hR : 19 ≤ R) :
    HasUniformInnerExitPredecessorCanonicalRightNormalizedColumnLower
      R referenceStart y (16 * Real.exp 10209) := by
  constructor
  · positivity
  intro p hp
  let z := canonicalRightFaceSite p (y - directionStep p)
  let x₀ := canonicalRightFaceSite p referenceStart
  have hz : z ∈ squareDisk R :=
    (canonicalRightFaceSite_mem_squareDisk_iff R p
      (y - directionStep p)).2 hp
  have hz1 : z.1 = (R : ℤ) := by
    exact canonicalRightFaceSite_exit_predecessor_first p hy hp
  have hx₀ : x₀ ∈ squareDisk r :=
    (canonicalRightFaceSite_mem_squareDisk_iff r p referenceStart).2 href
  simpa only [z, x₀] using
    radius_le_exp_constant_mul_normalizedColumn hz hz1 hx₀ hrR hR

/-- The uniform normalized edge gradient follows from the single signed
column lower bound.  The constant `6400` is the explicit sum of the four
direction-independent mode envelopes. -/
theorem hasUniformInnerExitPredecessorCanonicalRightNormalizedGradient_of_columnLower
    {r R : ℕ} {referenceStart y : Site} {lowerConstant : ℝ}
    (hrR : 2 * r ≤ R)
    (hlower :
      HasUniformInnerExitPredecessorCanonicalRightNormalizedColumnLower
        R referenceStart y lowerConstant) :
    HasUniformInnerExitPredecessorCanonicalRightNormalizedGradient
      r R referenceStart y (6400 * lowerConstant) := by
  rcases hlower with ⟨hlower0, hlower⟩
  intro p hp x hx e hxe
  let z := canonicalRightFaceSite p (y - directionStep p)
  let x' := canonicalRightFaceSite p x
  let x₀ := canonicalRightFaceSite p referenceStart
  let e' := canonicalRightFaceDirection p e
  have hz : z ∈ squareDisk R :=
    (canonicalRightFaceSite_mem_squareDisk_iff R p
      (y - directionStep p)).2 hp
  have hx' : x' ∈ squareDisk r :=
    (canonicalRightFaceSite_mem_squareDisk_iff r p x).2 hx
  have hxe' : x' + directionStep e' ∈ squareDisk r := by
    rw [← canonicalRightFaceSite_add_directionStep]
    exact (canonicalRightFaceSite_mem_squareDisk_iff r p
      (x + directionStep e)).2 hxe
  have hedge := abs_rightBoundaryCornerNormalizedEdgeProfile_le
    r R hz hx' e' hxe' hrR
  have hcol : (R : ℝ) ≤ lowerConstant *
      rightBoundaryCornerNormalizedColumnProfile R z x₀ := by
    simpa only [z, x₀] using hlower p hp
  have hR0 : 0 ≤ (R : ℝ) := by positivity
  calc
    (R : ℝ) *
          |rightBoundaryCornerNormalizedEdgeProfile R z x' e'| ≤
        (R : ℝ) * 6400 :=
      mul_le_mul_of_nonneg_left hedge hR0
    _ = 6400 * (R : ℝ) := by ring
    _ ≤ 6400 * (lowerConstant *
          rightBoundaryCornerNormalizedColumnProfile R z x₀) :=
      mul_le_mul_of_nonneg_left hcol (by norm_num)
    _ = (6400 * lowerConstant) *
          rightBoundaryCornerNormalizedColumnProfile R z x₀ := by ring

/-- Fully discharged corner-robust canonical right-face gradient estimate. -/
theorem hasUniformInnerExitPredecessorCanonicalRightGradient_of_lazyKernel
    {r R : ℕ} {referenceStart y : Site}
    (hy : y ∉ squareDisk R)
    (href : referenceStart ∈ squareDisk r)
    (hrR : 2 * r ≤ R) (hR : 19 ≤ R) :
    HasUniformInnerExitPredecessorCanonicalRightGradient
      r R referenceStart y (102400 * Real.exp 10209) := by
  apply hasUniformInnerExitPredecessorCanonicalRightGradient_iff_normalized.mpr
  have hlower :=
    hasUniformInnerExitPredecessorCanonicalRightNormalizedColumnLower_of_lazyKernel
      hy href hrR hR
  have hgrad :=
    hasUniformInnerExitPredecessorCanonicalRightNormalizedGradient_of_columnLower
      hrR hlower
  simpa only [show (6400 : ℝ) * (16 * Real.exp 10209) =
    102400 * Real.exp 10209 by ring] using hgrad

/-- For a genuine exit site, the two signed spectral formulations are
exactly equivalent.  This is the face reduction which retains the normal
reflection signs responsible for corner cancellation. -/
theorem hasUniformInnerExitPredecessorSignedSineGradient_iff_boundary
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) :
    HasUniformInnerExitPredecessorSignedSineGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorBoundarySignedSineGradient
        r R referenceStart y relativeConstant := by
  unfold HasUniformInnerExitPredecessorSignedSineGradient
  unfold HasUniformInnerExitPredecessorBoundarySignedSineGradient
  constructor <;> intro h p hp x hx e hxe
  · simpa only [squareSineMode_exit_predecessor p hy hp] using
      h p hp x hx e hxe
  · simpa only [squareSineMode_exit_predecessor p hy hp] using
      h p hp x hx e hxe

/-- Exact equivalence between the predecessor target-gradient input and its
cancellation-preserving finite sine sum. -/
theorem hasUniformInnerExitPredecessorTargetGradient_iff_signedSineGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hrR : r ≤ R) (href : referenceStart ∈ squareDisk R) :
    HasUniformInnerExitPredecessorTargetGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorSignedSineGradient
        r R referenceStart y relativeConstant := by
  unfold HasUniformInnerExitPredecessorTargetGradient
  unfold HasUniformInnerExitPredecessorSignedSineGradient
  constructor
  · intro h p hp x hx e hxe
    have hxR : x ∈ squareDisk R := squareDisk_mono hrR hx
    have hxeR : x + directionStep e ∈ squareDisk R :=
      squareDisk_mono hrR hxe
    have hb := h p hp x hx e hxe
    rw [diskGreen_toReal_target_edge_sub_eq_signed_sine_sum hp e hxR hxeR,
      diskGreen_toReal_eq_signed_sine_sum hp href] at hb
    exact hb
  · intro h p hp x hx e hxe
    have hxR : x ∈ squareDisk R := squareDisk_mono hrR hx
    have hxeR : x + directionStep e ∈ squareDisk R :=
      squareDisk_mono hrR hxe
    have hb := h p hp x hx e hxe
    rw [← diskGreen_toReal_target_edge_sub_eq_signed_sine_sum hp e hxR hxeR,
      ← diskGreen_toReal_eq_signed_sine_sum hp href] at hb
    exact hb

theorem hasUniformInnerExitPredecessorGreenGradient_iff_signedSineGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hrR : r ≤ R) (href : referenceStart ∈ squareDisk R) :
    HasUniformInnerExitPredecessorGreenGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorSignedSineGradient
        r R referenceStart y relativeConstant := by
  rw [hasUniformInnerExitPredecessorGreenGradient_iff_targetGradient,
    hasUniformInnerExitPredecessorTargetGradient_iff_signedSineGradient hrR href]

/-- Exact corner-robust equivalence between predecessor Green gradients and
the boundary-face signed sine inequality. -/
theorem hasUniformInnerExitPredecessorGreenGradient_iff_boundarySignedSineGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hrR : r ≤ R)
    (href : referenceStart ∈ squareDisk R) :
    HasUniformInnerExitPredecessorGreenGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorBoundarySignedSineGradient
        r R referenceStart y relativeConstant := by
  rw [hasUniformInnerExitPredecessorGreenGradient_iff_signedSineGradient
      hrR href,
    hasUniformInnerExitPredecessorSignedSineGradient_iff_boundary hy]

/-- Exact equivalence between predecessor Green gradients and the
normal-resolvent/single-tangential-sum formulation. -/
theorem hasUniformInnerExitPredecessorGreenGradient_iff_columnProfileGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hrR : r ≤ R)
    (href : referenceStart ∈ squareDisk R) :
    HasUniformInnerExitPredecessorGreenGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorColumnProfileGradient
        r R referenceStart y relativeConstant := by
  rw [hasUniformInnerExitPredecessorGreenGradient_iff_targetGradient]
  unfold HasUniformInnerExitPredecessorTargetGradient
  unfold HasUniformInnerExitPredecessorColumnProfileGradient
  constructor
  · intro h p hp x hx e hxe
    have hxR : x ∈ squareDisk R := squareDisk_mono hrR hx
    have hxeR : x + directionStep e ∈ squareDisk R :=
      squareDisk_mono hrR hxe
    have hb := h p hp x hx e hxe
    rw [diskGreen_toReal_exit_predecessor_target_edge_sub_eq_columnProfile
        p hy hp e hxR hxeR,
      diskGreen_toReal_exit_predecessor_eq_columnProfile p hy hp href] at hb
    exact hb
  · intro h p hp x hx e hxe
    have hxR : x ∈ squareDisk R := squareDisk_mono hrR hx
    have hxeR : x + directionStep e ∈ squareDisk R :=
      squareDisk_mono hrR hxe
    have hb := h p hp x hx e hxe
    rw [← diskGreen_toReal_exit_predecessor_target_edge_sub_eq_columnProfile
        p hy hp e hxR hxeR,
      ← diskGreen_toReal_exit_predecessor_eq_columnProfile p hy hp href] at hb
    exact hb

/-- The column-profile inequality is exactly the fully resolved signed
tangential inequality.  The proof only substitutes the normal resolvent and
cancels its common positive normalization. -/
theorem hasUniformInnerExitPredecessorColumnProfileGradient_iff_resolved
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hrR : r ≤ R) (href : referenceStart ∈ squareDisk R) :
    HasUniformInnerExitPredecessorColumnProfileGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorResolvedColumnGradient
        r R referenceStart y relativeConstant := by
  unfold HasUniformInnerExitPredecessorColumnProfileGradient
  unfold HasUniformInnerExitPredecessorResolvedColumnGradient
  let scale : ℝ := 4 / (2 * (R + 1 : ℝ)) ^ 2
  have hscale : 0 < scale := by
    dsimp [scale]
    positivity
  constructor
  · intro h p hp x hx e hxe
    have hxR : x ∈ squareDisk R := squareDisk_mono hrR hx
    have hxeR : x + directionStep e ∈ squareDisk R :=
      squareDisk_mono hrR hxe
    have hb := h p hp x hx e hxe
    rw [exitPredecessorColumnProfile_eq_resolved p y hxeR,
      exitPredecessorColumnProfile_eq_resolved p y hxR,
      exitPredecessorColumnProfile_eq_resolved p y href] at hb
    change (R : ℝ) *
          |scale *
            (exitPredecessorResolvedColumnProfile R p y
                (x + directionStep e) -
              exitPredecessorResolvedColumnProfile R p y x)| ≤
        relativeConstant *
          (scale *
            exitPredecessorResolvedColumnProfile R p y referenceStart) at hb
    rw [abs_mul, abs_of_pos hscale] at hb
    have hb' : scale *
          ((R : ℝ) *
            |exitPredecessorResolvedColumnProfile R p y
                (x + directionStep e) -
              exitPredecessorResolvedColumnProfile R p y x|) ≤
        scale *
          (relativeConstant *
            exitPredecessorResolvedColumnProfile R p y referenceStart) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hb
    exact le_of_mul_le_mul_left hb' hscale
  · intro h p hp x hx e hxe
    have hxR : x ∈ squareDisk R := squareDisk_mono hrR hx
    have hxeR : x + directionStep e ∈ squareDisk R :=
      squareDisk_mono hrR hxe
    have hb := h p hp x hx e hxe
    rw [exitPredecessorColumnProfile_eq_resolved p y hxeR,
      exitPredecessorColumnProfile_eq_resolved p y hxR,
      exitPredecessorColumnProfile_eq_resolved p y href]
    change (R : ℝ) *
          |scale *
            (exitPredecessorResolvedColumnProfile R p y
                (x + directionStep e) -
              exitPredecessorResolvedColumnProfile R p y x)| ≤
        relativeConstant *
          (scale *
            exitPredecessorResolvedColumnProfile R p y referenceStart)
    rw [abs_mul, abs_of_pos hscale]
    have hb' := mul_le_mul_of_nonneg_left hb hscale.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using hb'

theorem hasUniformInnerExitPredecessorResolvedColumnGradient_iff_canonicalRight
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ} :
    HasUniformInnerExitPredecessorResolvedColumnGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorCanonicalRightGradient
        r R referenceStart y relativeConstant := by
  unfold HasUniformInnerExitPredecessorResolvedColumnGradient
  unfold HasUniformInnerExitPredecessorCanonicalRightGradient
  constructor <;> intro h p hp x hx e hxe
  · have hb := h p hp x hx e hxe
    rw [exitPredecessorResolvedColumnProfile_edge_sub_eq_canonicalRight,
      exitPredecessorResolvedColumnProfile_eq_canonicalRight] at hb
    exact hb
  · rw [exitPredecessorResolvedColumnProfile_edge_sub_eq_canonicalRight,
      exitPredecessorResolvedColumnProfile_eq_canonicalRight]
    exact h p hp x hx e hxe

/-- Exact equivalence from the Green-column estimate to the final explicit
one-dimensional signed-sum inequality. -/
theorem hasUniformInnerExitPredecessorGreenGradient_iff_resolvedColumnGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hrR : r ≤ R)
    (href : referenceStart ∈ squareDisk R) :
    HasUniformInnerExitPredecessorGreenGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorResolvedColumnGradient
        r R referenceStart y relativeConstant := by
  rw [hasUniformInnerExitPredecessorGreenGradient_iff_columnProfileGradient
      hy hrR href,
    hasUniformInnerExitPredecessorColumnProfileGradient_iff_resolved hrR href]

/-- Final exact reduction: predecessor Green gradients are equivalent to one
canonical right-face hyperbolic signed-sum inequality. -/
theorem hasUniformInnerExitPredecessorGreenGradient_iff_canonicalRightGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hrR : r ≤ R)
    (href : referenceStart ∈ squareDisk R) :
    HasUniformInnerExitPredecessorGreenGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorCanonicalRightGradient
        r R referenceStart y relativeConstant := by
  rw [hasUniformInnerExitPredecessorGreenGradient_iff_resolvedColumnGradient
      hy hrR href,
    hasUniformInnerExitPredecessorResolvedColumnGradient_iff_canonicalRight]

/-- Canonical potential-kernel version of the predecessor-column target.
The potential increment and the increment of its harmonic extension stay in
one signed absolute value, so the exact Green cancellation is not lost. -/
def HasUniformInnerExitPredecessorCanonicalSignedDefect
    (r R : ℕ) (referenceStart y : Site) (relativeConstant : ℝ) : Prop :=
  ∀ p : Direction, y - directionStep p ∈ squareDisk R →
    ∀ x ∈ squareDisk r, ∀ e : Direction,
      x + directionStep e ∈ squareDisk r →
        (R : ℝ) *
            |(diskGreenPotentialRemainder R
                PotentialConvergence.planarPotentialKernel
                (x + directionStep e) (y - directionStep p) -
              diskGreenPotentialRemainder R
                PotentialConvergence.planarPotentialKernel
                x (y - directionStep p)) -
              (PotentialConvergence.planarPotentialKernel
                  ((x + directionStep e) - (y - directionStep p)) -
                PotentialConvergence.planarPotentialKernel
                  (x - (y - directionStep p)))| ≤
          relativeConstant *
            (diskGreen R referenceStart (y - directionStep p)).toReal

/-- Exact equivalence between the predecessor Green-column estimate and its
signed canonical potential-kernel form. -/
theorem hasUniformInnerExitPredecessorGreenGradient_iff_canonicalSignedDefect
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ} :
    HasUniformInnerExitPredecessorGreenGradient
        r R referenceStart y relativeConstant ↔
      HasUniformInnerExitPredecessorCanonicalSignedDefect
        r R referenceStart y relativeConstant := by
  constructor
  · intro h p hp x hx e hxe
    rw [← diskGreen_difference_eq_remainder_sub_potential]
    exact h p hp x hx e hxe
  · intro h p hp x hx e hxe
    rw [diskGreen_difference_eq_remainder_sub_potential]
    exact h p hp x hx e hxe

/-- The finite last-step sum preserves the zero-safe, cross-multiplied edge
gradient.  In particular the proof is unchanged at corners, where only one
predecessor may contribute; it never divides by the reference exit mass. -/
theorem hasUniformInnerSquareExitKernelScaledEdgeGradient_of_predecessorGreenGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hcolumns : HasUniformInnerExitPredecessorGreenGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelScaledEdgeGradient
      r R referenceStart y relativeConstant := by
  intro x hx e hxe
  unfold squareGreenExitKernel
  let f : Direction → ℝ := fun p ↦
    if y - directionStep p ∈ squareDisk R then
      (diskGreen R (x + directionStep e)
          (y - directionStep p)).toReal -
        (diskGreen R x (y - directionStep p)).toReal
    else 0
  let g : Direction → ℝ := fun p ↦
    if y - directionStep p ∈ squareDisk R then
      (diskGreen R referenceStart (y - directionStep p)).toReal
    else 0
  have hterm : ∀ p : Direction,
      (R : ℝ) * |f p| ≤ relativeConstant * g p := by
    intro p
    by_cases hp : y - directionStep p ∈ squareDisk R
    · simpa only [f, g, if_pos hp] using hcolumns p hp x hx e hxe
    · simp [f, g, hp]
  have hsum : (R : ℝ) * ∑ p : Direction, |f p| ≤
      relativeConstant * ∑ p : Direction, g p := by
    calc
      (R : ℝ) * ∑ p : Direction, |f p| =
          ∑ p : Direction, (R : ℝ) * |f p| := by
        rw [Finset.mul_sum]
      _ ≤ ∑ p : Direction, relativeConstant * g p :=
        Finset.sum_le_sum fun p hp ↦ hterm p
      _ = relativeConstant * ∑ p : Direction, g p := by
        rw [Finset.mul_sum]
  have habs : |∑ p : Direction, f p| ≤ ∑ p : Direction, |f p| :=
    Finset.abs_sum_le_sum_abs _ _
  have hR0 : (0 : ℝ) ≤ R := by positivity
  have hscaled : (R : ℝ) * |∑ p : Direction, f p| ≤
      relativeConstant * ∑ p : Direction, g p :=
    (mul_le_mul_of_nonneg_left habs hR0).trans hsum
  have hkernelDiff :
      (1 / 4 : ℝ) * (∑ p : Direction,
          if y - directionStep p ∈ squareDisk R then
            (diskGreen R (x + directionStep e)
              (y - directionStep p)).toReal else 0) -
        (1 / 4 : ℝ) * (∑ p : Direction,
          if y - directionStep p ∈ squareDisk R then
            (diskGreen R x (y - directionStep p)).toReal else 0) =
        (1 / 4 : ℝ) * ∑ p : Direction, f p := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    apply congrArg (fun t : ℝ ↦ (1 / 4 : ℝ) * t)
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpred : y - directionStep p ∈ squareDisk R
    · simp [f, hpred]
    · simp [f, hpred]
  have hkernelRef :
      (1 / 4 : ℝ) * (∑ p : Direction,
          if y - directionStep p ∈ squareDisk R then
            (diskGreen R referenceStart (y - directionStep p)).toReal
          else 0) =
        (1 / 4 : ℝ) * ∑ p : Direction, g p := by
    rfl
  rw [hkernelDiff, hkernelRef]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  nlinarith

/-- Positive-mass packaging of the preceding zero-safe edge estimate into
the legacy signed-defect interface. -/
theorem hasUniformInnerCanonicalSignedExitDefect_of_predecessorGreenGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (href : 0 < squareGreenExitKernel R referenceStart y)
    (hcolumns : HasUniformInnerExitPredecessorGreenGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerCanonicalSignedExitDefect
      r R referenceStart y relativeConstant := by
  refine ⟨href, ?_⟩
  intro x hx e hxe
  rw [← squareGreenExitKernel_sub_eq_signedRemainder_sub_signedPotential
    (a := PotentialConvergence.planarPotentialKernel)]
  exact
    hasUniformInnerSquareExitKernelScaledEdgeGradient_of_predecessorGreenGradient
      hcolumns x hx e hxe

/-- Direct source-facing consequence: predecessor-column Green gradients
imply the corner-robust exit-kernel gradient. -/
theorem hasUniformInnerSquareExitKernelRelativeGradient_of_predecessorGreenGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hR : 0 < R)
    (href : 0 < squareGreenExitKernel R referenceStart y)
    (hcolumns : HasUniformInnerExitPredecessorGreenGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelRelativeGradient
      r R referenceStart y relativeConstant :=
  (hasUniformInnerSquareExitKernelRelativeGradient_iff_canonicalSignedDefect hR).2
    (hasUniformInnerCanonicalSignedExitDefect_of_predecessorGreenGradient
      href hcolumns)

/-- Source-facing composition of the boundary sine estimate through the
predecessor columns to the relative square exit-kernel gradient. -/
theorem hasUniformInnerSquareExitKernelRelativeGradient_of_boundarySignedSineGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hR : 0 < R) (hrR : r ≤ R)
    (hrefMem : referenceStart ∈ squareDisk R)
    (href : 0 < squareGreenExitKernel R referenceStart y)
    (hboundary : HasUniformInnerExitPredecessorBoundarySignedSineGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelRelativeGradient
      r R referenceStart y relativeConstant :=
  hasUniformInnerSquareExitKernelRelativeGradient_of_predecessorGreenGradient
    hR href
      ((hasUniformInnerExitPredecessorGreenGradient_iff_boundarySignedSineGradient
        hy hrR hrefMem).2 hboundary)

/-- Direct source-facing bridge from the single tangential column profiles
to the corner-robust relative square exit-kernel gradient. -/
theorem hasUniformInnerSquareExitKernelRelativeGradient_of_columnProfileGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hR : 0 < R) (hrR : r ≤ R)
    (hrefMem : referenceStart ∈ squareDisk R)
    (href : 0 < squareGreenExitKernel R referenceStart y)
    (hprofile : HasUniformInnerExitPredecessorColumnProfileGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelRelativeGradient
      r R referenceStart y relativeConstant :=
  hasUniformInnerSquareExitKernelRelativeGradient_of_predecessorGreenGradient
    hR href
      ((hasUniformInnerExitPredecessorGreenGradient_iff_columnProfileGradient
        hy hrR hrefMem).2 hprofile)

/-- Direct source-facing bridge from the explicit hyperbolic
single-tangential-sum inequality to the corner-robust relative exit-kernel
gradient. -/
theorem hasUniformInnerSquareExitKernelRelativeGradient_of_resolvedColumnGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hR : 0 < R) (hrR : r ≤ R)
    (hrefMem : referenceStart ∈ squareDisk R)
    (href : 0 < squareGreenExitKernel R referenceStart y)
    (hresolved : HasUniformInnerExitPredecessorResolvedColumnGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelRelativeGradient
      r R referenceStart y relativeConstant :=
  hasUniformInnerSquareExitKernelRelativeGradient_of_predecessorGreenGradient
    hR href
      ((hasUniformInnerExitPredecessorGreenGradient_iff_resolvedColumnGradient
        hy hrR hrefMem).2 hresolved)

theorem hasUniformInnerSquareExitKernelRelativeGradient_of_canonicalRightGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hR : 0 < R) (hrR : r ≤ R)
    (hrefMem : referenceStart ∈ squareDisk R)
    (href : 0 < squareGreenExitKernel R referenceStart y)
    (hright : HasUniformInnerExitPredecessorCanonicalRightGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelRelativeGradient
      r R referenceStart y relativeConstant :=
  hasUniformInnerSquareExitKernelRelativeGradient_of_predecessorGreenGradient
    hR href
      ((hasUniformInnerExitPredecessorGreenGradient_iff_canonicalRightGradient
        hy hrR hrefMem).2 hright)

/-- Zero-safe bridge from the canonical right-face inequality to the
cross-multiplied square exit-kernel edge estimate. -/
theorem hasUniformInnerSquareExitKernelScaledEdgeGradient_of_canonicalRightGradient
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hy : y ∉ squareDisk R) (hrR : r ≤ R)
    (hrefMem : referenceStart ∈ squareDisk R)
    (hright : HasUniformInnerExitPredecessorCanonicalRightGradient
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelScaledEdgeGradient
      r R referenceStart y relativeConstant :=
  hasUniformInnerSquareExitKernelScaledEdgeGradient_of_predecessorGreenGradient
    ((hasUniformInnerExitPredecessorGreenGradient_iff_canonicalRightGradient
      hy hrR hrefMem).2 hright)

/-- Full exit-word composition of the cancellation-preserving boundary sine
estimate.  All geometric hypotheses are local to the actual inner paths;
the conclusion is the source `(1 + C / n³)^m` multiplier, with no boundary
atom lower bound. -/
theorem annularProfileWordKernelMass_le_of_boundarySignedSineGradient_cubicScale
    {β : Type*} {N m n : ℕ} {delta : ℝ} (hnProfile : 2 ≤ n)
    (Q : Finset (NatPath N)) (words : Finset β)
    (r radius pathLength : β → Fin m → ℕ)
    (path : β → Fin m → ℕ → Site)
    (direction : β → Fin m → ℕ → Direction)
    (referenceStart exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ)
    {relativeConstant : ℝ}
    (hn : 0 < n)
    (hcontinuation : ∀ b ∈ words, ∀ q ∈ Q, 0 ≤ continuation b q)
    (hexit : ∀ b ∈ words, ∀ i,
      exitSite b i ∉ squareDisk (radius b i))
    (hR : ∀ b ∈ words, ∀ i, 0 < radius b i)
    (hrR : ∀ b ∈ words, ∀ i, r b i ≤ radius b i)
    (hpathLength : ∀ b ∈ words, ∀ i, pathLength b i ≤ r b i)
    (hscale : ∀ b ∈ words, ∀ i, n ^ 3 * r b i ≤ radius b i)
    (hconstant : 0 ≤ relativeConstant)
    (hstart : ∀ b i, path b i 0 = referenceStart b i)
    (hstep : ∀ b ∈ words, ∀ i, ∀ k < pathLength b i,
      path b i (k + 1) = path b i k + directionStep (direction b i k))
    (hinner : ∀ b ∈ words, ∀ i, ∀ k ≤ pathLength b i,
      path b i k ∈ squareDisk (r b i))
    (hrefMem : ∀ b ∈ words, ∀ i,
      referenceStart b i ∈ squareDisk (radius b i))
    (hrefPos : ∀ b ∈ words, ∀ i,
      0 < squareGreenExitKernel (radius b i)
        (referenceStart b i) (exitSite b i))
    (hboundary : ∀ b ∈ words, ∀ i,
      HasUniformInnerExitPredecessorBoundarySignedSineGradient
        (r b i) (radius b i) (referenceStart b i) (exitSite b i)
          relativeConstant) :
    annularProfileWordKernelMass n delta Q words radius
        (fun b i ↦ path b i (pathLength b i)) exitSite continuation ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        annularProfileWordKernelMass n delta Q words radius
          referenceStart exitSite continuation := by
  rw [show referenceStart = fun b i ↦ path b i 0 by
    funext b i
    exact (hstart b i).symm]
  apply annularProfileWordKernelMass_le_of_relativeGradient_cubicScale
    hnProfile Q words r radius pathLength path exitSite continuation hn
    hcontinuation hexit hR hpathLength hscale hconstant
  intro b hb i
  apply hasLocalizedSquareExitKernelRelativeGradient_of_uniformInner
    (referenceStart := referenceStart b i)
    (direction := direction b i)
  · exact hstart b i
  · exact hstep b hb i
  · exact hinner b hb i
  · exact hasUniformInnerSquareExitKernelRelativeGradient_of_boundarySignedSineGradient
      (hexit b hb i) (hR b hb i) (hrR b hb i) (hrefMem b hb i)
      (hrefPos b hb i) (hboundary b hb i)

/-- Source exit-word comparison from the one canonical right-face signed
tangential inequality.  This is the denominator-free replacement for the
legacy potential-boundary route. -/
theorem annularProfileWordKernelMass_le_of_canonicalRightGradient_cubicScale
    {β : Type*} {N m n : ℕ} {delta : ℝ} (hnProfile : 2 ≤ n)
    (Q : Finset (NatPath N)) (words : Finset β)
    (r radius pathLength : β → Fin m → ℕ)
    (path : β → Fin m → ℕ → Site)
    (direction : β → Fin m → ℕ → Direction)
    (referenceStart exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ)
    {relativeConstant : ℝ}
    (hn : 0 < n)
    (hcontinuation : ∀ b ∈ words, ∀ q ∈ Q, 0 ≤ continuation b q)
    (hexit : ∀ b ∈ words, ∀ i,
      exitSite b i ∉ squareDisk (radius b i))
    (hR : ∀ b ∈ words, ∀ i, 0 < radius b i)
    (hrR : ∀ b ∈ words, ∀ i, r b i ≤ radius b i)
    (hpathLength : ∀ b ∈ words, ∀ i, pathLength b i ≤ r b i)
    (hscale : ∀ b ∈ words, ∀ i, n ^ 3 * r b i ≤ radius b i)
    (hconstant : 0 ≤ relativeConstant)
    (hstart : ∀ b i, path b i 0 = referenceStart b i)
    (hstep : ∀ b ∈ words, ∀ i, ∀ k < pathLength b i,
      path b i (k + 1) = path b i k + directionStep (direction b i k))
    (hinner : ∀ b ∈ words, ∀ i, ∀ k ≤ pathLength b i,
      path b i k ∈ squareDisk (r b i))
    (hrefMem : ∀ b ∈ words, ∀ i,
      referenceStart b i ∈ squareDisk (radius b i))
    (hright : ∀ b ∈ words, ∀ i,
      HasUniformInnerExitPredecessorCanonicalRightGradient
        (r b i) (radius b i) (referenceStart b i) (exitSite b i)
          relativeConstant) :
    annularProfileWordKernelMass n delta Q words radius
        (fun b i ↦ path b i (pathLength b i)) exitSite continuation ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        annularProfileWordKernelMass n delta Q words radius
          referenceStart exitSite continuation := by
  apply annularProfileWordKernelMass_le_of_scaledEdgeGradient_cubicScale
    hnProfile Q words r radius pathLength path direction referenceStart
      exitSite continuation hn hcontinuation hexit hR hpathLength hscale
      hconstant
  · intro b hb i
    exact hstart b i
  · exact hstep
  · exact hinner
  intro b hb i
  exact hasUniformInnerSquareExitKernelScaledEdgeGradient_of_canonicalRightGradient
    (hexit b hb i) (hrR b hb i) (hrefMem b hb i) (hright b hb i)

/-- Corner-normalized form of the source exit-word comparison.  The
strictly positive first tangential sine factor has already been cancelled,
so this is the sharpest source-facing analytic premise in the spectral
route. -/
theorem annularProfileWordKernelMass_le_of_canonicalRightNormalizedGradient_cubicScale
    {β : Type*} {N m n : ℕ} {delta : ℝ} (hnProfile : 2 ≤ n)
    (Q : Finset (NatPath N)) (words : Finset β)
    (r radius pathLength : β → Fin m → ℕ)
    (path : β → Fin m → ℕ → Site)
    (direction : β → Fin m → ℕ → Direction)
    (referenceStart exitSite : β → Fin m → Site)
    (continuation : β → NatPath N → ℝ)
    {relativeConstant : ℝ}
    (hn : 0 < n)
    (hcontinuation : ∀ b ∈ words, ∀ q ∈ Q, 0 ≤ continuation b q)
    (hexit : ∀ b ∈ words, ∀ i,
      exitSite b i ∉ squareDisk (radius b i))
    (hR : ∀ b ∈ words, ∀ i, 0 < radius b i)
    (hrR : ∀ b ∈ words, ∀ i, r b i ≤ radius b i)
    (hpathLength : ∀ b ∈ words, ∀ i, pathLength b i ≤ r b i)
    (hscale : ∀ b ∈ words, ∀ i, n ^ 3 * r b i ≤ radius b i)
    (hconstant : 0 ≤ relativeConstant)
    (hstart : ∀ b i, path b i 0 = referenceStart b i)
    (hstep : ∀ b ∈ words, ∀ i, ∀ k < pathLength b i,
      path b i (k + 1) = path b i k + directionStep (direction b i k))
    (hinner : ∀ b ∈ words, ∀ i, ∀ k ≤ pathLength b i,
      path b i k ∈ squareDisk (r b i))
    (hrefMem : ∀ b ∈ words, ∀ i,
      referenceStart b i ∈ squareDisk (radius b i))
    (hright : ∀ b ∈ words, ∀ i,
      HasUniformInnerExitPredecessorCanonicalRightNormalizedGradient
        (r b i) (radius b i) (referenceStart b i) (exitSite b i)
          relativeConstant) :
    annularProfileWordKernelMass n delta Q words radius
        (fun b i ↦ path b i (pathLength b i)) exitSite continuation ≤
      (1 + relativeConstant / (n : ℝ) ^ 3) ^ m *
        annularProfileWordKernelMass n delta Q words radius
          referenceStart exitSite continuation := by
  apply annularProfileWordKernelMass_le_of_canonicalRightGradient_cubicScale
    hnProfile Q words r radius pathLength path direction referenceStart
      exitSite continuation hn hcontinuation hexit hR hrR hpathLength hscale
      hconstant hstart hstep hinner hrefMem
  intro b hb i
  exact
    (hasUniformInnerExitPredecessorCanonicalRightGradient_iff_normalized).2
      (hright b hb i)

/-- Source-facing version whose only analytic premise is the signed
potential-kernel defect for each admissible last-step predecessor. -/
theorem hasUniformInnerSquareExitKernelRelativeGradient_of_predecessorCanonicalSignedDefect
    {r R : ℕ} {referenceStart y : Site} {relativeConstant : ℝ}
    (hR : 0 < R)
    (href : 0 < squareGreenExitKernel R referenceStart y)
    (hcolumns : HasUniformInnerExitPredecessorCanonicalSignedDefect
      r R referenceStart y relativeConstant) :
    HasUniformInnerSquareExitKernelRelativeGradient
      r R referenceStart y relativeConstant :=
  hasUniformInnerSquareExitKernelRelativeGradient_of_predecessorGreenGradient
    hR href
      (hasUniformInnerExitPredecessorGreenGradient_iff_canonicalSignedDefect.2
        hcolumns)

end Erdos1166.KilledGreen
