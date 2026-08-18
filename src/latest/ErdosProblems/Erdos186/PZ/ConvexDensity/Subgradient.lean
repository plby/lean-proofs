/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.ConvexApproxND

/-!
# Supporting affine functionals for convex functions on boxes

This file supplies the analytic input left open in `ConvexApproxND`.  The
proof is finite-dimensional but does not use differentiability.  We separate
the point `(v, f v)` from the open strict epigraph of `f`.  The vertical
coefficient of the separating functional is strictly negative, so it can be
normalized to produce a genuine subgradient at `v`.

The final results convert that continuous-linear subgradient into standard
coordinates and prove the local implication used in the Pham--Zakharov bad
cell argument: failure of the supporting affine approximation forces a
positive error, hence a quantitative secant-slope jump, along one coordinate
step through the cell.
-/

open scoped BigOperators
open Set

namespace Erdos186.PZ.ConvexDensity.Subgradient

set_option autoImplicit false

noncomputable section

/-! ## Separation of the open strict epigraph -/

/-- The strict epigraph of a continuous function on an open set is open. -/
private theorem isOpen_strictEpigraph {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f : E → ℝ} (hs : IsOpen s) (hf : ContinuousOn f s) :
    IsOpen {z : E × ℝ | z.1 ∈ s ∧ f z.1 < z.2} := by
  let g : E × ℝ → ℝ := fun z ↦ f z.1 - z.2
  have hfst : ContinuousOn (fun z : E × ℝ ↦ f z.1)
      (s ×ˢ (Set.univ : Set ℝ)) :=
    hf.comp continuous_fst.continuousOn (fun _z hz ↦ hz.1)
  have hg : ContinuousOn g (s ×ˢ (Set.univ : Set ℝ)) :=
    hfst.sub continuous_snd.continuousOn
  have hopen : IsOpen (s ×ˢ (Set.univ : Set ℝ)) := hs.prod isOpen_univ
  have hpre : IsOpen ((s ×ˢ (Set.univ : Set ℝ)) ∩ g ⁻¹' Set.Iio 0) :=
    hg.isOpen_inter_preimage hopen isOpen_Iio
  have heq : {z : E × ℝ | z.1 ∈ s ∧ f z.1 < z.2} =
      (s ×ˢ (Set.univ : Set ℝ)) ∩ g ⁻¹' Set.Iio 0 := by
    ext z
    simp [g]
  rw [heq]
  exact hpre

/-- A convex function on an open finite-dimensional real domain has a
continuous-linear subgradient at every point of the domain.

The conclusion is the global supporting inequality on the given domain;
there is no differentiability assumption. -/
theorem exists_continuousLinear_subgradient {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {f : E → ℝ} (hs : IsOpen s)
    (hf : ConvexOn ℝ s f) {v : E} (hv : v ∈ s) :
    ∃ p : E →L[ℝ] ℝ, ∀ x ∈ s, f v + p (x - v) ≤ f x := by
  let A : Set (E × ℝ) := {z | z.1 ∈ s ∧ f z.1 < z.2}
  have hAconv : Convex ℝ A := hf.convex_strict_epigraph
  have hAopen : IsOpen A := isOpen_strictEpigraph hs (hf.continuousOn hs)
  have hvA : (v, f v) ∉ A := by simp [A, hv]
  obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hAconv hAopen hvA
  let u : E →L[ℝ] ℝ := L.comp (.inl ℝ E ℝ)
  let a : ℝ := L (0, 1)
  have hdecomp (x : E) (t : ℝ) : L (x, t) = u x + a * t := by
    rw [show (x, t) = (x, 0) + (0, t) by ext <;> simp, map_add]
    have hvertical : L (0, t) = t * L (0, 1) := by
      convert L.map_smul t (0, 1) using 1 <;> simp
    rw [hvertical]
    simp [u, a, mul_comm]
  have ha : a < 0 := by
    have hsep := hL (v, f v + 1) (by simp [A, hv])
    rw [hdecomp, hdecomp] at hsep
    linarith
  have hgraph (x : E) (hx : x ∈ s) : L (x, f x) ≤ L (v, f v) := by
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let delta : ℝ := epsilon / (-a)
    have hdelta : 0 < delta := div_pos hepsilon (neg_pos.mpr ha)
    have hsep := hL (x, f x + delta) (by simp [A, hx, hdelta])
    rw [hdecomp, hdecomp] at hsep ⊢
    have hadelta : a * delta = -epsilon := by
      dsimp [delta]
      field_simp [ha.ne]
    rw [mul_add, hadelta] at hsep
    linarith
  let p : E →L[ℝ] ℝ := (-a)⁻¹ • u
  refine ⟨p, fun x hx ↦ ?_⟩
  have hsupport := hgraph x hx
  rw [hdecomp, hdecomp] at hsupport
  have hnegapos : 0 < -a := neg_pos.mpr ha
  have hu : u (x - v) ≤ (-a) * (f x - f v) := by
    rw [map_sub]
    linarith
  have hp : p (x - v) ≤ f x - f v := by
    rw [show p (x - v) = (-a)⁻¹ * u (x - v) by simp [p]]
    rw [inv_mul_le_iff₀ hnegapos]
    simpa [mul_comm] using hu
  linarith

/-- At an interior point of an arbitrary convex set, the supporting
functional extends from the interior to the whole set.  The extension uses
only convexity: apply the interior support and the convexity inequality at
the midpoint of the base point and the target point. -/
theorem exists_continuousLinear_subgradient_of_mem_interior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} {f : E → ℝ} (hf : ConvexOn ℝ s f)
    {v : E} (hv : v ∈ interior s) :
    ∃ p : E →L[ℝ] ℝ, ∀ x ∈ s, f v + p (x - v) ≤ f x := by
  have hfint : ConvexOn ℝ (interior s) f :=
    hf.subset interior_subset hf.1.interior
  obtain ⟨p, hp⟩ :=
    exists_continuousLinear_subgradient isOpen_interior hfint hv
  refine ⟨p, fun x hx ↦ ?_⟩
  let y : E := (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • x
  have hy : y ∈ interior s := by
    exact hf.1.combo_interior_self_mem_interior hv hx
      (by norm_num) (by norm_num) (by norm_num)
  have hsupport := hp y hy
  have hconv := hf.2 (interior_subset hv) hx
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hdiff : y - v = (1 / 2 : ℝ) • (x - v) := by
    dsimp [y]
    module
  rw [hdiff, map_smul] at hsupport
  norm_num only [smul_eq_mul] at hsupport hconv
  linarith

/-! ## Standard-coordinate and box versions -/

/-- Coordinates of a continuous linear functional in the standard basis. -/
def subgradientCoordinates {n : ℕ} (p : (Fin n → ℝ) →L[ℝ] ℝ) :
    Fin n → ℝ :=
  fun i ↦ p (Pi.single i 1)

/-- Evaluation of a functional is the dot product with its standard-basis
coordinates. -/
theorem continuousLinear_eq_sum_subgradientCoordinates {n : ℕ}
    (p : (Fin n → ℝ) →L[ℝ] ℝ) (x : Fin n → ℝ) :
    p x = ∑ i, subgradientCoordinates p i * x i := by
  rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin n ↦ ℝ) p x]
  apply Finset.sum_congr rfl
  intro i _hi
  let q : ℝ →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.single ℝ (fun _ : Fin n ↦ ℝ) i
  simp only [ContinuousLinearMap.comp_apply, subgradientCoordinates]
  change p (q (x i)) = p (Pi.single i 1) * x i
  rw [mul_comm]
  change p (q (x i)) = x i • p (Pi.single i 1)
  rw [← map_smul]
  apply congrArg p
  calc
    q (x i) = q (x i • (1 : ℝ)) := by simp
    _ = x i • q 1 := by rw [map_smul]
    _ = x i • Pi.single i 1 := by rfl

/-- Coordinate form of the subgradient theorem, exactly matching
`ConvexApproxND.tangentAffine`. -/
theorem exists_tangentAffine_support_on_open {n : ℕ}
    {s : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hs : IsOpen s) (hf : ConvexOn ℝ s f) {v : Fin n → ℝ} (hv : v ∈ s) :
    ∃ p : Fin n → ℝ, ∀ x ∈ s,
      ConvexApproxND.tangentAffine f v p x ≤ f x := by
  obtain ⟨l, hl⟩ := exists_continuousLinear_subgradient hs hf hv
  refine ⟨subgradientCoordinates l, fun x hx ↦ ?_⟩
  have h := hl x hx
  rw [continuousLinear_eq_sum_subgradientCoordinates] at h
  simpa [ConvexApproxND.tangentAffine, Pi.sub_apply] using h

/-- Literal closed-box version: convexity on the box and interior membership
of the base point produce an affine support on every point of the box. -/
theorem exists_tangentAffine_support_on_closedBox {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {lower upper : Fin n → ℝ}
    {v : Fin n → ℝ}
    (hf : ConvexOn ℝ (Set.Icc lower upper) f)
    (hv : v ∈ interior (Set.Icc lower upper)) :
    ∃ p : Fin n → ℝ, ∀ x ∈ Set.Icc lower upper,
      ConvexApproxND.tangentAffine f v p x ≤ f x := by
  obtain ⟨l, hl⟩ :=
    exists_continuousLinear_subgradient_of_mem_interior hf hv
  refine ⟨subgradientCoordinates l, fun x hx ↦ ?_⟩
  have h := hl x hx
  rw [continuousLinear_eq_sum_subgradientCoordinates] at h
  simpa [ConvexApproxND.tangentAffine, Pi.sub_apply] using h

/-- Supporting affine functional on a closed inner box, obtained from
convexity on an expanded closed box.  The inclusion hypothesis is the exact
interiority condition: it is normally discharged coordinatewise from strict
inequalities between the inner and outer endpoints. -/
theorem exists_tangentAffine_support_on_innerBox {n : ℕ}
    {f : (Fin n → ℝ) → ℝ}
    {outerLower outerUpper innerLower innerUpper : Fin n → ℝ}
    {v : Fin n → ℝ}
    (hf : ConvexOn ℝ (Set.Icc outerLower outerUpper) f)
    (hinner : Set.Icc innerLower innerUpper ⊆
      interior (Set.Icc outerLower outerUpper))
    (hv : v ∈ Set.Icc innerLower innerUpper) :
    ∃ p : Fin n → ℝ, ∀ x ∈ Set.Icc innerLower innerUpper,
      ConvexApproxND.tangentAffine f v p x ≤ f x := by
  have hopen : IsOpen (interior (Set.Icc outerLower outerUpper)) := isOpen_interior
  have hconv : ConvexOn ℝ (interior (Set.Icc outerLower outerUpper)) f :=
    hf.subset interior_subset hf.1.interior
  obtain ⟨p, hp⟩ := exists_tangentAffine_support_on_open
    hopen hconv (hinner hv)
  exact ⟨p, fun x hx ↦ hp x (hinner hx)⟩

/-! ## The bad-cell coordinate jump -/

/-- Coordinate paths stay in an order interval when both endpoints do. -/
theorem coordinatePath_mem_Icc {n : ℕ} {lower upper v x : Fin n → ℝ}
    (hv : v ∈ Set.Icc lower upper) (hx : x ∈ Set.Icc lower upper)
    (k : ℕ) : ConvexApproxND.coordinatePath v x k ∈ Set.Icc lower upper := by
  constructor <;> intro i <;> simp only [ConvexApproxND.coordinatePath]
  · split_ifs <;> first | exact hx.1 i | exact hv.1 i
  · split_ifs <;> first | exact hx.2 i | exact hv.2 i

/-- The signed coordinate-path residuals telescope to the error of the
supporting affine functional. -/
def coordinateResidual {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (v x p : Fin n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < n then
    (f (ConvexApproxND.coordinatePath v x (k + 1)) -
        f (ConvexApproxND.coordinatePath v x k)) -
      p ⟨k, hk⟩ * (x ⟨k, hk⟩ - v ⟨k, hk⟩)
  else 0

@[simp]
theorem coordinateResidual_of_lt {n k : ℕ} (f : (Fin n → ℝ) → ℝ)
    (v x p : Fin n → ℝ) (hk : k < n) :
    coordinateResidual f v x p k =
      (f (ConvexApproxND.coordinatePath v x (k + 1)) -
          f (ConvexApproxND.coordinatePath v x k)) -
        p ⟨k, hk⟩ * (x ⟨k, hk⟩ - v ⟨k, hk⟩) := by
  simp [coordinateResidual, hk]

theorem sum_coordinate_residuals_eq_tangent_error {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (v x p : Fin n → ℝ) :
    ∑ k ∈ Finset.range n, coordinateResidual f v x p k =
      f x - ConvexApproxND.tangentAffine f v p x := by
  classical
  let g : (Fin n → ℝ) → ℝ := fun y ↦
    f y - ConvexApproxND.tangentAffine f v p y
  calc
    ∑ k ∈ Finset.range n, coordinateResidual f v x p k =
        ∑ k ∈ Finset.range n,
          (g (ConvexApproxND.coordinatePath v x (k + 1)) -
            g (ConvexApproxND.coordinatePath v x k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt := Finset.mem_range.mp hk
      rw [coordinateResidual_of_lt f v x p hklt]
      dsimp [g]
      have hAff :=
        ConvexApproxND.tangentAffine_coordinatePath_succ_sub f v x p hklt
      rw [← hAff]
      ring
    _ = g x - g v := ConvexApproxND.sum_coordinatePath_increments g v x
    _ = f x - ConvexApproxND.tangentAffine f v p x := by
      simp [g]

/-- If a supporting affine model is bad at a point of a cell, one of the
coordinate steps through that cell has a positive residual larger than the
average error.  This is the nonsmooth bad-cell implication needed before
pigeonholing a coordinate. -/
theorem exists_coordinate_residual_gt_of_bad {n : ℕ}
    (hn : 0 < n) (f : (Fin n → ℝ) → ℝ) (v x p : Fin n → ℝ)
    (epsilon : ℝ)
    (hsupport : ConvexApproxND.tangentAffine f v p x ≤ f x)
    (hbad : epsilon <
      |f x - ConvexApproxND.tangentAffine f v p x|) :
    ∃ (k : ℕ) (hk : k < n),
      epsilon / n <
        (f (ConvexApproxND.coordinatePath v x (k + 1)) -
            f (ConvexApproxND.coordinatePath v x k)) -
          p ⟨k, hk⟩ * (x ⟨k, hk⟩ - v ⟨k, hk⟩) := by
  classical
  have herror : epsilon <
      f x - ConvexApproxND.tangentAffine f v p x := by
    rwa [abs_of_nonneg (sub_nonneg.mpr hsupport)] at hbad
  by_contra h
  push Not at h
  have hsum :
      f x - ConvexApproxND.tangentAffine f v p x ≤
        ∑ _k ∈ Finset.range n, epsilon / n := by
    rw [← sum_coordinate_residuals_eq_tangent_error]
    apply Finset.sum_le_sum
    intro k hk
    rw [coordinateResidual_of_lt f v x p (Finset.mem_range.mp hk)]
    exact h k (Finset.mem_range.mp hk)
  have hconst : ∑ _k ∈ Finset.range n, epsilon / n = epsilon := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc
      (n : ℝ) * (epsilon / (n : ℝ)) = epsilon * (n : ℝ) / (n : ℝ) := by
        ring
      _ = epsilon := mul_div_cancel_right₀ epsilon hn0
  rw [hconst] at hsum
  linarith

/-- Quantitative secant-slope version of the bad-cell lemma.  If the selected
coordinate displacement is at most the cell side length `h`, the residual
forces the displayed slope jump above the supporting coordinate. -/
theorem exists_coordinate_secantSlope_jump_of_bad {n : ℕ}
    (hn : 0 < n) (f : (Fin n → ℝ) → ℝ) (v x p : Fin n → ℝ)
    (epsilon h : ℝ) (hepsilon : 0 ≤ epsilon)
    (hcoord : ∀ i, v i ≤ x i ∧ x i - v i ≤ h)
    (hsupport : ConvexApproxND.tangentAffine f v p x ≤ f x)
    (hbad : epsilon <
      |f x - ConvexApproxND.tangentAffine f v p x|) :
    ∃ (k : ℕ) (hk : k < n),
      0 < x ⟨k, hk⟩ - v ⟨k, hk⟩ ∧
      p ⟨k, hk⟩ + epsilon / ((n : ℝ) * h) <
        (f (ConvexApproxND.coordinatePath v x (k + 1)) -
          f (ConvexApproxND.coordinatePath v x k)) /
            (x ⟨k, hk⟩ - v ⟨k, hk⟩) := by
  obtain ⟨k, hk, hjump⟩ :=
    exists_coordinate_residual_gt_of_bad hn f v x p epsilon hsupport hbad
  let i : Fin n := ⟨k, hk⟩
  have hdelta_nonneg : 0 ≤ x i - v i := sub_nonneg.mpr (hcoord i).1
  have hdelta_pos : 0 < x i - v i := by
    by_contra hzero
    have hdelta_zero : x i - v i = 0 := le_antisymm (not_lt.mp hzero) hdelta_nonneg
    have hpath : ConvexApproxND.coordinatePath v x (k + 1) =
        ConvexApproxND.coordinatePath v x k := by
      funext j
      rw [ConvexApproxND.coordinatePath_succ_apply v x hk]
      split_ifs with hji
      · subst j
        simp [ConvexApproxND.coordinatePath, i,
          sub_eq_zero.mp hdelta_zero]
      · rfl
    simp [i, hdelta_zero, hpath] at hjump
    have : 0 ≤ epsilon / (n : ℝ) := div_nonneg hepsilon (Nat.cast_nonneg n)
    linarith
  have hhpos : 0 < h := lt_of_lt_of_le hdelta_pos (hcoord i).2
  have hscaled : epsilon / ((n : ℝ) * h) * (x i - v i) ≤
      epsilon / (n : ℝ) := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      epsilon / ((n : ℝ) * h) * (x i - v i) ≤
          epsilon / ((n : ℝ) * h) * h := by
        exact mul_le_mul_of_nonneg_left (hcoord i).2
          (div_nonneg hepsilon (mul_nonneg hnreal.le hhpos.le))
      _ = epsilon / (n : ℝ) := by field_simp [hnreal.ne', hhpos.ne']
  refine ⟨k, hk, hdelta_pos, ?_⟩
  rw [lt_div_iff₀ hdelta_pos]
  dsimp [i] at hscaled ⊢
  nlinarith

/-! ## Radial bad-cell jumps on a fixed coordinate fibre

The coordinate-path lemma above is useful for local estimates, but the
Pham--Zakharov counting argument needs all jumps assigned to a coordinate to
live on the same coordinate fibre.  The following radial decomposition is
the key observation.  A point `y` in the positive box of side `h` based at
`b` is a convex combination of `b` and the `n` axial points

`b + ((n+1)h) e_i`.

Thus a large error above a supporting affine functional at `b` already
occurs at one of those axial points.  Comparing supporting functionals at
the two endpoints turns this into a genuine subgradient-coordinate jump.
-/

/-- Error above the affine functional determined by a continuous-linear
subgradient at `b`. -/
def supportError {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (b : Fin n → ℝ) (p : (Fin n → ℝ) →L[ℝ] ℝ)
    (x : Fin n → ℝ) : ℝ :=
  f x - (f b + p (x - b))

@[simp]
theorem supportError_apply_base {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (b : Fin n → ℝ) (p : (Fin n → ℝ) →L[ℝ] ℝ) :
    supportError f b p b = 0 := by
  simp [supportError]

/-- Jensen's inequality remains true after subtracting a supporting affine
functional.  This elementary formulation avoids packaging the affine
functional as a separate `AffineMap`. -/
theorem supportError_map_sum_le {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {s : Set (Fin n → ℝ)} (hf : ConvexOn ℝ s f)
    (b : Fin n → ℝ) (p : (Fin n → ℝ) →L[ℝ] ℝ)
    {I : Type*} [Fintype I] (w : I → ℝ) (z : I → Fin n → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hz : ∀ i, z i ∈ s) :
    supportError f b p (∑ i, w i • z i) ≤
      ∑ i, w i * supportError f b p (z i) := by
  classical
  have hJ : f (∑ i, w i • z i) ≤ ∑ i, w i * f (z i) := by
    simpa [smul_eq_mul] using hf.map_sum_le
      (t := (Finset.univ : Finset I))
      (fun i _hi ↦ hw0 i) (by simpa using hw1) (fun i _hi ↦ hz i)
  have hpSum :
      p ((∑ i, w i • z i) - b) = ∑ i, w i * p (z i - b) := by
    calc
      p ((∑ i, w i • z i) - b) =
          p (∑ i, w i • (z i - b)) := by
            congr 1
            funext j
            simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            symm
            calc
              ∑ i, w i * (z i j - b j) =
                  ∑ i, (w i * z i j - w i * b j) := by
                    apply Finset.sum_congr rfl
                    intro i _hi
                    ring
              _ = (∑ i, w i * z i j) - ∑ i, w i * b j :=
                by rw [Finset.sum_sub_distrib]
              _ = (∑ i, w i * z i j) - b j := by
                rw [← Finset.sum_mul, hw1, one_mul]
      _ = ∑ i, p (w i • (z i - b)) := by rw [map_sum]
      _ = ∑ i, w i * p (z i - b) := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp
  rw [supportError, hpSum]
  simp only [supportError, mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  have hconst : ∑ _i : I, w _i * f b = f b := by
    rw [← Finset.sum_mul, hw1, one_mul]
  rw [hconst]
  linarith

/-- A point in the positive coordinate box based at `b` is a convex
combination of `b` and axial points at distance `(n+1)h`.  The weights are
indexed by `Option (Fin n)`, with `none` carrying the unused mass. -/
theorem positiveBox_eq_sum_axial {n : ℕ} (b y : Fin n → ℝ) (h : ℝ)
    (hh : 0 < h) (hcoord : ∀ i, 0 ≤ y i - b i ∧ y i - b i ≤ h) :
    ∃ w : Option (Fin n) → ℝ,
      (∀ a, 0 ≤ w a) ∧ (∑ a, w a) = 1 ∧
      y = ∑ a, w a •
        (match a with
        | none => b
        | some i => b + (((n : ℝ) + 1) * h) • Pi.single i 1) := by
  classical
  let R : ℝ := ((n : ℝ) + 1) * h
  have hR : 0 < R := mul_pos (by positivity) hh
  let a : Fin n → ℝ := fun i ↦ y i - b i
  let S : ℝ := ∑ i, a i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _hi ↦ (hcoord i).1
  have hSle : S ≤ (n : ℝ) * h := by
    calc
      S ≤ ∑ _i : Fin n, h :=
        Finset.sum_le_sum fun i _hi ↦ (hcoord i).2
      _ = (n : ℝ) * h := by simp
  let w : Option (Fin n) → ℝ
    | none => 1 - S / R
    | some i => a i / R
  have hw0 : ∀ q, 0 ≤ w q := by
    intro q
    cases q with
    | none =>
        dsimp [w]
        rw [sub_nonneg, div_le_one hR]
        dsimp [R]
        nlinarith [hh]
    | some i => exact div_nonneg (hcoord i).1 hR.le
  have hw1 : ∑ q, w q = 1 := by
    rw [Fintype.sum_option]
    dsimp [w]
    have : ∑ i, a i / R = S / R := by
      rw [Finset.sum_div]
    rw [this]
    ring
  refine ⟨w, hw0, hw1, ?_⟩
  funext j
  rw [Finset.sum_apply]
  rw [Fintype.sum_option]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  dsimp [w]
  simp only [Pi.single_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (1 - S / R) * b j + ∑ i, a i / R * b j = b j := by
    rw [← Finset.sum_mul]
    have : ∑ i, a i / R = S / R := by rw [Finset.sum_div]
    rw [this]
    ring
  rw [← add_assoc, hfirst]
  have hsecond :
      ∑ i, a i / R *
        (((n : ℝ) + 1) * h * if j = i then 1 else 0) = a j := by
    rw [Finset.sum_eq_single j]
    · simp [R, hR.ne']
    · intro i _hi hij
      simp [Ne.symm hij]
    · simp
  rw [hsecond]
  simp [a]

/-- Fixed-fibre form of the bad-cell lemma.  A positive error somewhere in
the cell forces the same error at one of the axial endpoints at distance
`(n+1)h` from the cell base. -/
theorem exists_axial_supportError_gt_of_bad {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {s : Set (Fin n → ℝ)}
    (hf : ConvexOn ℝ s f) (b y : Fin n → ℝ)
    (p : (Fin n → ℝ) →L[ℝ] ℝ) (h epsilon : ℝ)
    (hh : 0 < h) (hepsilon : 0 ≤ epsilon)
    (hcoord : ∀ i, 0 ≤ y i - b i ∧ y i - b i ≤ h)
    (hpoints : ∀ i,
      b + (((n : ℝ) + 1) * h) • Pi.single i 1 ∈ s)
    (hbase : b ∈ s)
    (hbad : epsilon < supportError f b p y) :
    ∃ i : Fin n, epsilon < supportError f b p
      (b + (((n : ℝ) + 1) * h) • Pi.single i 1) := by
  classical
  obtain ⟨w, hw0, hw1, hy⟩ := positiveBox_eq_sum_axial b y h hh hcoord
  let z : Option (Fin n) → Fin n → ℝ
    | none => b
    | some i => b + (((n : ℝ) + 1) * h) • Pi.single i 1
  have hz : ∀ q, z q ∈ s := by
    intro q
    cases q with
    | none => exact hbase
    | some i => exact hpoints i
  have hJ := supportError_map_sum_le hf b p w z hw0 hw1 hz
  rw [← hy] at hJ
  have hsum : epsilon < ∑ q, w q * supportError f b p (z q) :=
    hbad.trans_le hJ
  by_contra h
  push Not at h
  have hall : ∀ q, supportError f b p (z q) ≤ epsilon := by
    intro q
    cases q with
    | none => simp [z, hepsilon]
    | some i => exact h i
  have hle : ∑ q, w q * supportError f b p (z q) ≤
      ∑ q, w q * epsilon := by
    exact Finset.sum_le_sum fun q _hq ↦
      mul_le_mul_of_nonneg_left (hall q) (hw0 q)
  have hrhs : ∑ q, w q * epsilon = epsilon := by
    rw [← Finset.sum_mul, hw1, one_mul]
  rw [hrhs] at hle
  linarith

/-- Comparing a large axial error at one supporting functional with a
supporting functional at the axial endpoint gives a coordinate jump. -/
theorem subgradient_coordinate_jump_of_axial_error {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (b : Fin n → ℝ)
    (p q : (Fin n → ℝ) →L[ℝ] ℝ) (i : Fin n)
    (R epsilon : ℝ) (hR : 0 < R)
    (hq : f (b + R • Pi.single i 1) +
        q (b - (b + R • Pi.single i 1)) ≤ f b)
    (herror : epsilon < supportError f b p
      (b + R • Pi.single i 1)) :
    p (Pi.single i 1) + epsilon / R < q (Pi.single i 1) := by
  simp only [supportError] at herror
  have hp : p ((b + R • Pi.single i 1) - b) =
      R * p (Pi.single i 1) := by
    rw [show (b + R • Pi.single i 1) - b =
      R • Pi.single i 1 by module, map_smul]
    rfl
  have hq' : q (b - (b + R • Pi.single i 1)) =
      -R * q (Pi.single i 1) := by
    rw [show b - (b + R • Pi.single i 1) =
      (-R) • Pi.single i 1 by module, map_smul]
    rfl
  rw [hp] at herror
  rw [hq'] at hq
  have hmul : epsilon <
      (q (Pi.single i 1) - p (Pi.single i 1)) * R := by
    nlinarith
  have hdiv : epsilon / R <
      q (Pi.single i 1) - p (Pi.single i 1) :=
    (div_lt_iff₀ hR).2 hmul
  linarith

/-- Complete nonsmooth radial bad-cell jump.  Both endpoint functionals are
genuine supports; no differentiability or assumed affine approximation is
used. -/
theorem exists_subgradient_coordinate_jump_of_bad {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {s : Set (Fin n → ℝ)}
    (hf : ConvexOn ℝ s f) (b y : Fin n → ℝ)
    (p : (Fin n → ℝ) →L[ℝ] ℝ) (h epsilon : ℝ)
    (hh : 0 < h) (hepsilon : 0 ≤ epsilon)
    (hcoord : ∀ i, 0 ≤ y i - b i ∧ y i - b i ≤ h)
    (hbase : b ∈ s)
    (hpoints : ∀ i,
      b + (((n : ℝ) + 1) * h) • Pi.single i 1 ∈ s)
    (hsupportAt : ∀ i, ∃ q : (Fin n → ℝ) →L[ℝ] ℝ,
      ∀ x ∈ s,
        f (b + (((n : ℝ) + 1) * h) • Pi.single i 1) +
            q (x - (b + (((n : ℝ) + 1) * h) • Pi.single i 1)) ≤ f x)
    (hbad : epsilon < supportError f b p y) :
    ∃ (i : Fin n) (q : (Fin n → ℝ) →L[ℝ] ℝ),
      (∀ x ∈ s,
        f (b + (((n : ℝ) + 1) * h) • Pi.single i 1) +
            q (x - (b + (((n : ℝ) + 1) * h) • Pi.single i 1)) ≤ f x) ∧
      p (Pi.single i 1) +
          epsilon / (((n : ℝ) + 1) * h) < q (Pi.single i 1) := by
  obtain ⟨i, hi⟩ := exists_axial_supportError_gt_of_bad hf b y p h epsilon
    hh hepsilon hcoord hpoints hbase hbad
  obtain ⟨q, hq⟩ := hsupportAt i
  refine ⟨i, q, hq, ?_⟩
  exact subgradient_coordinate_jump_of_axial_error f b p q i
    (((n : ℝ) + 1) * h) epsilon (mul_pos (by positivity) hh)
    (hq b hbase) hi

/-- Arbitrarily chosen subgradients of a convex function are monotone along
a coordinate line. -/
theorem subgradient_coordinate_mono {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (p q : (Fin n → ℝ) →L[ℝ] ℝ) (i : Fin n) (t : ℝ)
    (ht : 0 < t)
    (hp : f x + p ((x + t • Pi.single i 1) - x) ≤
      f (x + t • Pi.single i 1))
    (hq : f (x + t • Pi.single i 1) +
        q (x - (x + t • Pi.single i 1)) ≤ f x) :
    p (Pi.single i 1) ≤ q (Pi.single i 1) := by
  have hp' : p ((x + t • Pi.single i 1) - x) =
      t * p (Pi.single i 1) := by
    rw [show (x + t • Pi.single i 1) - x =
      t • Pi.single i 1 by module, map_smul]
    rfl
  have hq' : q (x - (x + t • Pi.single i 1)) =
      -t * q (Pi.single i 1) := by
    rw [show x - (x + t • Pi.single i 1) =
      (-t) • Pi.single i 1 by module, map_smul]
    rfl
  rw [hp'] at hp
  rw [hq'] at hq
  nlinarith

/-- A `[0,1]`-valued convex function has every subgradient coordinate in
`[-1/c,1/c]` whenever the two coordinate test points at distance `c` remain
in its domain. -/
theorem subgradient_coordinate_mem_Icc {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {s : Set (Fin n → ℝ)}
    (x : Fin n → ℝ) (p : (Fin n → ℝ) →L[ℝ] ℝ)
    (i : Fin n) (c : ℝ) (hc : 0 < c)
    (hrange : ∀ z ∈ s, f z ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ s)
    (hminus : x - c • Pi.single i 1 ∈ s)
    (hplus : x + c • Pi.single i 1 ∈ s)
    (hsupport : ∀ z ∈ s, f x + p (z - x) ≤ f z) :
    p (Pi.single i 1) ∈ Set.Icc (-1 / c) (1 / c) := by
  have hm := hsupport (x - c • Pi.single i 1) hminus
  have hp := hsupport (x + c • Pi.single i 1) hplus
  have hpm : p ((x - c • Pi.single i 1) - x) =
      -c * p (Pi.single i 1) := by
    rw [show (x - c • Pi.single i 1) - x =
      (-c) • Pi.single i 1 by module, map_smul]
    rfl
  have hpp : p ((x + c • Pi.single i 1) - x) =
      c * p (Pi.single i 1) := by
    rw [show (x + c • Pi.single i 1) - x =
      c • Pi.single i 1 by module, map_smul]
    rfl
  rw [hpm] at hm
  rw [hpp] at hp
  have hfx := hrange x hx
  have hfm := hrange _ hminus
  have hfp := hrange _ hplus
  constructor
  · apply (div_le_iff₀ hc).2
    nlinarith [hm, hfx.1, hfm.2]
  · apply (le_div_iff₀ hc).2
    nlinarith [hp, hfx.1, hfp.2]

/-! ## Finite assembly of a common-fibre residue class -/

/-- A finite collection of jumps at positions in one residue class consumes
at least `card * Delta` of the available oscillation.  This is the exact
finite sorting bridge between the fibre pigeonhole and
`ConvexApproxND.residue_class_jump_telescope`. -/
theorem card_mul_jump_le_oscillation {q : ℕ} (hq : 0 < q)
    (S : Finset ℕ) (hS : S.Nonempty) (r : Fin q)
    (g : ℕ → ℝ) (Delta lower upper : ℝ)
    (hresidue : ∀ a ∈ S, a % q = r)
    (hmono : Monotone g)
    (hjump : ∀ a ∈ S, g a + Delta ≤ g (a + q))
    (hlower : ∀ a ∈ S, lower ≤ g a)
    (hupper : ∀ a ∈ S, g (a + q) ≤ upper) :
    (S.card : ℝ) * Delta ≤ upper - lower := by
  classical
  let k := S.card
  have hk : 0 < k := by simpa [k] using Finset.card_pos.mpr hS
  let ell := k - 1
  have hell : ell + 1 = k := by omega
  let e : Fin k ↪o ℕ := S.orderEmbOfFin rfl
  let a : ℕ → ℕ := fun j ↦
    if hj : j < k then e ⟨j, hj⟩ else e ⟨0, hk⟩
  have hamem (j : ℕ) (hj : j ≤ ell) : a j ∈ S := by
    have hjk : j < k := by omega
    simp only [a, dif_pos hjk]
    exact Finset.orderEmbOfFin_mem S rfl ⟨j, hjk⟩
  have hastrict (j : ℕ) (hj : j < ell) : a j < a (j + 1) := by
    have hjk : j < k := by omega
    have hsjk : j + 1 < k := by omega
    simp only [a, dif_pos hjk, dif_pos hsjk]
    exact e.strictMono (by simp)
  have hares (j : ℕ) (hj : j < ell) :
      a j % q = a (j + 1) % q := by
    rw [hresidue (a j) (hamem j (by omega)),
      hresidue (a (j + 1)) (hamem (j + 1) (by omega))]
  have hajump (j : ℕ) (hj : j ≤ ell) :
      g (a j) + Delta ≤ g (a j + q) :=
    hjump (a j) (hamem j hj)
  have htel := ConvexApproxND.residue_class_jump_telescope hq
    a g Delta hastrict hares hmono hajump
  have hlo : lower ≤ g (a 0) := hlower (a 0) (hamem 0 (by omega))
  have hup : g (a ell + q) ≤ upper := hupper (a ell) (hamem ell (by omega))
  rw [hell] at htel
  change (k : ℝ) * Delta ≤ upper - lower
  linarith

end

end Erdos186.PZ.ConvexDensity.Subgradient
