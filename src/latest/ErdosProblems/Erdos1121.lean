/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1121.
https://www.erdosproblems.com/forum/thread/1121

Informal authors:
- A. W. Goodman
- R. E. Goodman

Formal authors:
- Aristotle
- Amogh Parab

URLs:
- https://www.erdosproblems.com/forum/thread/1121#post-5504
-/
/-
# Erdős Problem 1121 — Goodman's Circle Covering Theorem

## Problem Statement (content.tex)

If C₁,…,Cₙ are circles in ℝ² with radii r₁,…,rₙ such that no line disjoint from
all the circles divides them into two non-empty sets then the circles can be covered
by a circle of radius r = ∑ rᵢ.

## Reference

A. W. Goodman and R. E. Goodman, "A Circle Covering Theorem",
*The American Mathematical Monthly*, Vol. 52, No. 9 (Nov., 1945), pp. 494–498.
-/
import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedSimpArgs false
set_option linter.style.induction false
set_option linter.style.refine false
set_option linter.style.multiGoal false
set_option linter.style.maxHeartbeats false

namespace Erdos1121

open scoped BigOperators
open Finset

/-! ## Geometric Structures -/

/-- A circle in ℝ² with a center and positive radius. -/
structure Circle2D where
  center : EuclideanSpace ℝ (Fin 2)
  radius : ℝ
  radius_pos : 0 < radius

/-- A line in ℝ² specified by a point on the line and a unit direction vector. -/
structure Line2D where
  point : EuclideanSpace ℝ (Fin 2)
  direction : EuclideanSpace ℝ (Fin 2)
  direction_unit : ‖direction‖ = 1

/-! ## 2D Perpendicular (90° Rotation) -/

/-- 90° counterclockwise rotation of a 2D vector: (a, b) ↦ (-b, a).
    This produces the normal to a direction vector. -/
noncomputable def perp2D (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(v 1), v 0]

@[simp] lemma perp2D_norm (v : EuclideanSpace ℝ (Fin 2)) : ‖perp2D v‖ = ‖v‖ := by
  simp only [EuclideanSpace.norm_eq, perp2D]
  congr 1; simp [Fin.sum_univ_two, EuclideanSpace.equiv]; ring

@[simp] lemma perp2D_inner_self (v : EuclideanSpace ℝ (Fin 2)) :
    @inner ℝ _ _ (perp2D v) v = 0 := by
  simp only [perp2D, inner]; simp [Fin.sum_univ_two, EuclideanSpace.equiv]; ring

@[simp] lemma perp2D_perp2D (v : EuclideanSpace ℝ (Fin 2)) : perp2D (perp2D v) = -v := by
  simp [perp2D, EuclideanSpace.equiv]
  ext i; fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## Geometric Predicates -/

/-- Signed distance from a point to a line, measured using the outward normal
    `perp2D L.direction` (the 90° rotation of the direction). -/
noncomputable def Line2D.signedDist (L : Line2D) (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  @inner ℝ _ _ (perp2D L.direction) (x - L.point)

/-- A circle is **disjoint from a line** if every point of the circle is off the line,
    equivalently the distance from the center to the line exceeds the radius. -/
def Circle2D.disjointFromLine (C : Circle2D) (L : Line2D) : Prop :=
  |L.signedDist C.center| > C.radius

/-- Two points are on **different sides** of a line if their signed distances from
    the line have opposite signs. -/
def Line2D.onDifferentSides (L : Line2D) (x y : EuclideanSpace ℝ (Fin 2)) : Prop :=
  (L.signedDist x > 0 ∧ L.signedDist y < 0) ∨
  (L.signedDist x < 0 ∧ L.signedDist y > 0)

/-- Two circles are on **different sides** of a line. Since both circles are disjoint
    from the line, each lies entirely on one side, so the side is determined by the center. -/
def Circle2D.onDifferentSidesOfLine (C₁ C₂ : Circle2D) (L : Line2D) : Prop :=
  L.onDifferentSides C₁.center C₂.center

/-! ## Nonseparability Condition -/

/-- A collection of circles is **nonseparable** if no line disjoint from all the circles
    divides them into two non-empty groups — i.e., there is no line that avoids every
    circle and places some circles on one side and others on the other side. -/
def CirclesNonseparable {n : ℕ} (circles : Fin n → Circle2D) : Prop :=
  ∀ L : Line2D, (∀ i, (circles i).disjointFromLine L) →
    ¬∃ i j, (circles i).onDifferentSidesOfLine (circles j) L

/-! ## 1D Non-separability and Covering Lemma -/

/-- Intervals `[s i - r i, s i + r i]` on ℝ are **1D-nonseparable** if no point on the line
    can separate them into two nonempty groups without lying in at least one interval. -/
def Nonseparable1D {n : ℕ} (s r : Fin n → ℝ) : Prop :=
  ∀ c : ℝ, (∀ i, |s i - c| > r i) → ∀ i j, (0 < s i - c ↔ 0 < s j - c)

/-- Nonseparable1D is preserved under negation of centers. -/
lemma Nonseparable1D.neg {n : ℕ} {s r : Fin n → ℝ}
    (hr : ∀ i, 0 ≤ r i) (hns : Nonseparable1D s r) :
    Nonseparable1D (fun i => -s i) r := by
  intro c hc
  contrapose! hns
  simp_all +decide [Nonseparable1D]
  use -c
  grind

/-- Nonseparable1D is preserved under composition with an equivalence. -/
lemma Nonseparable1D.comp_equiv {n : ℕ} {s r : Fin n → ℝ}
    (hns : Nonseparable1D s r) (σ : Fin n ≃ Fin n) :
    Nonseparable1D (s ∘ σ) (r ∘ σ) := by
  intro c hc; have := hns c; simp_all +decide [← Equiv.eq_symm_apply]
  exact fun i j => this (fun i => by simpa using hc (σ.symm i)) _ _

/-! ### Algebraic identity -/

/-- The algebraic identity: `∑ j, a j * (2 * ∑_{k < j} a k + a j) = (∑ a)²`. -/
lemma sum_weighted_Iio_eq_sq {n : ℕ} (a : Fin n → ℝ) :
    ∑ j : Fin n, a j * (2 * ∑ k ∈ Finset.Iio j, a k + a j) =
    (∑ j : Fin n, a j) ^ 2 := by
  induction' n with n ih
  · norm_num
  · simp +decide [Fin.sum_univ_castSucc, ih]
    convert congr_arg (· + a (Fin.last n) * (2 * ∑ k, a (Fin.castSucc k) + a (Fin.last n)))
      (ih fun i ↦ a (Fin.castSucc i)) using 1; ring_nf!
    · simp +decide [add_comm, add_left_comm, add_assoc]
      refine' Finset.sum_congr rfl fun i hi => _
      rw [show (Iio (Fin.castSucc i) : Finset (Fin (n + 1))) =
        Finset.image (Fin.castSucc) (Iio i) from ?_, Finset.sum_image] <;> aesop
    · ring

/-! ### Sorted center bound -/

-- For sorted intervals (left endpoints in increasing order), nonseparability forces
-- each center to be within `2 * ∑_{k < j} r_k + r_j` of the minimum left endpoint.
set_option maxHeartbeats 800000 in
lemma sorted_center_bound {n : ℕ} (s r : Fin (n + 1) → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hsorted : Monotone (fun i : Fin (n + 1) => s i - r i))
    (hns : Nonseparable1D s r) (j : Fin (n + 1)) :
    s j ≤ s 0 - r 0 + 2 * ∑ k ∈ Finset.Iio j, r k + r j := by
  induction' j with j ih
  induction' j using Nat.strong_induction_on with j ih
  by_contra h_contra
  have h_gt : ∀ k < ⟨j, ih⟩, s ⟨j, ih⟩ - r ⟨j, ih⟩ > s k + r k := by
    intros k hk_lt_j
    have h_sum_lt : ∑ k ∈ Finset.Iio ⟨j, ih⟩, r k ≥ ∑ k ∈ Finset.Iio k, r k + r k := by
      rw [← Finset.sum_erase_add _ _ (show k ∈ Iio ⟨j, ih⟩ from Finset.mem_Iio.mpr hk_lt_j),
        add_comm]
      rw [add_comm]; gcongr
      · aesop
      · grind
    linarith [hr k, hr ⟨j, ih⟩,
      ‹∀ m < j, ∀ (ih : m < n + 1), s ⟨m, ih⟩ ≤ s 0 - r 0 + 2 * ∑ k ∈ Iio ⟨m, ih⟩,
        r k + r ⟨m, ih⟩› _ hk_lt_j (by linarith [Fin.is_lt k])]
  obtain ⟨c, hc⟩ : ∃ c, ∀ k < ⟨j, ih⟩, s k + r k < c ∧ c < s ⟨j, ih⟩ - r ⟨j, ih⟩ := by
    by_cases hj : j = 0
    · aesop
    · obtain ⟨k₀, hk₀⟩ : ∃ k₀ < ⟨j, ih⟩, ∀ k < ⟨j, ih⟩, s k + r k ≤ s k₀ + r k₀ := by
        have := Finset.exists_max_image (Finset.Iio ⟨j, ih⟩) (fun k => s k + r k)
          ⟨⟨0, by linarith⟩, Finset.mem_Iio.mpr (Nat.pos_of_ne_zero hj)⟩; aesop
      exact ⟨(s k₀ + r k₀ + s ⟨j, ih⟩ - r ⟨j, ih⟩) / 2,
        fun k hk => ⟨by linarith [h_gt k hk, hk₀.2 k hk],
          by linarith [h_gt k hk, hk₀.2 k hk, h_gt k₀ hk₀.1]⟩⟩
  have h_abs : ∀ k, |s k - c| > r k := by
    intro k; by_cases hk : k < ⟨j, ih⟩ <;> simp_all +decide [abs_eq_max_neg]
    · exact Or.inr (by linarith [hc k hk, hr k])
    · specialize hc ⟨j - 1, Nat.lt_succ_of_le (Nat.sub_le_of_le_add <| by linarith)⟩
      rcases j with (_ | j) <;> norm_num at *
      · erw [Finset.sum_empty] at h_contra; linarith [hr 0]
      · exact Or.inl (by linarith [hsorted hk, hr k])
  have := hns c h_abs
  specialize this ⟨j, ih⟩ 0
  specialize hc 0; simp_all +decide
  rcases j with (_ | j) <;> simp_all +decide
  · erw [Finset.sum_empty] at h_contra; linarith
  · linarith [this.mp (by linarith [hc (Nat.succ_pos _), hr 0, hr ⟨j + 1, by linarith⟩]),
      hc (Nat.succ_pos _), hr 0, hr ⟨j + 1, by linarith⟩]

/-! ### Sorted weighted sum bound -/

/-- For sorted nonseparable intervals: `∑ s_j r_j ≤ (s 0 - r 0) * R + R²`. -/
lemma sorted_weighted_sum_le {n : ℕ} (s r : Fin (n + 1) → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hsorted : Monotone (fun i : Fin (n + 1) => s i - r i))
    (hns : Nonseparable1D s r) :
    ∑ j, s j * r j ≤ (s 0 - r 0) * ∑ j, r j + (∑ j, r j) ^ 2 := by
  have h_mul : ∀ j, s j * r j ≤
      (s 0 - r 0) * r j + 2 * r j * ∑ k ∈ Finset.Iio j, r k + r j ^ 2 := by
    intro j
    have := sorted_center_bound s r hr hsorted hns j
    nlinarith only [this, hr j]
  convert Finset.sum_le_sum fun i _ => h_mul i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum _ _ _,
    ← sum_weighted_Iio_eq_sq]
  simpa only [sq, mul_add, mul_assoc, mul_left_comm, Finset.sum_add_distrib] using by ring

/-! ### 1D Covering Lemmas -/

/-- **1D Covering Lemma (lower bound).**
    Under 1D-nonseparability, `Σ s_j r_j - R² ≤ (s i - r i) * R`. -/
theorem one_dim_covering_lower {n : ℕ} (s r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hns : Nonseparable1D s r) (i : Fin n) :
    ∑ j, s j * r j - (∑ j, r j) ^ 2 ≤ (s i - r i) * ∑ j, r j := by
  rcases n with (_ | n) <;> simp_all +decide [Finset.sum_div _ _ _, sq]
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (n + 1) ≃ Fin (n + 1),
      ∀ j k : Fin (n + 1), j ≤ k → s (σ j) - r (σ j) ≤ s (σ k) - r (σ k) := by
    have h_sorted : ∃ σ : Fin (n + 1) → Fin (n + 1),
        (∀ i, σ i ∈ Finset.univ) ∧
        (∀ i j, i < j → (s (σ i) - r (σ i)) ≤ (s (σ j) - r (σ j))) ∧
        Function.Injective σ := by
      have h_ind : ∀ (n : ℕ), ∀ (f : Fin n → ℝ),
          ∃ σ : Fin n → Fin n, (∀ i, σ i ∈ Finset.univ) ∧
          (∀ i j, i < j → f (σ i) ≤ f (σ j)) ∧ Function.Injective σ := by
        intro n f; induction' n with n ih <;> simp_all +decide [Finset.card_univ]
        obtain ⟨m, hm⟩ : ∃ m : Fin (n + 1), ∀ i : Fin (n + 1), f i ≥ f m := by
          simpa using Finset.exists_min_image Finset.univ (fun i => f i) ⟨0, Finset.mem_univ 0⟩
        obtain ⟨σ, hσ₁, hσ₂⟩ := ih (fun i => f (Fin.succAbove m i))
        refine' ⟨Fin.cons m (fun i => Fin.succAbove m (σ i)), _, _⟩ <;>
          simp_all +decide [Function.Injective]
        · intro i j hij
          induction i using Fin.inductionOn <;> induction j using Fin.inductionOn <;> aesop
        · simp +decide [Fin.forall_fin_succ, Function.Injective]; tauto
      exact h_ind _ fun i => s i - r i
    obtain ⟨σ, hσ₁, hσ₂, hσ₃⟩ := h_sorted
    exact ⟨Equiv.ofBijective σ ⟨hσ₃, Finite.injective_iff_surjective.mp hσ₃⟩,
      fun j k hjk => by cases lt_or_eq_of_le hjk <;> aesop⟩
  have h_sorted_bound :
      ∑ j, s (σ j) * r (σ j) ≤
        (s (σ 0) - r (σ 0)) * (∑ j, r (σ j)) + (∑ j, r (σ j)) ^ 2 := by
    convert sorted_weighted_sum_le (fun j => s (σ j)) (fun j => r (σ j))
      (fun j => hr (σ j)) (fun j k hjk => hσ j k hjk) (hns.comp_equiv σ) using 1
  have h_perm : ∑ j, s (σ j) * r (σ j) = ∑ j, s j * r j ∧
      ∑ j, r (σ j) = ∑ j, r j := by
    exact ⟨Equiv.sum_comp σ fun j => s j * r j, Equiv.sum_comp σ fun j => r j⟩
  have := hσ 0 (σ.symm i) (Nat.zero_le _); simp_all +decide
  nlinarith [hr i, hr (σ 0), Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hr j]

/-- **1D Covering Lemma (upper bound).**
    Under 1D-nonseparability, `(s i + r i) * R ≤ Σ s_j r_j + R²`. -/
theorem one_dim_covering_upper {n : ℕ} (s r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hns : Nonseparable1D s r) (i : Fin n) :
    (s i + r i) * ∑ j, r j ≤ ∑ j, s j * r j + (∑ j, r j) ^ 2 := by
  have := one_dim_covering_lower (fun j => -s j) r hr (?_) i
  · norm_num [Finset.sum_neg_distrib] at *; linarith
  · exact Nonseparable1D.neg hr hns

/-! ## Internal 2D Nonseparability (normal–offset form) -/

/-- Internal nonseparability definition using normal–offset representation of lines.
    Equivalent to `CirclesNonseparable` but more convenient for the analytic proof. -/
def NonseparableInternal {n : ℕ} (center : Fin n → EuclideanSpace ℝ (Fin 2))
    (radius : Fin n → ℝ) : Prop :=
  ∀ (w : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
    ‖w‖ = 1 →
    (∀ i, |@inner ℝ (EuclideanSpace ℝ (Fin 2)) _ w (center i) - c| > radius i) →
    ∀ i j, (0 < @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ w (center i) - c ↔
            0 < @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ w (center j) - c)

/-! ## Bridge: CirclesNonseparable → NonseparableInternal -/

/-- Key computation: the signed distance from a point to the line constructed from
    a normal vector `w` and offset `c` equals `-(⟪w, x⟫ - c)`. -/
lemma signedDist_of_constructed_line (w x : EuclideanSpace ℝ (Fin 2)) (c : ℝ) (hw : ‖w‖ = 1) :
    (⟨c • w, perp2D w, (perp2D_norm w).trans hw⟩ : Line2D).signedDist x =
    -(@inner ℝ _ _ w x - c) := by
  simp only [Line2D.signedDist, perp2D_perp2D, inner_neg_left, inner_sub_right,
    inner_smul_right, real_inner_self_eq_norm_sq, hw]
  ring

/-
The geometric nonseparability condition (no separating line) implies the internal
    analytic nonseparability condition.
-/
lemma circlesNonseparable_implies_internal {n : ℕ} (circles : Fin n → Circle2D)
    (hns : CirclesNonseparable circles) :
    NonseparableInternal (fun i => (circles i).center) (fun i => (circles i).radius) := by
  intro w c hw hc i j;
  contrapose! hns;
  unfold CirclesNonseparable;
  simp +zetaDelta at *;
  refine' ⟨ ⟨ c • w, perp2D w, _ ⟩, _, i, j, _ ⟩ <;>
    simp_all +decide [Circle2D.disjointFromLine, Circle2D.onDifferentSidesOfLine];
  · intro i; specialize hc i; simp_all +decide [ Line2D.signedDist ];
    simp_all +decide [ inner_sub_right, inner_smul_right ];
  · cases hns <;> simp_all +decide [ Line2D.onDifferentSides, Line2D.signedDist ];
    · simp_all +decide [ inner_sub_right, inner_smul_right ];
      exact Or.inr (lt_of_le_of_ne (by linarith) (by
        intro H
        specialize hc j
        norm_num [H] at hc
        linarith [(circles j).radius_pos]));
    · simp_all +decide [ inner_sub_right, inner_smul_right ];
      exact Or.inl (lt_of_le_of_ne (by linarith) fun h => by
        have := hc i
        norm_num [h] at this
        linarith [(circles i).radius_pos])

/-! ## Projection Lemma -/

/-- 2D nonseparability implies 1D nonseparability of projections onto any line. -/
theorem projection_nonseparable {n : ℕ}
    (center : Fin n → EuclideanSpace ℝ (Fin 2))
    (radius : Fin n → ℝ)
    (hns : NonseparableInternal center radius)
    (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖ = 1) :
    Nonseparable1D (fun i => @inner ℝ (EuclideanSpace ℝ (Fin 2)) _ w (center i)) radius := by
  intros c hc i j; exact (hns w c hw hc i j)

/-! ## Helper: norm bound from 1D covering applied to all projections -/

/-- The weighted centroid is within distance `R - r_i` of each center `O_i`. -/
lemma weighted_centroid_dist_le {n : ℕ}
    (center : Fin n → EuclideanSpace ℝ (Fin 2))
    (radius : Fin n → ℝ)
    (hradii : ∀ i, 0 ≤ radius i)
    (hns : NonseparableInternal center radius)
    (hR : 0 < ∑ j : Fin n, radius j)
    (i : Fin n) :
    dist (center i) ((∑ j : Fin n, radius j)⁻¹ • ∑ j, radius j • center j) +
      radius i ≤ ∑ j : Fin n, radius j := by
  by_contra! h_contra
  set T₀ := (∑ j, radius j)⁻¹ • (∑ j, radius j • center j)
  have hw : ‖(center i - T₀)‖ ≠ 0 := by
    intro h; simp_all +decide [sub_eq_iff_eq_add]; linarith [hradii i,
      Finset.single_le_sum (fun a _ => hradii a) (Finset.mem_univ i)]
  set w := ‖(center i - T₀)‖⁻¹ • (center i - T₀)
  have hw_norm : ‖w‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw]
  have h_apply_upper :
      (∑ j, radius j) * (inner ℝ w (center i) + radius i) ≤
      (∑ j, radius j) * inner ℝ w T₀ + (∑ j, radius j) ^ 2 := by
    have h_apply_upper :
        (∑ j, radius j) * (inner ℝ w (center i) + radius i) ≤
        (∑ j, radius j * inner ℝ w (center j)) + (∑ j, radius j) ^ 2 := by
      have := one_dim_covering_upper (fun j => inner ℝ w (center j)) radius hradii
        (projection_nonseparable center radius hns w hw_norm) i
      simpa only [mul_comm, Finset.mul_sum _ _ _] using this
    convert h_apply_upper using 2
    simp +zetaDelta at *
    simp +decide [mul_comm,
      inner_smul_left, inner_smul_right]
    simp +decide [← mul_assoc, ← Finset.sum_mul, hR.ne']
    simp +decide [inner_sum, inner_smul_right]
  have h_inner : inner ℝ w (center i) = inner ℝ w T₀ + ‖center i - T₀‖ := by
    have h_inner : inner ℝ w (center i - T₀) = ‖center i - T₀‖ := by
      simp +zetaDelta at *
      simp +decide [inner_smul_left, inner_self_eq_norm_sq_to_K]
      rw [inv_mul_eq_div, sq, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hw)]
    rw [← h_inner, inner_sub_right]; ring
  nlinarith! [norm_nonneg (center i - T₀), dist_eq_norm (center i) T₀]

/-! ## Internal Goodman Theorem -/

/-- Internal version of Goodman's theorem using `NonseparableInternal`. -/
theorem goodman_circle_covering_internal {n : ℕ}
    (center : Fin n → EuclideanSpace ℝ (Fin 2))
    (radius : Fin n → ℝ)
    (hradii : ∀ i, 0 ≤ radius i)
    (hns : NonseparableInternal center radius) :
    ∃ T : EuclideanSpace ℝ (Fin 2),
      ∀ i, Metric.closedBall (center i) (radius i) ⊆
           Metric.closedBall T (∑ j : Fin n, radius j) := by
  set R := ∑ j, radius j with hRdef
  by_cases hR : R = 0
  · have h_radii_zero : ∀ i, radius i = 0 := by
      rw [Finset.sum_eq_zero_iff_of_nonneg] at hR <;> aesop
    by_cases hn : n = 0 <;> simp_all +decide [NonseparableInternal]
    · aesop
    · contrapose! hns
      obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin 2),
          ‖w‖ = 1 ∧ ∃ i j, inner ℝ w (center i) ≠ inner ℝ w (center j) := by
        obtain ⟨i, hi⟩ := hns (center ⟨0, Nat.pos_of_ne_zero hn⟩)
        obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin 2),
            inner ℝ w (center i - center ⟨0, Nat.pos_of_ne_zero hn⟩) ≠ 0 := by
          exact ⟨center i - center ⟨0, Nat.pos_of_ne_zero hn⟩,
            by simp [sub_eq_zero, hi]⟩
        refine' ⟨‖w‖⁻¹ • w, _, i, ⟨0, Nat.pos_of_ne_zero hn⟩, _⟩ <;>
          simp_all +decide [norm_smul, inner_smul_left]
        · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr
            (show w ≠ 0 from by rintro rfl; simp +decide at hw))]
        · exact ⟨fun h => hw <| by rw [inner_sub_right, h, sub_self],
            fun h => hw <| by simp +decide [h]⟩
      obtain ⟨i, j, hij⟩ := hw.2
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c ∉ Set.range (fun i => inner ℝ w (center i)) ∧
          (∃ i, inner ℝ w (center i) < c) ∧ (∃ j, c < inner ℝ w (center j)) := by
        cases lt_or_gt_of_ne hij
        · obtain ⟨c, hc⟩ : ∃ c : ℝ, inner ℝ w (center i) < c ∧
              c < inner ℝ w (center j) ∧
              c ∉ Set.range (fun i => inner ℝ w (center i)) := by
            have h_finite : Set.Finite (Set.range (fun i => inner ℝ w (center i))) :=
              Set.toFinite _
            have h_infinite :
                Set.Infinite (Set.Ioo (inner ℝ w (center i)) (inner ℝ w (center j))) :=
              Set.Ioo_infinite ‹_›
            exact Exists.elim (h_infinite.diff h_finite |> Set.Infinite.nonempty)
              fun x hx => ⟨x, hx.1.1, hx.1.2, hx.2⟩
          exact ⟨c, hc.2.2, ⟨i, hc.1⟩, ⟨j, hc.2.1⟩⟩
        · have h_finite : Set.Finite (Set.range (fun i => inner ℝ w (center i))) :=
            Set.toFinite _
          exact Exists.imp (by aesop) (Set.Infinite.nonempty
            (Set.Infinite.diff (Set.Ioo_infinite
              (by linarith : inner ℝ w (center j) < inner ℝ w (center i))) h_finite))
      exact ⟨w, c, hw.1, fun i => sub_ne_zero_of_ne <| by aesop,
        by obtain ⟨i, hi⟩ := hc.2.1; obtain ⟨j, hj⟩ := hc.2.2;
           exact ⟨i, j, Or.inr ⟨by linarith, by linarith⟩⟩⟩
  · have h_dist : ∀ i, dist (center i)
        ((R⁻¹) • ∑ j, radius j • center j) + radius i ≤ R := by
      convert weighted_centroid_dist_le center radius hradii hns
        (lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => hradii _) (Ne.symm hR)) using 1
    use (R⁻¹) • ∑ j, radius j • center j
    intro i x hx; specialize h_dist i; rw [Metric.mem_closedBall] at *
    linarith [dist_triangle x (center i) (R⁻¹ • ∑ j, radius j • center j)]

/-! ## Main Theorem -/

/-- **Erdős Problem 1121** (Goodman's Circle Covering Theorem):
    If circles C₁,…,Cₙ in ℝ² with radii r₁,…,rₙ are nonseparable — no line
    disjoint from all of them divides them into two non-empty groups — then they
    can all be covered by a single circle of radius r = r₁ + ⋯ + rₙ. -/
theorem erdos_1121 {n : ℕ} (circles : Fin n → Circle2D)
    (hns : CirclesNonseparable circles) :
    ∃ T : EuclideanSpace ℝ (Fin 2),
      ∀ i, Metric.closedBall (circles i).center (circles i).radius ⊆
           Metric.closedBall T (∑ j, (circles j).radius) :=
  goodman_circle_covering_internal
    (fun i => (circles i).center)
    (fun i => (circles i).radius)
    (fun i => le_of_lt (circles i).radius_pos)
    (circlesNonseparable_implies_internal circles hns)

#print axioms erdos_1121
-- 'Erdos1121.erdos_1121' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1121
