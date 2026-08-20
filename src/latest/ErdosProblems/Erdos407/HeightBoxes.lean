/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.PadicSubspaceDefs
import ErdosProblems.Erdos407.Primitive

/-!
# Rational heights and logarithmic approximation boxes

This file contains the elementary height-and-pigeonhole layer of the
specialized rational p-adic Subspace Theorem used for Erdős Problem 407.
The ground field is `ℚ`, the local places are exactly `∞`, `2`, and `3`, and
all vector spaces are presented with coordinates indexed by `Fin n`.

The main ingredients are:

* primitive integral and projective heights, together with Northcott
  finiteness in this rational setting;
* extraction of arbitrarily long, rapidly growing height sequences;
* a finite-partition infinite pigeonhole principle;
* an Archimedean height estimate for rational linear forms;
* normalized logarithms, their integer boxes, and the resulting uniform
  error estimates;
* local exponent constants `c_{v,i}`, approximation boxes, and exact
  product/exponent bounds for their radii.

No form of the Subspace Theorem is used here.
-/

namespace Erdos407.HeightBoxes

open scoped BigOperators LinearAlgebra.Projectivization

open Erdos407.PadicSubspace

abbrev Place23 := PadicSubspace.Place23
abbrev RatVector (n : ℕ) := Fin n → ℚ
abbrev IntVector (n : ℕ) := Fin n → ℤ
abbrev RatLinearForm (n : ℕ) := PadicSubspace.RatLinearForm n

/-! ## Primitive and projective heights -/

/-- The integral box height is unchanged by multiplication by `-1`. -/
@[simp] theorem boxHeight_neg {n : ℕ} (x : IntVector n) :
    boxHeight (-x) = boxHeight x := by
  simp [boxHeight]

/-- The primitive height of a rational vector.  The value at zero is set to
zero.  On a nonzero vector this is the box height of its primitive integral
representative. -/
noncomputable def primitiveHeight {n : ℕ} (x : RatVector n) : ℕ :=
  if x = 0 then 0 else boxHeight (Primitive.normalize x)

@[simp] theorem primitiveHeight_zero {n : ℕ} :
    primitiveHeight (0 : RatVector n) = 0 := by
  simp [primitiveHeight]

theorem primitiveHeight_eq_boxHeight_normalize {n : ℕ} {x : RatVector n}
    (hx : x ≠ 0) :
    primitiveHeight x = boxHeight (Primitive.normalize x) := by
  simp [primitiveHeight, hx]

theorem primitiveHeight_pos {n : ℕ} {x : RatVector n} (hx : x ≠ 0) :
    0 < primitiveHeight x := by
  rw [primitiveHeight_eq_boxHeight_normalize hx]
  exact boxHeight_pos (Primitive.normalize_ne_zero hx)

/-- Primitive height is invariant under nonzero rational scaling. -/
theorem primitiveHeight_smul {n : ℕ} (x : RatVector n) {a : ℚ} (ha : a ≠ 0) :
    primitiveHeight (a • x) = primitiveHeight x := by
  by_cases hx : x = 0
  · subst x
    simp
  have hax : a • x ≠ 0 := smul_ne_zero ha hx
  rw [primitiveHeight_eq_boxHeight_normalize hax,
    primitiveHeight_eq_boxHeight_normalize hx]
  have hproj : Primitive.ProjectivelyEquivalent (a • x) x :=
    ⟨a, ha, rfl⟩
  rcases Primitive.normalize_eq_or_eq_neg_of_projectivelyEquivalent hax hx hproj with h | h
  · rw [h]
  · rw [h, boxHeight_neg]

/-- The height of a rational projective point, computed using the canonical
primitive integral representative from `Primitive.lean`. -/
noncomputable def projectiveHeight {n : ℕ}
    (p : Projectivization ℚ (RatVector n)) : ℕ :=
  boxHeight (Primitive.projectiveNormalize p)

theorem projectiveHeight_pos {n : ℕ}
    (p : Projectivization ℚ (RatVector n)) : 0 < projectiveHeight p := by
  exact boxHeight_pos (Primitive.projectiveNormalize_ne_zero p)

theorem projectiveHeight_mk {n : ℕ} (x : RatVector n) (hx : x ≠ 0) :
    projectiveHeight (Projectivization.mk ℚ x hx) = primitiveHeight x := by
  rw [primitiveHeight_eq_boxHeight_normalize hx]
  unfold projectiveHeight Primitive.projectiveNormalize
  have hmk : Projectivization.mk ℚ
      (Projectivization.rep (Projectivization.mk ℚ x hx))
      (Projectivization.rep_nonzero (Projectivization.mk ℚ x hx)) =
      Projectivization.mk ℚ x hx :=
    Projectivization.mk_rep (Projectivization.mk ℚ x hx)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).mp hmk
  have ha0 : a ≠ 0 := by
    intro haZero
    rw [haZero, zero_smul] at ha
    exact Projectivization.rep_nonzero (Projectivization.mk ℚ x hx) ha.symm
  have hproj : Primitive.ProjectivelyEquivalent
      (Projectivization.rep (Projectivization.mk ℚ x hx)) x :=
    ⟨a, ha0, ha.symm⟩
  rcases Primitive.normalize_eq_or_eq_neg_of_projectivelyEquivalent
      (Projectivization.rep_nonzero (Projectivization.mk ℚ x hx)) hx hproj with h | h
  · rw [h]
  · rw [h, boxHeight_neg]

/-- Rational projective points of bounded height form a finite set. -/
theorem finite_projectiveHeight_le {n H : ℕ} :
    {p : Projectivization ℚ (RatVector n) | projectiveHeight p ≤ H}.Finite := by
  exact Primitive.finite_preimage_projectiveNormalize
    (PadicSubspace.finite_boxHeight_le (n := n) (H := H))

/-- Homogeneous coordinates `[1:x₁:...:xₙ]` for a rational affine point. -/
def affineCoordinates {n : ℕ} (x : RatVector n) : RatVector (n + 1) :=
  Fin.cases 1 x

@[simp] theorem affineCoordinates_zero (x : RatVector 0) :
    affineCoordinates x 0 = 1 := rfl

theorem affineCoordinates_ne_zero {n : ℕ} (x : RatVector n) :
    affineCoordinates x ≠ 0 := by
  intro h
  have := congrFun h (0 : Fin (n + 1))
  simp [affineCoordinates] at this

/-- Embed affine `n`-space into projective `n`-space by `x ↦ [1:x]`. -/
noncomputable def affinePoint {n : ℕ} (x : RatVector n) :
    Projectivization ℚ (RatVector (n + 1)) :=
  Projectivization.mk ℚ (affineCoordinates x) (affineCoordinates_ne_zero x)

theorem affinePoint_injective {n : ℕ} :
    Function.Injective (affinePoint : RatVector n →
      Projectivization ℚ (RatVector (n + 1))) := by
  intro x y hxy
  rw [affinePoint, affinePoint, Projectivization.mk_eq_mk_iff'] at hxy
  obtain ⟨a, ha⟩ := hxy
  have ha0 := congrFun ha (0 : Fin (n + 1))
  have haone : a = 1 := by
    simpa [affineCoordinates] using ha0
  funext i
  have hai := congrFun ha i.succ
  simpa [affineCoordinates, haone] using hai.symm

/-- The usual multiplicative affine height over `ℚ`. -/
noncomputable def affineHeight {n : ℕ} (x : RatVector n) : ℕ :=
  projectiveHeight (affinePoint x)

theorem affineHeight_pos {n : ℕ} (x : RatVector n) : 0 < affineHeight x :=
  projectiveHeight_pos (affinePoint x)

/-- Rational affine points of bounded height form a finite set. -/
theorem finite_affineHeight_le {n H : ℕ} :
    {x : RatVector n | affineHeight x ≤ H}.Finite := by
  apply Set.Finite.of_finite_image (f := affinePoint)
  · exact (finite_projectiveHeight_le (n := n + 1) (H := H)).subset
      (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  · exact affinePoint_injective.injOn

/-! ## Proper heights and rapidly growing finite sequences -/

/-- A natural-valued height is proper on `X` when all its bounded sublevel
sets inside `X` are finite. -/
def IsProperHeight {α : Type*} (X : Set α) (h : α → ℕ) : Prop :=
  ∀ H, {x | x ∈ X ∧ h x ≤ H}.Finite

theorem IsProperHeight.unbounded {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : IsProperHeight X h) (hX : X.Infinite) (H : ℕ) :
    ∃ x ∈ X, H < h x := by
  by_contra hnone
  push_neg at hnone
  exact hX ((hproper H).subset fun x hx => ⟨hx, hnone x hx⟩)

theorem exists_fastGrowing_list {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : IsProperHeight X h) (hX : X.Infinite)
    (H₀ A m : ℕ) :
    ∃ xs : List X, xs.length = m ∧
      (∀ x ∈ xs, H₀ < h x.1) ∧
      xs.Pairwise (fun (x y : X) => A * h x.1 < h y.1) := by
  induction m generalizing H₀ with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ m ih =>
      obtain ⟨x, hxX, hxH⟩ := hproper.unbounded hX H₀
      let xX : X := ⟨x, hxX⟩
      obtain ⟨xs, hlen, hH, hgrow⟩ := ih (max H₀ (A * h x))
      refine ⟨xX :: xs, by simp [hlen], ?_, ?_⟩
      · simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨hxH, fun y hy => (le_max_left _ _).trans_lt (hH y hy)⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hgrow⟩
        intro y hy
        exact (le_max_right H₀ (A * h x)).trans_lt (hH y hy)

/-- List form with distinctness made explicit.  A strictly height-growing
pairwise list cannot repeat an element. -/
theorem exists_fastGrowing_list_nodup {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : IsProperHeight X h) (hX : X.Infinite)
    (H₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ xs : List X, xs.length = m ∧ xs.Nodup ∧
      (∀ x ∈ xs, H₀ < h x.1) ∧
      xs.Pairwise (fun (x y : X) => A * h x.1 < h y.1) := by
  obtain ⟨xs, hlen, hH, hgrow⟩ := exists_fastGrowing_list hproper hX H₀ A m
  refine ⟨xs, hlen, ?_, hH, hgrow⟩
  apply (List.nodup_iff_injective_get).2
  intro i j hij
  rcases lt_trichotomy i j with hijlt | hijeq | hjilt
  · have hg : A * h (xs.get i).1 < h (xs.get j).1 :=
      (List.pairwise_iff_get.mp hgrow) i j hijlt
    have heq : h (xs.get i).1 = h (xs.get j).1 :=
      congrArg (fun z : X => h z.1) hij
    have hcontra : A * h (xs.get i).1 < h (xs.get i).1 := by
      rwa [← heq] at hg
    have hle : h (xs.get i).1 ≤ A * h (xs.get i).1 :=
      Nat.le_mul_of_pos_left _ hA
    exact (not_lt_of_ge hle hcontra).elim
  · exact hijeq
  · have hg : A * h (xs.get j).1 < h (xs.get i).1 :=
      (List.pairwise_iff_get.mp hgrow) j i hjilt
    have heq : h (xs.get i).1 = h (xs.get j).1 :=
      congrArg (fun z : X => h z.1) hij
    have hcontra : A * h (xs.get j).1 < h (xs.get j).1 := by
      rwa [heq] at hg
    have hle : h (xs.get j).1 ≤ A * h (xs.get j).1 :=
      Nat.le_mul_of_pos_left _ hA
    exact (not_lt_of_ge hle hcontra).elim

/-- `Fin`-indexed form used by the Subspace-Theorem construction.  The
sequence has `m+1` terms, so its first term and all `m` consecutive gaps are
available without empty-index side conditions. -/
theorem exists_fastGrowing {α : Type*} {X : Set α} {h : α → ℕ}
    (hproper : IsProperHeight X h) (hX : X.Infinite)
    (H₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ x : Fin (m + 1) → X,
      H₀ < h (x 0).1 ∧
      (∀ i : Fin m, A * h (x i.castSucc).1 < h (x i.succ).1) ∧
      Function.Injective x := by
  obtain ⟨xs, hlen, hnodup, hH, hgrow⟩ :=
    exists_fastGrowing_list_nodup hproper hX H₀ A (m + 1) hA
  let e : Fin (m + 1) → Fin xs.length := fun i => Fin.cast hlen.symm i
  let x : Fin (m + 1) → X := fun i => xs.get (e i)
  refine ⟨x, ?_, ?_, ?_⟩
  · exact hH _ (List.get_mem xs (e 0))
  · intro i
    have hi : e i.castSucc < e i.succ := by
      change i.castSucc.val < i.succ.val
      simp
    exact (List.pairwise_iff_get.mp hgrow) (e i.castSucc) (e i.succ) hi
  · exact (List.nodup_iff_injective_get.mp hnodup).comp
      (Fin.cast_injective hlen.symm)

/-- The box height is proper on every set of integral vectors. -/
theorem boxHeight_isProper {n : ℕ} (X : Set (IntVector n)) :
    IsProperHeight X boxHeight := by
  intro H
  exact PadicSubspace.finite_boxHeight_le.subset fun _ hx => hx.2

theorem exists_fastGrowing_boxHeight {n : ℕ} {X : Set (IntVector n)}
    (hX : X.Infinite) (H₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ xs : List X, xs.length = m ∧ xs.Nodup ∧
      (∀ x ∈ xs, H₀ < boxHeight (n := n) x.1) ∧
      xs.Pairwise (fun x y =>
        A * boxHeight (n := n) x.1 < boxHeight (n := n) y.1) :=
  exists_fastGrowing_list_nodup (boxHeight_isProper X) hX H₀ A m hA

/-- `Fin`-indexed specialization of rapid growth for the integral box
height. -/
theorem exists_fastGrowing_boxHeight_fin {n : ℕ} {X : Set (IntVector n)}
    (hX : X.Infinite) (H₀ A m : ℕ) (hA : 1 ≤ A) :
    ∃ x : Fin (m + 1) → X,
      H₀ < boxHeight (n := n) (x 0).1 ∧
      (∀ i : Fin m,
        A * boxHeight (n := n) (x i.castSucc).1 <
          boxHeight (n := n) (x i.succ).1) ∧
      Function.Injective x :=
  exists_fastGrowing (boxHeight_isProper X) hX H₀ A m hA

/-! ## Finite partitions and infinite fibres -/

/-- If an infinite set is covered by finitely many fibres, one fibre is
infinite. -/
theorem exists_infinite_fiber {α κ : Type*} [Finite κ]
    (X : Set α) (hX : X.Infinite) (box : α → κ) :
    ∃ k : κ, {x | x ∈ X ∧ box x = k}.Infinite := by
  classical
  by_contra hnone
  push_neg at hnone
  have hfinite : X.Finite := by
    have hunion : X = ⋃ k : κ, {x | x ∈ X ∧ box x = k} := by
      ext x
      simp
    rw [hunion]
    exact Set.finite_iUnion hnone
  exact hX hfinite

/-- Set-indexed version of finite-box pigeonholing. -/
theorem exists_infinite_box {α κ : Type*} [Finite κ]
    {X : Set α} (hX : X.Infinite) (B : κ → Set α)
    (hcover : X ⊆ ⋃ k, B k) :
    ∃ k, (X ∩ B k).Infinite := by
  classical
  by_contra hnone
  push_neg at hnone
  have hfiniteUnion : (⋃ k, X ∩ B k).Finite := Set.finite_iUnion hnone
  apply hX
  apply hfiniteUnion.subset
  intro x hx
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (hcover hx)
  exact Set.mem_iUnion.mpr ⟨k, ⟨hx, hxk⟩⟩

/-! ## Archimedean comparison for rational linear forms -/

/-- The `ℓ¹` size of the coefficients of a rational linear form. -/
def linearFormConstant {n : ℕ} (L : RatLinearForm n) : ℚ :=
  ∑ i, |L (Pi.single i 1)|

theorem linearFormConstant_nonneg {n : ℕ} (L : RatLinearForm n) :
    0 ≤ linearFormConstant L := by
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem linearForm_eq_sum_coeff {n : ℕ} (L : RatLinearForm n)
    (x : RatVector n) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  classical
  calc
    L x = L (∑ i, x i • Pi.single i (1 : ℚ)) := by
      congr 1
      funext j
      simp [Pi.single_apply]
    _ = ∑ i, L (x i • Pi.single i (1 : ℚ)) := map_sum L _ _
    _ = ∑ i, L (Pi.single i 1) * x i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [mul_comm]

/-- Evaluation of a fixed rational linear form at an integral vector is at
most its coefficient `ℓ¹` size times the box height. -/
theorem abs_linearForm_intCast_le {n : ℕ} (L : RatLinearForm n)
    (x : IntVector n) :
    |L (PadicSubspace.intCastVec x)| ≤
      linearFormConstant L * boxHeight x := by
  rw [linearForm_eq_sum_coeff]
  calc
    |∑ i, L (Pi.single i 1) * (x i : ℚ)| ≤
        ∑ i, |L (Pi.single i 1) * (x i : ℚ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |L (Pi.single i 1)| * (x i).natAbs := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    _ ≤ ∑ i, |L (Pi.single i 1)| * boxHeight x := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast natAbs_le_boxHeight x i)
          (abs_nonneg _)
    _ = linearFormConstant L * boxHeight x := by
      rw [← Finset.sum_mul]
      rfl

/-! ## Normalized logarithms and finite logarithmic boxes -/

/-- The logarithm of `a`, normalized by the logarithm of the height `H`. -/
noncomputable def normalizedLog (H a : ℝ) : ℝ := Real.log a / Real.log H

theorem normalizedLog_mul {H a b : ℝ} (hH : 1 < H)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    normalizedLog H (a * b) = normalizedLog H a + normalizedLog H b := by
  rw [normalizedLog, normalizedLog, normalizedLog, Real.log_mul ha hb]
  field_simp [ne_of_gt (Real.log_pos hH)]

theorem sum_normalizedLog_eq_normalizedLog_prod {ι : Type*}
    {H : ℝ} (hH : 1 < H) (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, a i ≠ 0) :
    ∑ i ∈ s, normalizedLog H (a i) =
      normalizedLog H (∏ i ∈ s, a i) := by
  simp only [normalizedLog]
  rw [Real.log_prod ha, Finset.sum_div]

/-- Integer index of the half-open logarithmic interval of width `η`
containing `t`. -/
noncomputable def logBoxIndex (η t : ℝ) : ℤ := ⌊t / η⌋

theorem logBoxIndex_lower {η t : ℝ} (hη : 0 < η) :
    (logBoxIndex η t : ℝ) * η ≤ t := by
  have h := Int.floor_le (t / η)
  rw [logBoxIndex]
  exact (le_div_iff₀ hη).mp h

theorem logBoxIndex_upper {η t : ℝ} (hη : 0 < η) :
    t < ((logBoxIndex η t : ℝ) + 1) * η := by
  have h := Int.lt_floor_add_one (t / η)
  rw [logBoxIndex]
  exact (div_lt_iff₀ hη).mp h

/-- Two real numbers in the same logarithmic box differ by less than the
box width. -/
theorem abs_sub_lt_of_logBoxIndex_eq {η s t : ℝ} (hη : 0 < η)
    (hbox : logBoxIndex η s = logBoxIndex η t) :
    |s - t| < η := by
  have hslo := logBoxIndex_lower (t := s) hη
  have hshi := logBoxIndex_upper (t := s) hη
  have htlo := logBoxIndex_lower (t := t) hη
  have hthi := logBoxIndex_upper (t := t) hη
  rw [hbox] at hslo hshi
  rw [abs_lt]
  constructor <;> linarith

/-- The finite type of integer logarithmic boxes meeting `[lo, hi]`. -/
def BoundedLogBox (η lo hi : ℝ) :=
  {k : ℤ // ⌊lo / η⌋ ≤ k ∧ k ≤ ⌊hi / η⌋}

noncomputable instance (η lo hi : ℝ) : Fintype (BoundedLogBox η lo hi) :=
  by
    unfold BoundedLogBox
    exact Set.Finite.fintype (Set.finite_Icc ⌊lo / η⌋ ⌊hi / η⌋)

/-- A point of `[lo,hi]` determines one of the bounded logarithmic boxes. -/
noncomputable def boundedLogBoxOf {η lo hi t : ℝ} (hη : 0 < η)
    (ht : t ∈ Set.Icc lo hi) : BoundedLogBox η lo hi :=
  ⟨logBoxIndex η t,
    Int.floor_mono (div_le_div_of_nonneg_right ht.1 hη.le),
    Int.floor_mono (div_le_div_of_nonneg_right ht.2 hη.le)⟩

theorem boundedLogBoxOf_eq_iff {η lo hi s t : ℝ} (hη : 0 < η)
    (hs : s ∈ Set.Icc lo hi) (ht : t ∈ Set.Icc lo hi) :
    boundedLogBoxOf hη hs = boundedLogBoxOf hη ht ↔
      logBoxIndex η s = logBoxIndex η t := by
  exact Subtype.ext_iff

theorem abs_sub_lt_of_boundedLogBoxOf_eq {η lo hi s t : ℝ}
    (hη : 0 < η) (hs : s ∈ Set.Icc lo hi) (ht : t ∈ Set.Icc lo hi)
    (hbox : boundedLogBoxOf hη hs = boundedLogBoxOf hη ht) :
    |s - t| < η := by
  apply abs_sub_lt_of_logBoxIndex_eq hη
  exact (boundedLogBoxOf_eq_iff hη hs ht).mp hbox

/-- Coordinatewise finite logarithmic pigeonholing. -/
theorem exists_infinite_same_logBox {α ι : Type*} [Finite ι]
    {X : Set α} (hX : X.Infinite) (η lo hi : ℝ) (hη : 0 < η)
    (f : α → ι → ℝ) (hf : ∀ x ∈ X, ∀ i, f x i ∈ Set.Icc lo hi) :
    ∃ b : ι → BoundedLogBox η lo hi,
      {x : X | (fun i => boundedLogBoxOf hη (hf x.1 x.2 i)) = b}.Infinite := by
  classical
  let box : X → (ι → BoundedLogBox η lo hi) := fun x i =>
    boundedLogBoxOf hη (hf x.1 x.2 i)
  letI : Infinite X := hX.to_subtype
  have hUniv : (Set.univ : Set X).Infinite := Set.infinite_univ
  obtain ⟨b, hb⟩ := exists_infinite_fiber (Set.univ : Set X)
    hUniv box
  refine ⟨b, ?_⟩
  simpa [box] using hb

/-! ## Local constants and approximation boxes -/

/-- The real-valued local norm at one of `∞,2,3`. -/
def realPlaceNorm (v : Place23) (q : ℚ) : ℝ :=
  (PadicSubspace.placeNorm v q : ℝ)

theorem realPlaceNorm_nonneg (v : Place23) (q : ℚ) :
    0 ≤ realPlaceNorm v q := by
  unfold realPlaceNorm
  norm_cast
  exact PadicSubspace.placeNorm_nonneg v q

/-- The normalized local exponent `c_{v,i}` attached to a point and a
family of local forms. -/
noncomputable def localConstant {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (H : ℝ) (x : RatVector n)
    (v : Place23) (i : Fin n) : ℝ :=
  normalizedLog H (realPlaceNorm v (L v i x))

/-! ### A non-assumed uniform range for the logarithmic boxes -/

/-- A fixed height threshold dominating the denominator and all three local
coefficient constants of a rational linear form. -/
noncomputable def linearFormHeightCutoff {n : ℕ} (f : RatLinearForm n) : ℕ :=
  max 2 (max (PadicSubspace.linearFormDenominator f)
    (Finset.univ.sup fun v : Place23 =>
      ⌈PadicSubspace.linearFormPlaceConstant v f⌉₊))

theorem two_le_linearFormHeightCutoff {n : ℕ} (f : RatLinearForm n) :
    2 ≤ linearFormHeightCutoff f :=
  le_max_left _ _

theorem linearFormDenominator_le_heightCutoff {n : ℕ} (f : RatLinearForm n) :
    PadicSubspace.linearFormDenominator f ≤ linearFormHeightCutoff f := by
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem linearFormPlaceConstant_le_heightCutoff {n : ℕ}
    (f : RatLinearForm n) (v : Place23) :
    PadicSubspace.linearFormPlaceConstant v f ≤
      (linearFormHeightCutoff f : ℚ) := by
  have hceil : PadicSubspace.linearFormPlaceConstant v f ≤
      (⌈PadicSubspace.linearFormPlaceConstant v f⌉₊ : ℚ) :=
    Nat.le_ceil _
  have hsup : ⌈PadicSubspace.linearFormPlaceConstant v f⌉₊ ≤
      Finset.univ.sup (fun u : Place23 =>
        ⌈PadicSubspace.linearFormPlaceConstant u f⌉₊) :=
    Finset.le_sup (f := fun u : Place23 =>
      ⌈PadicSubspace.linearFormPlaceConstant u f⌉₊) (Finset.mem_univ v)
  exact hceil.trans (by
    exact_mod_cast hsup.trans
      ((le_max_right (PadicSubspace.linearFormDenominator f) _).trans
        (le_max_right 2 _)))

/-- Once the height dominates the fixed local coefficient constant, every
local value of the form is at most the square of the height. -/
theorem placeNorm_fixedForm_le_height_sq {n : ℕ}
    (f : RatLinearForm n) (x : IntVector n) (hx : x ≠ 0)
    (hC : ∀ v, PadicSubspace.linearFormPlaceConstant v f ≤
      (boxHeight x : ℚ)) (v : Place23) :
    PadicSubspace.placeNorm v (f (PadicSubspace.intCastVec x)) ≤
      (boxHeight x : ℚ) ^ 2 := by
  calc
    PadicSubspace.placeNorm v (f (PadicSubspace.intCastVec x)) ≤
        PadicSubspace.linearFormPlaceConstant v f * boxHeight x :=
      PadicSubspace.placeNorm_linearForm_le_constant_mul_boxHeight v f x hx
    _ ≤ (boxHeight x : ℚ) * boxHeight x :=
      mul_le_mul_of_nonneg_right (hC v) (by positivity)
    _ = (boxHeight x : ℚ) ^ 2 := by ring

/-- Product formula plus the two other local upper bounds and the fixed
denominator give `1 ≤ |f(x)|_v H(x)^5` at every retained place. -/
theorem one_le_placeNorm_fixedForm_mul_height_pow_five {n : ℕ}
    (f : RatLinearForm n) (x : IntVector n) (hx : x ≠ 0)
    (hfx : f (PadicSubspace.intCastVec x) ≠ 0)
    (hC : ∀ v, PadicSubspace.linearFormPlaceConstant v f ≤
      (boxHeight x : ℚ))
    (hD : PadicSubspace.linearFormDenominator f ≤ boxHeight x)
    (v : Place23) :
    1 ≤ PadicSubspace.placeNorm v (f (PadicSubspace.intCastVec x)) *
      (boxHeight x : ℚ) ^ 5 := by
  classical
  let q : ℚ := f (PadicSubspace.intCastVec x)
  let H : ℚ := boxHeight x
  let a : Place23 → ℚ := fun u => PadicSubspace.placeNorm u q
  have hH : 0 ≤ H := by positivity
  have ha (u : Place23) : 0 ≤ a u :=
    PadicSubspace.placeNorm_nonneg u q
  have hbound (u : Place23) : a u ≤ H ^ 2 := by
    exact placeNorm_fixedForm_le_height_sq f x hx hC u
  have hrest : (∏ u ∈ (Finset.univ.erase v), a u) ≤ H ^ 4 := by
    calc
      (∏ u ∈ (Finset.univ.erase v), a u) ≤
          ∏ _u ∈ (Finset.univ.erase v), H ^ 2 :=
        Finset.prod_le_prod
          (fun u _ => ha u) (fun u _ => hbound u)
      _ = H ^ 4 := by
        rw [Finset.prod_const]
        have hcard : (Finset.univ.erase v).card = 2 := by simp
        rw [hcard]
        ring
  have hDq : (PadicSubspace.linearFormDenominator f : ℚ) ≤ H := by
    change (PadicSubspace.linearFormDenominator f : ℚ) ≤
      (boxHeight x : ℚ)
    exact_mod_cast hD
  have hbase : 1 ≤ (∏ u : Place23, a u) *
      (PadicSubspace.linearFormDenominator f : ℚ) := by
    rw [PadicSubspace.prod_placeNorm_eq_threePlaceProduct]
    exact PadicSubspace.one_le_normProduct23_linearForm_mul_denominator f x hfx
  have hsplit : (∏ u : Place23, a u) =
      a v * ∏ u ∈ (Finset.univ.erase v), a u := by
    exact (Finset.mul_prod_erase Finset.univ a (Finset.mem_univ v)).symm
  calc
    1 ≤ (∏ u : Place23, a u) *
        (PadicSubspace.linearFormDenominator f : ℚ) := hbase
    _ = (a v * ∏ u ∈ (Finset.univ.erase v), a u) *
        (PadicSubspace.linearFormDenominator f : ℚ) := by rw [hsplit]
    _ ≤ (a v * H ^ 4) * H := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hrest (ha v)) hDq
        (by positivity) (mul_nonneg (ha v) (by positivity))
    _ = a v * H ^ 5 := by ring

/-- Concrete normalized-log range for a fixed form at a point whose height
dominates its three coefficient constants and its denominator.  This is the
`Set.Icc` input used by finite logarithmic pigeonholing; the interval is
proved rather than assumed. -/
theorem localConstant_fixedForm_mem_Icc_of_largeHeight {n : ℕ}
    (f : RatLinearForm n) (x : IntVector n) (hx : x ≠ 0)
    (hfx : f (PadicSubspace.intCastVec x) ≠ 0)
    (hH2 : 2 ≤ boxHeight x)
    (hC : ∀ v, PadicSubspace.linearFormPlaceConstant v f ≤
      (boxHeight x : ℚ))
    (hD : PadicSubspace.linearFormDenominator f ≤ boxHeight x)
    (v : Place23) (i : Fin n) :
    localConstant (fun _ _ => f) (boxHeight x : ℝ)
      (PadicSubspace.intCastVec x) v i ∈ Set.Icc (-5 : ℝ) 2 := by
  let q : ℚ := f (PadicSubspace.intCastVec x)
  let H : ℝ := boxHeight x
  let lv : ℝ := realPlaceNorm v q
  have hHgt : 1 < H := by
    change (1 : ℝ) < (boxHeight x : ℝ)
    exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hH2)
  have hlogH : 0 < Real.log H := Real.log_pos hHgt
  have hlvQ : 0 < PadicSubspace.placeNorm v q :=
    (PadicSubspace.placeNorm_pos_iff v q).2 hfx
  have hlv : 0 < lv := by
    unfold lv realPlaceNorm
    exact_mod_cast hlvQ
  have huQ := placeNorm_fixedForm_le_height_sq f x hx hC v
  have hu : lv ≤ H ^ 2 := by
    unfold lv H realPlaceNorm
    exact_mod_cast huQ
  have hlQ := one_le_placeNorm_fixedForm_mul_height_pow_five
    f x hx hfx hC hD v
  have hl : (1 : ℝ) ≤ lv * H ^ 5 := by
    unfold lv H realPlaceNorm
    exact_mod_cast hlQ
  change -5 ≤ normalizedLog H lv ∧ normalizedLog H lv ≤ 2
  constructor
  · unfold normalizedLog
    apply (le_div_iff₀ hlogH).2
    have hlog := Real.log_le_log zero_lt_one hl
    rw [Real.log_one,
      Real.log_mul hlv.ne' (pow_pos (zero_lt_one.trans hHgt) 5).ne',
      Real.log_pow] at hlog
    norm_num at hlog ⊢
    nlinarith
  · unfold normalizedLog
    apply (div_le_iff₀ hlogH).2
    have hlog := Real.log_le_log hlv hu
    rw [Real.log_pow] at hlog
    norm_num at hlog ⊢
    nlinarith

/-- Cutoff-only form of `localConstant_fixedForm_mem_Icc_of_largeHeight`.
All four large-height inequalities are discharged by the single fixed
threshold `linearFormHeightCutoff f`. -/
theorem localConstant_fixedForm_mem_Icc {n : ℕ}
    (f : RatLinearForm n) (x : IntVector n) (hx : x ≠ 0)
    (hfx : f (PadicSubspace.intCastVec x) ≠ 0)
    (hlarge : linearFormHeightCutoff f ≤ boxHeight x)
    (v : Place23) (i : Fin n) :
    localConstant (fun _ _ => f) (boxHeight x : ℝ)
      (PadicSubspace.intCastVec x) v i ∈ Set.Icc (-5 : ℝ) 2 := by
  apply localConstant_fixedForm_mem_Icc_of_largeHeight f x hx hfx
  · exact (two_le_linearFormHeightCutoff f).trans hlarge
  · intro u
    exact (linearFormPlaceConstant_le_heightCutoff f u).trans
      (by exact_mod_cast hlarge)
  · exact (linearFormDenominator_le_heightCutoff f).trans hlarge

/-- Product of all `3n` local form values, after coercion to `ℝ`. -/
noncomputable def realLocalFormProduct {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (x : RatVector n) : ℝ :=
  ∏ v, ∏ i, realPlaceNorm v (L v i x)

theorem realLocalFormProduct_pos {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (x : RatVector n)
    (hpos : ∀ v i, 0 < realPlaceNorm v (L v i x)) :
    0 < realLocalFormProduct L x := by
  exact Finset.prod_pos fun v _ => Finset.prod_pos fun i _ => hpos v i

/-- The sum of the normalized local constants is the normalized logarithm
of the complete local product. -/
theorem sum_localConstant_eq {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) {H : ℝ} (hH : 1 < H)
    (x : RatVector n)
    (hpos : ∀ v i, 0 < realPlaceNorm v (L v i x)) :
    (∑ v, ∑ i, localConstant L H x v i) =
      normalizedLog H (realLocalFormProduct L x) := by
  calc
    (∑ v, ∑ i, localConstant L H x v i) =
        ∑ v, normalizedLog H (∏ i, realPlaceNorm v (L v i x)) := by
      apply Finset.sum_congr rfl
      intro v hv
      exact sum_normalizedLog_eq_normalizedLog_prod hH Finset.univ
        (fun i => realPlaceNorm v (L v i x))
        (fun i _ => (hpos v i).ne')
    _ = normalizedLog H (∏ v, ∏ i, realPlaceNorm v (L v i x)) :=
      sum_normalizedLog_eq_normalizedLog_prod hH Finset.univ
        (fun v => ∏ i, realPlaceNorm v (L v i x))
        (fun v _ => (Finset.prod_pos fun i _ => hpos v i).ne')
    _ = normalizedLog H (realLocalFormProduct L x) := rfl

/-- The strong product inequality `P·H ≤ 1` implies that the sum of all
normalized local exponents is at most `-1`. -/
theorem sum_localConstant_le_neg_one {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) {H : ℝ} (hH : 1 < H)
    (x : RatVector n)
    (hpos : ∀ v i, 0 < realPlaceNorm v (L v i x))
    (hstrong : realLocalFormProduct L x * H ≤ 1) :
    (∑ v, ∑ i, localConstant L H x v i) ≤ -1 := by
  rw [sum_localConstant_eq L hH x hpos]
  have hP : 0 < realLocalFormProduct L x :=
    realLocalFormProduct_pos L x hpos
  have hlog := Real.log_le_log (mul_pos hP (zero_lt_one.trans hH)) hstrong
  rw [Real.log_mul hP.ne' (zero_lt_one.trans hH).ne', Real.log_one] at hlog
  have hlogH : 0 < Real.log H := Real.log_pos hH
  unfold normalizedLog
  apply (div_le_iff₀ hlogH).2
  nlinarith

/-- A fixed array of local exponents. -/
abbrev LocalConstants (n : ℕ) := Place23 → Fin n → ℝ

/-- Radii `H ^ c_{v,i}` belonging to local exponents `c`. -/
noncomputable def exponentRadius {n : ℕ} (H : ℝ) (c : LocalConstants n)
    (v : Place23) (i : Fin n) : ℝ :=
  H ^ c v i

/-- Product of all `3n` real radii. -/
noncomputable def exponentRadiiProduct {n : ℕ} (H : ℝ)
    (c : LocalConstants n) : ℝ :=
  ∏ v, ∏ i, exponentRadius H c v i

theorem exponentRadiiProduct_eq_rpow_sum {n : ℕ} {H : ℝ} (hH : 0 < H)
    (c : LocalConstants n) :
    exponentRadiiProduct H c = H ^ (∑ v, ∑ i, c v i) := by
  simp only [exponentRadiiProduct, exponentRadius]
  calc
    (∏ v, ∏ i, H ^ c v i) = ∏ v, H ^ (∑ i, c v i) := by
      apply Finset.prod_congr rfl
      intro v hv
      exact (Real.rpow_sum_of_pos hH (c v) Finset.univ).symm
    _ = H ^ (∑ v, ∑ i, c v i) :=
      (Real.rpow_sum_of_pos hH (fun v => ∑ i, c v i) Finset.univ).symm

theorem exponentRadiiProduct_le {n : ℕ} {H δ : ℝ} (hH : 1 ≤ H)
    {c : LocalConstants n} (hc : (∑ v, ∑ i, c v i) ≤ -δ) :
    exponentRadiiProduct H c ≤ H ^ (-δ) := by
  rw [exponentRadiiProduct_eq_rpow_sum (zero_lt_one.trans_le hH)]
  exact Real.rpow_le_rpow_of_exponent_le hH hc

/-- A point lies in the local approximation box with radii `H^c` when all
of its local linear-form values satisfy the corresponding bounds. -/
def InApproximationBox {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (H : ℝ)
    (c : LocalConstants n) (x : RatVector n) : Prop :=
  ∀ v i, realPlaceNorm v (L v i x) ≤ exponentRadius H c v i

/-- Coordinatewise enlargement of exponents enlarges an approximation box. -/
theorem InApproximationBox.mono {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n} {H : ℝ} (hH : 1 ≤ H)
    {c d : LocalConstants n} (hcd : ∀ v i, c v i ≤ d v i)
    {x : RatVector n} (hx : InApproximationBox L H c x) :
    InApproximationBox L H d x := by
  intro v i
  exact (hx v i).trans (Real.rpow_le_rpow_of_exponent_le hH (hcd v i))

/-- Local constants recover the local norm exactly when the height base is
greater than one and the local value is positive. -/
theorem rpow_localConstant {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) {H : ℝ} (hH : 1 < H)
    (x : RatVector n) (v : Place23) (i : Fin n)
    (hpos : 0 < realPlaceNorm v (L v i x)) :
    H ^ localConstant L H x v i = realPlaceNorm v (L v i x) := by
  simp only [localConstant, normalizedLog]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hH)]
  have hlog : Real.log H ≠ 0 := (Real.log_pos hH).ne'
  have harg : Real.log H *
      (Real.log (realPlaceNorm v (L v i x)) / Real.log H) =
      Real.log (realPlaceNorm v (L v i x)) := by
    field_simp
  rw [harg, Real.exp_log hpos]

/-- Rounding every local constant upward by at most `η` gives an
approximation box containing the point. -/
theorem mem_approximationBox_of_localConstant_le {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) {H η : ℝ} (hH : 1 < H)
    (x : RatVector n) (c : LocalConstants n)
    (hpos : ∀ v i, 0 < realPlaceNorm v (L v i x))
    (hc : ∀ v i, localConstant L H x v i ≤ c v i) :
    InApproximationBox L H c x := by
  intro v i
  rw [← rpow_localConstant L hH x v i (hpos v i)]
  exact Real.rpow_le_rpow_of_exponent_le hH.le (hc v i)

/-- For at most five variables there are at most fifteen local coordinates. -/
theorem localCoordinate_card_le_fifteen {n : ℕ} (hn : n ≤ 5) :
    Fintype.card (Place23 × Fin n) ≤ 15 := by
  simp
  omega

/-- The accumulated error from rounding all `3n` exponents by at most `η`.
This is the elementary product/volume exponent estimate used in dimensions
at most five. -/
theorem sum_le_of_local_error {n : ℕ} (hn : n ≤ 5)
    {a c : LocalConstants n} {η δ : ℝ}
    (hη : 0 ≤ η)
    (ha : (∑ v, ∑ i, a v i) ≤ -δ)
    (herr : ∀ v i, c v i ≤ a v i + η) :
    (∑ v, ∑ i, c v i) ≤ -δ + 15 * η := by
  calc
    (∑ v, ∑ i, c v i) ≤ ∑ v, ∑ i, (a v i + η) :=
      Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun i _ => herr v i
    _ = (∑ v, ∑ i, a v i) + (3 * n : ℕ) * η := by
      simp [Finset.sum_add_distrib]
      ring
    _ ≤ -δ + 15 * η := by
      have hcard : (3 * n : ℝ) ≤ 15 := by norm_cast; omega
      have hmul : (3 * n : ℝ) * η ≤ 15 * η :=
        mul_le_mul_of_nonneg_right hcard hη
      have hadd := add_le_add ha hmul
      norm_num [Nat.cast_mul] at hadd ⊢
      exact hadd

theorem exponentRadiiProduct_le_of_local_error {n : ℕ} (hn : n ≤ 5)
    {H η δ : ℝ} (hH : 1 ≤ H) {a c : LocalConstants n}
    (hη : 0 ≤ η)
    (ha : (∑ v, ∑ i, a v i) ≤ -δ)
    (herr : ∀ v i, c v i ≤ a v i + η) :
    exponentRadiiProduct H c ≤ H ^ (-δ + 15 * η) := by
  rw [exponentRadiiProduct_eq_rpow_sum (zero_lt_one.trans_le hH)]
  exact Real.rpow_le_rpow_of_exponent_le hH
    (sum_le_of_local_error hn hη ha herr)

#print axioms finite_projectiveHeight_le
#print axioms finite_affineHeight_le
#print axioms exists_fastGrowing_list_nodup
#print axioms exists_infinite_fiber
#print axioms abs_linearForm_intCast_le
#print axioms one_le_placeNorm_fixedForm_mul_height_pow_five
#print axioms localConstant_fixedForm_mem_Icc
#print axioms exists_infinite_same_logBox
#print axioms exponentRadiiProduct_le_of_local_error

end Erdos407.HeightBoxes
