/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.RankDrop

/-!
# Concrete three-place successive minima

This file supplies the actual adapted-basis package used at the exterior-power
endpoint of the rational Subspace Theorem.  Over `ℚ` an adelic dilation acts
at the unique Archimedean place and does not change the `2`- or `3`-adic
components.  Accordingly, the local dilation factor below is `lambda` at
`∞` and `1` at the two finite places.

Rather than postulating infima, we construct an adapted basis directly.  A
maximal independent family in the scale-one approximation domain is extended
to a rational basis.  The complementary vectors are replaced by nonzero
integer multiples and then by sufficiently large powers of `6`; this makes
them integral away from `2,3` and puts them in the prescribed finite-place
balls.  Sorting the two blocks by their exact Archimedean entry scale gives
positive ordered numbers `lambda_j`, with precisely the scale-one rank many
of them at most one.

The determinant/product-formula argument gives the lower product estimate
usually obtained from the lower half of adelic Minkowski's second theorem.
It is stated explicitly, together with the largest-minimum and ratio-gap
consequences needed in GLR, Section 5.3.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix

namespace AdelicMinima

open Erdos407 HeightBoxes

abbrev RatVector (n : ℕ) := Fin n → ℚ
abbrev LocalForms (n : ℕ) := Place23 → Fin n → RatLinearForm n

/-- Over `ℚ`, adelic scalar dilation occurs only at the real place. -/
def placeScale (v : Place23) (lambda : ℝ) : ℝ :=
  if v = Place23.infinite then lambda else 1

@[simp] theorem placeScale_infinite (lambda : ℝ) :
    placeScale Place23.infinite lambda = lambda := by
  simp [placeScale]

@[simp] theorem placeScale_two (lambda : ℝ) :
    placeScale Place23.two lambda = 1 := by
  simp [placeScale, Place23.two, Place23.infinite]

@[simp] theorem placeScale_three (lambda : ℝ) :
    placeScale Place23.three lambda = 1 := by
  simp [placeScale, Place23.three, Place23.infinite]

/-- The finite-place part of an approximation domain. -/
def FinitePlaceAdmissible {n : ℕ} (L : LocalForms n) (Q : ℕ)
    (c : LocalConstants n) (x : RatVector n) : Prop :=
  AdelicMinkowski.InZOneSix x ∧
    ∀ v, v ≠ Place23.infinite → ∀ i,
      realPlaceNorm v (L v i x) ≤ exponentRadius (Q : ℝ) c v i

/-- The exact real dilation at which a vector enters the Archimedean box. -/
noncomputable def entryScale {n : ℕ} [NeZero n] (L : LocalForms n) (Q : ℕ)
    (c : LocalConstants n) (x : RatVector n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i : Fin n =>
    realPlaceNorm Place23.infinite (L Place23.infinite i x) /
      exponentRadius (Q : ℝ) c Place23.infinite i

theorem exponentRadius_pos_of_one_le {n : ℕ} {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n) (v : Place23) (i : Fin n) :
    0 < exponentRadius (Q : ℝ) c v i := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (Nat.zero_lt_of_lt hQ)

theorem entryScale_nonneg {n : ℕ} [NeZero n] (L : LocalForms n) {Q : ℕ}
    (hQ : 1 ≤ Q) (c : LocalConstants n) (x : RatVector n) :
    0 ≤ entryScale L Q c x := by
  classical
  exact (div_nonneg (realPlaceNorm_nonneg _ _)
      (exponentRadius_pos_of_one_le hQ c _ _).le).trans
    (Finset.le_sup' (fun i : Fin n =>
      realPlaceNorm Place23.infinite (L Place23.infinite i x) /
        exponentRadius (Q : ℝ) c Place23.infinite i) (Finset.mem_univ 0))

theorem entryScale_bounds {n : ℕ} [NeZero n] (L : LocalForms n) {Q : ℕ}
    (hQ : 1 ≤ Q) (c : LocalConstants n) (x : RatVector n) (i : Fin n) :
    realPlaceNorm Place23.infinite (L Place23.infinite i x) ≤
      entryScale L Q c x * exponentRadius (Q : ℝ) c Place23.infinite i := by
  classical
  have hsup :
      realPlaceNorm Place23.infinite (L Place23.infinite i x) /
          exponentRadius (Q : ℝ) c Place23.infinite i ≤ entryScale L Q c x := by
    exact Finset.le_sup' (fun j : Fin n =>
      realPlaceNorm Place23.infinite (L Place23.infinite j x) /
        exponentRadius (Q : ℝ) c Place23.infinite j) (Finset.mem_univ i)
  have hr := exponentRadius_pos_of_one_le hQ c Place23.infinite i
  exact (div_le_iff₀ hr).mp hsup

theorem entryScale_le_iff {n : ℕ} [NeZero n] (L : LocalForms n) {Q : ℕ}
    (hQ : 1 ≤ Q) (c : LocalConstants n) (x : RatVector n) {lambda : ℝ} :
    entryScale L Q c x ≤ lambda ↔
      ∀ i, realPlaceNorm Place23.infinite (L Place23.infinite i x) ≤
        lambda * exponentRadius (Q : ℝ) c Place23.infinite i := by
  classical
  constructor
  · intro h i
    exact (entryScale_bounds L hQ c x i).trans
      (mul_le_mul_of_nonneg_right h
        (exponentRadius_pos_of_one_le hQ c _ _).le)
  · intro h
    unfold entryScale
    apply Finset.sup'_le Finset.univ_nonempty
    intro i hi
    exact (div_le_iff₀ (exponentRadius_pos_of_one_le hQ c _ _)).mpr (h i)

theorem entryScale_pos {n : ℕ} [NeZero n] (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n) {x : RatVector n} (hx : x ≠ 0) :
    0 < entryScale L Q c x := by
  have hLI := hL Place23.infinite
  have hspan : Submodule.span ℚ (Set.range (L Place23.infinite)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hLI]
    simp
  by_contra hnot
  have hzero : entryScale L Q c x = 0 :=
    le_antisymm (not_lt.mp hnot) (entryScale_nonneg L hQ c x)
  have heval : ∀ i, L Place23.infinite i x = 0 := by
    intro i
    have hb := entryScale_bounds L hQ c x i
    rw [hzero, zero_mul] at hb
    have hn := realPlaceNorm_nonneg Place23.infinite
      (L Place23.infinite i x)
    have hz : realPlaceNorm Place23.infinite
        (L Place23.infinite i x) = 0 := le_antisymm hb hn
    have hzq : placeNorm Place23.infinite (L Place23.infinite i x) = 0 := by
      unfold realPlaceNorm at hz
      exact_mod_cast hz
    exact (placeNorm_eq_zero_iff _ _).mp hzq
  have hall : ∀ f ∈ Submodule.span ℚ (Set.range (L Place23.infinite)), f x = 0 := by
    apply Submodule.span_induction
    · rintro f ⟨i, rfl⟩
      exact heval i
    · simp
    · intro f g hf hg hfx hgx
      simp [map_add, hfx, hgx]
    · intro a f hf hfx
      simp [map_smul, hfx]
  have hcoord : ∀ i, x i = 0 := by
    intro i
    let e : RatLinearForm n := LinearMap.proj i
    have he : e ∈ Submodule.span ℚ (Set.range (L Place23.infinite)) := by
      rw [hspan]
      exact Submodule.mem_top
    simpa [e] using hall e he
  exact hx (funext hcoord)

theorem finitePlaceAdmissible_entryScale_mem {n : ℕ} [NeZero n] (L : LocalForms n)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n) {x : RatVector n}
    (hx : FinitePlaceAdmissible L Q c x) :
    x ∈ Erdos407.RankDrop.realSIntegralApproximationDomain L Q c ↔
      entryScale L Q c x ≤ 1 := by
  constructor
  · intro h
    apply (entryScale_le_iff L hQ c x).2
    intro i
    simpa using h.2 Place23.infinite i
  · intro h
    refine ⟨hx.1, ?_⟩
    intro v i
    by_cases hv : v = Place23.infinite
    · subst v
      simpa using (entryScale_le_iff L hQ c x).1 h i
    · exact hx.2 v hv i

theorem realPlaceNorm_six_pow_two (k : ℕ) :
    realPlaceNorm Place23.two ((6 : ℚ) ^ k) = (1 / 2 : ℝ) ^ k := by
  have hq : padicNorm 2 ((6 : ℚ) ^ k) = (1 / 2 : ℚ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, padicNorm.mul, ih, pow_succ]
        congr 1
        have h22 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ :=
          padicNorm.padicNorm_p_of_prime
        have h23 : padicNorm 2 (3 : ℚ) = 1 :=
          padicNorm.padicNorm_of_prime_of_ne (p := 2) (q := 3) (by omega)
        rw [show (6 : ℚ) = 2 * 3 by norm_num, padicNorm.mul, h22, h23]
        norm_num
  unfold realPlaceNorm
  rw [placeNorm_two]
  rw [hq]
  norm_num

theorem realPlaceNorm_six_pow_three (k : ℕ) :
    realPlaceNorm Place23.three ((6 : ℚ) ^ k) = (1 / 3 : ℝ) ^ k := by
  have hq : padicNorm 3 ((6 : ℚ) ^ k) = (1 / 3 : ℚ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, padicNorm.mul, ih, pow_succ]
        congr 1
        have h32 : padicNorm 3 (2 : ℚ) = 1 :=
          padicNorm.padicNorm_of_prime_of_ne (p := 3) (q := 2) (by omega)
        have h33 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ :=
          padicNorm.padicNorm_p_of_prime
        rw [show (6 : ℚ) = 2 * 3 by norm_num, padicNorm.mul, h32, h33]
        norm_num
  unfold realPlaceNorm
  rw [placeNorm_three]
  rw [hq]
  norm_num

/-- Multiplying an integral vector by a large enough power of six makes all
of its finite-place form values fit any prescribed positive radii. -/
theorem exists_sixPow_finitePlaceAdmissible {n : ℕ} (L : LocalForms n)
    {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n) (z : Fin n → ℤ) :
    ∃ k : ℕ, FinitePlaceAdmissible L Q c
      (((6 : ℚ) ^ k) • intCastVec z) := by
  let A : ℕ → Place23 → Fin n → ℝ := fun k v i =>
    realPlaceNorm v ((6 : ℚ) ^ k) *
      realPlaceNorm v (L v i (intCastVec z))
  have htwo : ∀ i, Filter.Tendsto (fun k => A k Place23.two i)
      Filter.atTop (nhds 0) := by
    intro i
    simpa [A, realPlaceNorm_six_pow_two] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1)).mul_const
          (realPlaceNorm Place23.two (L Place23.two i (intCastVec z)))
  have hthree : ∀ i, Filter.Tendsto (fun k => A k Place23.three i)
      Filter.atTop (nhds 0) := by
    intro i
    simpa [A, realPlaceNorm_six_pow_three] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
        (by norm_num : (1 : ℝ) / 3 < 1)).mul_const
          (realPlaceNorm Place23.three (L Place23.three i (intCastVec z)))
  have hevent : ∀ v, v ≠ Place23.infinite → ∀ i,
      ∀ᶠ k : ℕ in Filter.atTop,
        A k v i ≤ exponentRadius (Q : ℝ) c v i := by
    intro v hv i
    fin_cases v
    · exact (hv rfl).elim
    · exact (htwo i).eventually (Iic_mem_nhds
        (exponentRadius_pos_of_one_le hQ c Place23.two i))
    · exact (hthree i).eventually (Iic_mem_nhds
        (exponentRadius_pos_of_one_le hQ c Place23.three i))
  have hall : ∀ᶠ k : ℕ in Filter.atTop, ∀ v,
      v ≠ Place23.infinite → ∀ i,
        A k v i ≤ exponentRadius (Q : ℝ) c v i := by
    apply Filter.eventually_all.2
    intro v
    apply Filter.eventually_all.2
    intro hv
    apply Filter.eventually_all.2
    intro i
    exact hevent v hv i
  obtain ⟨k, hk⟩ := hall.exists
  refine ⟨k, ?_, ?_⟩
  · refine ⟨0, fun i => (6 : ℤ) ^ k * z i, fun i => ?_⟩
    simp [AdelicMinkowski.denominator]
  · intro v hv i
    have hmap : L v i (((6 : ℚ) ^ k) • intCastVec z) =
        (6 : ℚ) ^ k * L v i (intCastVec z) := by
      simp
    rw [hmap, Erdos407.RankDrop.realPlaceNorm_mul]
    exact hk v hv i

/-- Extend a finite independent family by a prescribed finite number of
vectors, provided the resulting cardinality does not exceed the ambient
dimension. -/
theorem exists_linearIndependent_append {n r d : ℕ}
    (x : Fin r → RatVector n) (hx : LinearIndependent ℚ x)
    (hrd : r + d ≤ n) :
    ∃ y : Fin d → RatVector n, LinearIndependent ℚ (Fin.append x y) := by
  induction d with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_⟩
      simpa using hx
  | succ d ih =>
      have hrd' : r + d ≤ n := by omega
      obtain ⟨y, hy⟩ := ih hrd'
      have hlt : r + d < Module.finrank ℚ (RatVector n) := by
        simp
        omega
      obtain ⟨z, hz⟩ := exists_linearIndependent_snoc_of_lt_finrank hy hlt
      refine ⟨Fin.snoc y z, ?_⟩
      simpa only [Fin.append_snoc] using hz

/-- An arbitrary rational vector has a nonzero projectively equivalent
`S`-integral representative satisfying all fixed finite-place inequalities. -/
theorem exists_projectivelyEquivalent_finitePlaceAdmissible {n : ℕ}
    (L : LocalForms n) {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n)
    {y : RatVector n} (hy : y ≠ 0) :
    ∃ a : ℚ, a ≠ 0 ∧ FinitePlaceAdmissible L Q c (a • y) := by
  let z : Fin n → ℤ := Primitive.normalize y
  obtain ⟨k, hk⟩ := exists_sixPow_finitePlaceAdmissible L hQ c z
  let a : ℚ := (6 : ℚ) ^ k * (Primitive.normalizationScale y)⁻¹
  have hs : Primitive.normalizationScale y ≠ 0 :=
    Primitive.normalizationScale_ne_zero hy
  have ha : a ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero hs)
  refine ⟨a, ha, ?_⟩
  have hyrel : y = Primitive.normalizationScale y • intCastVec z := by
    funext i
    have hi := congrFun (Primitive.eq_normalizationScale_smul y) i
    exact hi
  have heq : a • y = ((6 : ℚ) ^ k) • intCastVec z := by
    rw [hyrel]
    simp [a, smul_smul, hs]
  rw [heq]
  exact hk

/-- Complete an independent family to full dimension while requiring every
new vector to satisfy the finite-place part of the approximation box. -/
theorem exists_finitePlaceAdmissible_extension {n r : ℕ}
    (L : LocalForms n) {Q : ℕ} (hQ : 1 ≤ Q) (c : LocalConstants n)
    (x : Fin r → RatVector n) (hx : LinearIndependent ℚ x) (hr : r ≤ n) :
    ∃ y : Fin (n - r) → RatVector n,
      LinearIndependent ℚ (Fin.append x y) ∧
      ∀ j, FinitePlaceAdmissible L Q c (y j) := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_append x hx (by omega : r + (n - r) ≤ n)
  have hy0 : ∀ j, y j ≠ 0 := by
    intro j
    have hne := hy.ne_zero (Fin.natAdd r j)
    simpa [Fin.append_right] using hne
  choose a ha hadm using fun j =>
    exists_projectivelyEquivalent_finitePlaceAdmissible L hQ c (hy0 j)
  let uLow : Fin r → ℚˣ := fun _ => 1
  let uHigh : Fin (n - r) → ℚˣ := fun j => Units.mk0 (a j) (ha j)
  let u : Fin (r + (n - r)) → ℚˣ := Fin.append uLow uHigh
  let y' : Fin (n - r) → RatVector n := fun j => a j • y j
  have heq : u • Fin.append x y = Fin.append x y' := by
    funext i
    by_cases hi : (i : ℕ) < r
    · let j : Fin r := ⟨i, hi⟩
      have hieq : i = Fin.castAdd (n - r) j := by ext; rfl
      rw [hieq]
      simp [u, uLow, y', Fin.append_left]
    · have hir : r ≤ (i : ℕ) := Nat.le_of_not_gt hi
      let j : Fin (n - r) := ⟨(i : ℕ) - r, by omega⟩
      have hieq : i = Fin.natAdd r j := by ext; simp [j]; omega
      rw [hieq]
      simp [u, uHigh, y', Fin.append_right]
  refine ⟨y', ?_, hadm⟩
  rw [← heq]
  exact hy.units_smul u

theorem span_range_eq_span_of_rank_family {n : ℕ}
    (D : Set (RatVector n))
    (x : Fin (rationalSetRank D) → RatVector n)
    (hx : LinearIndependent ℚ x) (hxD : ∀ i, x i ∈ D) :
    Submodule.span ℚ (Set.range x) = Submodule.span ℚ D := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact hxD i
  · rw [finrank_span_eq_card hx]
    unfold rationalSetRank Set.finrank
    exact Fintype.card_fin _

/-- In an independent appended family, every right-hand vector lies outside
the span of the left-hand family. -/
theorem append_right_not_mem_span_left {n r d : ℕ}
    {x : Fin r → RatVector n} {y : Fin d → RatVector n}
    (hxy : LinearIndependent ℚ (Fin.append x y)) (j : Fin d) :
    y j ∉ Submodule.span ℚ (Set.range x) := by
  let e : Fin (r + 1) → Fin (r + d) :=
    Fin.snoc (fun i => Fin.castAdd d i) (Fin.natAdd r j)
  have he : Function.Injective e := by
    apply Fin.snoc_injective_of_injective
    · exact Fin.castAdd_injective r d
    · rintro ⟨i, hi⟩
      have hval : (i : ℕ) = r + (j : ℕ) := congrArg Fin.val hi
      omega
  have hsub : LinearIndependent ℚ ((Fin.append x y) ∘ e) := hxy.comp e he
  have heq : (Fin.append x y) ∘ e = Fin.snoc x (y j) := by
    funext i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp [e, Fin.append_right]
    · simp [e, Fin.append_left]
  rw [heq, linearIndependent_finSnoc] at hsub
  exact hsub.2

theorem monotone_append {r d : ℕ} {a : Fin r → ℝ} {b : Fin d → ℝ}
    (ha : Monotone a) (hb : Monotone b) (hab : ∀ i j, a i ≤ b j) :
    Monotone (Fin.append a b) := by
  intro i j hij
  by_cases hi : (i : ℕ) < r
  · let i' : Fin r := ⟨i, hi⟩
    have hieq : i = Fin.castAdd d i' := by ext; rfl
    rw [hieq, Fin.append_left]
    by_cases hj : (j : ℕ) < r
    · let j' : Fin r := ⟨j, hj⟩
      have hjeq : j = Fin.castAdd d j' := by ext; rfl
      rw [hjeq, Fin.append_left]
      apply ha
      exact Fin.mk_le_mk.mpr hij
    · let j' : Fin d := ⟨(j : ℕ) - r, by omega⟩
      have hjeq : j = Fin.natAdd r j' := by ext; simp [j']; omega
      rw [hjeq, Fin.append_right]
      exact hab i' j'
  · have hir : r ≤ (i : ℕ) := Nat.le_of_not_gt hi
    have hjr : r ≤ (j : ℕ) := hir.trans hij
    let i' : Fin d := ⟨(i : ℕ) - r, by omega⟩
    let j' : Fin d := ⟨(j : ℕ) - r, by omega⟩
    have hieq : i = Fin.natAdd r i' := by ext; simp [i']; omega
    have hjeq : j = Fin.natAdd r j' := by ext; simp [j']; omega
    rw [hieq, hjeq, Fin.append_right, Fin.append_right]
    apply hb
    exact Fin.mk_le_mk.mpr (by simp [i', j']; omega)

theorem linearIndependent_append_perms {n r d : ℕ}
    {x : Fin r → RatVector n} {y : Fin d → RatVector n}
    (hxy : LinearIndependent ℚ (Fin.append x y))
    (sx : Equiv.Perm (Fin r)) (sy : Equiv.Perm (Fin d)) :
    LinearIndependent ℚ (Fin.append (x ∘ sx) (y ∘ sy)) := by
  let s : Equiv.Perm (Fin (r + d)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr sx sy).trans finSumFinEquiv)
  have hs := hxy.comp s s.injective
  have heq : (Fin.append x y) ∘ s = Fin.append (x ∘ sx) (y ∘ sy) := by
    funext i
    obtain ⟨u, rfl⟩ := finSumFinEquiv.surjective i
    cases u with
    | inl i => simp [s, Fin.append_left, Function.comp_def]
    | inr i => simp [s, Fin.append_right, Function.comp_def]
  rw [← heq]
  exact hs

/-- A genuine rank-adapted basis for one rational three-place approximation
domain.  The first `rank` vectors span the scale-one domain, and the remaining
vectors enter strictly after scale one. -/
structure AdaptedBasisCertificate {n : ℕ} (L : LocalForms n) (Q : ℕ)
    (c : LocalConstants n) where
  rank : ℕ
  rank_eq : rank = Erdos407.RankDrop.realSApproximationRank L Q c
  rank_le : rank ≤ n
  lambda : Fin n → ℝ
  point : Fin n → RatVector n
  lambda_pos : ∀ j, 0 < lambda j
  lambda_mono : Monotone lambda
  independent : LinearIndependent ℚ point
  sIntegral : ∀ j, AdelicMinkowski.InZOneSix (point j)
  local_bound : ∀ j v i,
    realPlaceNorm v (L v i (point j)) ≤
      placeScale v (lambda j) * exponentRadius (Q : ℝ) c v i
  low_le_one : ∀ j : Fin n, (j : ℕ) < rank → lambda j ≤ 1
  high_gt_one : ∀ j : Fin n, rank ≤ (j : ℕ) → 1 < lambda j
  prefix_span :
    Submodule.span ℚ (Set.range (point ∘ Fin.castLE rank_le)) =
      Erdos407.RankDrop.realSApproximationSpan L Q c

theorem exists_adaptedBasisCertificate {n : ℕ} (hn : 0 < n)
    (L : LocalForms n) (hL : IsNonsingularFamily L) {Q : ℕ}
    (hQ : 1 ≤ Q) (c : LocalConstants n) :
    Nonempty (AdaptedBasisCertificate L Q c) := by
  letI : NeZero n := ⟨hn.ne'⟩
  let D := Erdos407.RankDrop.realSIntegralApproximationDomain L Q c
  let R := rationalSetRank D
  have hR : R ≤ n := rationalSetRank_le_dimension D
  obtain ⟨x, hx, hxD⟩ := exists_independent_family_card_rationalSetRank D
  have hspan : Submodule.span ℚ (Set.range x) =
      Erdos407.RankDrop.realSApproximationSpan L Q c := by
    exact span_range_eq_span_of_rank_family D x hx hxD
  obtain ⟨y, hxy, hyadm⟩ :=
    exists_finitePlaceAdmissible_extension L hQ c x hx hR
  let lx : Fin R → ℝ := fun j => entryScale L Q c (x j)
  let ly : Fin (n - R) → ℝ := fun j => entryScale L Q c (y j)
  let sx : Equiv.Perm (Fin R) := Tuple.sort lx
  let sy : Equiv.Perm (Fin (n - R)) := Tuple.sort ly
  let xs : Fin R → RatVector n := x ∘ sx
  let ys : Fin (n - R) → RatVector n := y ∘ sy
  let ls : Fin (R + (n - R)) → ℝ := Fin.append (lx ∘ sx) (ly ∘ sy)
  let ps : Fin (R + (n - R)) → RatVector n := Fin.append xs ys
  have hsum : R + (n - R) = n := Nat.add_sub_of_le hR
  let e : Fin n ≃o Fin (R + (n - R)) := Fin.castOrderIso hsum.symm
  let lambda : Fin n → ℝ := ls ∘ e
  let point : Fin n → RatVector n := ps ∘ e
  have hxadm : ∀ j, FinitePlaceAdmissible L Q c (x j) := by
    intro j
    refine ⟨(hxD j).1, ?_⟩
    intro v hv i
    exact (hxD j).2 v i
  have hlxle : ∀ j, lx j ≤ 1 := by
    intro j
    exact (finitePlaceAdmissible_entryScale_mem L hQ c (hxadm j)).1 (hxD j)
  have hysOut : ∀ j, y j ∉ Submodule.span ℚ (Set.range x) :=
    append_right_not_mem_span_left hxy
  have hlygt : ∀ j, 1 < ly j := by
    intro j
    apply lt_of_not_ge
    intro hle
    have hyD : y j ∈ D :=
      (finitePlaceAdmissible_entryScale_mem L hQ c (hyadm j)).2 hle
    apply hysOut j
    rw [hspan]
    exact Erdos407.RankDrop.mem_realSApproximationSpan hyD
  have hlxpos : ∀ j, 0 < lx j := by
    intro j
    exact entryScale_pos L hL hQ c (hx.ne_zero j)
  have hlypos : ∀ j, 0 < ly j := by
    intro j
    exact entryScale_pos L hL hQ c
      ((append_right_not_mem_span_left hxy j) ∘ fun h => by simp [h])
  have hlsmono : Monotone ls := by
    apply monotone_append
    · exact Tuple.monotone_sort lx
    · exact Tuple.monotone_sort ly
    · intro i j
      exact (hlxle (sx i)).trans (hlygt (sy j)).le
  have hpsLI : LinearIndependent ℚ ps :=
    linearIndependent_append_perms hxy sx sy
  have hscale : ∀ j, lambda j = entryScale L Q c (point j) := by
    intro j
    by_cases hj : ((e j : Fin (R + (n - R))) : ℕ) < R
    · let i : Fin R := ⟨e j, hj⟩
      have heji : e j = Fin.castAdd (n - R) i := by ext; rfl
      rw [show lambda j = ls (e j) by rfl,
        show point j = ps (e j) by rfl, heji]
      simp [ls, ps, lx, xs, Fin.append_left]
    · have hebound : (e j : ℕ) < R + (n - R) := (e j).isLt
      have hge : R ≤ (e j : ℕ) := Nat.le_of_not_gt hj
      have hej : (e j : ℕ) = (j : ℕ) := rfl
      let i : Fin (n - R) := ⟨(e j : ℕ) - R, by omega⟩
      have heji : e j = Fin.natAdd R i := by ext; simp [i]; omega
      rw [show lambda j = ls (e j) by rfl,
        show point j = ps (e j) by rfl, heji]
      simp [ls, ps, ly, ys, Fin.append_right]
  refine ⟨{
    rank := R
    rank_eq := ?_
    rank_le := hR
    lambda := lambda
    point := point
    lambda_pos := ?_
    lambda_mono := ?_
    independent := ?_
    sIntegral := ?_
    local_bound := ?_
    low_le_one := ?_
    high_gt_one := ?_
    prefix_span := ?_ }⟩
  · rfl
  · intro j
    change 0 < ls (e j)
    by_cases hj : ((e j : Fin (R + (n - R))) : ℕ) < R
    · let i : Fin R := ⟨e j, hj⟩
      have heji : e j = Fin.castAdd (n - R) i := by ext; rfl
      rw [heji]
      simpa [ls, Fin.append_left] using hlxpos (sx i)
    · have hebound : (e j : ℕ) < R + (n - R) := (e j).isLt
      have hge : R ≤ (e j : ℕ) := Nat.le_of_not_gt hj
      have hej : (e j : ℕ) = (j : ℕ) := rfl
      let i : Fin (n - R) := ⟨(e j : ℕ) - R, by omega⟩
      have heji : e j = Fin.natAdd R i := by ext; simp [i]; omega
      rw [heji]
      simpa [ls, Fin.append_right] using hlypos (sy i)
  · exact hlsmono.comp e.monotone
  · exact hpsLI.comp e e.injective
  · intro j
    change AdelicMinkowski.InZOneSix (ps (e j))
    by_cases hj : ((e j : Fin (R + (n - R))) : ℕ) < R
    · let i : Fin R := ⟨e j, hj⟩
      have heji : e j = Fin.castAdd (n - R) i := by ext; rfl
      rw [heji]
      simpa [ps, xs, Fin.append_left] using (hxadm (sx i)).1
    · have hebound : (e j : ℕ) < R + (n - R) := (e j).isLt
      have hge : R ≤ (e j : ℕ) := Nat.le_of_not_gt hj
      have hej : (e j : ℕ) = (j : ℕ) := rfl
      let i : Fin (n - R) := ⟨(e j : ℕ) - R, by omega⟩
      have heji : e j = Fin.natAdd R i := by ext; simp [i]; omega
      rw [heji]
      simpa [ps, ys, Fin.append_right] using (hyadm (sy i)).1
  · intro j v i
    by_cases hv : v = Place23.infinite
    · subst v
      simp only [placeScale_infinite]
      rw [hscale j]
      exact entryScale_bounds L hQ c (point j) i
    · simp only [placeScale, if_neg hv, one_mul]
      change realPlaceNorm v (L v i (ps (e j))) ≤ _
      by_cases hj : ((e j : Fin (R + (n - R))) : ℕ) < R
      · let k : Fin R := ⟨e j, hj⟩
        have hejk : e j = Fin.castAdd (n - R) k := by ext; rfl
        rw [hejk]
        simpa [ps, xs, Fin.append_left] using (hxadm (sx k)).2 v hv i
      · have hebound : (e j : ℕ) < R + (n - R) := (e j).isLt
        have hge : R ≤ (e j : ℕ) := Nat.le_of_not_gt hj
        have hej : (e j : ℕ) = (j : ℕ) := rfl
        let k : Fin (n - R) := ⟨(e j : ℕ) - R, by omega⟩
        have hejk : e j = Fin.natAdd R k := by ext; simp [k]; omega
        rw [hejk]
        simpa [ps, ys, Fin.append_right] using (hyadm (sy k)).2 v hv i
  · intro j hj
    have hej : (e j : ℕ) = (j : ℕ) := rfl
    have helo : ((e j : Fin (R + (n - R))) : ℕ) < R := by simpa [hej] using hj
    let i : Fin R := ⟨e j, helo⟩
    have heji : e j = Fin.castAdd (n - R) i := by ext; rfl
    change ls (e j) ≤ 1
    rw [heji]
    simpa [ls, Fin.append_left] using hlxle (sx i)
  · intro j hj
    have hej : (e j : ℕ) = (j : ℕ) := rfl
    have hehi : R ≤ ((e j : Fin (R + (n - R))) : ℕ) := by simpa [hej] using hj
    have hebound : (e j : ℕ) < R + (n - R) := (e j).isLt
    let i : Fin (n - R) := ⟨(e j : ℕ) - R, by omega⟩
    have heji : e j = Fin.natAdd R i := by ext; simp [i]; omega
    change 1 < ls (e j)
    rw [heji]
    simpa [ls, Fin.append_right] using hlygt (sy i)
  · have hprefix : point ∘ Fin.castLE hR = xs := by
      funext i
      change ps (e (Fin.castLE hR i)) = xs i
      have heq : e (Fin.castLE hR i) = Fin.castAdd (n - R) i := by ext; rfl
      rw [heq]
      simp [ps, xs, Fin.append_left]
    rw [hprefix]
    have hsrange : Set.range xs = Set.range x := by
      apply Set.Subset.antisymm
      · rintro _ ⟨i, rfl⟩
        exact ⟨sx i, rfl⟩
      · rintro _ ⟨i, rfl⟩
        exact ⟨sx.symm i, by simp [xs]⟩
    rw [hsrange]
    exact hspan

end AdelicMinima

end Erdos407.PadicSubspace
