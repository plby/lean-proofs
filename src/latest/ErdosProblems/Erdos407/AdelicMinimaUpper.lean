/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AdelicSuccessiveMinima
import ErdosProblems.Erdos407.FinitePlaceLattice
import ErdosProblems.Erdos407.MinkowskiSecondInduction

/-!
# Upper product certificates for the three-place successive minima

This file is the integration layer between the finite-place congruence
lattice, the real box form of Minkowski's second theorem, and the
rank-adapted certificate used in the Subspace Theorem argument.

The reciprocal in `product_le` is important.  The finite-place lattice has
covolume comparable to the reciprocal of the finite radii, while the real
box theorem divides by the product of the Archimedean radii.  Thus the final
factor is the reciprocal of the product of *all* local radii, namely
`Q ^ (-(∑ v, ∑ i, c v i))`.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators

namespace AdelicMinimaUpper

open Erdos407 HeightBoxes
open AdelicMinima
open Module Submodule

/-! ## Product-nonincreasing basis exchange -/

/-- If a new vector is outside the span of a protected part of a full
family, then it can replace one of the unprotected vectors without destroying
linear independence.  This is the one-step exchange used to retain every
original scale-at-most-one point while adjoining a basis of the complete
scale-one domain. -/
theorem exists_exchange_index
    {K : Type*} [Field K] {n : ℕ}
    (p : Fin n → Fin n → K) (hp : LinearIndependent K p)
    (kept : Set (Fin n)) (x : Fin n → K)
    (hx : x ∉ Submodule.span K (p '' kept)) :
    ∃ i : Fin n, i ∉ kept ∧
      LinearIndependent K (Function.update p i x) := by
  classical
  let b : Basis (Fin n) K (Fin n → K) :=
    basisOfPiSpaceOfLinearIndependent hp
  have hb : (b : Fin n → Fin n → K) = p :=
    coe_basisOfPiSpaceOfLinearIndependent hp
  have hsupp : ¬ ((b.repr x).support : Set (Fin n)) ⊆ kept := by
    intro hs
    apply hx
    rw [← hb]
    exact (b.mem_span_image).2 hs
  obtain ⟨i, hi, hiProtected⟩ := Set.not_subset.mp hsupp
  have hcoeff : b.repr x i ≠ 0 := Finsupp.mem_support_iff.mp hi
  refine ⟨i, hiProtected, hp.update i x ?_⟩
  refine ⟨1, by simp, b.repr x, ?_, ?_⟩
  · simpa [mem_nonZeroDivisors_iff] using hcoeff
  · rw [one_smul, ← hb]
    exact (b.linearCombination_repr x).symm

/-- Replacing one positive scale by a smaller nonnegative scale cannot
increase their product. -/
theorem prod_update_le
    {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (x : ℝ)
    (ha : ∀ j, 0 ≤ a j) (_hx : 0 ≤ x) (hxi : x ≤ a i) :
    ∏ j, Function.update a i x j ≤ ∏ j, a j := by
  classical
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  calc
    x * ∏ j ∈ Finset.univ \ {i}, a j ≤
        a i * ∏ j ∈ Finset.univ \ {i}, a j :=
      mul_le_mul_of_nonneg_right hxi
        (Finset.prod_nonneg fun j _ ↦ ha j)
    _ = ∏ j, a j := by
      rw [Finset.sdiff_singleton_eq_erase,
        Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]

/-- Starting from a full positive weighted family, retain all of its vectors
of weight at most one and exchange in a spanning family of the complete low
subspace.  Every exchange removes a vector of weight greater than one and
inserts one of weight at most one.  The resulting full family therefore has
no larger weight product, and its low vectors span exactly `D`.

This is the generic finite-dimensional step which turns a product-controlled
family into genuine rank-threshold data. -/
theorem exists_product_adapted_exchange
    {K : Type*} [Field K] {n r : ℕ}
    (p : Fin n → Fin n → K) (hp : LinearIndependent K p)
    (weight : (Fin n → K) → ℝ) (D : Submodule K (Fin n → K))
    (Good : (Fin n → K) → Prop)
    (hp_good : ∀ i, Good (p i))
    (hp_pos : ∀ i, 0 < weight (p i))
    (hp_low_mem : ∀ i, weight (p i) ≤ 1 → p i ∈ D)
    (x : Fin r → Fin n → K)
    (hx_good : ∀ j, Good (x j))
    (hx_pos : ∀ j, 0 < weight (x j))
    (hx_le : ∀ j, weight (x j) ≤ 1)
    (hx_mem : ∀ j, x j ∈ D)
    (hx_span : Submodule.span K (Set.range x) = D) :
    ∃ q : Fin n → Fin n → K,
      LinearIndependent K q ∧
      (∀ i, Good (q i)) ∧
      (∏ i, weight (q i)) ≤ ∏ i, weight (p i) ∧
      Submodule.span K (q '' {i | weight (q i) ≤ 1}) = D := by
  classical
  let State : Finset (Fin r) → Prop := fun processed ↦
    ∃ (q : Fin n → Fin n → K) (kept : Finset (Fin n)),
      LinearIndependent K q ∧
      (∀ i, Good (q i)) ∧
      (∀ i, i ∈ kept →
        q i ∈ D ∧ 0 < weight (q i) ∧ weight (q i) ≤ 1) ∧
      (∀ i, i ∉ kept → q i = p i ∧ 1 < weight (q i)) ∧
      (∀ j, j ∈ processed →
        x j ∈ Submodule.span K (q '' (kept : Set (Fin n)))) ∧
      (∏ i, weight (q i)) ≤ ∏ i, weight (p i)
  have hState : ∀ processed : Finset (Fin r), State processed := by
    intro processed
    induction processed using Finset.induction with
    | empty =>
        let kept : Finset (Fin n) :=
          Finset.univ.filter fun i ↦ weight (p i) ≤ 1
        refine ⟨p, kept, hp, hp_good, ?_, ?_, ?_, le_rfl⟩
        · intro i hi
          have hi' : weight (p i) ≤ 1 := (Finset.mem_filter.mp hi).2
          exact ⟨hp_low_mem i hi', hp_pos i, hi'⟩
        · intro i hi
          have hi' : ¬ weight (p i) ≤ 1 := by
            intro h
            exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
          exact ⟨rfl, lt_of_not_ge hi'⟩
        · simp
    | @insert j processed hj ih =>
        obtain ⟨q, kept, hq, hqgood, hkept, hout, hprocessed, hprod⟩ := ih
        by_cases hjspan :
            x j ∈ Submodule.span K (q '' (kept : Set (Fin n)))
        · refine ⟨q, kept, hq, hqgood, hkept, hout, ?_, hprod⟩
          intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact hjspan
          · exact hprocessed k hk
        · obtain ⟨i, hi, hupdate⟩ :=
            exists_exchange_index q hq (kept : Set (Fin n)) (x j) hjspan
          let q' : Fin n → Fin n → K := Function.update q i (x j)
          let kept' : Finset (Fin n) := insert i kept
          refine ⟨q', kept', hupdate, ?_, ?_, ?_, ?_, ?_⟩
          · intro k
            by_cases hki : k = i
            · subst k
              simpa [q'] using hx_good j
            · simpa [q', hki] using hqgood k
          · intro k hk
            rcases Finset.mem_insert.mp hk with hki | hkold
            · subst k
              simp only [q', Function.update_self]
              exact ⟨hx_mem j, hx_pos j, hx_le j⟩
            · have hki : k ≠ i := by
                intro h
                subst k
                exact hi hkold
              simpa [q', hki] using hkept k hkold
          · intro k hk
            have hki : k ≠ i := by
              intro h
              subst k
              exact hk (Finset.mem_insert_self i kept)
            have hkold : k ∉ kept := by
              intro h
              exact hk (Finset.mem_insert_of_mem h)
            simpa [q', hki] using hout k hkold
          · intro k hk
            have holdSpan :
                Submodule.span K (q '' (kept : Set (Fin n))) ≤
                  Submodule.span K (q' '' (kept' : Set (Fin n))) := by
              apply Submodule.span_mono
              rintro y ⟨a, ha, rfl⟩
              have hai : a ≠ i := by
                intro h
                subst a
                exact hi ha
              refine ⟨a, Finset.mem_insert_of_mem ha, ?_⟩
              simp [q', hai]
            rcases Finset.mem_insert.mp hk with hkj | hkold
            · subst k
              apply Submodule.subset_span
              refine ⟨i, Finset.mem_insert_self i kept, ?_⟩
              simp [q']
            · exact holdSpan (hprocessed k hkold)
          · have hq_nonneg : ∀ k, 0 ≤ weight (q k) := by
              intro k
              by_cases hk : k ∈ kept
              · exact (hkept k hk).2.1.le
              · exact (zero_lt_one.trans (hout k hk).2).le
            have hwi : weight (x j) ≤ weight (q i) :=
              (hx_le j).trans (hout i hi).2.le
            have hupd :
                (∏ k, weight (q' k)) ≤ ∏ k, weight (q k) := by
              have heq : (fun k ↦ weight (q' k)) =
                  Function.update (fun k ↦ weight (q k)) i (weight (x j)) := by
                funext k
                by_cases hki : k = i
                · subst k
                  simp [q']
                · simp [q', hki]
              rw [heq]
              exact prod_update_le (fun k ↦ weight (q k)) i (weight (x j))
                hq_nonneg (hx_pos j).le hwi
            exact hupd.trans hprod
  obtain ⟨q, kept, hq, hqgood, hkept, hout, hprocessed, hprod⟩ :=
    hState Finset.univ
  refine ⟨q, hq, hqgood, hprod, ?_⟩
  have hlow : {i | weight (q i) ≤ 1} = (kept : Set (Fin n)) := by
    ext i
    constructor
    · intro hi
      by_contra hik
      exact (not_lt_of_ge hi) (hout i hik).2
    · intro hi
      exact (hkept i hi).2.2
  rw [hlow]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    exact (hkept i hi).1
  · rw [← hx_span]
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    exact hprocessed j (Finset.mem_univ j)

/-! ## The adelic scale-one exchange -/

/-- The minimal downstream interface required from the geometric-of-numbers
construction: a full finite-place-admissible rational family together with a
bound for the product of its exact Archimedean entry scales. -/
structure RawEntryScaleProductCertificate
    {n : ℕ} [NeZero n] (L : LocalForms n) (Q : ℕ)
    (c : LocalConstants n) (bound : ℝ) where
  point : Fin n → (Fin n → ℚ)
  independent : LinearIndependent ℚ point
  finitePlaceAdmissible : ∀ i, FinitePlaceAdmissible L Q c (point i)
  product_le : (∏ i, entryScale L Q c (point i)) ≤ bound

/-! ## Archimedean evaluation coordinates -/

/-- The real coefficient matrix of the Archimedean family of rational
linear forms. -/
noncomputable def archimedeanFormMatrix {n : ℕ} (L : LocalForms n) :
    Matrix (Fin n) (Fin n) ℝ :=
  (Erdos407.PadicSubspace.formMatrix L Place23.infinite).map (Rat.castHom ℝ)

@[simp] theorem archimedeanFormMatrix_apply {n : ℕ} (L : LocalForms n)
    (i k : Fin n) :
    archimedeanFormMatrix L i k =
      (L Place23.infinite i (Pi.single k 1) : ℝ) := rfl

theorem archimedeanFormMatrix_det_ne_zero {n : ℕ} {L : LocalForms n}
    (hL : IsNonsingularFamily L) :
    (archimedeanFormMatrix L).det ≠ 0 := by
  change ((Erdos407.PadicSubspace.formMatrix L Place23.infinite).map
    (fun x : ℚ ↦ (x : ℝ))).det ≠ 0
  rw [← Rat.cast_det]
  exact_mod_cast Erdos407.PadicSubspace.formMatrix_det_ne_zero hL Place23.infinite

/-- Evaluation by all Archimedean local forms, after extending their
rational coefficient matrix to `ℝ`. -/
noncomputable def archimedeanEvaluationEquiv {n : ℕ} (L : LocalForms n)
    (hL : IsNonsingularFamily L) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (archimedeanFormMatrix L).toLinearEquiv'
    ((archimedeanFormMatrix L).invertibleOfIsUnitDet
      (isUnit_iff_ne_zero.mpr (archimedeanFormMatrix_det_ne_zero hL)))

@[simp] theorem archimedeanEvaluationEquiv_apply {n : ℕ}
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    (x : Fin n → ℝ) (i : Fin n) :
    archimedeanEvaluationEquiv L hL x i =
      ∑ k, archimedeanFormMatrix L i k * x k := by
  rfl

/-- A real lattice basis transported into Archimedean form-evaluation
coordinates. -/
noncomputable def archimedeanEvaluationBasis {n : ℕ} (L : LocalForms n)
    (hL : IsNonsingularFamily L) (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  b.map (archimedeanEvaluationEquiv L hL)

@[simp] theorem archimedeanEvaluationBasis_apply {n : ℕ}
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) (j i : Fin n) :
    archimedeanEvaluationBasis L hL b j i =
      ∑ k, archimedeanFormMatrix L i k * b j k := by
  simp [archimedeanEvaluationBasis]

/-- Determinant change under Archimedean evaluation coordinates. -/
theorem abs_det_archimedeanEvaluationBasis {n : ℕ}
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    |(Matrix.of (archimedeanEvaluationBasis L hL b)).det| =
      |(Matrix.of b).det| * |(archimedeanFormMatrix L).det| := by
  have hmatrix : Matrix.of (archimedeanEvaluationBasis L hL b) =
      Matrix.of b * (archimedeanFormMatrix L).transpose := by
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  rw [hmatrix, Matrix.det_mul, Matrix.det_transpose, abs_mul]

theorem archimedeanEvaluationEquiv_ratCast {n : ℕ}
    (L : LocalForms n) (hL : IsNonsingularFamily L)
    (x : Fin n → ℚ) (i : Fin n) :
    archimedeanEvaluationEquiv L hL (fun k ↦ (x k : ℝ)) i =
      (L Place23.infinite i x : ℝ) := by
  rw [archimedeanEvaluationEquiv_apply,
    Erdos407.PadicSubspace.linearForm_eq_sum_coeff]
  push_cast
  rfl

/-- Map a real Minkowski certificate for the Archimedean image of a rational
lattice basis back to rational points.  The same integral coefficients are
used on the rational basis.  Exact entry scales can only decrease relative
to the geometric scales, so the product bound is preserved. -/
noncomputable def rawEntryScaleProductCertificate_of_realCertificate
    {n : ℕ} [NeZero n] (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n)
    (qb : Fin n → (Fin n → ℚ))
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (hb : ∀ j k, b j k = (qb j k : ℝ))
    (hadmissible : ∀ x : Fin n → ℚ,
      (∃ z : Fin n → ℤ, x = ∑ j, (z j : ℚ) • qb j) →
        FinitePlaceAdmissible L Q c x)
    {bound : ℝ}
    (C : Erdos407.AdelicMinkowski.SuccessiveProductCertificate
      (Submodule.span ℤ
        (Set.range (archimedeanEvaluationBasis L hL b))).toAddSubgroup
      (fun i ↦ exponentRadius (Q : ℝ) c Place23.infinite i) bound) :
    RawEntryScaleProductCertificate L Q c bound := by
  classical
  have hcoeff : ∀ i, ∃ z : Fin n → ℤ,
      C.point i = ∑ j, (z j) • archimedeanEvaluationBasis L hL b j := by
    intro i
    have hi := C.point_mem i
    change C.point i ∈ Submodule.span ℤ
      (Set.range (archimedeanEvaluationBasis L hL b)) at hi
    rw [Submodule.mem_span_range_iff_exists_fun] at hi
    obtain ⟨z, hz⟩ := hi
    exact ⟨z, hz.symm⟩
  choose z hz using hcoeff
  let q : Fin n → (Fin n → ℚ) := fun i ↦
    ∑ j, (z i j : ℚ) • qb j
  have hcast : ∀ i, (fun k ↦ (q i k : ℝ)) =
      ∑ j, (z i j) • b j := by
    intro i
    funext k
    simp only [q, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Int.cast_sum, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb]
    simpa [smul_eq_mul] using
      (Int.cast_smul_eq_zsmul ℝ (z i j) (qb j k : ℝ)).symm
  have heval : ∀ i,
      archimedeanEvaluationEquiv L hL (fun k ↦ (q i k : ℝ)) = C.point i := by
    intro i
    calc
      archimedeanEvaluationEquiv L hL (fun k ↦ (q i k : ℝ)) =
          archimedeanEvaluationEquiv L hL (∑ j, (z i j) • b j) := by
        rw [hcast i]
      _ = ∑ j, (z i j) • archimedeanEvaluationEquiv L hL (b j) := by
        rw [map_sum]
        simp_rw [map_zsmul]
      _ = ∑ j, (z i j) • archimedeanEvaluationBasis L hL b j := by
        rfl
      _ = C.point i := (hz i).symm
  have hq_independent : LinearIndependent ℚ q := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let gR : Fin n → ℝ := fun j ↦ (g j : ℝ)
    have hreal : ∑ j, gR j • C.point j = 0 := by
      calc
        ∑ j, gR j • C.point j =
            ∑ j, gR j • archimedeanEvaluationEquiv L hL
              (fun k ↦ (q j k : ℝ)) := by simp_rw [heval]
        _ = archimedeanEvaluationEquiv L hL
              (∑ j, gR j • (fun k ↦ (q j k : ℝ))) := by
          rw [map_sum]
          simp_rw [map_smul]
        _ = archimedeanEvaluationEquiv L hL 0 := by
          congr 1
          funext k
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gR,
            Pi.zero_apply]
          have hk := congrFun hg k
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            Pi.zero_apply] at hk
          exact_mod_cast hk
        _ = 0 := map_zero _
    have hi := (Fintype.linearIndependent_iff.mp C.independent) gR hreal i
    change (g i : ℝ) = 0 at hi
    exact_mod_cast hi
  have hq_admissible : ∀ i, FinitePlaceAdmissible L Q c (q i) := by
    intro i
    apply hadmissible (q i)
    exact ⟨z i, rfl⟩
  have hscale : ∀ i, entryScale L Q c (q i) ≤ C.scale i := by
    intro i
    apply (entryScale_le_iff L hQ c (q i)).2
    intro k
    have hm := C.mem_scaledBox i
    rw [HeightBoxes.realPlaceNorm, Erdos407.PadicSubspace.placeNorm_infinite,
      Rat.cast_abs]
    change |(L Place23.infinite k (q i) : ℝ)| ≤ _
    rw [← archimedeanEvaluationEquiv_ratCast L hL (q i) k,
      heval i]
    exact (abs_le.mpr ⟨hm.1 k, hm.2 k⟩)
  refine {
    point := q
    independent := hq_independent
    finitePlaceAdmissible := hq_admissible
    product_le := ?_ }
  exact (Finset.prod_le_prod
    (fun i _ ↦ entryScale_nonneg L hQ c (q i))
    (fun i _ ↦ hscale i)).trans C.product_le

/-- Any full finite-place-admissible family can be exchanged, without
increasing the product of its exact Archimedean entry scales, so that its
scale-at-most-one vectors span the complete adelic approximation domain.

This theorem is the interface needed by a coarse Minkowski product theorem:
the input family need not already know anything about successive minima or
the rank-one threshold. -/
theorem exists_entryScale_adapted_exchange
    {n : ℕ} [NeZero n] (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n) (p : Fin n → (Fin n → ℚ))
    (hp : LinearIndependent ℚ p)
    (hp_admissible : ∀ i, FinitePlaceAdmissible L Q c (p i)) :
    ∃ q : Fin n → (Fin n → ℚ),
      LinearIndependent ℚ q ∧
      (∀ i, FinitePlaceAdmissible L Q c (q i)) ∧
      (∏ i, entryScale L Q c (q i)) ≤
        ∏ i, entryScale L Q c (p i) ∧
      Submodule.span ℚ (q '' {i | entryScale L Q c (q i) ≤ 1}) =
        Erdos407.RankDrop.realSApproximationSpan L Q c := by
  let D : Set (Fin n → ℚ) :=
    Erdos407.RankDrop.realSIntegralApproximationDomain L Q c
  obtain ⟨x, hx, hxD⟩ :=
    exists_independent_family_card_rationalSetRank D
  have hx_span : Submodule.span ℚ (Set.range x) =
      Erdos407.RankDrop.realSApproximationSpan L Q c := by
    exact span_range_eq_span_of_rank_family D x hx hxD
  have hx_admissible : ∀ j, FinitePlaceAdmissible L Q c (x j) := by
    intro j
    exact ⟨(hxD j).1, fun v hv i ↦ (hxD j).2 v i⟩
  have hx_pos : ∀ j, 0 < entryScale L Q c (x j) := by
    intro j
    exact entryScale_pos L hL hQ c (hx.ne_zero j)
  have hx_le : ∀ j, entryScale L Q c (x j) ≤ 1 := by
    intro j
    exact (finitePlaceAdmissible_entryScale_mem L hQ c
      (hx_admissible j)).1 (hxD j)
  have hp_pos : ∀ i, 0 < entryScale L Q c (p i) := by
    intro i
    exact entryScale_pos L hL hQ c (hp.ne_zero i)
  have hp_low_mem : ∀ i, entryScale L Q c (p i) ≤ 1 →
      p i ∈ Erdos407.RankDrop.realSApproximationSpan L Q c := by
    intro i hi
    apply Erdos407.RankDrop.mem_realSApproximationSpan
    exact (finitePlaceAdmissible_entryScale_mem L hQ c
      (hp_admissible i)).2 hi
  exact exists_product_adapted_exchange p hp
    (entryScale L Q c)
    (Erdos407.RankDrop.realSApproximationSpan L Q c)
    (FinitePlaceAdmissible L Q c) hp_admissible hp_pos hp_low_mem
    x hx_admissible hx_pos hx_le
    (fun j ↦ Erdos407.RankDrop.mem_realSApproximationSpan (hxD j)) hx_span

/-- Sorting a full admissible family whose exact low vectors already span
the approximation subspace produces an `AdaptedBasisCertificate`.  The
sorting is only a permutation, so its scale product is unchanged. -/
theorem exists_adaptedBasisCertificate_of_entryScale_span
    {n : ℕ} [NeZero n] (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n) (q : Fin n → (Fin n → ℚ))
    (hq : LinearIndependent ℚ q)
    (hq_admissible : ∀ i, FinitePlaceAdmissible L Q c (q i))
    (hq_span :
      Submodule.span ℚ (q '' {i | entryScale L Q c (q i) ≤ 1}) =
        Erdos407.RankDrop.realSApproximationSpan L Q c) :
    ∃ A : AdaptedBasisCertificate L Q c,
      (∏ i, A.lambda i) = ∏ i, entryScale L Q c (q i) := by
  classical
  let R := Erdos407.RankDrop.realSApproximationRank L Q c
  have hR : R ≤ n :=
    Erdos407.RankDrop.realSApproximationRank_le_dimension L Q c
  let ell : Fin n → ℝ := fun i ↦ entryScale L Q c (q i)
  let s : Equiv.Perm (Fin n) := Tuple.sort ell
  let lambda : Fin n → ℝ := ell ∘ s
  let point : Fin n → (Fin n → ℚ) := q ∘ s
  have hq_pos : ∀ i, 0 < ell i := by
    intro i
    exact entryScale_pos L hL hQ c (hq.ne_zero i)
  have hlambda_mono : Monotone lambda := Tuple.monotone_sort ell
  let lowFamily : {i : Fin n // ell i ≤ 1} → (Fin n → ℚ) :=
    fun i ↦ q i
  have hlow_li : LinearIndependent ℚ lowFamily :=
    hq.comp (fun i : {i : Fin n // ell i ≤ 1} ↦ (i : Fin n))
      Subtype.val_injective
  have hlow_range : Set.range lowFamily = q '' {i | ell i ≤ 1} := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hlow_span : Submodule.span ℚ (Set.range lowFamily) =
      Erdos407.RankDrop.realSApproximationSpan L Q c := by
    rw [hlow_range]
    simpa [ell] using hq_span
  have hcard_low :
      (Finset.univ.filter fun i : Fin n ↦ ell i ≤ 1).card = R := by
    calc
      (Finset.univ.filter fun i : Fin n ↦ ell i ≤ 1).card =
          Fintype.card {i : Fin n // ell i ≤ 1} :=
        (Fintype.card_subtype fun i : Fin n ↦ ell i ≤ 1).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range lowFamily)) :=
        (finrank_span_eq_card hlow_li).symm
      _ = Module.finrank ℚ
          (Erdos407.RankDrop.realSApproximationSpan L Q c) := by rw [hlow_span]
      _ = R := rfl
  let lowEquiv : {i : Fin n // lambda i ≤ 1} ≃
      {i : Fin n // ell i ≤ 1} :=
    s.subtypeEquiv fun _ ↦ Iff.rfl
  have hcard_sorted :
      (Finset.univ.filter fun i : Fin n ↦ lambda i ≤ 1).card = R := by
    calc
      (Finset.univ.filter fun i : Fin n ↦ lambda i ≤ 1).card =
          Fintype.card {i : Fin n // lambda i ≤ 1} :=
        (Fintype.card_subtype fun i : Fin n ↦ lambda i ≤ 1).symm
      _ = Fintype.card {i : Fin n // ell i ≤ 1} :=
        Fintype.card_congr lowEquiv
      _ = (Finset.univ.filter fun i : Fin n ↦ ell i ≤ 1).card :=
        Fintype.card_subtype fun i : Fin n ↦ ell i ≤ 1
      _ = R := hcard_low
  have hlow : ∀ j : Fin n, (j : ℕ) < R → lambda j ≤ 1 := by
    intro j hj
    apply (Tuple.lt_card_le_iff_apply_le_of_monotone hlambda_mono).1
    simpa [hcard_sorted] using hj
  have hhigh : ∀ j : Fin n, R ≤ (j : ℕ) → 1 < lambda j := by
    intro j hj
    apply lt_of_not_ge
    intro hle
    have hjlt : (j : ℕ) < R := by
      rw [← hcard_sorted]
      exact (Tuple.lt_card_le_iff_apply_le_of_monotone hlambda_mono).2 hle
    exact (Nat.not_lt_of_ge hj) hjlt
  have hprefix_range :
      Set.range (point ∘ Fin.castLE hR) = q '' {i | ell i ≤ 1} := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨s (Fin.castLE hR j), ?_, rfl⟩
      change lambda (Fin.castLE hR j) ≤ 1
      exact hlow _ j.isLt
    · rintro ⟨i, hi, rfl⟩
      have hsle : lambda (s.symm i) ≤ 1 := by
        simpa [lambda] using hi
      have hslt : ((s.symm i : Fin n) : ℕ) < R := by
        rw [← hcard_sorted]
        exact (Tuple.lt_card_le_iff_apply_le_of_monotone hlambda_mono).2 hsle
      let j : Fin R := ⟨s.symm i, hslt⟩
      refine ⟨j, ?_⟩
      simp [point, j]
  refine ⟨{
    rank := R
    rank_eq := rfl
    rank_le := hR
    lambda := lambda
    point := point
    lambda_pos := fun j ↦ hq_pos (s j)
    lambda_mono := hlambda_mono
    independent := hq.comp s s.injective
    sIntegral := fun j ↦ (hq_admissible (s j)).1
    local_bound := ?_
    low_le_one := hlow
    high_gt_one := hhigh
    prefix_span := ?_ }, ?_⟩
  · intro j v i
    by_cases hv : v = Place23.infinite
    · subst v
      simp only [placeScale_infinite]
      exact entryScale_bounds L hQ c (point j) i
    · simp only [placeScale, if_neg hv, one_mul]
      exact (hq_admissible (s j)).2 v hv i
  · rw [hprefix_range, ← hlow_range]
    exact hlow_span
  · exact Equiv.prod_comp s ell

/-- A raw product certificate yields a genuine rank-adapted certificate with
the same product upper bound.  All vectors of scale at most one are first
retained/exchanged to recover the exact approximation span; the resulting
family is then sorted. -/
theorem exists_adaptedBasisCertificate_of_rawProduct
    {n : ℕ} [NeZero n] (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n) {bound : ℝ}
    (raw : RawEntryScaleProductCertificate L Q c bound) :
    ∃ A : AdaptedBasisCertificate L Q c,
      (∏ i, A.lambda i) ≤ bound := by
  obtain ⟨q, hq, hq_admissible, hq_product, hq_span⟩ :=
    exists_entryScale_adapted_exchange L hL hQ c raw.point
      raw.independent raw.finitePlaceAdmissible
  obtain ⟨A, hA_product⟩ :=
    exists_adaptedBasisCertificate_of_entryScale_span L hL hQ c q hq
      hq_admissible hq_span
  refine ⟨A, ?_⟩
  rw [hA_product]
  exact hq_product.trans raw.product_le

/-- A rank-adapted successive-minimum certificate together with the upper
half of the adelic Minkowski product estimate.  The parameter
`upperConstant` is external to the certificate, so a constructor uniform in
`Q` and `c` really does provide one constant depending only on the fixed
forms (and the dimension). -/
noncomputable def upperConstant {n : ℕ} (L : LocalForms n) : ℝ :=
  Erdos407.MinkowskiSecondBox.minkowskiSecondConstant n *
    |(archimedeanFormMatrix L).det| *
      Erdos407.PadicSubspace.FinitePlaceLattice.finiteLatticeConstant L

theorem upperConstant_pos {n : ℕ} (L : LocalForms n)
    (hL : IsNonsingularFamily L) : 0 < upperConstant L := by
  unfold upperConstant Erdos407.MinkowskiSecondBox.minkowskiSecondConstant
  have hdet : 0 < |(archimedeanFormMatrix L).det| :=
    abs_pos.mpr (archimedeanFormMatrix_det_ne_zero hL)
  have hfinite :=
    Erdos407.PadicSubspace.FinitePlaceLattice.finiteLatticeConstant_pos L
  positivity

/-- Split the product of the `3n` radii into its Archimedean factor and the
two finite-place factors. -/
theorem exponentRadiiProduct_eq_infinite_mul_finite {n : ℕ}
    (Q : ℝ) (c : LocalConstants n) :
    exponentRadiiProduct Q c =
      (∏ i, exponentRadius Q c Place23.infinite i) *
        (∏ u : Fin 2, ∏ i,
          exponentRadius Q c
            (Erdos407.PadicSubspace.FinitePlaceLattice.finitePlace u) i) := by
  simp [exponentRadiiProduct, Fin.prod_univ_succ,
    Erdos407.PadicSubspace.FinitePlaceLattice.finitePlace,
    Place23.infinite, Place23.two, Place23.three]

structure UpperAdaptedBasisCertificate {n : ℕ} (L : LocalForms n) (Q : ℕ)
    (c : LocalConstants n) (upperConstant : ℝ)
    extends AdaptedBasisCertificate L Q c where
  upperConstant_pos : 0 < upperConstant
  product_le :
    ∏ j, toAdaptedBasisCertificate.lambda j ≤
      upperConstant * (exponentRadiiProduct (Q : ℝ) c)⁻¹

/-- Bundle the generic exchange-and-sort construction with a raw Minkowski
product estimate in the reciprocal-radii orientation. -/
theorem nonempty_upperAdaptedBasisCertificate_of_rawProduct
    {n : ℕ} [NeZero n] (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n) (upperConstant : ℝ)
    (hupper : 0 < upperConstant)
    (raw : RawEntryScaleProductCertificate L Q c
      (upperConstant * (exponentRadiiProduct (Q : ℝ) c)⁻¹)) :
    Nonempty (UpperAdaptedBasisCertificate L Q c upperConstant) := by
  obtain ⟨A, hA⟩ :=
    exists_adaptedBasisCertificate_of_rawProduct L hL hQ c raw
  exact ⟨{
    toAdaptedBasisCertificate := A
    upperConstant_pos := hupper
    product_le := hA }⟩

/-- Unconditional construction of the rank-adapted adelic successive-minima
certificate with the upper Minkowski product bound.  The constant depends
only on the fixed local forms and the dimension. -/
theorem exists_upperAdaptedBasisCertificate
    {n : ℕ} (hn : 0 < n) (L : LocalForms n)
    (hL : IsNonsingularFamily L) {Q : ℕ} (hQ : 1 ≤ Q)
    (c : LocalConstants n) :
    Nonempty (UpperAdaptedBasisCertificate L Q c (upperConstant L)) := by
  let : NeZero n := ⟨hn.ne'⟩
  let rf : Fin 2 → Fin n → ℝ := fun u i ↦
    exponentRadius (Q : ℝ) c
      (Erdos407.PadicSubspace.FinitePlaceLattice.finitePlace u) i
  have hrf : ∀ u i, 0 < rf u i := by
    intro u i
    exact exponentRadius_pos_of_one_le hQ c _ _
  obtain ⟨K, e, he_lower, _he_upper, hdet⟩ :=
    Erdos407.PadicSubspace.FinitePlaceLattice.exists_finiteLatticeBasis
      L rf hrf
  let qb : Fin n → (Fin n → ℚ) :=
    Erdos407.PadicSubspace.FinitePlaceLattice.finiteRationalBasis
      (K := K) L e
  let b : Basis (Fin n) ℝ (Fin n → ℝ) :=
    Erdos407.PadicSubspace.FinitePlaceLattice.finiteRealBasis
      (K := K) L e
  let rInf : Fin n → ℝ := fun i ↦
    exponentRadius (Q : ℝ) c Place23.infinite i
  have hrInf : ∀ i, 0 < rInf i := by
    intro i
    exact exponentRadius_pos_of_one_le hQ c _ _
  obtain ⟨C⟩ :=
    Erdos407.MinkowskiSecondBox.realBox_has_minkowskiSecondCertificate
      (archimedeanEvaluationBasis L hL b) rInf hrInf
  have hb : ∀ j k, b j k = (qb j k : ℝ) := by
    intro j k
    exact Erdos407.PadicSubspace.FinitePlaceLattice.finiteRealBasis_apply
      L e j k
  have hadmissible : ∀ x : Fin n → ℚ,
      (∃ z : Fin n → ℤ, x = ∑ j, (z j : ℚ) • qb j) →
        FinitePlaceAdmissible L Q c x := by
    intro x hx
    have hx' : ∃ z : Fin n → ℤ,
        x = ∑ j, (z j : ℚ) •
          Erdos407.PadicSubspace.FinitePlaceLattice.finiteRationalBasis
            (K := K) L e j := by
      simpa [qb] using hx
    have ha :=
      Erdos407.PadicSubspace.FinitePlaceLattice.finiteRationalBasis_span_admissible
        L rf e he_lower x hx'
    refine ⟨ha.1, ?_⟩
    intro v hv i
    fin_cases v
    · exact (hv rfl).elim
    · change (padicNorm 2
        (L Place23.two i x) : ℝ) ≤
          exponentRadius (Q : ℝ) c Place23.two i
      simpa [rf] using ha.2 (0 : Fin 2) i
    · change (padicNorm 3
        (L Place23.three i x) : ℝ) ≤
          exponentRadius (Q : ℝ) c Place23.three i
      simpa [rf] using ha.2 (1 : Fin 2) i
  let raw₀ := rawEntryScaleProductCertificate_of_realCertificate
    L hL hQ c qb b hb hadmissible C
  rw [Pi.basisFun_det_apply] at hdet
  have hdet' : |(Matrix.of b).det| ≤
      Erdos407.PadicSubspace.FinitePlaceLattice.finiteLatticeConstant L *
        (∏ u, ∏ i, rf u i)⁻¹ := by
    simpa [b, Pi.basisFun_det_apply] using hdet
  have hbound :
      Erdos407.MinkowskiSecondBox.minkowskiSecondConstant n *
          |(Matrix.of (archimedeanEvaluationBasis L hL b)).det| *
            (∏ i, rInf i)⁻¹ ≤
        upperConstant L * (exponentRadiiProduct (Q : ℝ) c)⁻¹ := by
    rw [abs_det_archimedeanEvaluationBasis]
    calc
      Erdos407.MinkowskiSecondBox.minkowskiSecondConstant n *
            (|(Matrix.of b).det| * |(archimedeanFormMatrix L).det|) *
              (∏ i, rInf i)⁻¹ =
          (Erdos407.MinkowskiSecondBox.minkowskiSecondConstant n *
            |(archimedeanFormMatrix L).det| * (∏ i, rInf i)⁻¹) *
              |(Matrix.of b).det| := by ring
      _ ≤ (Erdos407.MinkowskiSecondBox.minkowskiSecondConstant n *
            |(archimedeanFormMatrix L).det| * (∏ i, rInf i)⁻¹) *
          (Erdos407.PadicSubspace.FinitePlaceLattice.finiteLatticeConstant L *
            (∏ u, ∏ i, rf u i)⁻¹) := by
        apply mul_le_mul_of_nonneg_left hdet'
        exact mul_nonneg
          (mul_nonneg
            (Erdos407.MinkowskiSecondBox.minkowskiSecondConstant_nonneg n)
            (abs_nonneg _))
          (inv_nonneg.mpr (Finset.prod_nonneg fun i _ ↦ (hrInf i).le))
      _ = upperConstant L * (exponentRadiiProduct (Q : ℝ) c)⁻¹ := by
        rw [exponentRadiiProduct_eq_infinite_mul_finite]
        change _ = upperConstant L *
          ((∏ i, rInf i) * (∏ u, ∏ i, rf u i))⁻¹
        rw [mul_inv]
        unfold upperConstant
        ring
  have hrawBound :
      (∏ i, entryScale L Q c (raw₀.point i)) ≤
        upperConstant L * (exponentRadiiProduct (Q : ℝ) c)⁻¹ :=
    raw₀.product_le.trans hbound
  let raw : RawEntryScaleProductCertificate L Q c
      (upperConstant L * (exponentRadiiProduct (Q : ℝ) c)⁻¹) := {
    point := raw₀.point
    independent := raw₀.independent
    finitePlaceAdmissible := raw₀.finitePlaceAdmissible
    product_le := hrawBound }
  exact nonempty_upperAdaptedBasisCertificate_of_rawProduct
    L hL hQ c (upperConstant L) (upperConstant_pos L hL) raw

/-- The reciprocal of the full local-radius product has exactly the desired
negative total exponent. -/
theorem inv_exponentRadiiProduct_eq_rpow_neg_sum {n : ℕ} {Q : ℕ}
    (hQ : 1 ≤ Q) (c : LocalConstants n) :
    (exponentRadiiProduct (Q : ℝ) c)⁻¹ =
      (Q : ℝ) ^ (-(∑ v, ∑ i, c v i)) := by
  rw [exponentRadiiProduct_eq_rpow_sum (by exact_mod_cast (Nat.zero_lt_of_lt hQ))]
  exact (Real.rpow_neg (by positivity) _).symm

/-- Exponent form of the product estimate carried by an upper adapted
certificate. -/
theorem UpperAdaptedBasisCertificate.product_le_rpow_neg_sum
    {n : ℕ} {L : LocalForms n} {Q : ℕ} {c : LocalConstants n}
    {upperConstant : ℝ}
    (A : UpperAdaptedBasisCertificate L Q c upperConstant) (hQ : 1 ≤ Q) :
    ∏ j, A.toAdaptedBasisCertificate.lambda j ≤
      upperConstant * (Q : ℝ) ^ (-(∑ v, ∑ i, c v i)) := by
  rw [← inv_exponentRadiiProduct_eq_rpow_neg_sum hQ c]
  exact A.product_le

end AdelicMinimaUpper

end Erdos407.PadicSubspace
