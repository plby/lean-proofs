/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.LargeHeightGlue
import ErdosProblems.Erdos407.RankDrop
import ErdosProblems.Erdos407.SIntegerApproximation
import ErdosProblems.Erdos407.EvertseBasis
import ErdosProblems.Erdos407.SIntegralRankGap
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The exterior-power endpoint of the rational three-place Subspace Theorem

This file contains the last reduction in the specialization of the Subspace
Theorem to `K = ℚ` and `S = {∞, 2, 3}`.  The exterior coordinate space is
indexed by the `q`-element subsets of the original coordinate set.  In
particular its dimension is `n.choose q`, and is at most ten when `n ≤ 5`.

The elementary lemmas below isolate the parts of GLR, §§5.2--5.3 which do
not depend on a choice of norms: triangular changes have determinant one,
`N-1` independent exterior points together with failure of full rank give
rank exactly `N-1`, ceiling on a real exponent grid loses less than one mesh,
and a finite family of proper rational subspaces dualizes to a finite family
of proper rational hyperplanes.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix ExteriorAlgebra

namespace ExteriorEndpoint

/-! ## Exterior coordinate indices and the dimension-ten bound -/

/-- Coordinate indices for the `q`-th exterior power of `ℚⁿ`. -/
abbrev ExteriorIndex (n q : ℕ) :=
  {I // I ∈ (Finset.univ : Finset (Fin n)).powersetCard q}

/-- The standard coordinate model of the `q`-th exterior power. -/
abbrev ExteriorVector (n q : ℕ) := ExteriorIndex n q → ℚ

@[simp] theorem card_exteriorIndex (n q : ℕ) :
    Fintype.card (ExteriorIndex n q) = n.choose q := by
  simp [ExteriorIndex]

/-- The exterior coordinate type is canonically finite-dimensional of the
expected binomial dimension. -/
theorem finrank_exteriorVector (n q : ℕ) :
    Module.finrank ℚ (ExteriorVector n q) = n.choose q := by
  simp [ExteriorVector]

/-- Every exterior space which can occur from an original space of dimension
at most five has dimension at most ten. -/
theorem exteriorDimension_le_ten {n q : ℕ} (hn : n ≤ 5) :
    n.choose q ≤ 10 := by
  by_cases hq : q ≤ n
  · interval_cases n <;> interval_cases q <;> norm_num [Nat.choose] at *
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hq)]
    omega

/-- A proper nonzero exterior degree has ambient dimension at least two,
which is the dimensional hypothesis needed when Theorem 4.14 is applied in
the exterior space. -/
theorem two_le_exteriorDimension {n q : ℕ} (hq0 : 0 < q) (hqn : q < n) :
    2 ≤ n.choose q := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0.ne'
  rw [Nat.choose_succ_succ]
  have hleft : 0 < m.choose k := Nat.choose_pos (by omega)
  have hright : 0 < m.choose k.succ := Nat.choose_pos (by omega)
  omega

/-! ## Exterior coordinate equivalences and local forms -/

/-- The standard exterior-power basis, written as a coordinate equivalence
indexed by `q`-element subsets. -/
noncomputable def exteriorCoordinateEquiv (n q : ℕ) :
    (⋀[ℚ]^q (Fin n → ℚ)) ≃ₗ[ℚ]
      (Set.powersetCard (Fin n) q → ℚ) :=
  ((Pi.basisFun ℚ (Fin n)).exteriorPower q).repr ≪≫ₗ
    Finsupp.linearEquivFunOnFinite ℚ ℚ (Set.powersetCard (Fin n) q)

/-- The determinant formula for a standard exterior coordinate. -/
def standardExteriorCoordinate {n q : ℕ} (x : Fin q → Fin n → ℚ)
    (J : Set.powersetCard (Fin n) q) : ℚ :=
  Matrix.det (fun i j ↦ x i (Set.powersetCard.ofFinEmbEquiv.symm J j))

/-- The standard-basis coordinates of a decomposable exterior vector are its
Plücker minors. -/
theorem exteriorCoordinateEquiv_iMulti {n q : ℕ}
    (x : Fin q → Fin n → ℚ) (J : Set.powersetCard (Fin n) q) :
    exteriorCoordinateEquiv n q (exteriorPower.ιMulti ℚ q x) J =
      standardExteriorCoordinate x J := by
  rw [exteriorCoordinateEquiv]
  change ((Pi.basisFun ℚ (Fin n)).exteriorPower q).repr
      (exteriorPower.ιMulti ℚ q x) J = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

/-- A fixed enumeration of the exterior coordinates. -/
noncomputable def exteriorIndexEquivFin (n q : ℕ) :
    Set.powersetCard (Fin n) q ≃ Fin (n.choose q) :=
  (Fintype.equivFin (Set.powersetCard (Fin n) q)).trans <|
    Equiv.cast <| congrArg Fin <| by
      rw [Fintype.card_eq_nat_card, Set.powersetCard.card,
        Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Exterior coordinates reindexed by `Fin (n.choose q)`, the coordinate
type required by the dimension-generic rank-stabilization theorem. -/
noncomputable def exteriorFinCoordinateEquiv (n q : ℕ) :
    (⋀[ℚ]^q (Fin n → ℚ)) ≃ₗ[ℚ]
      (Fin (n.choose q) → ℚ) :=
  exteriorCoordinateEquiv n q ≪≫ₗ
    LinearEquiv.funCongrLeft ℚ ℚ (exteriorIndexEquivFin n q).symm

/-- Evaluation by all local forms at one place. -/
def localEvaluationMap {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
  LinearMap.pi (L v)

/-- Reindex each local basis of forms by a place-dependent permutation. -/
def permutedLocalForms {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (π : Place23 → Equiv.Perm (Fin n)) :
    Place23 → Fin n → RatLinearForm n :=
  fun v i ↦ L v (π v i)

theorem permutedLocalForms_nonsingular {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    (hL : IsNonsingularFamily L)
    (π : Place23 → Equiv.Perm (Fin n)) :
    IsNonsingularFamily (permutedLocalForms L π) := by
  intro v
  exact (hL v).comp (π v) (π v).injective

theorem localEvaluationMap_eq_mulVec {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (x : Fin n → ℚ) :
    localEvaluationMap L v x = Matrix.mulVec (formMatrix L v) x := by
  funext i
  exact linearForm_eq_sum_coeff (L v i) x

theorem localEvaluationMap_injective {n : ℕ}
    {L : Place23 → Fin n → RatLinearForm n}
    (hL : IsNonsingularFamily L) (v : Place23) :
    Function.Injective (localEvaluationMap L v) := by
  intro x y hxy
  rw [localEvaluationMap_eq_mulVec, localEvaluationMap_eq_mulVec] at hxy
  exact (Matrix.mulVec_injective_of_det_ne_zero
    (formMatrix_det_ne_zero hL v)) hxy

noncomputable def localEvaluationEquiv {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (v : Place23) :
    (Fin n → ℚ) ≃ₗ[ℚ] (Fin n → ℚ) :=
  LinearEquiv.ofInjectiveEndo (localEvaluationMap L v)
    (localEvaluationMap_injective hL v)

/-- The exterior power of the local evaluation equivalence, conjugated into
the `Fin (n.choose q)` coordinate model. -/
noncomputable def exteriorEvaluationEquiv {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (v : Place23) (q : ℕ) :
    (Fin (n.choose q) → ℚ) ≃ₗ[ℚ]
      (Fin (n.choose q) → ℚ) :=
  (exteriorFinCoordinateEquiv n q).symm ≪≫ₗ
    LinearEquiv.ofInjectiveEndo
      (exteriorPower.map q (localEvaluationMap L v))
      (exteriorPower.map_injective_field (n := q)
        (localEvaluationMap_injective hL v)) ≪≫ₗ
    exteriorFinCoordinateEquiv n q

/-- Coordinate forms pulled back along an automorphism. -/
noncomputable def coordinateForms {d : ℕ}
    (e : (Fin d → ℚ) ≃ₗ[ℚ] (Fin d → ℚ)) (i : Fin d) :
    RatLinearForm d :=
  (LinearMap.proj i).comp e.toLinearMap

theorem coordinateForms_linearIndependent {d : ℕ}
    (e : (Fin d → ℚ) ≃ₗ[ℚ] (Fin d → ℚ)) :
    LinearIndependent ℚ (coordinateForms e) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hi := LinearMap.congr_fun hg (e.symm (Pi.single i 1))
  simpa [coordinateForms, Pi.single_apply] using hi

/-- The nonsingular local form families on the exterior coordinate space. -/
noncomputable def exteriorLocalForms {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (q : ℕ) :
    Place23 → Fin (n.choose q) → RatLinearForm (n.choose q) :=
  fun v ↦ coordinateForms (exteriorEvaluationEquiv L hL v q)

theorem exteriorLocalForms_nonsingular {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (q : ℕ) :
    IsNonsingularFamily (exteriorLocalForms L hL q) := by
  intro v
  exact coordinateForms_linearIndependent _

/-- Coordinates of a decomposable exterior vector, in the finite coordinate
model used by the rank-stabilization theorem. -/
noncomputable def finWedgeCoordinates {n q : ℕ}
    (x : Fin q → Fin n → ℚ) : Fin (n.choose q) → ℚ :=
  exteriorFinCoordinateEquiv n q (exteriorPower.ιMulti ℚ q x)

@[simp] theorem finWedgeCoordinates_apply_equiv {n q : ℕ}
    (x : Fin q → Fin n → ℚ) (J : Set.powersetCard (Fin n) q) :
    finWedgeCoordinates x (exteriorIndexEquivFin n q J) =
      standardExteriorCoordinate x J := by
  simp [finWedgeCoordinates, exteriorFinCoordinateEquiv,
    exteriorCoordinateEquiv_iMulti]

/-- Evaluating the induced exterior forms on Plücker coordinates is exactly
the same as first evaluating every original vector by the original local
family and then taking Plücker coordinates. -/
theorem exteriorLocalForms_apply_finWedgeCoordinates {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L)
    (v : Place23) (i : Fin (n.choose q)) (x : Fin q → Fin n → ℚ) :
    exteriorLocalForms L hL q v i (finWedgeCoordinates x) =
      finWedgeCoordinates (fun j ↦ localEvaluationMap L v (x j)) i := by
  change exteriorLocalForms L hL q v i (finWedgeCoordinates x) =
    exteriorFinCoordinateEquiv n q
      (exteriorPower.ιMulti ℚ q (fun j ↦ localEvaluationMap L v (x j))) i
  have hcomp : (⇑(localEvaluationMap L v) ∘ x) =
      (fun j ↦ localEvaluationMap L v (x j)) := by
    funext j
    rfl
  rw [← hcomp]
  simp [exteriorLocalForms, coordinateForms, exteriorEvaluationEquiv,
    finWedgeCoordinates, exteriorPower.map_apply_ιMulti]

/-! ## Recovering a subspace from its Plücker line -/

/-- The unique `k`-element subset of `Fin k`. -/
noncomputable def fullExteriorIndex (k : ℕ) : Set.powersetCard (Fin k) k :=
  ⟨Finset.univ, by simp [Set.powersetCard.mem_iff]⟩

/-- The identity map, regarded as an order embedding. -/
def identityOrderEmbedding (k : ℕ) : Fin k ↪o Fin k where
  toFun := id
  inj' := Function.injective_id
  map_rel_iff' := Iff.rfl

theorem enum_fullExteriorIndex (k : ℕ) :
    Set.powersetCard.ofFinEmbEquiv.symm (fullExteriorIndex k) =
      identityOrderEmbedding k := by
  apply (OrderEmbedding.range_inj).mp
  ext i
  constructor
  · intro _
    exact ⟨i, rfl⟩
  · rintro ⟨j, rfl⟩
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (fullExteriorIndex k) j).mpr (by simp [fullExteriorIndex])

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

theorem iMulti_family_fullExteriorIndex {k : ℕ} (v : Fin k → E) :
    exteriorPower.ιMulti_family ℚ k v (fullExteriorIndex k) =
      exteriorPower.ιMulti ℚ k v := by
  rw [exteriorPower.ιMulti_family, enum_fullExteriorIndex]
  congr 1

/-- The exterior product of a linearly independent tuple is nonzero. -/
theorem iMulti_ne_zero_of_linearIndependent {k : ℕ} {v : Fin k → E}
    (hv : LinearIndependent ℚ v) : exteriorPower.ιMulti ℚ k v ≠ 0 := by
  have hli := exteriorPower.ιMulti_family_linearIndependent_field (n := k) hv
  rw [← iMulti_family_fullExteriorIndex v]
  exact hli.ne_zero (fullExteriorIndex k)

/-- Over `ℚ`, a decomposable exterior product vanishes exactly when its
arguments are linearly dependent. -/
theorem iMulti_eq_zero_iff_not_linearIndependent {k : ℕ} (v : Fin k → E) :
    exteriorPower.ιMulti ℚ k v = 0 ↔ ¬ LinearIndependent ℚ v := by
  constructor
  · intro h hli
    exact iMulti_ne_zero_of_linearIndependent hli h
  · exact AlternatingMap.map_linearDependent _ v

/-- Exterior multiplication by a fixed decomposable `k`-vector, written as
the linear map `x ↦ x ∧ v₁ ∧ ⋯ ∧ vₖ`. -/
noncomputable def wedgeWith {k : ℕ} (v : Fin k → E) :
    E →ₗ[ℚ] (⋀[ℚ]^(k + 1) E) :=
  { toFun := fun x ↦ (exteriorPower.ιMulti ℚ (k + 1)).curryLeft x v
    map_add' := by
      intro x y
      exact DFunLike.congr_fun
        (map_add (exteriorPower.ιMulti ℚ (k + 1)).curryLeft x y) v
    map_smul' := by
      intro c x
      exact DFunLike.congr_fun
        (map_smul (exteriorPower.ιMulti ℚ (k + 1)).curryLeft c x) v }

@[simp] theorem wedgeWith_apply {k : ℕ} (v : Fin k → E) (x : E) :
    wedgeWith v x =
      exteriorPower.ιMulti ℚ (k + 1) (Matrix.vecCons x v) := by
  change (exteriorPower.ιMulti ℚ (k + 1)).curryLeft x v = _
  exact AlternatingMap.curryLeft_apply_apply _ _ _

/-- The kernel of exterior multiplication by a nonzero decomposable
`k`-vector is precisely the represented `k`-space.  This is the formal
Plücker recovery statement used after Lemma 5.3. -/
theorem wedgeWith_ker {k : ℕ} {v : Fin k → E}
    (hv : LinearIndependent ℚ v) :
    LinearMap.ker (wedgeWith v) = Submodule.span ℚ (Set.range v) := by
  ext x
  rw [LinearMap.mem_ker, wedgeWith_apply,
    iMulti_eq_zero_iff_not_linearIndependent]
  change ¬ LinearIndependent ℚ (Fin.cons x v) ↔ _
  rw [linearIndependent_finCons (K := ℚ) (x := x) (v := v)]
  simp only [hv, true_and, not_not]

theorem wedgeWith_eq_smul_of_iMulti_eq_smul {k : ℕ}
    {v w : Fin k → E} {c : ℚ}
    (h : exteriorPower.ιMulti ℚ k v = c • exteriorPower.ιMulti ℚ k w) :
    wedgeWith v = c • wedgeWith w := by
  have h' := congrArg Subtype.val h
  simp only [exteriorPower.ιMulti_apply_coe, Submodule.coe_smul_of_tower] at h'
  ext x
  simp only [wedgeWith_apply, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.ιMulti_succ_apply, Matrix.tail_cons, LinearMap.smul_apply,
    Submodule.coe_smul_of_tower]
  rw [h']
  simp

/-- Proportional nonzero Plücker coordinates recover the same original
subspace. -/
theorem span_eq_of_iMulti_eq_smul {k : ℕ}
    {v w : Fin k → E} (hv : LinearIndependent ℚ v)
    (hw : LinearIndependent ℚ w) {c : ℚ} (hc : c ≠ 0)
    (h : exteriorPower.ιMulti ℚ k v = c • exteriorPower.ιMulti ℚ k w) :
    Submodule.span ℚ (Set.range v) = Submodule.span ℚ (Set.range w) := by
  rw [← wedgeWith_ker hv, ← wedgeWith_ker hw,
    wedgeWith_eq_smul_of_iMulti_eq_smul h]
  exact LinearMap.ker_smul _ _ hc

/-! ### Functorial recovery from the omitted-wedge hyperplane -/

/-- The map on `q`-th exterior powers induced by quotienting by `W`. -/
noncomputable def exteriorQuotientMap (W : Submodule ℚ E) (q : ℕ) :
    (⋀[ℚ]^q E) →ₗ[ℚ] (⋀[ℚ]^q (E ⧸ W)) :=
  exteriorPower.map q W.mkQ

/-- The exterior hyperplane canonically associated to a codimension-`q`
subspace.  In a basis adapted to `W`, this is precisely the span of all
`q`-fold basis wedges except the wedge of the complementary vectors. -/
noncomputable def exteriorKernel (W : Submodule ℚ E) (q : ℕ) :
    Submodule ℚ (⋀[ℚ]^q E) :=
  LinearMap.ker (exteriorQuotientMap W q)

theorem mem_exteriorKernel_iff (W : Submodule ℚ E) (q : ℕ)
    (x : ⋀[ℚ]^q E) :
    x ∈ exteriorKernel W q ↔ exteriorQuotientMap W q x = 0 := Iff.rfl

theorem iMulti_mem_exteriorKernel_iff (W : Submodule ℚ E) (q : ℕ)
    (x : Fin q → E) :
    exteriorPower.ιMulti ℚ q x ∈ exteriorKernel W q ↔
      exteriorPower.ιMulti ℚ q (W.mkQ ∘ x) = 0 := by
  rw [mem_exteriorKernel_iff]
  simp [exteriorQuotientMap, exteriorPower.map_apply_ιMulti]

theorem iMulti_mem_exteriorKernel_of_mem (W : Submodule ℚ E)
    {q : ℕ} (x : Fin q → E) (i : Fin q) (hi : x i ∈ W) :
    exteriorPower.ιMulti ℚ q x ∈ exteriorKernel W q := by
  rw [iMulti_mem_exteriorKernel_iff,
    iMulti_eq_zero_iff_not_linearIndependent]
  intro hli
  have hzero : (W.mkQ ∘ x) i = 0 := by
    simp only [Function.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero W).mpr hi
  exact hli.ne_zero i hzero

/-- A nonzero vector in a `q`-dimensional space extends to an ordered basis
of length `q`, with the vector in the zeroth position. -/
theorem exists_linearIndependent_fin_with_head [Module.Finite ℚ E]
    {q : ℕ} (hq : 0 < q) {x : E} (hx : x ≠ 0)
    (hdim : Module.finrank ℚ E = q) :
    ∃ v : Fin q → E, LinearIndependent ℚ v ∧ v ⟨0, hq⟩ = x := by
  have extend : ∀ (r : ℕ) (hr : 0 < r), r ≤ q →
      ∃ v : Fin r → E, LinearIndependent ℚ v ∧ v ⟨0, hr⟩ = x := by
    intro r
    induction r with
    | zero => omega
    | succ r ih =>
        intro hrpos hrq
        by_cases hr0 : r = 0
        · subst r
          let v : Fin 1 → E := fun _ ↦ x
          refine ⟨v, ?_, rfl⟩
          exact Fintype.linearIndependent_iff.mpr fun g hg i ↦ by
            have hi : i = 0 := Fin.eq_zero i
            subst i
            have hsum : g 0 • x = 0 := by simpa [v] using hg
            exact (smul_eq_zero.mp hsum).resolve_right hx
        · have hrpos' : 0 < r := Nat.pos_of_ne_zero hr0
          have hrle : r ≤ q := by omega
          obtain ⟨v, hv, hv0⟩ := ih hrpos' hrle
          have hrlt : r < Module.finrank ℚ E := by omega
          obtain ⟨z, hz⟩ :=
            exists_linearIndependent_snoc_of_lt_finrank hv hrlt
          refine ⟨Fin.snoc v z, hz, ?_⟩
          change (Fin.snoc v z : Fin (r + 1) → E)
            (Fin.castSucc ⟨0, hrpos'⟩) = x
          rw [Fin.snoc_castSucc]
          exact hv0
  exact extend q hq le_rfl

theorem exists_iMulti_ne_zero_with_head [Module.Finite ℚ E]
    {q : ℕ} (hq : 0 < q) {x : E} (hx : x ≠ 0)
    (hdim : Module.finrank ℚ E = q) :
    ∃ y : Fin q → E, y ⟨0, hq⟩ = x ∧
      exteriorPower.ιMulti ℚ q y ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ :=
    exists_linearIndependent_fin_with_head hq hx hdim
  exact ⟨v, hv0, iMulti_ne_zero_of_linearIndependent hv⟩

/-- Membership in `W` can be read only from its exterior kernel: a vector
belongs to `W` iff every `q`-fold wedge having it as first factor belongs to
that kernel. -/
def ExteriorKernelDetects (W : Submodule ℚ E) {q : ℕ} (hq : 0 < q)
    (x : E) : Prop :=
  ∀ z : Fin q → E, z ⟨0, hq⟩ = x →
    exteriorPower.ιMulti ℚ q z ∈ exteriorKernel W q

theorem exteriorKernelDetects_iff [Module.Finite ℚ E]
    (W : Submodule ℚ E) {q : ℕ} (hq : 0 < q)
    (hdim : Module.finrank ℚ (E ⧸ W) = q) (x : E) :
    ExteriorKernelDetects W hq x ↔ x ∈ W := by
  constructor
  · intro hx
    by_contra hxW
    have hxq : W.mkQ x ≠ 0 := by
      simpa [Submodule.Quotient.mk_eq_zero] using hxW
    obtain ⟨y, hy0, hyne⟩ :=
      exists_iMulti_ne_zero_with_head hq hxq hdim
    let s : (E ⧸ W) → E := Function.surjInv W.mkQ_surjective
    have hs : Function.RightInverse s W.mkQ :=
      Function.rightInverse_surjInv W.mkQ_surjective
    let i0 : Fin q := ⟨0, hq⟩
    let z : Fin q → E := Function.update (s ∘ y) i0 x
    have hz0 : z i0 = x := by simp [z]
    have hmap : W.mkQ ∘ z = y := by
      funext i
      by_cases hi : i = i0
      · subst i
        simp only [Function.comp_apply, hz0, hy0, i0]
      · simp [z, hi, hs (y i)]
    have hzker := hx z hz0
    rw [iMulti_mem_exteriorKernel_iff, hmap] at hzker
    exact hyne hzker
  · intro hx z hz0
    apply iMulti_mem_exteriorKernel_of_mem W z ⟨0, hq⟩
    rwa [hz0]

/-- The original subspace is recovered functorially and injectively from
the exterior hyperplane.  This is the precise dualization step implicit at
the end of GLR §5.3. -/
theorem exteriorKernel_injective [Module.Finite ℚ E]
    {W Z : Submodule ℚ E} {q : ℕ} (hq : 0 < q)
    (hWdim : Module.finrank ℚ (E ⧸ W) = q)
    (hZdim : Module.finrank ℚ (E ⧸ Z) = q)
    (hker : exteriorKernel W q = exteriorKernel Z q) : W = Z := by
  ext x
  rw [← exteriorKernelDetects_iff W hq hWdim x,
    ← exteriorKernelDetects_iff Z hq hZdim x]
  simp only [ExteriorKernelDetects]
  rw [hker]

/-- Exterior indices other than one distinguished coordinate. -/
abbrev OmittedExteriorIndex {n q : ℕ}
    (J₀ : Set.powersetCard (Fin n) q) :=
  {J : Set.powersetCard (Fin n) q // J ≠ J₀}

@[simp] theorem card_omittedExteriorIndex {n q : ℕ}
    (J₀ : Set.powersetCard (Fin n) q) :
    Fintype.card (OmittedExteriorIndex J₀) = n.choose q - 1 := by
  have hcard : Fintype.card (Set.powersetCard (Fin n) q) = n.choose q := by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Fintype.card_subtype_compl]
  simp [hcard]

/-- All exterior basis wedges except the distinguished one are linearly
independent.  These are the `D - 1` integral witnesses in Lemma 5.3. -/
theorem omittedExteriorWedges_linearIndependent {n q : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℚ v)
    (J₀ : Set.powersetCard (Fin n) q) :
    LinearIndependent ℚ
      (fun J : OmittedExteriorIndex J₀ ↦
        exteriorPower.ιMulti_family ℚ q v J.1) := by
  exact (exteriorPower.ιMulti_family_linearIndependent_field (n := q) hv).comp
    (fun J : OmittedExteriorIndex J₀ ↦ J.1) Subtype.val_injective

/-- The original subspace spanned by the basis vectors outside the selected
`q`-tuple. -/
noncomputable def basisComplementSubspace {n q : ℕ} (v : Fin n → E)
    (J₀ : Set.powersetCard (Fin n) q) : Submodule ℚ E :=
  Submodule.span ℚ
    (Set.range (fun i : {i : Fin n // i ∉ J₀.1} ↦ v i.1))

theorem basis_mem_basisComplementSubspace {n q : ℕ} (v : Fin n → E)
    (J₀ : Set.powersetCard (Fin n) q) {i : Fin n} (hi : i ∉ J₀.1) :
    v i ∈ basisComplementSubspace v J₀ := by
  apply Submodule.subset_span
  exact ⟨⟨i, hi⟩, rfl⟩

/-- Any subfamily using only indices outside the omitted exterior coordinate
lies in the original complementary subspace recovered from that coordinate. -/
theorem span_basis_le_basisComplementSubspace {n q : ℕ}
    (v : Fin n → E) (J₀ : Set.powersetCard (Fin n) q)
    {ι : Type*} (f : ι → Fin n) (hf : ∀ a, f a ∉ J₀.1) :
    Submodule.span ℚ (Set.range (v ∘ f)) ≤ basisComplementSubspace v J₀ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact basis_mem_basisComplementSubspace v J₀ (hf a)

/-- The span of all basis `q`-wedges except the distinguished wedge. -/
noncomputable def omittedExteriorSpan {n q : ℕ} (v : Fin n → E)
    (J₀ : Set.powersetCard (Fin n) q) :
    Submodule ℚ (⋀[ℚ]^q E) :=
  Submodule.span ℚ
    (Set.range (fun J : OmittedExteriorIndex J₀ ↦
      exteriorPower.ιMulti_family ℚ q v J.1))

theorem finrank_basisComplementSubspace {n q : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℚ v)
    (J₀ : Set.powersetCard (Fin n) q) :
    Module.finrank ℚ (basisComplementSubspace v J₀) = n - q := by
  let u := fun i : {i : Fin n // i ∉ J₀.1} ↦ v i.1
  have hu : LinearIndependent ℚ u := hv.comp _ Subtype.val_injective
  rw [basisComplementSubspace, finrank_span_eq_card hu]
  simp only [Fintype.card_subtype_compl, Fintype.card_fin]
  rw [show Fintype.card {i : Fin n // i ∈ J₀.1} = q by
    simpa using J₀.2]

theorem finrank_quotient_basisComplementSubspace {n q : ℕ}
    [Module.Finite ℚ E] {v : Fin n → E} (hv : LinearIndependent ℚ v)
    (hdim : Module.finrank ℚ E = n)
    (J₀ : Set.powersetCard (Fin n) q) :
    Module.finrank ℚ (E ⧸ basisComplementSubspace v J₀) = q := by
  have hsum := (basisComplementSubspace v J₀).finrank_quotient_add_finrank
  rw [finrank_basisComplementSubspace hv J₀, hdim] at hsum
  have hqn : q ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ J₀.1)
    simpa [J₀.2] using this
  omega

theorem omittedExteriorSpan_le_exteriorKernel {n q : ℕ}
    {v : Fin n → E} (J₀ : Set.powersetCard (Fin n) q) :
    omittedExteriorSpan v J₀ ≤
      exteriorKernel (basisComplementSubspace v J₀) q := by
  apply Submodule.span_le.mpr
  rintro _ ⟨J, rfl⟩
  have hnsub : ¬J.1.1 ⊆ J₀.1 := by
    intro hsub
    apply J.2
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by simpa [J.1.2, J₀.2])
  rw [Finset.not_subset] at hnsub
  obtain ⟨i, hiJ, hiJ₀⟩ := hnsub
  have hirange :
      i ∈ Set.range (Set.powersetCard.ofFinEmbEquiv.symm J.1) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem J.1 i).mpr hiJ
  obtain ⟨a, ha⟩ := hirange
  change exteriorPower.ιMulti ℚ q
      (fun a ↦ v (Set.powersetCard.ofFinEmbEquiv.symm J.1 a)) ∈ _
  apply iMulti_mem_exteriorKernel_of_mem
    (basisComplementSubspace v J₀) _ a
  apply Submodule.subset_span
  refine ⟨⟨i, hiJ₀⟩, ?_⟩
  simpa [ha]

theorem finrank_omittedExteriorSpan {n q : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℚ v)
    (J₀ : Set.powersetCard (Fin n) q) :
    Module.finrank ℚ (omittedExteriorSpan v J₀) = n.choose q - 1 := by
  rw [omittedExteriorSpan,
    finrank_span_eq_card (omittedExteriorWedges_linearIndependent hv J₀),
    card_omittedExteriorIndex]

theorem finrank_exteriorKernel_basisComplementSubspace {n q : ℕ}
    [Module.Finite ℚ E] {v : Fin n → E} (hv : LinearIndependent ℚ v)
    (hdim : Module.finrank ℚ E = n)
    (J₀ : Set.powersetCard (Fin n) q) :
    Module.finrank ℚ (exteriorKernel (basisComplementSubspace v J₀) q) =
      n.choose q - 1 := by
  let W := basisComplementSubspace v J₀
  let f := exteriorQuotientMap W q
  have hqdim : Module.finrank ℚ (E ⧸ W) = q :=
    finrank_quotient_basisComplementSubspace hv hdim J₀
  have hsurj : Function.Surjective f :=
    exteriorPower.map_surjective W.mkQ_surjective
  have hrange : Module.finrank ℚ f.range =
      Module.finrank ℚ (⋀[ℚ]^q (E ⧸ W)) := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hsum := f.finrank_range_add_finrank_ker
  rw [hrange, exteriorPower.finrank_eq, hqdim, Nat.choose_self,
    exteriorPower.finrank_eq, hdim] at hsum
  change Module.finrank ℚ f.ker = n.choose q - 1
  omega

/-- The omitted-wedge hyperplane is exactly the kernel attached to the
complementary original subspace. -/
theorem omittedExteriorSpan_eq_exteriorKernel {n q : ℕ}
    [Module.Finite ℚ E] {v : Fin n → E} (hv : LinearIndependent ℚ v)
    (hdim : Module.finrank ℚ E = n)
    (J₀ : Set.powersetCard (Fin n) q) :
    omittedExteriorSpan v J₀ =
      exteriorKernel (basisComplementSubspace v J₀) q := by
  apply Submodule.eq_of_le_of_finrank_eq
    (omittedExteriorSpan_le_exteriorKernel J₀)
  rw [finrank_omittedExteriorSpan hv J₀,
    finrank_exteriorKernel_basisComplementSubspace hv hdim J₀]

/-- Equality of two exterior hyperplanes recovers equality of their
complementary original subspaces, even when the adapted bases and omitted
coordinates differ. -/
theorem basisComplementSubspace_eq_of_omittedExteriorSpan_eq {n q : ℕ}
    [Module.Finite ℚ E] {v w : Fin n → E}
    (hv : LinearIndependent ℚ v) (hw : LinearIndependent ℚ w)
    (hdim : Module.finrank ℚ E = n) (hq : 0 < q)
    (J : Set.powersetCard (Fin n) q)
    (K : Set.powersetCard (Fin n) q)
    (hspan : omittedExteriorSpan v J = omittedExteriorSpan w K) :
    basisComplementSubspace v J = basisComplementSubspace w K := by
  apply exteriorKernel_injective hq
    (finrank_quotient_basisComplementSubspace hv hdim J)
    (finrank_quotient_basisComplementSubspace hw hdim K)
  rw [← omittedExteriorSpan_eq_exteriorKernel hv hdim J,
    ← omittedExteriorSpan_eq_exteriorKernel hw hdim K]
  exact hspan

/-- A finite family of exterior hyperplanes recovers only finitely many
original complementary subspaces.  This is the finite-set form of the
Plücker dualization used in the final cover. -/
theorem finite_basisComplementSubspaces_of_finite_exteriorSpans {n q : ℕ}
    [Module.Finite ℚ E] (hdim : Module.finrank ℚ E = n) (hq : 0 < q)
    {C : Set (Submodule ℚ (⋀[ℚ]^q E))} (hC : C.Finite) :
    {W : Submodule ℚ E |
      ∃ v : Fin n → E, LinearIndependent ℚ v ∧
        ∃ J : Set.powersetCard (Fin n) q,
          W = basisComplementSubspace v J ∧
          omittedExteriorSpan v J ∈ C}.Finite := by
  let X : Set (Submodule ℚ E) :=
    {W | ∃ v : Fin n → E, LinearIndependent ℚ v ∧
      ∃ J : Set.powersetCard (Fin n) q,
        W = basisComplementSubspace v J ∧
        omittedExteriorSpan v J ∈ C}
  have hrep (W : X) :
      ∃ v : Fin n → E, LinearIndependent ℚ v ∧
        ∃ J : Set.powersetCard (Fin n) q,
          W.1 = basisComplementSubspace v J ∧
          omittedExteriorSpan v J ∈ C := W.2
  choose v hv J hW hmem using hrep
  let f : X → Submodule ℚ (⋀[ℚ]^q E) :=
    fun W ↦ omittedExteriorSpan (v W) (J W)
  have hfmem (W : X) : f W ∈ C := hmem W
  have hfinj : Function.Injective f := by
    intro W Z hWZ
    apply Subtype.ext
    rw [hW W, hW Z]
    exact basisComplementSubspace_eq_of_omittedExteriorSpan_eq
      (hv W) (hv Z) hdim hq (J W) (J Z) hWZ
  have hpre : (f ⁻¹' C).Finite :=
    hC.preimage (Set.injOn_of_injective hfinj)
  have hpreuniv : f ⁻¹' C = Set.univ :=
    Set.eq_univ_of_forall hfmem
  have huniv : (Set.univ : Set X).Finite := by
    rw [← hpreuniv]
    exact hpre
  letI : Finite X := Set.finite_univ_iff.mp huniv
  exact Set.toFinite X

/-- The Plücker vector of the basis subfamily selected by `J`, transported
to the finite-coordinate model used by `RankDrop`. -/
noncomputable def finExteriorBasisWedge {n q : ℕ}
    (v : Fin n → Fin n → ℚ) (J : Set.powersetCard (Fin n) q) :
    Fin (n.choose q) → ℚ :=
  exteriorFinCoordinateEquiv n q
    (exteriorPower.ιMulti_family ℚ q v J)

theorem finExteriorBasisWedge_eq_finWedgeCoordinates {n q : ℕ}
    (v : Fin n → Fin n → ℚ) (J : Set.powersetCard (Fin n) q) :
    finExteriorBasisWedge v J =
      finWedgeCoordinates
        (fun a ↦ v (Set.powersetCard.ofFinEmbEquiv.symm J a)) := by
  simp only [finExteriorBasisWedge, finWedgeCoordinates,
    exteriorPower.ιMulti_family]
  rfl

/-- The `D-1` exterior witnesses of Lemma 5.3 remain independent after
transport to the `Fin D` coordinate space. -/
theorem omittedFinExteriorBasisWedges_linearIndependent {n q : ℕ}
    {v : Fin n → Fin n → ℚ} (hv : LinearIndependent ℚ v)
    (J₀ : Set.powersetCard (Fin n) q) :
    LinearIndependent ℚ
      (fun J : OmittedExteriorIndex J₀ ↦ finExteriorBasisWedge v J.1) := by
  exact (omittedExteriorWedges_linearIndependent hv J₀).map'
    (exteriorFinCoordinateEquiv n q).toLinearMap
    (LinearMap.ker_eq_bot.mpr (exteriorFinCoordinateEquiv n q).injective)

/-- Consequently the span of the exterior approximation domain has rank at
least `D-1` as soon as it contains all omitted basis wedges. -/
theorem exteriorSpan_finrank_ge_pred {n q : ℕ}
    {v : Fin n → Fin n → ℚ} (hv : LinearIndependent ℚ v)
    (J₀ : Set.powersetCard (Fin n) q)
    (W : Submodule ℚ (Fin (n.choose q) → ℚ))
    (hmem : ∀ J : OmittedExteriorIndex J₀,
      finExteriorBasisWedge v J.1 ∈ W) :
    n.choose q - 1 ≤ Module.finrank ℚ W := by
  let w : OmittedExteriorIndex J₀ → W := fun J ↦
    ⟨finExteriorBasisWedge v J.1, hmem J⟩
  have hwcomp : LinearIndependent ℚ (W.subtype ∘ w) := by
    change LinearIndependent ℚ
      (fun J : OmittedExteriorIndex J₀ ↦ finExteriorBasisWedge v J.1)
    exact omittedFinExteriorBasisWedges_linearIndependent hv J₀
  have hw : LinearIndependent ℚ w := hwcomp.of_comp W.subtype
  rw [← card_omittedExteriorIndex J₀]
  exact hw.fintype_card_le_finrank

theorem exteriorSpan_finrank_eq_pred {n q : ℕ}
    {v : Fin n → Fin n → ℚ} (hv : LinearIndependent ℚ v)
    (J₀ : Set.powersetCard (Fin n) q)
    (W : Submodule ℚ (Fin (n.choose q) → ℚ))
    (hmem : ∀ J : OmittedExteriorIndex J₀,
      finExteriorBasisWedge v J.1 ∈ W)
    (hproperRank : Module.finrank ℚ W < n.choose q) :
    Module.finrank ℚ W + 1 = n.choose q := by
  have hlower := exteriorSpan_finrank_ge_pred hv J₀ W hmem
  omega

/-- Increasing enumeration of an exterior-coordinate subset. -/
def ExteriorIndex.enum {n q : ℕ} (I : ExteriorIndex n q) : Fin q → Fin n :=
  fun i ↦ (I.1.orderIsoOfFin (Finset.mem_powersetCard.mp I.2).2 i).1

theorem ExteriorIndex.enum_injective {n q : ℕ} (I : ExteriorIndex n q) :
    Function.Injective I.enum := by
  intro i j hij
  exact (I.1.orderIsoOfFin (Finset.mem_powersetCard.mp I.2).2).injective
    (Subtype.ext hij)

/-- The same exterior-coordinate index, converted from the index type used
by Mathlib's standard exterior basis. -/
def exteriorIndexOfSet {n q : ℕ}
    (J : Set.powersetCard (Fin n) q) : ExteriorIndex n q :=
  ⟨J.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, J.2⟩⟩

theorem exteriorIndexOfSet_enum {n q : ℕ}
    (J : Set.powersetCard (Fin n) q) :
    (exteriorIndexOfSet J).enum = Set.powersetCard.ofFinEmbEquiv.symm J := by
  funext i
  apply Fin.ext
  simp only [ExteriorIndex.enum, exteriorIndexOfSet]
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

/-- Plücker coordinates of an ordered `q`-tuple of rational vectors. -/
def wedgeCoordinates {n q : ℕ} (x : Fin q → Fin n → ℚ) :
    ExteriorVector n q :=
  fun I ↦ Matrix.det (fun i j ↦ x j (I.enum i))

/-- Determinant obtained by evaluating a selected `q`-tuple of local forms
on an ordered `q`-tuple of vectors. -/
def wedgeEvaluation {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (I : ExteriorIndex n q) (x : Fin q → Fin n → ℚ) : ℚ :=
  Matrix.det (fun i j ↦ L v (I.enum i) (x j))

/-- Under the standard exterior basis, evaluation of a Plücker coordinate
by the induced local forms is the determinant `wedgeEvaluation`.  The
transpose only reconciles the row convention for vectors with the row
convention for selected forms. -/
theorem standardExteriorCoordinate_localEvaluation {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (J : Set.powersetCard (Fin n) q) (x : Fin q → Fin n → ℚ) :
    standardExteriorCoordinate
        (fun j ↦ localEvaluationMap L v (x j)) J =
      wedgeEvaluation L v (exteriorIndexOfSet J) x := by
  let B : Matrix (Fin q) (Fin q) ℚ :=
    fun i j ↦ L v ((exteriorIndexOfSet J).enum i) (x j)
  change Matrix.det
      (fun i j ↦ localEvaluationMap L v (x i)
        (Set.powersetCard.ofFinEmbEquiv.symm J j)) = B.det
  calc
    _ = B.transpose.det := by
      apply congrArg Matrix.det
      ext i j
      rw [Matrix.transpose_apply]
      change L v (Set.powersetCard.ofFinEmbEquiv.symm J j) (x i) =
        L v ((exteriorIndexOfSet J).enum j) (x i)
      rw [exteriorIndexOfSet_enum]
    _ = B.det := by simpa only using Matrix.det_transpose B

/-- Fully coordinate-level form of the exterior evaluation identity: the
induced local form indexed by `J`, evaluated at the Plücker vector of `x`,
is the determinant of the corresponding original local evaluations. -/
theorem exteriorLocalForms_apply_wedgeCoordinates {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L)
    (v : Place23) (J : Set.powersetCard (Fin n) q)
    (x : Fin q → Fin n → ℚ) :
    exteriorLocalForms L hL q v (exteriorIndexEquivFin n q J)
        (finWedgeCoordinates x) =
      wedgeEvaluation L v (exteriorIndexOfSet J) x := by
  rw [exteriorLocalForms_apply_finWedgeCoordinates,
    finWedgeCoordinates_apply_equiv]
  exact standardExteriorCoordinate_localEvaluation L v J x

/-- Ultrametric row-product determinant bound.  Unlike the Archimedean
Leibniz estimate, this has no factorial loss. -/
theorem padicNorm_det_le_rowProduct {n p : ℕ} [Fact p.Prime]
    (M : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ)
    (hc : ∀ i, 0 ≤ c i) (hM : ∀ i j, padicNorm p (M i j) ≤ c i) :
    padicNorm p M.det ≤ ∏ i, c i := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  apply padicNorm.sum_le'
  · intro σ _
    let abv : AbsoluteValue ℚ ℚ :=
      IsAbsoluteValue.toAbsoluteValue (padicNorm p)
    have hprod : padicNorm p (∏ i, M.transpose (σ i) i) ≤ ∏ i, c i := by
      change abv (∏ i, M.transpose (σ i) i) ≤ _
      rw [abv.map_prod]
      exact Finset.prod_le_prod (fun i _ ↦ padicNorm.nonneg _)
        (fun i _ ↦ hM i (σ i))
    change abv (Equiv.Perm.sign σ • ∏ i, M.transpose (σ i) i) ≤ _
    rw [abv.map_units_int_smul]
    exact hprod
  · exact Finset.prod_nonneg fun i _ ↦ hc i

/-- Exterior determinant bound used in (5.10) and (5.11).  Passing a
smaller radius in one selected row gives the distinguished-wedge saving
without a separate argument. -/
theorem placeNorm_wedgeEvaluation_le {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (I : ExteriorIndex n q) (x : Fin q → Fin n → ℚ)
    (c : Fin q → ℚ) (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i j, placeNorm v (L v (I.enum i) (x j)) ≤ c i) :
    placeNorm v (wedgeEvaluation L v I x) ≤
      (Nat.factorial q : ℚ) * ∏ i, c i := by
  exact placeNorm_det_le_rowProduct v
    (fun i j ↦ L v (I.enum i) (x j)) c hc hx

/-- The sharp finite-place version of `(5.10)`: at `2` and `3`, the
ultrametric triangle inequality removes the Archimedean factorial. -/
theorem placeNorm_wedgeEvaluation_le_nonarch {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (v : Place23)
    (hv : v ≠ Place23.infinite) (I : ExteriorIndex n q)
    (x : Fin q → Fin n → ℚ) (c : Fin q → ℚ)
    (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i j, placeNorm v (L v (I.enum i) (x j)) ≤ c i) :
    placeNorm v (wedgeEvaluation L v I x) ≤ ∏ i, c i := by
  fin_cases v
  · exact (hv rfl).elim
  · exact padicNorm_det_le_rowProduct
      (fun i j ↦ L Place23.two (I.enum i) (x j)) c hc hx
  · exact padicNorm_det_le_rowProduct
      (fun i j ↦ L Place23.three (I.enum i) (x j)) c hc hx

/-- Coordinate form of (5.10) at the Archimedean place (and a harmlessly
weaker form at finite places): rowwise original-form bounds multiply to a
bound for the corresponding induced exterior form. -/
theorem placeNorm_exteriorLocalForms_apply_le {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L)
    (v : Place23) (J : Set.powersetCard (Fin n) q)
    (x : Fin q → Fin n → ℚ) (c : Fin q → ℚ)
    (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i j,
      placeNorm v (L v ((exteriorIndexOfSet J).enum i) (x j)) ≤ c i) :
    placeNorm v
        (exteriorLocalForms L hL q v (exteriorIndexEquivFin n q J)
          (finWedgeCoordinates x)) ≤
      (Nat.factorial q : ℚ) * ∏ i, c i := by
  rw [exteriorLocalForms_apply_wedgeCoordinates]
  exact placeNorm_wedgeEvaluation_le L v (exteriorIndexOfSet J) x c hc hx

/-- Sharp finite-place coordinate form of (5.10).  In particular, if a
distinguished row has the extra ratio saving from (5.11), that saving enters
the product without an Archimedean factorial. -/
theorem placeNorm_exteriorLocalForms_apply_le_nonarch {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L)
    (v : Place23) (hv : v ≠ Place23.infinite)
    (J : Set.powersetCard (Fin n) q) (x : Fin q → Fin n → ℚ)
    (c : Fin q → ℚ) (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i j,
      placeNorm v (L v ((exteriorIndexOfSet J).enum i) (x j)) ≤ c i) :
    placeNorm v
        (exteriorLocalForms L hL q v (exteriorIndexEquivFin n q J)
          (finWedgeCoordinates x)) ≤ ∏ i, c i := by
  rw [exteriorLocalForms_apply_wedgeCoordinates]
  exact placeNorm_wedgeEvaluation_le_nonarch L v hv
    (exteriorIndexOfSet J) x c hc hx

/-- Real-radius version used by the logarithmic boxes.  It permits radii
such as `Q ^ c` and successive-minimum factors without first rounding them
to rationals. -/
theorem realPlaceNorm_exteriorLocalForms_apply_le {n q : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (hL : IsNonsingularFamily L)
    (v : Place23) (J : Set.powersetCard (Fin n) q)
    (x : Fin q → Fin n → ℚ) (c : Fin q → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hx : ∀ i j,
      HeightBoxes.realPlaceNorm v
        (L v ((exteriorIndexOfSet J).enum i) (x j)) ≤ c i) :
    HeightBoxes.realPlaceNorm v
        (exteriorLocalForms L hL q v (exteriorIndexEquivFin n q J)
          (finWedgeCoordinates x)) ≤
      (Nat.factorial q : ℝ) * ∏ i, c i := by
  rw [exteriorLocalForms_apply_wedgeCoordinates]
  exact PadicSubspace.real_placeNorm_det_le_rowProduct v
    (fun i j ↦ L v ((exteriorIndexOfSet J).enum i) (x j)) c hc hx

/-- A determinant row bound with one permutation-dependent saved entry.
For every Leibniz term the saved entry may occur in a different row.  This
is the precise shape needed in (5.11): if the selected columns are not the
distinguished tail, every matching pairs some tail row with an earlier
column. -/
theorem real_placeNorm_det_le_rowProduct_with_saving {m : ℕ}
    (place : Place23) (M : Matrix (Fin m) (Fin m) ℚ)
    (r : Fin m → ℝ) (saving : ℝ)
    (hr : ∀ i, 0 ≤ r i) (hsaving : 0 ≤ saving)
    (hbase : ∀ i j,
      HeightBoxes.realPlaceNorm place (M i j) ≤ r i)
    (hsaved : ∀ σ : Equiv.Perm (Fin m), ∃ i,
      HeightBoxes.realPlaceNorm place (M i (σ i)) ≤ saving * r i) :
    HeightBoxes.realPlaceNorm place M.det ≤
      (Nat.factorial m : ℝ) * saving * ∏ i, r i := by
  let abv : AbsoluteValue ℚ ℚ :=
    IsAbsoluteValue.toAbsoluteValue (placeNorm place)
  rw [← Matrix.det_transpose, Matrix.det_apply]
  calc
    HeightBoxes.realPlaceNorm place
        (∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ •
          ∏ i, Mᵀ (σ i) i) ≤
        ∑ σ : Equiv.Perm (Fin m),
          HeightBoxes.realPlaceNorm place
            (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) := by
      change ((placeNorm place
          (∑ σ : Equiv.Perm (Fin m), Equiv.Perm.sign σ •
            ∏ i, Mᵀ (σ i) i) : ℚ) : ℝ) ≤
        ∑ σ : Equiv.Perm (Fin m),
          ((placeNorm place
            (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) : ℚ) : ℝ)
      exact_mod_cast (abv.sum_le Finset.univ
        (fun σ : Equiv.Perm (Fin m) =>
          Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i))
    _ = ∑ σ : Equiv.Perm (Fin m),
          ∏ i, HeightBoxes.realPlaceNorm place (M i (σ i)) := by
      apply Finset.sum_congr rfl
      intro σ _
      change ((placeNorm place
          (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) : ℚ) : ℝ) = _
      have hq : placeNorm place
          (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) =
          ∏ i, placeNorm place (M i (σ i)) := by
        change abv (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) = _
        rw [abv.map_units_int_smul, abv.map_prod]
        rfl
      calc
        ((placeNorm place
            (Equiv.Perm.sign σ • ∏ i, Mᵀ (σ i) i) : ℚ) : ℝ) =
            ((∏ i, placeNorm place (M i (σ i)) : ℚ) : ℝ) :=
          congrArg ((↑) : ℚ → ℝ) hq
        _ = ∏ i, HeightBoxes.realPlaceNorm place (M i (σ i)) := by
          push_cast
          rfl
    _ ≤ ∑ _σ : Equiv.Perm (Fin m), saving * ∏ i, r i := by
      apply Finset.sum_le_sum
      intro σ _
      obtain ⟨i, hi⟩ := hsaved σ
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j ↦ HeightBoxes.realPlaceNorm place (M j (σ j)))
        (Finset.mem_univ i)]
      rw [← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i)]
      have hprodnonneg : 0 ≤ ∏ j ∈ Finset.univ.erase i,
          HeightBoxes.realPlaceNorm place (M j (σ j)) :=
        Finset.prod_nonneg fun j _ ↦ HeightBoxes.realPlaceNorm_nonneg place _
      have hprodle : (∏ j ∈ Finset.univ.erase i,
          HeightBoxes.realPlaceNorm place (M j (σ j))) ≤
          ∏ j ∈ Finset.univ.erase i, r j := by
        apply Finset.prod_le_prod
        · intro j _
          exact HeightBoxes.realPlaceNorm_nonneg place _
        · intro j _
          exact hbase j (σ j)
      calc
        HeightBoxes.realPlaceNorm place (M i (σ i)) *
            ∏ j ∈ Finset.univ.erase i,
              HeightBoxes.realPlaceNorm place (M j (σ j)) ≤
            (saving * r i) * ∏ j ∈ Finset.univ.erase i, r j := by
          exact mul_le_mul hi hprodle hprodnonneg
            (mul_nonneg hsaving (hr i))
        _ = saving * (r i * ∏ j ∈ Finset.univ.erase i, r j) := by ring
    _ = (Nat.factorial m : ℝ) * saving * ∏ i, r i := by
      simp [Fintype.card_perm]
      ring

/-- The determinant form of Evertse's pairwise-minimum estimate.  All
selected rows have size at least `lower`, while one selected column has
size at most `upper`.  Hence every permutation term saves the ratio
`upper / lower`. -/
theorem realPlaceNorm_exteriorLocalForms_apply_le_with_saving
    {n q : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (place : Place23)
    (I J : Set.powersetCard (Fin n) q)
    (v : Fin n → Fin n → ℚ) (mu : Fin n → ℝ)
    (A lower upper : ℝ) (hA : 0 ≤ A) (hlower : 0 < lower)
    (hupper : 0 ≤ upper)
    (hrows : ∀ a : Fin q, lower ≤
      mu ((exteriorIndexOfSet I).enum a))
    (hlowColumn : ∃ b : Fin q,
      mu ((exteriorIndexOfSet J).enum b) ≤ upper)
    (hentry : ∀ a b : Fin q,
      HeightBoxes.realPlaceNorm place
          (L place ((exteriorIndexOfSet I).enum a)
            (v ((exteriorIndexOfSet J).enum b))) ≤
        A * min (mu ((exteriorIndexOfSet I).enum a))
          (mu ((exteriorIndexOfSet J).enum b))) :
    HeightBoxes.realPlaceNorm place
        (exteriorLocalForms L hL q place (exteriorIndexEquivFin n q I)
          (finExteriorBasisWedge v J)) ≤
      (Nat.factorial q : ℝ) * (upper / lower) *
        ∏ a, A * mu ((exteriorIndexOfSet I).enum a) := by
  rw [finExteriorBasisWedge_eq_finWedgeCoordinates,
    exteriorLocalForms_apply_wedgeCoordinates]
  let M : Matrix (Fin q) (Fin q) ℚ := fun a b ↦
    L place ((exteriorIndexOfSet I).enum a)
      (v ((exteriorIndexOfSet J).enum b))
  let r : Fin q → ℝ := fun a ↦
    A * mu ((exteriorIndexOfSet I).enum a)
  have hmuRows : ∀ a, 0 ≤ mu ((exteriorIndexOfSet I).enum a) := by
    intro a
    exact hlower.le.trans (hrows a)
  have hr : ∀ a, 0 ≤ r a := fun a ↦ mul_nonneg hA (hmuRows a)
  have hratio : 0 ≤ upper / lower := div_nonneg hupper hlower.le
  apply real_placeNorm_det_le_rowProduct_with_saving place M r
    (upper / lower) hr hratio
  · intro a b
    exact (hentry a b).trans <| by
      dsimp only [r]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) hA
  · intro σ
    obtain ⟨b, hb⟩ := hlowColumn
    let a : Fin q := σ.symm b
    refine ⟨a, ?_⟩
    have hcol : σ a = b := by simp [a]
    have hfirst : HeightBoxes.realPlaceNorm place (M a (σ a)) ≤
        A * upper := by
      calc
        HeightBoxes.realPlaceNorm place (M a (σ a)) ≤
            A * min (mu ((exteriorIndexOfSet I).enum a))
              (mu ((exteriorIndexOfSet J).enum (σ a))) := hentry a (σ a)
        _ ≤ A * mu ((exteriorIndexOfSet J).enum (σ a)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hA
        _ ≤ A * upper := by
          rw [hcol]
          exact mul_le_mul_of_nonneg_left hb hA
    have hratioRow : upper ≤
        (upper / lower) * mu ((exteriorIndexOfSet I).enum a) := by
      have hmul := mul_le_mul_of_nonneg_left (hrows a) hratio
      calc
        upper = (upper / lower) * lower := by
          field_simp
        _ ≤ (upper / lower) * mu ((exteriorIndexOfSet I).enum a) := hmul
    calc
      HeightBoxes.realPlaceNorm place (M a (σ a)) ≤ A * upper := hfirst
      _ ≤ A * ((upper / lower) *
          mu ((exteriorIndexOfSet I).enum a)) :=
        mul_le_mul_of_nonneg_left hratioRow hA
      _ = (upper / lower) * r a := by
        simp only [r]
        ring

/-- Turn rowwise bounds for one selected basis wedge into membership in an
exterior logarithmic box.  The caller may use a smaller row radius in the
distinguished coordinate, which is exactly the saving in (5.11). -/
theorem finExteriorBasisWedge_mem_approximationBox_of_rowBounds
    {n q : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (v : Fin n → Fin n → ℚ)
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose q))
    (Jvec : Set.powersetCard (Fin n) q)
    (r : Place23 → Set.powersetCard (Fin n) q → Fin q → ℝ)
    (hrnonneg : ∀ place K a, 0 ≤ r place K a)
    (hrow : ∀ place K a b,
      HeightBoxes.realPlaceNorm place
        (L place ((exteriorIndexOfSet K).enum a)
          (v (Set.powersetCard.ofFinEmbEquiv.symm Jvec b))) ≤
        r place K a)
    (hradius : ∀ place K,
      (Nat.factorial q : ℝ) * ∏ a, r place K a ≤
        HeightBoxes.exponentRadius (Q : ℝ) c place
          (exteriorIndexEquivFin n q K)) :
    HeightBoxes.InApproximationBox (exteriorLocalForms L hL q)
      (Q : ℝ) c (finExteriorBasisWedge v Jvec) := by
  intro place i
  let K := (exteriorIndexEquivFin n q).symm i
  have hi : i = exteriorIndexEquivFin n q K := by simp [K]
  rw [hi, finExteriorBasisWedge_eq_finWedgeCoordinates]
  exact (realPlaceNorm_exteriorLocalForms_apply_le L hL place K
    (fun b ↦ v (Set.powersetCard.ofFinEmbEquiv.symm Jvec b))
    (r place K) (hrnonneg place K) (hrow place K)).trans
      (hradius place K)

/-! ### `S`-integrality of Plücker coordinates -/

theorem inZOneSixScalar_sum {α : Type*} (s : Finset α) (f : α → ℚ)
    (hf : ∀ i ∈ s, SIntegerApproximation.InZOneSixScalar (f i)) :
    SIntegerApproximation.InZOneSixScalar (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SIntegerApproximation.InZOneSixScalar.zero
  | @insert i s his ih =>
      rw [Finset.sum_insert his]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

theorem inZOneSixScalar_prod {α : Type*} (s : Finset α) (f : α → ℚ)
    (hf : ∀ i ∈ s, SIntegerApproximation.InZOneSixScalar (f i)) :
    SIntegerApproximation.InZOneSixScalar (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using SIntegerApproximation.InZOneSixScalar.intCast 1
  | @insert i s his ih =>
      rw [Finset.prod_insert his]
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- A determinant of `S`-integer entries is again an `S`-integer. -/
theorem inZOneSixScalar_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : ∀ i j, SIntegerApproximation.InZOneSixScalar (M i j)) :
    SIntegerApproximation.InZOneSixScalar M.det := by
  classical
  rw [Matrix.det_apply]
  apply inZOneSixScalar_sum Finset.univ _
  intro σ hσ
  have hprod : SIntegerApproximation.InZOneSixScalar
      (∏ i, M (σ i) i) := by
    simpa using inZOneSixScalar_prod Finset.univ
      (fun i ↦ M (σ i) i) (fun i hi ↦ hM (σ i) i)
  have hsign := SIntegerApproximation.InZOneSixScalar.intCast
    (↑(Equiv.Perm.sign σ) : ℤ)
  have hmul := hsign.mul hprod
  simpa [Units.smul_def] using hmul

/-- For a finite rational vector, coordinatewise `S`-integrality is
equivalent to the existence of one common `6`-power denominator. -/
theorem inZOneSix_iff_forall_scalar {n : ℕ} (x : Fin n → ℚ) :
    AdelicMinkowski.InZOneSix x ↔
      ∀ i, SIntegerApproximation.InZOneSixScalar (x i) := by
  constructor
  · rintro ⟨k, z, hz⟩ i
    rw [SIntegerApproximation.inZOneSixScalar_iff]
    exact ⟨k, z i, hz i⟩
  · intro hx
    choose k z hz using fun i ↦
      (SIntegerApproximation.inZOneSixScalar_iff (x i)).mp (hx i)
    let K : ℕ := Finset.univ.sup k
    have hex : ∀ i, ∃ w : ℤ,
        x i = (w : ℚ) / AdelicMinkowski.denominator K := by
      intro i
      have hki : k i ≤ K :=
        Finset.le_sup (s := Finset.univ) (f := k) (Finset.mem_univ i)
      have hi : AdelicMinkowski.InDenominatorLattice (n := 1) (k i)
          (fun _ ↦ x i) :=
        ⟨fun _ ↦ z i, fun j ↦ by simpa using hz i⟩
      obtain ⟨w, hw⟩ := hi.mono hki
      exact ⟨w 0, by simpa using hw 0⟩
    choose w hw using hex
    exact ⟨K, w, hw⟩

theorem standardExteriorCoordinate_inZOneSix {n q : ℕ}
    (x : Fin q → Fin n → ℚ)
    (hx : ∀ i j, SIntegerApproximation.InZOneSixScalar (x i j))
    (J : Set.powersetCard (Fin n) q) :
    SIntegerApproximation.InZOneSixScalar
      (standardExteriorCoordinate x J) := by
  apply inZOneSixScalar_det
  intro i j
  exact hx i _

/-- Exterior products of `S`-integer vectors have one common `6`-power
denominator in the finite Plücker coordinate model. -/
theorem finWedgeCoordinates_inZOneSix {n q : ℕ}
    (x : Fin q → Fin n → ℚ)
    (hx : ∀ i, AdelicMinkowski.InZOneSix (x i)) :
    AdelicMinkowski.InZOneSix (finWedgeCoordinates x) := by
  rw [inZOneSix_iff_forall_scalar]
  intro i
  let J := (exteriorIndexEquivFin n q).symm i
  have hcoord := standardExteriorCoordinate_inZOneSix x
    (fun a b ↦ (inZOneSix_iff_forall_scalar (x a)).mp (hx a) b) J
  have hi : i = exteriorIndexEquivFin n q J := by simp [J]
  rw [hi, finWedgeCoordinates_apply_equiv]
  exact hcoord

theorem finExteriorBasisWedge_inZOneSix {n q : ℕ}
    (v : Fin n → Fin n → ℚ)
    (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (J : Set.powersetCard (Fin n) q) :
    AdelicMinkowski.InZOneSix (finExteriorBasisWedge v J) := by
  rw [finExteriorBasisWedge_eq_finWedgeCoordinates]
  apply finWedgeCoordinates_inZOneSix
  intro a
  exact hvS _

/-- Membership package for one exterior witness in the actual S-integral
real-radius domain consumed by `RankDrop`. -/
theorem finExteriorBasisWedge_mem_realSIntegralApproximationDomain
    {n q : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) (v : Fin n → Fin n → ℚ)
    (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose q))
    (J : Set.powersetCard (Fin n) q)
    (hbound : HeightBoxes.InApproximationBox
      (exteriorLocalForms L hL q) (Q : ℝ) c
      (finExteriorBasisWedge v J)) :
    finExteriorBasisWedge v J ∈
      Erdos407.RankDrop.realSIntegralApproximationDomain
        (exteriorLocalForms L hL q) Q c := by
  exact ⟨finExteriorBasisWedge_inZOneSix v hvS J, hbound⟩

/-- Lemma 5.3's exact-rank conclusion, separated from its analytic bounds:
the omitted wedges give rank at least `D-1`, while the determinant/product
argument gives failure of full rank. -/
theorem realSExteriorApproximationRank_eq_pred_of_basisWedges
    {n q : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) {v : Fin n → Fin n → ℚ}
    (hv : LinearIndependent ℚ v)
    (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose q))
    (J₀ : Set.powersetCard (Fin n) q)
    (hbound : ∀ J : OmittedExteriorIndex J₀,
      HeightBoxes.InApproximationBox
        (exteriorLocalForms L hL q) (Q : ℝ) c
        (finExteriorBasisWedge v J.1))
    (hproper : Erdos407.RankDrop.realSApproximationRank
      (exteriorLocalForms L hL q) Q c < n.choose q) :
    Erdos407.RankDrop.realSApproximationRank
        (exteriorLocalForms L hL q) Q c + 1 = n.choose q := by
  apply exteriorSpan_finrank_eq_pred hv J₀
    (Erdos407.RankDrop.realSApproximationSpan
      (exteriorLocalForms L hL q) Q c)
  · intro J
    apply Erdos407.RankDrop.mem_realSApproximationSpan
    exact finExteriorBasisWedge_mem_realSIntegralApproximationDomain
      L hL v hvS Q c J.1 (hbound J)
  · exact hproper

theorem realSExteriorApproximationRank_eq_pred_of_smallRadii
    {n q : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) {v : Fin n → Fin n → ℚ}
    (hv : LinearIndependent ℚ v)
    (hvS : ∀ i, AdelicMinkowski.InZOneSix (v i))
    (Q : ℕ) (c : HeightBoxes.LocalConstants (n.choose q))
    (J₀ : Set.powersetCard (Fin n) q)
    (hbound : ∀ J : OmittedExteriorIndex J₀,
      HeightBoxes.InApproximationBox
        (exteriorLocalForms L hL q) (Q : ℝ) c
        (finExteriorBasisWedge v J.1))
    (hsmall : (Nat.factorial (n.choose q) : ℝ) ^ 3 *
        HeightBoxes.exponentRadiiProduct (Q : ℝ) c <
      realFormDetProduct (exteriorLocalForms L hL q)) :
    Erdos407.RankDrop.realSApproximationRank
        (exteriorLocalForms L hL q) Q c + 1 = n.choose q := by
  apply realSExteriorApproximationRank_eq_pred_of_basisWedges
    L hL hv hvS Q c J₀ hbound
  exact Erdos407.RankDrop.realSApproximationRank_lt_of_radiiProduct
    (exteriorLocalForms L hL q) Q c hsmall

/-- Cutoff form of Lemma 5.3 for one discretized exterior exponent array.
The cutoff depends only on the exterior forms and exponents, not on the
adapted S-integral basis providing the `D-1` witnesses. -/
theorem exists_realSExteriorApproximationRank_eq_pred_cutoff
    {n q : ℕ} (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L)
    (c : HeightBoxes.LocalConstants (n.choose q))
    {delta : ℝ} (hdelta : 0 < delta)
    (hc : (∑ place, ∑ i, c place i) ≤ -delta) :
    ∃ Q₀ : ℕ, ∀ Q, Q₀ ≤ Q →
      ∀ (v : Fin n → Fin n → ℚ), LinearIndependent ℚ v →
      (∀ i, AdelicMinkowski.InZOneSix (v i)) →
      ∀ J₀ : Set.powersetCard (Fin n) q,
      (∀ J : OmittedExteriorIndex J₀,
        HeightBoxes.InApproximationBox
          (exteriorLocalForms L hL q) (Q : ℝ) c
          (finExteriorBasisWedge v J.1)) →
      Erdos407.RankDrop.realSApproximationRank
          (exteriorLocalForms L hL q) Q c + 1 = n.choose q := by
  obtain ⟨Q₀, hQ₀⟩ := Erdos407.RankDrop.exists_sRankDeficient_cutoff
    (exteriorLocalForms L hL q) (exteriorLocalForms_nonsingular L hL q)
    c hdelta hc
  refine ⟨Q₀, ?_⟩
  intro Q hQ v hv hvS J₀ hbound
  apply realSExteriorApproximationRank_eq_pred_of_basisWedges
    L hL hv hvS Q c J₀ hbound
  exact hQ₀ Q hQ

/-- The `m` coordinate vectors other than `j` in an `(m+1)`-dimensional
coordinate space. -/
noncomputable def omittedCoordinateBasis {m : ℕ} (j : Fin (m + 1)) :
    Fin m → Fin (m + 1) → ℚ :=
  (Pi.basisFun ℚ (Fin (m + 1))) ∘ j.succAbove

theorem omittedCoordinateBasis_linearIndependent {m : ℕ} (j : Fin (m + 1)) :
    LinearIndependent ℚ (omittedCoordinateBasis j) := by
  have hbasis : LinearIndependent ℚ (Pi.basisFun ℚ (Fin (m + 1))) :=
    (Pi.basisFun ℚ (Fin (m + 1))).linearIndependent
  exact hbasis.comp j.succAbove Fin.succAbove_right_injective

/-- The omitted coordinate wedges provide the lower `N-1` successive-minimum
witness in Lemma 5.3. -/
theorem hasRankAtLeast_pred_of_omittedCoordinateBasis {m : ℕ}
    (j : Fin (m + 1)) (D : Set (Fin (m + 1) → ℚ))
    (hmem : ∀ i, omittedCoordinateBasis j i ∈ D) :
    AdelicMinkowski.HasRankAtLeast D m :=
  ⟨omittedCoordinateBasis j, omittedCoordinateBasis_linearIndependent j, hmem⟩

/-! ## The triangular basis change from GLR Lemma 5.2 -/

theorem evertseTransform_linearIndependent {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {x : Fin n → Fin n → ℚ}
    (hA : EvertseBasis.IsUnitLowerTriangular A)
    (hx : LinearIndependent ℚ x) :
    LinearIndependent ℚ (EvertseBasis.transformBasis A x) := by
  let X : Matrix (Fin n) (Fin n) ℚ := fun i j ↦ x i j
  have hX : IsUnit X := by
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    exact hx
  have hAdet : A.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular A hA.1]
    simp [hA.2]
  have hAu : IsUnit A := by
    rw [Matrix.isUnit_iff_isUnit_det, hAdet]
    exact isUnit_one
  have hmul : IsUnit (A * X) := hAu.mul hX
  let Y : Matrix (Fin n) (Fin n) ℚ :=
    fun i j ↦ EvertseBasis.transformBasis A x i j
  change LinearIndependent ℚ Y.row
  rw [Matrix.linearIndependent_rows_iff_isUnit]
  have heq : Y = A * X := by
    ext i j
    simp only [Y, Matrix.mul_apply, X, EvertseBasis.transformBasis,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [heq]
  exact hmul

theorem evertseTransform_inZOneSix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {x : Fin n → Fin n → ℚ}
    (hA : ∀ i j,
      AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ A i j))
    (hx : ∀ i, AdelicMinkowski.InZOneSix (x i)) :
    ∀ i, AdelicMinkowski.InZOneSix (EvertseBasis.transformBasis A x i) := by
  intro i
  rw [inZOneSix_iff_forall_scalar]
  intro k
  simp only [EvertseBasis.transformBasis, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  apply inZOneSixScalar_sum Finset.univ
  intro j hj
  apply SIntegerApproximation.InZOneSixScalar.mul
  · exact (inZOneSix_iff_forall_scalar (fun _ : Fin 1 ↦ A i j)).mp
      (hA i j) 0
  · exact (inZOneSix_iff_forall_scalar (x j)).mp (hx j) k

/-- Span of the first `k` vectors in an `n`-tuple. -/
noncomputable def initialBasisSpan {n : ℕ} (x : Fin n → Fin n → ℚ)
    (k : ℕ) (hk : k ≤ n) : Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ (Set.range (fun i : Fin k ↦ x (Fin.castLE hk i)))

theorem finrank_initialBasisSpan {n : ℕ} {x : Fin n → Fin n → ℚ}
    (hx : LinearIndependent ℚ x) (k : ℕ) (hk : k ≤ n) :
    Module.finrank ℚ (initialBasisSpan x k hk) = k := by
  rw [initialBasisSpan, finrank_span_eq_card]
  · simp
  · exact hx.comp (Fin.castLE hk) (Fin.castLE_injective hk)

/-- A lower-triangular change cannot move an initial vector outside the
corresponding initial span. -/
theorem initialBasisSpan_transform_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {x : Fin n → Fin n → ℚ}
    (hA : EvertseBasis.IsUnitLowerTriangular A)
    (k : ℕ) (hk : k ≤ n) :
    initialBasisSpan (EvertseBasis.transformBasis A x) k hk ≤
      initialBasisSpan x k hk := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  simp only [EvertseBasis.transformBasis]
  apply Submodule.sum_mem
  intro j _
  by_cases hj : j.val < k
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨⟨j.val, hj⟩, ?_⟩
    congr
  · have hij : Fin.castLE hk i < j := by
      change i.val < j.val
      omega
    have hz : A (Fin.castLE hk i) j = 0 := hA.1 hij
    simp [hz]

/-- Unit lower-triangular changes preserve every initial span.  This is the
precise flag-preservation statement used when the exterior hyperplane is
dualized back to the original `k`-space. -/
theorem initialBasisSpan_evertseTransform_eq {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {x : Fin n → Fin n → ℚ}
    (hA : EvertseBasis.IsUnitLowerTriangular A)
    (hx : LinearIndependent ℚ x) (k : ℕ) (hk : k ≤ n) :
    initialBasisSpan (EvertseBasis.transformBasis A x) k hk =
      initialBasisSpan x k hk := by
  apply Submodule.eq_of_le_of_finrank_eq
    (initialBasisSpan_transform_le hA k hk)
  rw [finrank_initialBasisSpan
      (evertseTransform_linearIndependent hA hx) k hk,
    finrank_initialBasisSpan hx k hk]

/-- Exterior-ready form of GLR Lemma 5.2: the transformed basis is both
linearly independent and S-integral, in addition to satisfying Evertse's
pairwise minimum bounds. -/
theorem exists_evertseBasis_exteriorReady {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (hL : IsNonsingularFamily L) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (x : Fin n → Fin n → ℚ) (mu : Place23 → Fin n → ℝ),
        LinearIndependent ℚ x →
        (∀ i, AdelicMinkowski.InZOneSix (x i)) →
        (∀ place i, 0 < mu place i) →
        (∀ place, Monotone (mu place)) →
        (∀ place k j,
          HeightBoxes.realPlaceNorm place (L place k (x j)) ≤ mu place j) →
        ∃ v : Fin n → Fin n → ℚ,
          LinearIndependent ℚ v ∧
          (∀ i, AdelicMinkowski.InZOneSix (v i)) ∧
          ∃ pi : Place23 → Equiv.Perm (Fin n), ∀ place i j,
            HeightBoxes.realPlaceNorm place (L place (pi place i) (v j)) ≤
              (if place = Place23.infinite then C else 1) *
                min (mu place i) (mu place j) := by
  obtain ⟨C, hC, hE⟩ := EvertseBasis.exists_evertseBasis L hL
  refine ⟨C, hC, ?_⟩
  intro x mu hx hxS hmu hmono hbound
  obtain ⟨A, hAtri, hAS, pi, hpi⟩ := hE x mu hx hmu hmono (by
    intro place k j
    exact hbound place k j)
  let v := EvertseBasis.transformBasis A x
  refine ⟨v, evertseTransform_linearIndependent hAtri hx,
    evertseTransform_inZOneSix hAS hxS, pi, ?_⟩
  intro place i j
  exact hpi place i j

/-- A unit lower-triangular rational matrix.  In the rational three-place
argument the entries below the diagonal are chosen in `ℤ[1/6]`; the
determinant calculation only uses triangularity and the unit diagonal. -/
def IsUnitLowerTriangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  A.IsLowerTriangular ∧ ∀ i, A i i = 1

theorem IsUnitLowerTriangular.det {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : IsUnitLowerTriangular A) : A.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular A hA.1]
  simp [hA.2]

theorem IsUnitLowerTriangular.det_ne_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} (hA : IsUnitLowerTriangular A) :
    A.det ≠ 0 := by
  rw [hA.det]
  exact one_ne_zero

/-- Coordinate form of the triangular basis furnished by GLR Lemma 5.2.
The coefficient condition is stated using the already formalized
three-place ring `ℤ[1/6]`. -/
structure TriangularSIntegralBasis (n : ℕ) where
  change : Matrix (Fin n) (Fin n) ℚ
  lower : IsUnitLowerTriangular change
  sIntegral : ∀ i j, AdelicMinkowski.InZOneSix (fun _ : Fin 1 ↦ change i j)

namespace TriangularSIntegralBasis

/-- The identity change of basis is an `S`-integral triangular change. -/
def identity (n : ℕ) : TriangularSIntegralBasis n where
  change := 1
  lower := by
    constructor
    · intro i j hij
      have hij' : i < j := hij
      rw [Matrix.one_apply]
      exact if_neg (ne_of_lt hij')
    · intro i
      simp
  sIntegral := by
    intro i j
    refine ⟨0, ?_⟩
    refine ⟨fun k ↦ if i = j then 1 else 0, fun k ↦ ?_⟩
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij,
      AdelicMinkowski.denominator]

theorem det (T : TriangularSIntegralBasis n) : T.change.det = 1 :=
  T.lower.det

theorem isUnit (T : TriangularSIntegralBasis n) : IsUnit T.change := by
  rw [Matrix.isUnit_iff_isUnit_det, T.det]
  exact isUnit_one

end TriangularSIntegralBasis

/-! ## Successive-minimum rank gap (the rank content of GLR Lemma 5.3) -/

/-- A positive total logarithmic growth over `m` consecutive minima forces
one successive-minimum gap to carry at least the average growth. -/
theorem exists_gap_ge_average {m : ℕ} (hm : 0 < m)
    (g : Fin m → ℝ) (ε : ℝ) (hsum : ε ≤ ∑ i, g i) :
    ∃ i, ε / m ≤ g i := by
  by_contra h
  push Not at h
  have hlt : (∑ i, g i) < ∑ _i : Fin m, ε / m := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (h i).le
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _, h ⟨0, hm⟩⟩
  have hcard : (∑ _i : Fin m, ε / m) = ε := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [hcard] at hlt
  exact (not_lt_of_ge hsum) hlt

/-- If a set in `ℚᴺ` contains `N-1` independent points but no independent
`N`-tuple, then its rational rank is exactly `N-1`.  In Lemma 5.3 the first
condition is supplied by all basis wedges except the distinguished wedge,
and the second by the successive-minimum gap and Minkowski's second theorem. -/
theorem rank_eq_pred_of_exterior_minima_gap {N : ℕ} (hN : 0 < N)
    (D : Set (Fin N → ℚ))
    (hlow : AdelicMinkowski.HasRankAtLeast D (N - 1))
    (hgap : ¬ AdelicMinkowski.HasRankAtLeast D N) :
    rationalSetRank D = N - 1 := by
  have hlo : N - 1 ≤ rationalSetRank D :=
    (Erdos407.RankDrop.hasRankAtLeast_iff_le_finrank D).mp hlow
  have hlt : rationalSetRank D < N := by
    by_contra h
    exact hgap ((Erdos407.RankDrop.hasRankAtLeast_iff_le_finrank D).mpr
      (not_lt.mp h))
  omega

/-- The same statement for an exterior coordinate space. -/
theorem exterior_rank_eq_pred_of_minima_gap {n q : ℕ}
    (hN : 0 < n.choose q) (D : Set (Fin (n.choose q) → ℚ))
    (hlow : AdelicMinkowski.HasRankAtLeast D (n.choose q - 1))
    (hgap : ¬ AdelicMinkowski.HasRankAtLeast D (n.choose q)) :
    rationalSetRank D = n.choose q - 1 :=
  rank_eq_pred_of_exterior_minima_gap hN D hlow hgap

/-! ## Discretizing the exterior exponents -/

/-- Every original coordinate occurs in exactly
`(n-1).choose(q-1)` exterior coordinates.  This is the combinatorial identity
behind the total exterior-exponent sum at the end of §5.3. -/
theorem sum_powersetCard_sum_apply {n q : ℕ} (hq : 0 < q)
    (c : Fin n → ℝ) :
    ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard q,
        ∑ i ∈ J, c i =
      (n - 1).choose (q - 1) * ∑ i, c i := by
  classical
  let P := (Finset.univ : Finset (Fin n)).powersetCard q
  calc
    ∑ J ∈ P, ∑ i ∈ J, c i =
        ∑ J ∈ P, ∑ i : Fin n, if i ∈ J then c i else 0 := by
      apply Finset.sum_congr rfl
      intro J hJ
      simp
    _ = ∑ i : Fin n, ∑ J ∈ P, if i ∈ J then c i else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n,
        ((P.filter fun J ↦ i ∈ J).card : ℝ) * c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp
    _ = ∑ i : Fin n, ((n - 1).choose (q - 1) : ℝ) * c i := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2
      change ((Finset.univ.powersetCard q).filter fun J ↦ i ∈ J).card = _
      rw [show (Finset.univ.powersetCard q).filter (fun J ↦ i ∈ J) =
          (Finset.univ.powersetCard q).filter ({i} ⊆ ·) by
        apply Finset.filter_congr
        intro J hJ
        simp]
      simpa using Finset.card_filter_powersetCard_subset
        ({i} : Finset (Fin n)) Finset.univ q (Finset.subset_univ _)
        (by simp; omega)
    _ = (n - 1).choose (q - 1) * ∑ i, c i := by
      rw [Finset.mul_sum]

theorem sum_exteriorEnumeration_eq_sum_finset {n q : ℕ}
    (J : Set.powersetCard (Fin n) q) (c : Fin n → ℝ) :
    ∑ i : Fin q, c (Set.powersetCard.ofFinEmbEquiv.symm J i) =
      ∑ i ∈ J.1, c i := by
  rw [Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change (∑ i : Fin q, c ((J.1.orderIsoOfFin J.2 i).1)) = _
  calc
    ∑ i : Fin q, c ((J.1.orderIsoOfFin J.2 i).1) =
        ∑ i : J.1, c i := by
      exact Equiv.sum_comp (J.1.orderIsoOfFin J.2).toEquiv
        (fun i : J.1 ↦ c i)
    _ = ∑ i ∈ J.1, c i := Finset.sum_attach J.1 c

/-- Coordinate-indexed version of `sum_powersetCard_sum_apply`, matching
the standard exterior basis used by `exteriorLocalForms`. -/
theorem sum_exteriorCoordinateSums {n q : ℕ} (hq : 0 < q)
    (c : Fin n → ℝ) :
    ∑ J : Set.powersetCard (Fin n) q,
        ∑ i : Fin q, c (Set.powersetCard.ofFinEmbEquiv.symm J i) =
      (n - 1).choose (q - 1) * ∑ i, c i := by
  calc
    _ = ∑ J : Set.powersetCard (Fin n) q, ∑ i ∈ J.1, c i := by
      apply Finset.sum_congr rfl
      intro J hJ
      exact sum_exteriorEnumeration_eq_sum_finset J c
    _ = ∑ J ∈ (Finset.univ : Finset (Fin n)).powersetCard q,
          ∑ i ∈ J, c i := by
      symm
      exact Finset.sum_subtype _ (fun _ ↦ Finset.mem_powersetCard_univ) _
    _ = _ := sum_powersetCard_sum_apply hq c

/-- Permuting the local forms does not alter the total exterior-coordinate
sum.  This is the form used with the place-dependent permutations supplied
by Lemma 5.2. -/
theorem sum_exteriorCoordinateSums_perm {n q : ℕ} (hq : 0 < q)
    (c : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    ∑ J : Set.powersetCard (Fin n) q,
        ∑ i : Fin q,
          c (π (Set.powersetCard.ofFinEmbEquiv.symm J i)) =
      (n - 1).choose (q - 1) * ∑ i, c i := by
  calc
    _ = (n - 1).choose (q - 1) * ∑ i, (c ∘ π) i := by
      simpa only [Function.comp_apply] using
        sum_exteriorCoordinateSums hq (c ∘ π)
    _ = _ := by
      have hsum : ∑ i, (c ∘ π) i = ∑ i, c i := by
        simpa only [Function.comp_apply] using Equiv.sum_comp π c
      rw [hsum]

/-- Adding the successive-minimum saving to one distinguished exterior
coordinate adds that saving exactly once to the total exponent sum. -/
theorem sum_exteriorCoordinateSums_with_saving {n q : ℕ} (hq : 0 < q)
    (c : Fin n → ℝ) (π : Equiv.Perm (Fin n))
    (J₀ : Set.powersetCard (Fin n) q) (saving : ℝ) :
    ∑ J : Set.powersetCard (Fin n) q,
        ((∑ i : Fin q,
          c (π (Set.powersetCard.ofFinEmbEquiv.symm J i))) +
          if J = J₀ then saving else 0) =
      (n - 1).choose (q - 1) * ∑ i, c i + saving := by
  rw [Finset.sum_add_distrib, sum_exteriorCoordinateSums_perm hq]
  simp

/-- Three-place version of the preceding identity. -/
theorem sum_localExteriorCoordinateSums_with_saving {n q : ℕ} (hq : 0 < q)
    (c : Place23 → Fin n → ℝ) (π : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) :
    ∑ v, ∑ J : Set.powersetCard (Fin n) q,
        ((∑ i : Fin q,
          c v (π v (Set.powersetCard.ofFinEmbEquiv.symm J i))) +
          if J = J₀ v then saving v else 0) =
      (n - 1).choose (q - 1) * (∑ v, ∑ i, c v i) + ∑ v, saving v := by
  simp_rw [sum_exteriorCoordinateSums_with_saving hq]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The undiscretized exterior exponent array: sum the original exponents
over a coordinate subset, and add the successive-minimum saving on the one
distinguished coordinate. -/
noncomputable def exteriorLocalConstants {n q : ℕ}
    (c : HeightBoxes.LocalConstants n)
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) :
    HeightBoxes.LocalConstants (n.choose q) :=
  fun v i ↦
    let J := (exteriorIndexEquivFin n q).symm i
    (∑ a : Fin q,
      c v (Set.powersetCard.ofFinEmbEquiv.symm J a)) +
      if J = J₀ v then saving v else 0

/-- The actual exponent array used after Lemma 5.2: its exterior coordinate
rows are indexed by the place-dependent permutation of the original forms.
Keeping the permutation explicit is essential because the rank-stabilized
exterior forms are `permutedLocalForms L pi`. -/
noncomputable def permutedExteriorLocalConstants {n q : ℕ}
    (c : HeightBoxes.LocalConstants n)
    (pi : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) :
    HeightBoxes.LocalConstants (n.choose q) :=
  fun place i ↦
    let J := (exteriorIndexEquivFin n q).symm i
    (∑ a : Fin q,
      c place (pi place (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
      if J = J₀ place then saving place else 0

theorem sum_permutedExteriorLocalConstants {n q : ℕ} (hq : 0 < q)
    (c : HeightBoxes.LocalConstants n)
    (pi : Place23 → Equiv.Perm (Fin n))
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) :
    (∑ place, ∑ i,
        permutedExteriorLocalConstants c pi J₀ saving place i) =
      (n - 1).choose (q - 1) * (∑ place, ∑ i, c place i) +
        ∑ place, saving place := by
  calc
    _ = ∑ place, ∑ J : Set.powersetCard (Fin n) q,
        ((∑ a : Fin q,
          c place (pi place
            (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
          if J = J₀ place then saving place else 0) := by
      apply Finset.sum_congr rfl
      intro place _
      simpa only [permutedExteriorLocalConstants] using
        (Equiv.sum_comp (exteriorIndexEquivFin n q).symm
          (fun J : Set.powersetCard (Fin n) q ↦
            ((∑ a : Fin q,
              c place (pi place
                (Set.powersetCard.ofFinEmbEquiv.symm J a))) +
              if J = J₀ place then saving place else 0)))
    _ = _ := sum_localExteriorCoordinateSums_with_saving hq c pi J₀ saving

theorem sum_exteriorLocalConstants {n q : ℕ} (hq : 0 < q)
    (c : HeightBoxes.LocalConstants n)
    (J₀ : Place23 → Set.powersetCard (Fin n) q)
    (saving : Place23 → ℝ) :
    (∑ v, ∑ i, exteriorLocalConstants c J₀ saving v i) =
      (n - 1).choose (q - 1) * (∑ v, ∑ i, c v i) +
        ∑ v, saving v := by
  calc
    _ = ∑ v, ∑ J : Set.powersetCard (Fin n) q,
        ((∑ a : Fin q,
          c v (Set.powersetCard.ofFinEmbEquiv.symm J a)) +
          if J = J₀ v then saving v else 0) := by
      apply Finset.sum_congr rfl
      intro v hv
      simpa only [exteriorLocalConstants] using
        (Equiv.sum_comp (exteriorIndexEquivFin n q).symm
          (fun J : Set.powersetCard (Fin n) q ↦
            ((∑ a : Fin q,
              c v (Set.powersetCard.ofFinEmbEquiv.symm J a)) +
              if J = J₀ v then saving v else 0)))
    _ = _ := by
      simpa using sum_localExteriorCoordinateSums_with_saving hq c
        (fun _ ↦ Equiv.refl (Fin n)) J₀ saving

/-- Round a real exponent upward on the grid of mesh `γ`. -/
noncomputable def discretizedExponent (γ a : ℝ) : ℝ :=
  γ * (⌈a / γ⌉ : ℤ)

/-- Upward grid rounding enlarges an exponent. -/
theorem le_discretizedExponent {γ a : ℝ} (hγ : 0 < γ) :
    a ≤ discretizedExponent γ a := by
  have hceil : a / γ ≤ (⌈a / γ⌉ : ℤ) := Int.le_ceil _
  have := mul_le_mul_of_nonneg_left hceil hγ.le
  have hcancel : γ * (a / γ) = a := by field_simp
  rw [discretizedExponent]
  calc
    a = γ * (a / γ) := hcancel.symm
    _ ≤ γ * (⌈a / γ⌉ : ℤ) := this

/-- Upward grid rounding loses strictly less than one mesh. -/
theorem discretizedExponent_lt_add {γ a : ℝ} (hγ : 0 < γ) :
    discretizedExponent γ a < a + γ := by
  have hceil : ((⌈a / γ⌉ : ℤ) : ℝ) - 1 < a / γ := by
    exact (Int.le_ceil_iff.mp le_rfl)
  have hmul := mul_lt_mul_of_pos_left hceil hγ
  rw [mul_sub, mul_one] at hmul
  have hcancel : γ * (a / γ) = a := by field_simp
  rw [hcancel] at hmul
  rw [discretizedExponent]
  linarith

/-- Simultaneous discretization loses less than `card α` meshes in the
total exponent.  This is the finite error term used after (5.11). -/
theorem sum_discretizedExponent_lt { α : Type* } [Fintype α] [Nonempty α]
    (γ : ℝ) (hγ : 0 < γ) (a : α → ℝ) :
    ∑ i, discretizedExponent γ (a i) <
      ∑ i, a i + Fintype.card α * γ := by
  calc
    ∑ i, discretizedExponent γ (a i) < ∑ i, (a i + γ) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact (discretizedExponent_lt_add hγ).le
      · let i : α := Classical.choice (inferInstance : Nonempty α)
        exact ⟨i, Finset.mem_univ i, discretizedExponent_lt_add hγ⟩
    _ = ∑ i, a i + Fintype.card α * γ := by
      simp [Finset.sum_add_distrib]

/-- Coordinatewise upward rounding of a three-place exponent array. -/
noncomputable def discretizedLocalConstants {d : ℕ} (γ : ℝ)
    (a : HeightBoxes.LocalConstants d) : HeightBoxes.LocalConstants d :=
  fun v i ↦ discretizedExponent γ (a v i)

theorem sum_discretizedLocalConstants_lt {d : ℕ} (hd : 0 < d)
    (γ : ℝ) (hγ : 0 < γ) (a : HeightBoxes.LocalConstants d) :
    (∑ v, ∑ i, discretizedLocalConstants γ a v i) <
      (∑ v, ∑ i, a v i) + 3 * d * γ := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hv : ∀ v : Place23,
      (∑ i, discretizedLocalConstants γ a v i) <
        (∑ i, a v i) + d * γ := by
    intro v
    simpa [discretizedLocalConstants] using
      sum_discretizedExponent_lt γ hγ (a v)
  calc
    (∑ v, ∑ i, discretizedLocalConstants γ a v i) <
        ∑ v, ((∑ i, a v i) + d * γ) := by
      apply Finset.sum_lt_sum
      · intro v hvv
        exact (hv v).le
      · exact ⟨Place23.infinite, Finset.mem_univ _, hv Place23.infinite⟩
    _ = (∑ v, ∑ i, a v i) + 3 * d * γ := by
      simp [Finset.sum_add_distrib]
      ring

/-- The exact three-place mesh estimate used in the last discretization of
§5.3. -/
theorem sum_discretizedLocalConstants_lt_neg_half {d : ℕ} (hd : 0 < d)
    (a : HeightBoxes.LocalConstants d) {γ δ : ℝ}
    (hγ : 0 < γ) (ha : (∑ v, ∑ i, a v i) ≤ -δ)
    (hmesh : 3 * d * γ ≤ δ / 2) :
    (∑ v, ∑ i, discretizedLocalConstants γ a v i) < -(δ / 2) := by
  have hround := sum_discretizedLocalConstants_lt hd γ hγ a
  calc
    (∑ v, ∑ i, discretizedLocalConstants γ a v i) <
        (∑ v, ∑ i, a v i) + 3 * d * γ := hround
    _ ≤ -δ + δ / 2 := add_le_add ha hmesh
    _ = -(δ / 2) := by ring

/-- If the undiscretized exterior exponent sum has margin `δ` and the
total rounding loss is at most half that margin, the discretized exponent
sum is still strictly negative.  This is the arithmetic conclusion at the
end of GLR §5.3. -/
theorem sum_discretizedExponent_lt_neg_half { α : Type* }
    [Fintype α] [Nonempty α] (a : α → ℝ) {γ δ : ℝ}
    (hγ : 0 < γ) (ha : ∑ i, a i ≤ -δ)
    (hmesh : Fintype.card α * γ ≤ δ / 2) :
    ∑ i, discretizedExponent γ (a i) < -(δ / 2) := by
  have hround := sum_discretizedExponent_lt γ hγ a
  calc
    ∑ i, discretizedExponent γ (a i) <
        ∑ i, a i + Fintype.card α * γ := hround
    _ ≤ -δ + δ / 2 := add_le_add ha hmesh
    _ = -(δ / 2) := by ring

/-! ## Dualization back to the original space -/

/-- A proper rational subspace is contained in a proper rational
hyperplane. -/
theorem exists_hyperplane_containing_proper_subspace {n : ℕ}
    (W : Submodule ℚ (Fin n → ℚ)) (hW : W < ⊤) :
    ∃ b : Fin n → ℚ, b ≠ 0 ∧
      ∀ x ∈ W, ∑ i, b i * x i = 0 := by
  obtain ⟨f, hf, hle, _⟩ :=
    GeneralPosition.properSubspace_le_kernel W hW
  refine ⟨coefficientVector f, coefficientVector_ne_zero hf, ?_⟩
  intro x hx
  rw [← linearForm_eq_dotProduct]
  exact hle hx

/-- If every integral point in `X` lies in one member of a finite family of
proper rational subspaces, then `X` lies in a finite family of proper
rational hyperplanes.  This is the dualization used after the exterior
rank-stabilization theorem has produced finitely many original `k`-spaces. -/
theorem finiteHyperplaneCover_of_finite_properSubspaces {n : ℕ}
    (X : Set (Fin n → ℤ))
    (C : Finset (Submodule ℚ (Fin n → ℚ)))
    (hproper : ∀ W ∈ C, W < ⊤)
    (hcover : ∀ x ∈ X, ∃ W ∈ C, intCastVec x ∈ W) :
    HasFiniteHyperplaneCover X := by
  classical
  choose b hb hvan using fun W : {W // W ∈ C} ↦
    exists_hyperplane_containing_proper_subspace W.1 (hproper W.1 W.2)
  let B : Finset (Fin n → ℚ) := Finset.univ.image b
  refine ⟨B, ?_, ?_⟩
  · intro c hc
    obtain ⟨W, _hW, rfl⟩ := Finset.mem_image.mp hc
    exact hb W
  · intro x hx
    obtain ⟨W, hWC, hxW⟩ := hcover x hx
    let sW : {W // W ∈ C} := ⟨W, hWC⟩
    refine ⟨b sW, Finset.mem_image.mpr ⟨sW, Finset.mem_univ _, rfl⟩, ?_⟩
    exact hvan sW (intCastVec x) hxW

/-! ## Applying the rank-stabilization theorem -/

/-- S-integral version of the codimension-one consumer.  This is the exact
interface needed by the exterior wedges: their coordinates lie in
`ℤ[1/6]`, and need not be integral.  The points ultimately covered are still
the original primitive integer solutions. -/
theorem finiteCover_of_sCodimOneApproximationSpaces_finite {n : ℕ}
    (L : Erdos407.RankDrop.LocalForms n)
    (c : HeightBoxes.LocalConstants n)
    (hfinite : (Erdos407.RankDrop.sCodimOneApproximationSpaces L c).Finite)
    (X : Set (Fin n → ℤ))
    (hcover : ∀ x ∈ X, ∃ Q : ℕ, 2 ≤ Q ∧
      Module.finrank ℚ (Erdos407.RankDrop.realSApproximationSpan L Q c) + 1 = n ∧
      intCastVec x ∈ Erdos407.RankDrop.realSIntegralApproximationDomain L Q c) :
    HasFiniteHyperplaneCover X := by
  apply Erdos407.RankDrop.finiteHyperplaneCover_of_finite_properSubspaces
    hfinite
  · intro W hW
    obtain ⟨Q, hQ, rfl, hrank⟩ := hW
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hfull :
        Module.finrank ℚ
          (Erdos407.RankDrop.realSApproximationSpan L Q c) = n := by
      rw [htop]
      simp
    omega
  · intro x hx
    obtain ⟨Q, hQ, hrank, hxQ⟩ := hcover x hx
    let W := Erdos407.RankDrop.realSApproximationSpan L Q c
    refine ⟨W, ⟨Q, hQ, rfl, hrank⟩, ?_⟩
    exact Submodule.subset_span hxQ

/-- Once GLR Theorem 4.14 gives finiteness of the codimension-one spans for
one fixed exponent array, every set of integral points which enters one of
those spans has a finite proper-hyperplane cover.  This statement is generic
in the ambient dimension, so it applies verbatim to exterior dimensions up
to ten. -/
theorem finiteCover_of_codimOneApproximationSpaces_finite {n : ℕ}
    (L : Erdos407.RankDrop.LocalForms n)
    (c : HeightBoxes.LocalConstants n)
    (hfinite : (Erdos407.RankDrop.codimOneApproximationSpaces L c).Finite)
    (X : Set (Fin n → ℤ))
    (hcover : ∀ x ∈ X, ∃ Q : ℕ, 2 ≤ Q ∧
      Module.finrank ℚ (Erdos407.RankDrop.realApproximationSpan L Q c) + 1 = n ∧
      x ∈ Erdos407.RankDrop.realIntegralApproximationDomain L Q c) :
    HasFiniteHyperplaneCover X := by
  apply Erdos407.RankDrop.finiteHyperplaneCover_of_finite_properSubspaces
    hfinite
  · intro W hW
    obtain ⟨Q, hQ, rfl, hrank⟩ := hW
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hfull :
        Module.finrank ℚ (Erdos407.RankDrop.realApproximationSpan L Q c) = n := by
      rw [htop]
      simp
    omega
  · intro x hx
    obtain ⟨Q, hQ, hrank, hxQ⟩ := hcover x hx
    let W := Erdos407.RankDrop.realApproximationSpan L Q c
    refine ⟨W, ⟨Q, hQ, rfl, hrank⟩, ?_⟩
    exact Submodule.subset_span ⟨x, hxQ, rfl⟩

end ExteriorEndpoint

end Erdos407.PadicSubspace
