/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Projection

/-!
# Integral bases adapted to saturated sublattices

This file isolates the algebraic basis-extension input in the usual proof of
Mahler's basis lemma.  A sublattice `P` of a finite free integer module is
called saturated if division by a nonzero integer cannot move a vector into
`P`.  Equivalently, the quotient has no integral torsion.

Smith normal form then has no nonunit elementary divisors: although we do not
need to choose their signs, saturation says that every ambient Smith vector
which occurs in the basis of `P` already belongs to `P`.  Hence `P` is spanned
by a subset of an ambient integral basis and has an integral complement.

The complement statement is the useful inductive form: an arbitrary basis of
`P` can be retained and extended by a basis of the complement.  Iterating this
construction gives one integral basis adapted to a finite saturated flag.
-/

namespace Erdos186.CFP.Bilu.SaturatedFlag

open scoped BigOperators
open Function Set Submodule
open Module

variable {M : Type*} [AddCommGroup M]

/-- A submodule is saturated if it is closed under division by every nonzero
integer which divides a vector in the ambient module. -/
def IsSaturated (P : Submodule ℤ M) : Prop :=
  ∀ (a : ℤ) (x : M), a ≠ 0 → a • x ∈ P → x ∈ P

/-- A basis is adapted to a submodule if that submodule is spanned by a
subfamily of the basis. -/
def IsAdaptedTo {κ : Type*} (b : Basis κ ℤ M)
    (P : Submodule ℤ M) : Prop :=
  ∃ s : Set κ, P = Submodule.span ℤ (b '' s)

@[simp] theorem isSaturated_bot [Module.IsTorsionFree ℤ M] :
    IsSaturated (⊥ : Submodule ℤ M) := by
  intro a x ha hx
  rw [Submodule.mem_bot] at hx ⊢
  exact (smul_eq_zero.mp hx).resolve_left ha

@[simp] theorem isSaturated_top : IsSaturated (⊤ : Submodule ℤ M) := by
  intro _ _ _ _
  exact Submodule.mem_top

/-- Saturation descends to a submodule of a containing submodule. -/
theorem IsSaturated.comap_subtype {P O : Submodule ℤ M}
    (hP : IsSaturated P) (hPO : P ≤ O) :
    IsSaturated (P.comap O.subtype) := by
  intro a x ha hx
  change (a • (x : M)) ∈ P at hx
  change (x : M) ∈ P
  exact hP a x ha hx

/-- Saturation is inherited by smaller ambient modules, in the form used for
successive members of a flag. -/
theorem IsSaturated.comap_subtype_of_le {P O : Submodule ℤ M}
    (hP : IsSaturated P) (hPO : P ≤ O) :
    IsSaturated (P.comap O.subtype) :=
  hP.comap_subtype hPO

/-! ## Intersections with rational spans -/

/-- The standard coordinatewise embedding `ℤ^d → ℚ^d`. -/
def rationalEmbed (d : ℕ) : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℚ) where
  toFun x i := (x i : ℚ)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

@[simp] theorem rationalEmbed_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    rationalEmbed d x i = (x i : ℚ) := rfl

theorem rationalEmbed_zsmul {d : ℕ} (a : ℤ) (x : Fin d → ℤ) :
    rationalEmbed d (a • x) = (a : ℚ) • rationalEmbed d x := by
  ext i
  simp [rationalEmbed]

/-- Integral points in the rational span of a set of integral points.  This
is the saturated/full lattice attached to a rational subspace. -/
def rationalSpanLattice {d : ℕ} (S : Set (Fin d → ℤ)) :
    Submodule ℤ (Fin d → ℤ) :=
  ((Submodule.span ℚ (rationalEmbed d '' S)).restrictScalars ℤ).comap
    (rationalEmbed d)

@[simp] theorem mem_rationalSpanLattice {d : ℕ} {S : Set (Fin d → ℤ)}
    {x : Fin d → ℤ} :
    x ∈ rationalSpanLattice S ↔
      rationalEmbed d x ∈ Submodule.span ℚ (rationalEmbed d '' S) :=
  Iff.rfl

/-- An intersection of `ℤ^d` with a rational subspace is saturated. -/
theorem isSaturated_rationalSpanLattice {d : ℕ}
    (S : Set (Fin d → ℤ)) : IsSaturated (rationalSpanLattice S) := by
  intro a x ha hx
  rw [mem_rationalSpanLattice] at hx ⊢
  have hax : (a : ℚ) • rationalEmbed d x ∈
      Submodule.span ℚ (rationalEmbed d '' S) := by
    rw [← rationalEmbed_zsmul]
    exact hx
  have hinv := (Submodule.span ℚ (rationalEmbed d '' S)).smul_mem
    (a : ℚ)⁻¹ hax
  simpa [smul_smul, ha] using hinv

/-- Rational-span lattices are monotone in their generating sets. -/
theorem rationalSpanLattice_mono {d : ℕ} {S T : Set (Fin d → ℤ)}
    (hST : S ⊆ T) : rationalSpanLattice S ≤ rationalSpanLattice T := by
  intro x hx
  rw [mem_rationalSpanLattice] at hx ⊢
  exact Submodule.span_mono (Set.image_mono hST) hx

/-- The standard coordinatewise embedding `ℤ^d → ℝ^d`. -/
def realEmbed (d : ℕ) : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) where
  toFun x i := (x i : ℝ)
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

@[simp] theorem realEmbed_apply {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    realEmbed d x i = (x i : ℝ) := rfl

theorem realEmbed_zsmul {d : ℕ} (a : ℤ) (x : Fin d → ℤ) :
    realEmbed d (a • x) = (a : ℝ) • realEmbed d x := by
  ext i
  simp [realEmbed]

/-- The full integral lattice in the real span of the first `i+1` vectors
of an ordered integral family. -/
def realPrefixLattice {d n : ℕ} (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    Submodule ℤ (Fin d → ℤ) :=
  ((Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i))).restrictScalars ℤ).comap
    (realEmbed d)

@[simp] theorem mem_realPrefixLattice {d n : ℕ}
    {x : Fin n → (Fin d → ℤ)} {i : Fin n} {z : Fin d → ℤ} :
    z ∈ realPrefixLattice x i ↔
      realEmbed d z ∈
        Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i)) :=
  Iff.rfl

/-- Full intersections with the real prefix spans are saturated. -/
theorem isSaturated_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    IsSaturated (realPrefixLattice x i) := by
  intro a z ha hz
  rw [mem_realPrefixLattice] at hz ⊢
  have haz : (a : ℝ) • realEmbed d z ∈
      Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i)) := by
    rw [← realEmbed_zsmul]
    exact hz
  have hinv :=
    (Submodule.span ℝ (realEmbed d '' (x '' Set.Iic i))).smul_mem
      (a : ℝ)⁻¹ haz
  simpa [smul_smul, ha] using hinv

/-- The full real-prefix lattices form an increasing flag. -/
theorem monotone_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) : Monotone (realPrefixLattice x) := by
  intro i j hij z hz
  rw [mem_realPrefixLattice] at hz ⊢
  apply Submodule.span_mono (Set.image_mono (Set.image_mono ?_)) hz
  intro k hk
  exact hk.trans hij

/-- The `i`th vector belongs to its prefix lattice. -/
theorem self_mem_realPrefixLattice {d n : ℕ}
    (x : Fin n → (Fin d → ℤ)) (i : Fin n) :
    x i ∈ realPrefixLattice x i := by
  rw [mem_realPrefixLattice]
  apply Submodule.subset_span
  exact ⟨x i, ⟨i, Set.mem_Iic.mpr le_rfl, rfl⟩, rfl⟩

section Smith

variable {ι : Type*} [Finite ι]

/-- The ambient Smith vectors selected by the Smith embedding already lie in
a saturated submodule.  This is the exact point where saturation is used. -/
theorem smithVector_mem_of_isSaturated (b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P) {n : ℕ}
    (snf : Basis.SmithNormalForm P ι n) (i : Fin n) :
    snf.bM (snf.f i) ∈ P := by
  classical
  have hai : snf.a i ≠ 0 := by
    intro hai
    apply (snf.bN.ne_zero i)
    apply Subtype.ext
    simpa [snf.snf i, hai]
  exact hP (snf.a i) (snf.bM (snf.f i)) hai <| by
    simpa [snf.snf i] using (snf.bN i).property

/-- A saturated submodule of a finite free integer module has an integral
complement.  The proof uses the two coordinate blocks in Smith normal form. -/
theorem exists_isCompl_of_isSaturated (b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P) :
    ∃ Q : Submodule ℤ M, IsCompl P Q := by
  classical
  let snf := P.smithNormalForm b
  let selected : Set ι := Set.range snf.2.f
  let Q : Submodule ℤ M :=
    Submodule.span ℤ (snf.2.bM '' selectedᶜ)
  have hselected :
      P = Submodule.span ℤ (snf.2.bM '' selected) := by
    apply le_antisymm
    · intro x hx
      let xp : P := ⟨x, hx⟩
      have hxp : xp ∈ Submodule.span ℤ (Set.range snf.2.bN) := by
        rw [snf.2.bN.span_eq]
        exact Submodule.mem_top
      exact Submodule.span_induction (R := ℤ) (s := Set.range snf.2.bN)
        (p := fun y _ ↦ (y : M) ∈
          Submodule.span ℤ (snf.2.bM '' selected))
        (fun y hy ↦ by
          obtain ⟨i, rfl⟩ := hy
          rw [snf.2.snf i]
          apply Submodule.smul_mem
          apply Submodule.subset_span
          exact ⟨snf.2.f i, ⟨i, rfl⟩, rfl⟩)
        (Submodule.zero_mem _)
        (fun _ _ _ _ hy hz ↦ Submodule.add_mem _ hy hz)
        (fun a _ _ hy ↦ Submodule.smul_mem _ a hy)
        hxp
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, ⟨i, rfl⟩, rfl⟩
      exact smithVector_mem_of_isSaturated b P hP snf.2 i
  refine ⟨Q, ?_⟩
  rw [hselected]
  exact snf.2.bM.linearIndependent.isCompl_span_image
    snf.2.bM.span_eq (isCompl_compl)

/-- An arbitrary chosen basis of a saturated submodule extends to an ambient
integral basis.  The new indices form a disjoint sum with a finite set of
complementary indices; vectors on the left block are definitionally the old
basis vectors after coercion to the ambient module. -/
theorem exists_basis_extending_of_isSaturated (b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P)
    {κ : Type*} (bP : Basis κ ℤ P) :
    ∃ (m : ℕ) (bM : Basis (κ ⊕ Fin m) ℤ M),
      ∀ i, bM (Sum.inl i) = (bP i : M) := by
  classical
  obtain ⟨Q, hPQ⟩ := exists_isCompl_of_isSaturated b P hP
  obtain ⟨m, bQ⟩ := Submodule.basisOfPid b Q
  let e : (P × Q) ≃ₗ[ℤ] M := P.prodEquivOfIsCompl Q hPQ
  let bM : Basis (κ ⊕ Fin m) ℤ M := (bP.prod bQ).map e
  refine ⟨m, bM, ?_⟩
  intro i
  simp [bM, e, Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]

/-- If an ambient basis extends a basis of `P`, then any submodule of `P`
spanned by selected old basis vectors is spanned by the same selected vectors
in the ambient basis.  This is the transport step used in flag induction. -/
theorem span_image_inl_eq_of_span_comap_eq
    {P R : Submodule ℤ M} (hRP : R ≤ P)
    {κ μ : Type*} (bP : Basis κ ℤ P) (bM : Basis (κ ⊕ μ) ℤ M)
    (hext : ∀ i, bM (Sum.inl i) = (bP i : M)) (s : Set κ)
    (hspan : R.comap P.subtype = Submodule.span ℤ (bP '' s)) :
    R = Submodule.span ℤ (bM '' (Sum.inl '' s)) := by
  have himage : P.subtype '' (bP '' s) = bM '' (Sum.inl '' s) := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, ⟨i, hi, rfl⟩, hext i⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨bP i, ⟨i, hi, rfl⟩, (hext i).symm⟩
  calc
    R = (R.comap P.subtype).map P.subtype :=
      (Submodule.map_comap_eq_self (by
        simpa [Submodule.range_subtype] using hRP)).symm
    _ = (Submodule.span ℤ (bP '' s)).map P.subtype := by rw [hspan]
    _ = Submodule.span ℤ (P.subtype '' (bP '' s)) := by
      rw [Submodule.map_span]
    _ = Submodule.span ℤ (bM '' (Sum.inl '' s)) := by rw [himage]

/-- In a basis obtained from complementary submodules, the left block spans
the first summand. -/
theorem span_range_inl_prod_eq {P Q : Submodule ℤ M} (hPQ : IsCompl P Q)
    {κ μ : Type*} [Fintype κ] [Fintype μ]
    (bP : Basis κ ℤ P) (bQ : Basis μ ℤ Q) :
    let bM := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
    P = Submodule.span ℤ (bM '' Set.range Sum.inl) := by
  classical
  let bM := (bP.prod bQ).map (P.prodEquivOfIsCompl Q hPQ)
  apply le_antisymm
  · intro x hx
    let xp : P := ⟨x, hx⟩
    have hxp : xp ∈ Submodule.span ℤ (Set.range bP) := by
      rw [bP.span_eq]
      exact Submodule.mem_top
    exact Submodule.span_induction (R := ℤ) (s := Set.range bP)
      (p := fun y _ ↦ (y : M) ∈
        Submodule.span ℤ (bM '' Set.range Sum.inl))
      (fun y hy ↦ by
        obtain ⟨i, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨Sum.inl i, ⟨i, rfl⟩, ?_⟩
        simp [bM])
      (Submodule.zero_mem _)
      (fun _ _ _ _ hy hz ↦ Submodule.add_mem _ hy hz)
      (fun a _ _ hy ↦ Submodule.smul_mem _ a hy)
      hxp
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa [bM] using (bP i).property

/-- Coordinate form of the preceding extension theorem: membership in the
saturated submodule is equivalent to vanishing of all complementary basis
coordinates. -/
theorem exists_basis_with_repr_eq_zero_iff (b : Basis ι ℤ M)
    (P : Submodule ℤ M) (hP : IsSaturated P) :
    ∃ (κ : Type) (_ : Fintype κ) (bM : Basis κ ℤ M) (s : Set κ),
      ∀ x : M, x ∈ P ↔ ∀ j ∉ s, bM.repr x j = 0 := by
  classical
  obtain ⟨Q, hPQ⟩ := exists_isCompl_of_isSaturated b P hP
  obtain ⟨n, bP⟩ := Submodule.basisOfPid b P
  obtain ⟨m, bQ⟩ := Submodule.basisOfPid b Q
  let e : (P × Q) ≃ₗ[ℤ] M := P.prodEquivOfIsCompl Q hPQ
  let bM : Basis (Fin n ⊕ Fin m) ℤ M := (bP.prod bQ).map e
  let s : Set (Fin n ⊕ Fin m) := Set.range Sum.inl
  refine ⟨Fin n ⊕ Fin m, inferInstance, bM, s, ?_⟩
  intro x
  constructor
  · intro hxP j hj
    have hx : ((P.prodEquivOfIsCompl Q hPQ).symm x).2 = 0 :=
      (P.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q hPQ).mpr hxP
    cases j with
    | inl i => exact False.elim (hj ⟨i, rfl⟩)
    | inr i =>
        change bQ.repr ((e.symm x).2) i = 0
        rw [hx]
        simp
  · intro hx
    apply (P.prodEquivOfIsCompl_symm_apply_snd_eq_zero Q hPQ).mp
    apply bQ.repr.injective
    ext i
    have hi := hx (Sum.inr i) (by simp [s])
    change bQ.repr ((e.symm x).2) i = 0 at hi
    simpa [e] using hi

end Smith

universe u

/-- Every finite descending flag of saturated submodules of a finite free
integer module admits one integral basis simultaneously adapted to every
member of the flag.

The flag is indexed from largest to smallest: `Antitone P` says that
`P j ≤ P i` whenever `i ≤ j`.  Each flag member is exactly the span of a
subfamily of the single output basis.  This form is independent of chosen
ranks and remains valid when consecutive flag members coincide. -/
theorem exists_basis_with_nested_supports_of_saturated_flag (n : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] {ι : Type} [Finite ι],
      (b₀ : Basis ι ℤ N) →
      (P : Fin n → Submodule ℤ N) →
      (∀ i, IsSaturated (P i)) → Antitone P →
      ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ N)
        (s : Fin n → Set κ), Antitone s ∧
          ∀ i, P i = Submodule.span ℤ (b '' s i) := by
  induction n with
  | zero =>
      intro N _ ι _ b₀ P _ _
      classical
      let := Fintype.ofFinite ι
      let b : Basis (Fin (Fintype.card ι)) ℤ N :=
        b₀.reindex (Fintype.equivFin ι)
      let s : Fin 0 → Set (Fin (Fintype.card ι)) := Fin.elim0
      exact ⟨Fin (Fintype.card ι), inferInstance, b, s,
        fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      intro N _ ι _ b₀ P hsat hanti
      classical
      let P₀ : Submodule ℤ N := P 0
      obtain ⟨p, bP₀⟩ := Submodule.basisOfPid b₀ P₀
      let tail : Fin n → Submodule ℤ P₀ :=
        fun i ↦ (P i.succ).comap P₀.subtype
      have htail_sat : ∀ i, IsSaturated (tail i) := by
        intro i
        apply (hsat i.succ).comap_subtype
        exact hanti (Fin.zero_le i.succ)
      have htail_anti : Antitone tail := by
        intro i j hij
        apply Submodule.comap_mono
        exact hanti (by simpa using hij)
      obtain ⟨κ, instκ, bP, sP, hsPanti, hbP⟩ :=
        ih (N := P₀) (ι := Fin p) bP₀ tail htail_sat htail_anti
      let : Fintype κ := instκ
      obtain ⟨Q, hP₀Q⟩ :=
        exists_isCompl_of_isSaturated b₀ P₀ (hsat 0)
      obtain ⟨m, bQ⟩ := Submodule.basisOfPid b₀ Q
      let e : (P₀ × Q) ≃ₗ[ℤ] N := P₀.prodEquivOfIsCompl Q hP₀Q
      let b : Basis (κ ⊕ Fin m) ℤ N := (bP.prod bQ).map e
      let s : Fin (n + 1) → Set (κ ⊕ Fin m) :=
        fun i ↦ Fin.cases (Set.range Sum.inl)
          (fun j ↦ Sum.inl '' sP j) i
      refine ⟨κ ⊕ Fin m, inferInstance, b, s, ?_, ?_⟩
      · intro i j hij
        obtain rfl | ⟨i', rfl⟩ := i.eq_zero_or_eq_succ
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact fun _ hx ↦ hx
          · rintro x ⟨k, hk, rfl⟩
            exact Set.mem_range.mpr ⟨k, rfl⟩
        · obtain rfl | ⟨j', rfl⟩ := j.eq_zero_or_eq_succ
          · exact False.elim ((not_le_of_gt (Fin.succ_pos i')) hij)
          · exact Set.image_mono (hsPanti (by simpa using hij))
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact span_range_inl_prod_eq hP₀Q bP bQ
        · apply span_image_inl_eq_of_span_comap_eq
            (P := P₀) (R := P j.succ) (hanti (Fin.zero_le j.succ))
            bP b (fun k ↦ by simp [b, e]) (sP j)
          simpa [tail, P₀] using hbP j

/-- Basis-adaptation form of
`exists_basis_with_nested_supports_of_saturated_flag`. -/
theorem exists_basis_adapted_to_saturated_flag (n : ℕ)
    {N : Type u} [AddCommGroup N] {ι : Type} [Finite ι]
    (b₀ : Basis ι ℤ N) (P : Fin n → Submodule ℤ N)
    (hsat : ∀ i, IsSaturated (P i)) (hanti : Antitone P) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ N),
      ∀ i, IsAdaptedTo b (P i) := by
  obtain ⟨κ, instκ, b, s, _hsanti, hs⟩ :=
    exists_basis_with_nested_supports_of_saturated_flag n b₀ P hsat hanti
  exact ⟨κ, instκ, b, fun i ↦ ⟨s i, hs i⟩⟩

/-- Increasing version of the nested-support theorem, obtained by reversing
the finite flag. -/
theorem exists_basis_with_nested_supports_of_monotone_saturated_flag
    (n : ℕ) {N : Type u} [AddCommGroup N] {ι : Type} [Finite ι]
    (b₀ : Basis ι ℤ N) (P : Fin n → Submodule ℤ N)
    (hsat : ∀ i, IsSaturated (P i)) (hmono : Monotone P) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ N)
      (s : Fin n → Set κ), Monotone s ∧
        ∀ i, P i = Submodule.span ℤ (b '' s i) := by
  let Prev : Fin n → Submodule ℤ N := fun i ↦ P i.rev
  have hPrev : Antitone Prev := by
    intro i j hij
    exact hmono (Fin.rev_anti hij)
  obtain ⟨κ, instκ, b, t, htanti, ht⟩ :=
    exists_basis_with_nested_supports_of_saturated_flag n b₀ Prev
      (fun i ↦ hsat i.rev) hPrev
  let s : Fin n → Set κ := fun i ↦ t i.rev
  refine ⟨κ, instκ, b, s, ?_, ?_⟩
  · intro i j hij
    exact htanti (Fin.rev_anti hij)
  · intro i
    simpa [s, Prev] using ht i.rev

/-- Coordinates outside a spanning subfamily vanish.  Applied to the nested
supports above, this is the triangular-zero part of an adapted flag basis. -/
theorem repr_eq_zero_of_mem_span_image {N : Type*} [AddCommGroup N]
    {κ : Type*} (b : Basis κ ℤ N) (s : Set κ) {x : N}
    (hx : x ∈ Submodule.span ℤ (b '' s)) {j : κ} (hj : j ∉ s) :
    b.repr x j = 0 := by
  have hsupp := b.repr_support_subset_of_mem_span s hx
  by_contra hne
  exact hj (hsupp (Finsupp.mem_support_iff.mpr hne))

/-- Direct standard-lattice specialization: a descending flag of sets of
integer vectors determines a descending flag of full lattices obtained by
intersecting their rational spans with `ℤ^d`, and one integral basis is
simultaneously adapted to every intersection. -/
theorem exists_basis_with_nested_supports_rationalSpanLattice
    {d n : ℕ} (S : Fin n → Set (Fin d → ℤ)) (hS : Antitone S) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ (Fin d → ℤ))
      (s : Fin n → Set κ), Antitone s ∧
        ∀ i, rationalSpanLattice (S i) =
          Submodule.span ℤ (b '' s i) := by
  let P : Fin n → Submodule ℤ (Fin d → ℤ) :=
    fun i ↦ rationalSpanLattice (S i)
  have hPanti : Antitone P := by
    intro i j hij
    exact rationalSpanLattice_mono (hS hij)
  simpa [P] using
    (exists_basis_with_nested_supports_of_saturated_flag n
      (Pi.basisFun ℤ (Fin d)) P
      (fun i ↦ isSaturated_rationalSpanLattice (S i)) hPanti)

/-- A single integral basis, with nested coordinate supports, adapted to the
full lattices in all real prefix spans of an ordered integral family. -/
theorem exists_basis_with_nested_supports_realPrefixLattice
    {d n : ℕ} (x : Fin n → (Fin d → ℤ)) :
    ∃ (κ : Type) (_ : Fintype κ) (b : Basis κ ℤ (Fin d → ℤ))
      (s : Fin n → Set κ), Monotone s ∧
        ∀ i, realPrefixLattice x i =
          Submodule.span ℤ (b '' s i) := by
  exact exists_basis_with_nested_supports_of_monotone_saturated_flag n
    (Pi.basisFun ℤ (Fin d)) (realPrefixLattice x)
    (isSaturated_realPrefixLattice x) (monotone_realPrefixLattice x)

/-- In the square case the adapted basis can be indexed by `Fin n`.  Besides
the exact prefix-span identities, the theorem records the triangular support
consequence: the coordinates of `x i` vanish outside the nested support at
level `i`. -/
theorem exists_fin_basis_with_nested_supports_realPrefixLattice
    {n : ℕ} (x : Fin n → (Fin n → ℤ)) :
    ∃ (b : Basis (Fin n) ℤ (Fin n → ℤ)) (s : Fin n → Set (Fin n)),
      Monotone s ∧
      (∀ i, realPrefixLattice x i =
        Submodule.span ℤ (b '' s i)) ∧
      ∀ i j, j ∉ s i → b.repr (x i) j = 0 := by
  classical
  obtain ⟨κ, instκ, bκ, sκ, hsmono, hs⟩ :=
    exists_basis_with_nested_supports_realPrefixLattice x
  let : Fintype κ := instκ
  let e : κ ≃ Fin n := bκ.indexEquiv (Pi.basisFun ℤ (Fin n))
  let b : Basis (Fin n) ℤ (Fin n → ℤ) := bκ.reindex e
  let s : Fin n → Set (Fin n) := fun i ↦ e '' sκ i
  have himage (i : Fin n) : b '' s i = bκ '' sκ i := by
    ext y
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp [b, e]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e k, ⟨k, hk, rfl⟩, by simp [b, e]⟩
  have hspan (i : Fin n) : realPrefixLattice x i =
      Submodule.span ℤ (b '' s i) := by
    rw [himage]
    exact hs i
  refine ⟨b, s, ?_, hspan, ?_⟩
  · intro i j hij
    exact Set.image_mono (hsmono hij)
  · intro i j hj
    apply repr_eq_zero_of_mem_span_image b (s i)
    · rw [← hspan i]
      exact self_mem_realPrefixLattice x i
    · exact hj

/-- For a real-linearly independent ordered family of `n` integral vectors
in `ℤ^n`, the adapted basis can be ordered so that the full lattice in the
first `i+1` real directions is *exactly* the span of the first `i+1` basis
vectors.  Consequently the coefficient matrix is triangular: row `i` has
zero entries in every column `j > i`.

This is the saturated-flag basis theorem used in the algebraic part of
Mahler reduction. -/
theorem exists_prefix_adapted_basis_realPrefixLattice
    {n : ℕ} (x : Fin n → (Fin n → ℤ))
    (hli : LinearIndependent ℝ (fun i ↦ realEmbed n (x i))) :
    ∃ b : Basis (Fin n) ℤ (Fin n → ℤ),
      (∀ i, realPrefixLattice x i =
        Submodule.span ℤ (b '' Set.Iic i)) ∧
      (∀ i j, i < j → b.repr (x i) j = 0) ∧
      ∀ i, b.repr (x i) i ≠ 0 := by
  classical
  obtain ⟨b, s, hsmono, hspan, hzero⟩ :=
    exists_fin_basis_with_nested_supports_realPrefixLattice x
  have hpivot : ∀ i : Fin n, ∃ j : Fin n,
      j ∈ s i ∧ b.repr (x i) j ≠ 0 ∧
        ∀ hi : 0 < i.val,
          j ∉ s (⟨i.val - 1, by omega⟩ : Fin n) := by
    intro i
    by_cases hi : 0 < i.val
    · let ip : Fin n := ⟨i.val - 1, by omega⟩
      have hset : Set.Iic ip = Set.Iio i := by
        ext k
        simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_iff_val_le_val,
          Fin.lt_iff_val_lt_val, ip]
        omega
      have hnot : x i ∉ realPrefixLattice x ip := by
        intro hmem
        have him := (mem_realPrefixLattice.mp hmem)
        apply hli.notMem_span_image (s := Set.Iio i) (lt_irrefl i)
        simpa [Set.image_image, Function.comp_def, hset] using him
      have hnotspan : x i ∉ Submodule.span ℤ (b '' s ip) := by
        rw [← hspan ip]
        exact hnot
      have hnsub : ¬ ((b.repr (x i)).support : Set (Fin n)) ⊆ s ip := by
        simpa [b.mem_span_image] using hnotspan
      obtain ⟨j, hjmem, hjnot⟩ := Set.not_subset.mp hnsub
      have hjne : b.repr (x i) j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
      have hjcur : j ∈ s i := by
        by_contra hj
        exact hjne (hzero i j hj)
      refine ⟨j, hjcur, hjne, ?_⟩
      intro _hi
      simpa [ip] using hjnot
    · have hxne : x i ≠ 0 := by
        intro hx
        apply hli.ne_zero i
        simp [hx]
      have hrepr : b.repr (x i) ≠ 0 := by
        intro hr
        apply hxne
        apply b.repr.injective
        simpa using hr
      obtain ⟨j, hjmem⟩ := Finsupp.support_nonempty_iff.mpr hrepr
      have hjne : b.repr (x i) j ≠ 0 := Finsupp.mem_support_iff.mp hjmem
      have hjcur : j ∈ s i := by
        by_contra hj
        exact hjne (hzero i j hj)
      exact ⟨j, hjcur, hjne, fun h ↦ (hi h).elim⟩
  choose p hp_mem hp_ne hp_prev using hpivot
  have hp_injective : Function.Injective p := by
    intro i j hpij
    by_contra hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hjpos : 0 < j.val := lt_of_le_of_lt (Nat.zero_le _) hijlt
      let jp : Fin n := ⟨j.val - 1, by omega⟩
      have hijp : i ≤ jp := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val ≤ j.val - 1
        omega
      have hpimem : p i ∈ s jp := hsmono hijp (hp_mem i)
      have hpjnot : p j ∉ s jp := by
        simpa [jp] using hp_prev j hjpos
      exact hpjnot (hpij ▸ hpimem)
    · have hipos : 0 < i.val := lt_of_le_of_lt (Nat.zero_le _) hjilt
      let ip : Fin n := ⟨i.val - 1, by omega⟩
      have hjip : j ≤ ip := by
        apply Fin.le_iff_val_le_val.mpr
        change j.val ≤ i.val - 1
        omega
      have hpjmem : p j ∈ s ip := hsmono hjip (hp_mem j)
      have hpinot : p i ∉ s ip := by
        simpa [ip] using hp_prev i hipos
      exact hpinot (hpij.symm ▸ hpjmem)
  have hp_bijective : Function.Bijective p :=
    (Fintype.bijective_iff_injective_and_card p).mpr
      ⟨hp_injective, rfl⟩
  let ep : Fin n ≃ Fin n := Equiv.ofBijective p hp_bijective
  have hs_eq (i : Fin n) : p '' Set.Iic i = s i := by
    apply Set.Subset.antisymm
    · rintro _ ⟨k, hk, rfl⟩
      exact hsmono (Set.mem_Iic.mp hk) (hp_mem k)
    · intro q hq
      obtain ⟨k, rfl⟩ := hp_bijective.2 q
      refine ⟨k, ?_, rfl⟩
      apply Set.mem_Iic.mpr
      by_contra hki
      have hik : i < k := lt_of_not_ge hki
      have hkpos : 0 < k.val := lt_of_le_of_lt (Nat.zero_le _) hik
      let kp : Fin n := ⟨k.val - 1, by omega⟩
      have hikp : i ≤ kp := by
        apply Fin.le_iff_val_le_val.mpr
        change i.val ≤ k.val - 1
        omega
      exact (hp_prev k hkpos) (hsmono hikp hq)
  let b' : Basis (Fin n) ℤ (Fin n → ℤ) := b.reindex ep.symm
  have hbimage (i : Fin n) : b' '' Set.Iic i = b '' s i := by
    rw [← hs_eq i]
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨p k, ⟨k, hk, rfl⟩, by simp [b', ep]⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by simp [b', ep]⟩
  have hspan' (i : Fin n) : realPrefixLattice x i =
      Submodule.span ℤ (b' '' Set.Iic i) := by
    rw [hbimage]
    exact hspan i
  refine ⟨b', hspan', ?_, ?_⟩
  · intro i j hij
    apply repr_eq_zero_of_mem_span_image b' (Set.Iic i)
    · rw [← hspan' i]
      exact self_mem_realPrefixLattice x i
    · exact fun hj ↦ (not_le_of_gt hij) (Set.mem_Iic.mp hj)
  · intro i
    simpa [b', ep] using hp_ne i

end Erdos186.CFP.Bilu.SaturatedFlag
