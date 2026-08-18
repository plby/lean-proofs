/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.LatticeBasis
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.LinearAlgebra.Basis.Fin

/-!
# A width-adapted triangular basis for a rectangular superlattice

The basis-replacement sentence in the printed proof of CFP Lemma 2.16 is
not valid for an arbitrary basis. This file supplies the required repair.

For a subgroup `Gamma <= Z^d` containing the rectangular lattice with
periods `v`, we construct an upper-triangular integral basis `b`. Every
entry in ambient coordinate `j` lies in `[0,v j]`, and entries below the
diagonal vanish. The induction is the elementary column-Hermite-normal-form
algorithm: take the least positive first coordinate, reduce the other
coordinates modulo their rectangular periods, and recurse in the kernel of
the first-coordinate projection.

If the coordinates have first been ordered so that box widths increase,
triangularity gives the anisotropic estimate

`sum_i w i * |b i j| <= d * v j * w j`.

This is the estimate actually needed to put the coefficient box with side
lengths `w i` inside a constant dilate of the original axis box.
-/

namespace Erdos186.CFP.AdaptedHNF

open scoped BigOperators
open Module
open LatticeBasis

/-! ## Head, tail, and the kernel lattice -/

/-- The first coordinate as an integral linear map. -/
def headLinear (n : ℕ) : LatticePoint (n + 1) →ₗ[ℤ] ℤ where
  toFun x := x 0
  map_add' _ _ := rfl
  map_smul' a x := by
    change (a • x) 0 = a • x 0
    rfl

/-- Adjoin a zero first coordinate. -/
def zeroConsLinear (n : ℕ) : LatticePoint n →ₗ[ℤ] LatticePoint (n + 1) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  map_smul' a x := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp

/-- Remove the first coordinate. -/
def tailLinear (n : ℕ) : LatticePoint (n + 1) →ₗ[ℤ] LatticePoint n where
  toFun x := Fin.tail x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem headLinear_apply (n : ℕ) (x : LatticePoint (n + 1)) :
    headLinear n x = x 0 := rfl

@[simp] theorem zeroConsLinear_apply_zero (n : ℕ) (x : LatticePoint n) :
    zeroConsLinear n x 0 = 0 := by simp [zeroConsLinear]

@[simp] theorem zeroConsLinear_apply_succ (n : ℕ) (x : LatticePoint n)
    (i : Fin n) :
    zeroConsLinear n x i.succ = x i := by simp [zeroConsLinear]

@[simp] theorem tailLinear_apply (n : ℕ) (x : LatticePoint (n + 1))
    (i : Fin n) :
    tailLinear n x i = x i.succ := rfl

@[simp] theorem zeroCons_tail (n : ℕ) (x : LatticePoint (n + 1))
    (hx : x 0 = 0) :
    zeroConsLinear n (tailLinear n x) = x := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa using hx.symm
  · rfl

/-- The lattice in the last `n` coordinates cut out by requiring zero in
the first coordinate and membership in `Gamma`. -/
def tailSublattice {n : ℕ} (Gamma : Sublattice (n + 1)) : Sublattice n :=
  Gamma.comap (zeroConsLinear n).toAddMonoidHom

@[simp] theorem mem_tailSublattice {n : ℕ} {Gamma : Sublattice (n + 1)}
    {x : LatticePoint n} :
    x ∈ tailSublattice Gamma ↔ zeroConsLinear n x ∈ Gamma :=
  Iff.rfl

/-- First-coordinate projection restricted to `Gamma`. -/
def headOnGamma {n : ℕ} (Gamma : Sublattice (n + 1)) : Gamma →ₗ[ℤ] ℤ where
  toFun x := (x : LatticePoint (n + 1)) 0
  map_add' _ _ := rfl
  map_smul' a x := by
    change (a • (x : LatticePoint (n + 1))) 0 = a • (x : LatticePoint (n + 1)) 0
    rfl

/-- The first-coordinate kernel inside `Gamma`. -/
def headKernel {n : ℕ} (Gamma : Sublattice (n + 1)) : Submodule ℤ Gamma :=
  LinearMap.ker (headOnGamma Gamma)

@[simp] theorem mem_headKernel {n : ℕ} {Gamma : Sublattice (n + 1)}
    {x : Gamma} :
    x ∈ headKernel Gamma ↔ (x : LatticePoint (n + 1)) 0 = 0 := by
  simp [headKernel, headOnGamma]

/-- The tail lattice is linearly equivalent to the first-coordinate kernel
inside the original lattice. -/
def tailKernelEquiv {n : ℕ} (Gamma : Sublattice (n + 1)) :
    tailSublattice Gamma ≃ₗ[ℤ] headKernel Gamma where
  toFun x := ⟨⟨zeroConsLinear n x, by
    change zeroConsLinear n (x : LatticePoint n) ∈ Gamma
    exact x.property⟩, by
      rw [mem_headKernel]
      simp⟩
  invFun y :=
    ⟨tailLinear n (y.1 : LatticePoint (n + 1)), by
      have hy0 : (y.1 : LatticePoint (n + 1)) 0 = 0 :=
        mem_headKernel.mp y.2
      simpa [mem_tailSublattice, zeroCons_tail n _ hy0] using y.1.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact zeroCons_tail n _ (mem_headKernel.mp y.2)
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    exact (zeroConsLinear n).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (zeroConsLinear n).map_smul a x

@[simp] theorem coe_tailKernelEquiv_apply {n : ℕ}
    (Gamma : Sublattice (n + 1)) (x : tailSublattice Gamma) :
    (((tailKernelEquiv Gamma x : headKernel Gamma) : Gamma) :
      LatticePoint (n + 1)) = zeroConsLinear n x := by
  change zeroConsLinear n (x : LatticePoint n) = zeroConsLinear n x
  rfl

/-! ## The least positive value of the head projection -/

/-- Positive natural values attained as first coordinates in `Gamma`. -/
def HeadValue {n : ℕ} (Gamma : Sublattice (n + 1)) (a : ℕ) : Prop :=
  0 < a ∧ ∃ x : Gamma, (x : LatticePoint (n + 1)) 0 = (a : ℤ)

/-- A rectangular superlattice has a positive attained head value. -/
theorem exists_headValue {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) : ∃ a, HeadValue Gamma a := by
  refine ⟨v 0, hv 0, axisVectorIn hrect 0, ?_⟩
  simp [axisVectorIn, axisVector_apply]

/-- The least positive first coordinate attained by `Gamma`. -/
noncomputable def headStep {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) : ℕ := by
  classical
  exact Nat.find (exists_headValue hv Gamma hrect)

theorem headStep_spec {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) :
    HeadValue Gamma (headStep hv Gamma hrect) := by
  classical
  exact Nat.find_spec (exists_headValue hv Gamma hrect)

theorem headStep_pos {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) : 0 < headStep hv Gamma hrect :=
  (headStep_spec hv Gamma hrect).1

theorem headStep_le_period {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) :
    headStep hv Gamma hrect ≤ v 0 := by
  classical
  exact Nat.find_min' (exists_headValue hv Gamma hrect)
    ⟨hv 0, axisVectorIn hrect 0, by simp [axisVectorIn, axisVector_apply]⟩

/-- A lattice element attaining the least positive head value. -/
noncomputable def headVector {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) : Gamma :=
  Classical.choose (headStep_spec hv Gamma hrect).2

@[simp] theorem headVector_head {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) :
    ((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) 0 =
      (headStep hv Gamma hrect : ℤ) :=
  Classical.choose_spec (headStep_spec hv Gamma hrect).2

/-! ## Euclidean reduction of the head vector -/

/-- Reduce all tail coordinates of the least-head vector into their
canonical residue intervals. -/
noncomputable def reducedHeadVector {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) : Gamma :=
  headVector hv Gamma hrect -
    ∑ i : Fin n,
      ((((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) i.succ /
          (v i.succ : ℤ)) • axisVectorIn hrect i.succ)

@[simp] theorem reducedHeadVector_head {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) :
    ((reducedHeadVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) 0 =
      (headStep hv Gamma hrect : ℤ) := by
  simp [reducedHeadVector, axisVectorIn, axisVector_apply, headVector_head]

theorem reducedHeadVector_succ {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) (j : Fin n) :
    ((reducedHeadVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) j.succ =
      ((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) j.succ %
        (v j.succ : ℤ) := by
  rw [reducedHeadVector]
  let S : Gamma :=
    ∑ i : Fin n,
      (((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) i.succ /
        (v i.succ : ℤ)) • axisVectorIn hrect i.succ
  change ((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) j.succ -
      ((S : Gamma) : LatticePoint (n + 1)) j.succ = _
  have hS : ((S : Gamma) : LatticePoint (n + 1)) j.succ =
      ∑ i : Fin n,
        (((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) i.succ /
          (v i.succ : ℤ)) * axisVector v i.succ j.succ := by
    simp [S]
  rw [hS]
  simp only [axisVector_apply]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
    have hdiv := Int.mul_ediv_add_emod
      (((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) j.succ)
      (v j.succ : ℤ)
    nlinarith [hdiv]
  · intro i _ hij
    have hsne : i.succ ≠ j.succ := fun h ↦ hij (Fin.succ_injective n h)
    simp [hsne]
  · simp

theorem reducedHeadVector_nonneg {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) (j : Fin (n + 1)) :
    0 ≤ ((reducedHeadVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) j := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · rw [reducedHeadVector_head]
    exact_mod_cast (Nat.zero_le (headStep hv Gamma hrect))
  · rw [reducedHeadVector_succ]
    exact Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt (hv i.succ)))

theorem reducedHeadVector_le_period {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) (j : Fin (n + 1)) :
    ((reducedHeadVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) j ≤
      (v j : ℤ) := by
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · rw [reducedHeadVector_head]
    exact_mod_cast headStep_le_period hv Gamma hrect
  · rw [reducedHeadVector_succ]
    exact (Int.emod_lt_of_pos _ (by exact_mod_cast hv i.succ)).le

/-! ## The triangular basis -/

/-- A basis is in bounded upper-triangular (column Hermite) form relative
to the ambient coordinate order. -/
def IsAdapted {d : ℕ} {v : Fin d → ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) : Prop :=
  ∀ i j,
    (j < i → (((b i : Gamma) : LatticePoint d) j) = 0) ∧
    0 ≤ (((b i : Gamma) : LatticePoint d) j) ∧
    (((b i : Gamma) : LatticePoint d) j) ≤ (v j : ℤ)

/-- The pivots of a triangular basis are strictly positive. -/
def HasPositiveDiagonal {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) : Prop :=
  ∀ i, 0 < (((b i : Gamma) : LatticePoint d) i)

/-- The tail rectangular lattice is contained in the tail of a rectangular
superlattice. -/
theorem rectangularSubgroup_tail_le {n : ℕ} {v : Fin (n + 1) → ℕ}
    {Gamma : Sublattice (n + 1)} (hrect : rectangularSubgroup v ≤ Gamma) :
    rectangularSubgroup (fun i : Fin n ↦ v i.succ) ≤ tailSublattice Gamma := by
  intro x hx
  apply hrect
  rw [mem_rectangularSubgroup_iff] at hx ⊢
  intro j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · simp
  · simpa using hx i

/-- Every head coordinate is divisible by the least positive head step. -/
theorem headStep_dvd {n : ℕ} {v : Fin (n + 1) → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice (n + 1))
    (hrect : rectangularSubgroup v ≤ Gamma) (x : Gamma) :
    (headStep hv Gamma hrect : ℤ) ∣ ((x : LatticePoint (n + 1)) 0) := by
  let a : ℕ := headStep hv Gamma hrect
  have ha : 0 < a := headStep_pos hv Gamma hrect
  let r : ℤ := ((x : LatticePoint (n + 1)) 0) % (a : ℤ)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast (ne_of_gt ha))
  have hra : r < (a : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast ha)
  let q : ℤ := ((x : LatticePoint (n + 1)) 0) / (a : ℤ)
  let y : Gamma := x - q • headVector hv Gamma hrect
  have hyhead : ((y : Gamma) : LatticePoint (n + 1)) 0 = r := by
    change ((x : LatticePoint (n + 1)) 0) -
        q * (((headVector hv Gamma hrect : Gamma) : LatticePoint (n + 1)) 0) = r
    rw [headVector_head]
    dsimp only [q, r, a]
    change ((x : LatticePoint (n + 1)) 0) -
      (((x : LatticePoint (n + 1)) 0) /
        (headStep hv Gamma hrect : ℤ)) * (headStep hv Gamma hrect : ℤ) =
      ((x : LatticePoint (n + 1)) 0) % (headStep hv Gamma hrect : ℤ)
    have hdiv := Int.mul_ediv_add_emod
      ((x : LatticePoint (n + 1)) 0) (headStep hv Gamma hrect : ℤ)
    clear hr0 hra
    nlinarith [hdiv]
  have hrzero : r = 0 := by
    by_contra hrne
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
    have hrnat : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    have hvalue : HeadValue Gamma r.toNat := by
      constructor
      · have hrnatpos : (0 : ℤ) < (r.toNat : ℤ) := by simpa [hrnat] using hrpos
        exact_mod_cast hrnatpos
      · exact ⟨y, hyhead.trans hrnat.symm⟩
    have hminimal : a ≤ r.toNat :=
      by
        classical
        exact Nat.find_min' (exists_headValue hv Gamma hrect) hvalue
    have hminimalZ : (a : ℤ) ≤ (r.toNat : ℤ) := by exact_mod_cast hminimal
    have : (a : ℤ) ≤ r := by simpa [hrnat] using hminimalZ
    omega
  exact Int.dvd_iff_emod_eq_zero.mpr hrzero

/-- Existence of an adapted triangular basis, including positivity of every
Hermite pivot. -/
theorem exists_adapted_basis_with_pos : ∀ {d : ℕ} {v : Fin d → ℕ},
    (∀ i, 0 < v i) → ∀ (Gamma : Sublattice d),
    rectangularSubgroup v ≤ Gamma →
    ∃ b : Basis (Fin d) ℤ Gamma,
      IsAdapted (v := v) b ∧ HasPositiveDiagonal b := by
  intro d
  induction d with
  | zero =>
      intro v hv Gamma hrect
      refine ⟨Basis.empty Gamma, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      intro v hv Gamma hrect
      let vt : Fin n → ℕ := fun i ↦ v i.succ
      have hvt : ∀ i, 0 < vt i := fun i ↦ hv i.succ
      have htail : rectangularSubgroup vt ≤ tailSublattice Gamma :=
        rectangularSubgroup_tail_le hrect
      obtain ⟨bt, hbt⟩ := ih hvt (tailSublattice Gamma) htail
      let bk : Basis (Fin n) ℤ (headKernel Gamma) := bt.map (tailKernelEquiv Gamma)
      let y : Gamma := reducedHeadVector hv Gamma hrect
      have hyhead : ((y : Gamma) : LatticePoint (n + 1)) 0 =
          (headStep hv Gamma hrect : ℤ) := reducedHeadVector_head hv Gamma hrect
      have hli : ∀ (c : ℤ), ∀ x ∈ headKernel Gamma,
          c • y + x = 0 → c = 0 := by
        intro c x hx hzero
        have hz := congrArg
          (fun z : Gamma ↦ ((z : LatticePoint (n + 1)) 0)) hzero
        have hx0 : ((x : Gamma) : LatticePoint (n + 1)) 0 = 0 :=
          mem_headKernel.mp hx
        change c * ((y : Gamma) : LatticePoint (n + 1)) 0 +
            ((x : Gamma) : LatticePoint (n + 1)) 0 = 0 at hz
        rw [hyhead, hx0, add_zero] at hz
        have ha : (headStep hv Gamma hrect : ℤ) ≠ 0 := by
          exact_mod_cast ne_of_gt (headStep_pos hv Gamma hrect)
        exact (mul_eq_zero.mp hz).resolve_right ha
      have hsp : ∀ z : Gamma, ∃ c : ℤ,
          z + c • y ∈ headKernel Gamma := by
        intro z
        obtain ⟨q, hq⟩ := headStep_dvd hv Gamma hrect z
        refine ⟨-q, ?_⟩
        rw [mem_headKernel]
        change ((z : LatticePoint (n + 1)) 0) +
          (-q) * ((y : Gamma) : LatticePoint (n + 1)) 0 = 0
        rw [hyhead]
        rw [hq]
        ring
      let b : Basis (Fin (n + 1)) ℤ Gamma := Basis.mkFinCons y bk hli hsp
      refine ⟨b, ?_, ?_⟩
      · intro i j
        refine Fin.cases ?_ (fun ii ↦ ?_) i
        · simp only [b, Basis.coe_mkFinCons, Fin.cons_zero, y]
          exact ⟨fun h ↦ (Nat.not_lt_zero _ h).elim,
            reducedHeadVector_nonneg hv Gamma hrect j,
            reducedHeadVector_le_period hv Gamma hrect j⟩
        · refine Fin.cases ?_ (fun jj ↦ ?_) j
          · have hk0 : ((((bk ii : headKernel Gamma) : Gamma) :
                LatticePoint (n + 1)) 0) = 0 :=
              mem_headKernel.mp (bk ii).property
            simp only [b, Basis.coe_mkFinCons, Fin.cons_succ]
            change (0 < ii.succ →
                ((((bk ii : headKernel Gamma) : Gamma) :
                  LatticePoint (n + 1)) 0) = 0) ∧
              0 ≤ ((((bk ii : headKernel Gamma) : Gamma) :
                  LatticePoint (n + 1)) 0) ∧
              ((((bk ii : headKernel Gamma) : Gamma) :
                  LatticePoint (n + 1)) 0) ≤ (v 0 : ℤ)
            rw [hk0]
            exact ⟨fun _ ↦ rfl, le_rfl, by exact_mod_cast Nat.zero_le (v 0)⟩
          · simp only [b, Basis.coe_mkFinCons, Fin.cons_succ, bk,
              Basis.map_apply, coe_tailKernelEquiv_apply,
              zeroConsLinear_apply_succ]
            simpa [vt] using hbt.1 ii jj
      · intro i
        refine Fin.cases ?_ (fun ii ↦ ?_) i
        · simp only [b, Basis.coe_mkFinCons, Fin.cons_zero, y,
            reducedHeadVector_head]
          exact_mod_cast headStep_pos hv Gamma hrect
        · simp only [b, Basis.coe_mkFinCons, Fin.cons_succ, bk,
            Basis.map_apply, coe_tailKernelEquiv_apply,
            zeroConsLinear_apply_succ]
          exact hbt.2 ii

/-- The adapted-basis existence theorem with the pivot information
forgotten. -/
theorem exists_adapted_basis {d : ℕ} {v : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice d)
    (hrect : rectangularSubgroup v ≤ Gamma) :
    ∃ b : Basis (Fin d) ℤ Gamma, IsAdapted (v := v) b := by
  obtain ⟨b, hb, _⟩ := exists_adapted_basis_with_pos hv Gamma hrect
  exact ⟨b, hb⟩

/-- Coordinatewise reconstruction of a lattice point from its basis
coefficients. -/
theorem basisCoeff_reconstruction_apply {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (y : Gamma) (j : Fin d) :
    ((y : Gamma) : LatticePoint d) j =
      ∑ i, basisCoeff b y i * (((b i : Gamma) : LatticePoint d) j) := by
  have h := congrArg Subtype.val (sum_basisCoeff_smul b y)
  have hj := congrFun h j
  simpa [mul_comm] using hj.symm

/-- In an adapted basis, ambient coordinate `j` only sees basis directions
with index at most `j`. -/
theorem basisCoeff_reconstruction_Iic {d : ℕ} {v : Fin d → ℕ}
    {Gamma : Sublattice d} (b : Basis (Fin d) ℤ Gamma)
    (hb : IsAdapted (v := v) b) (y : Gamma) (j : Fin d) :
    ((y : Gamma) : LatticePoint d) j =
      ∑ i ∈ Finset.Iic j,
        basisCoeff b y i * (((b i : Gamma) : LatticePoint d) j) := by
  rw [basisCoeff_reconstruction_apply b y j]
  symm
  apply Finset.sum_subset (by simp)
  intro i _ hi
  simp only [Finset.mem_Iic, not_le] at hi
  rw [(hb i j).1 hi, mul_zero]

/-! ## The anisotropic containment estimate -/

/-- If coefficient widths are nondecreasing in the triangular coordinate
order, the contribution to each ambient coordinate is bounded by the
matching width, up to the explicit rectangular constant `d * v j`. -/
theorem weighted_column_sum_le {d : ℕ} {v w : Fin d → ℕ}
    {Gamma : Sublattice d} {b : Basis (Fin d) ℤ Gamma}
    (hb : IsAdapted (v := v) b) (hw : ∀ i j, i ≤ j → w i ≤ w j) (j : Fin d) :
    ∑ i : Fin d, (w i : ℤ) * |(((b i : Gamma) : LatticePoint d) j)| ≤
      (d : ℤ) * (v j : ℤ) * (w j : ℤ) := by
  calc
    ∑ i : Fin d, (w i : ℤ) * |(((b i : Gamma) : LatticePoint d) j)| ≤
        ∑ _i : Fin d, (w j : ℤ) * (v j : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hij : i ≤ j
      · have hwi : (w i : ℤ) ≤ (w j : ℤ) := by exact_mod_cast hw i j hij
        have hbnonneg := (hb i j).2.1
        have hble := (hb i j).2.2
        rw [abs_of_nonneg hbnonneg]
        exact mul_le_mul hwi hble (by positivity) (by positivity)
      · have hji : j < i := lt_of_not_ge hij
        rw [(hb i j).1 hji, abs_zero, mul_zero]
        positivity
    _ = (d : ℤ) * (v j : ℤ) * (w j : ℤ) := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- Coordinate form of bounding-box containment. Any linear combination
whose `i`th coefficient has absolute value at most `w i` lies in the
axis-aligned box with half-width `d * v j * w j` in coordinate `j`. -/
theorem abs_sum_basis_smul_apply_le {d : ℕ} {v w : Fin d → ℕ}
    {Gamma : Sublattice d} {b : Basis (Fin d) ℤ Gamma}
    (hb : IsAdapted (v := v) b) (hw : ∀ i j, i ≤ j → w i ≤ w j)
    (a : Fin d → ℤ) (ha : ∀ i, |a i| ≤ (w i : ℤ)) (j : Fin d) :
    |((∑ i, a i • b i : Gamma) : LatticePoint d) j| ≤
      (d : ℤ) * (v j : ℤ) * (w j : ℤ) := by
  calc
    |((∑ i, a i • b i : Gamma) : LatticePoint d) j| =
        |∑ i, a i * (((b i : Gamma) : LatticePoint d) j)| := by
          congr 1
          simp
    _ ≤ ∑ i, |a i * (((b i : Gamma) : LatticePoint d) j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |(((b i : Gamma) : LatticePoint d) j)| := by
      simp [abs_mul]
    _ ≤ ∑ i, (w i : ℤ) * |(((b i : Gamma) : LatticePoint d) j)| := by
      exact Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_right (ha i) (abs_nonneg _)
    _ ≤ (d : ℤ) * (v j : ℤ) * (w j : ℤ) :=
      weighted_column_sum_le hb hw j

/-! ## Sorting arbitrary coordinate widths -/

/-- Permute coordinates by `sigma`, with new coordinate `i` equal to old
coordinate `sigma i`. -/
def coordinatePerm {d : ℕ} (sigma : Equiv.Perm (Fin d)) :
    LatticePoint d ≃ₗ[ℤ] LatticePoint d where
  toFun x := fun i ↦ x (sigma i)
  invFun x := fun i ↦ x (sigma.symm i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinatePerm_apply {d : ℕ} (sigma : Equiv.Perm (Fin d))
    (x : LatticePoint d) (i : Fin d) :
    coordinatePerm sigma x i = x (sigma i) := rfl

@[simp] theorem coordinatePerm_symm_apply {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (x : LatticePoint d) (i : Fin d) :
    (coordinatePerm sigma).symm x i = x (sigma.symm i) := rfl

/-- The image of a lattice after permuting ambient coordinates. -/
def permutedSublattice {d : ℕ} (sigma : Equiv.Perm (Fin d))
    (Gamma : Sublattice d) : Sublattice d :=
  Gamma.map (coordinatePerm sigma).toAddEquiv.toAddMonoidHom

@[simp] theorem mem_permutedSublattice_iff {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (Gamma : Sublattice d)
    (y : LatticePoint d) :
    y ∈ permutedSublattice sigma Gamma ↔
      (coordinatePerm sigma).symm y ∈ Gamma := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hy
    exact ⟨(coordinatePerm sigma).symm y, hy, by simp⟩

/-- Permuting ambient coordinates restricts to an equivalence of a lattice
with its permuted image. -/
def permutedSublatticeEquiv {d : ℕ} (sigma : Equiv.Perm (Fin d))
    (Gamma : Sublattice d) :
    Gamma ≃ₗ[ℤ] permutedSublattice sigma Gamma where
  toFun x := ⟨coordinatePerm sigma x, by
    rw [mem_permutedSublattice_iff]
    simpa using x.property⟩
  invFun y := ⟨(coordinatePerm sigma).symm y, by
    exact (mem_permutedSublattice_iff sigma Gamma _).mp y.property⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl

@[simp] theorem coe_permutedSublatticeEquiv_apply {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (Gamma : Sublattice d) (x : Gamma) :
    ((permutedSublatticeEquiv sigma Gamma x : permutedSublattice sigma Gamma) :
      LatticePoint d) = coordinatePerm sigma x := rfl

@[simp] theorem coe_permutedSublatticeEquiv_symm_apply {d : ℕ}
    (sigma : Equiv.Perm (Fin d)) (Gamma : Sublattice d)
    (x : permutedSublattice sigma Gamma) :
    (((permutedSublatticeEquiv sigma Gamma).symm x : Gamma) :
      LatticePoint d) = (coordinatePerm sigma).symm x := rfl

/-- Rectangular containment is invariant under simultaneous permutation of
the period vector and the ambient coordinates. -/
theorem rectangularSubgroup_perm_le {d : ℕ} {v : Fin d → ℕ}
    (sigma : Equiv.Perm (Fin d)) {Gamma : Sublattice d}
    (hrect : rectangularSubgroup v ≤ Gamma) :
    rectangularSubgroup (v ∘ sigma) ≤ permutedSublattice sigma Gamma := by
  intro y hy
  rw [mem_permutedSublattice_iff]
  apply hrect
  rw [mem_rectangularSubgroup_iff] at hy ⊢
  intro j
  have hj := hy (sigma.symm j)
  simpa using hj

/-- Arbitrary-width form of the adapted-basis theorem.

The returned permutation `sigma` orders the box widths.  The `i`th basis
coefficient is therefore paired with width `w (sigma i)`.  No monotonicity
hypothesis remains in the interface, and the final coordinate bound is in
the original (unpermuted) coordinate `j`. -/
theorem exists_widthAdapted_basis {d : ℕ} {v w : Fin d → ℕ}
    (hv : ∀ i, 0 < v i) (Gamma : Sublattice d)
    (hrect : rectangularSubgroup v ≤ Gamma) :
    ∃ (sigma : Equiv.Perm (Fin d)) (b : Basis (Fin d) ℤ Gamma),
      Monotone (w ∘ sigma) ∧
      ∀ (a : Fin d → ℤ),
        (∀ i, |a i| ≤ (w (sigma i) : ℤ)) →
        ∀ j,
          |((∑ i, a i • b i : Gamma) : LatticePoint d) j| ≤
            (d : ℤ) * (v j : ℤ) * (w j : ℤ) := by
  let sigma : Equiv.Perm (Fin d) := Tuple.sort w
  let vp : Fin d → ℕ := v ∘ sigma
  let wp : Fin d → ℕ := w ∘ sigma
  let GammaP : Sublattice d := permutedSublattice sigma Gamma
  have hvp : ∀ i, 0 < vp i := fun i ↦ hv (sigma i)
  have hrectP : rectangularSubgroup vp ≤ GammaP := by
    exact rectangularSubgroup_perm_le sigma hrect
  obtain ⟨bp, hbp⟩ := exists_adapted_basis hvp GammaP hrectP
  let e : Gamma ≃ₗ[ℤ] GammaP := permutedSublatticeEquiv sigma Gamma
  let b : Basis (Fin d) ℤ Gamma := bp.map e.symm
  have hwp : Monotone wp := Tuple.monotone_sort w
  refine ⟨sigma, b, hwp, ?_⟩
  intro a ha j
  let jp : Fin d := sigma.symm j
  have hbound := abs_sum_basis_smul_apply_le (v := vp) (w := wp)
    hbp hwp a (by simpa [wp] using ha) jp
  have hcoord :
      ((∑ i, a i • b i : Gamma) : LatticePoint d) j =
        ((∑ i, a i • bp i : GammaP) : LatticePoint d) jp := by
    change ((∑ i, a i • (bp.map e.symm) i : Gamma) : LatticePoint d) j = _
    simp only [Basis.map_apply]
    have heq : e (∑ i, a i • e.symm (bp i)) =
        ∑ i, a i • bp i := by simp
    have hfun := congrArg
      (fun z : GammaP ↦ ((z : LatticePoint d) jp)) heq
    calc
      ((∑ i, a i • e.symm (bp i) : Gamma) : LatticePoint d) j =
          coordinatePerm sigma
            (((∑ i, a i • e.symm (bp i) : Gamma) : LatticePoint d)) jp := by
              simp [jp]
      _ = ((e (∑ i, a i • e.symm (bp i)) : GammaP) :
            LatticePoint d) jp := rfl
      _ = ((∑ i, a i • bp i : GammaP) : LatticePoint d) jp := hfun
  rw [hcoord]
  simpa [vp, wp, jp] using hbound

/-! ## Proper GAP packaging -/

/-- The centered coefficient box in a lattice basis. Its displayed
coefficients are exactly `-radius i, ..., radius i`. -/
noncomputable def centeredBasisGAP {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ) : GAP d d where
  offset := fun j ↦ -∑ i, (radius i : ℤ) *
    (((b i : Gamma) : LatticePoint d) j)
  steps := fun i ↦ ((b i : Gamma) : LatticePoint d)
  widths := fun i ↦ 2 * radius i + 1
  width_pos := fun i ↦ Nat.zero_lt_succ _

@[simp] theorem centeredBasisGAP_widths {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ) (i : Fin d) :
    (centeredBasisGAP b radius).widths i = 2 * radius i + 1 := rfl

/-- Evaluation in the centered GAP is the corresponding signed basis
combination. -/
theorem centeredBasisGAP_coordPoint {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ)
    (n : (centeredBasisGAP b radius).Coord) :
    (centeredBasisGAP b radius).coordPoint n =
      ((∑ i, (((n i : ℕ) : ℤ) - (radius i : ℤ)) • b i : Gamma) :
        LatticePoint d) := by
  funext j
  simp only [GAP.coordPoint, centeredBasisGAP]
  have hcoe : (((∑ i, (((n i : ℕ) : ℤ) - (radius i : ℤ)) • b i : Gamma) :
        LatticePoint d) j) =
      ∑ i, (((n i : ℕ) : ℤ) - (radius i : ℤ)) *
        (((b i : Gamma) : LatticePoint d) j) := by simp
  rw [hcoe]
  change -∑ i, (radius i : ℤ) * (((b i : Gamma) : LatticePoint d) j) +
      ∑ i, ((n i : ℕ) : ℤ) * (((b i : Gamma) : LatticePoint d) j) =
    ∑ i, (((n i : ℕ) : ℤ) - (radius i : ℤ)) *
      (((b i : Gamma) : LatticePoint d) j)
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-- A coefficient box displayed in a genuine lattice basis is proper. -/
theorem centeredBasisGAP_proper {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ) :
    (centeredBasisGAP b radius).Proper := by
  intro n m hnm
  rw [centeredBasisGAP_coordPoint, centeredBasisGAP_coordPoint] at hnm
  have hsub :
      (∑ i, (((n i : ℕ) : ℤ) - (radius i : ℤ)) • b i : Gamma) =
        ∑ i, (((m i : ℕ) : ℤ) - (radius i : ℤ)) • b i := by
    apply Subtype.ext
    exact hnm
  funext i
  apply Fin.ext
  have hi := congrArg (fun z : Gamma ↦ b.repr z i) hsub
  simp at hi
  classical
  simp [Finsupp.single_apply] at hi
  exact hi

/-- The centered basis box is homogeneous. -/
theorem centeredBasisGAP_homogeneous {d : ℕ} {Gamma : Sublattice d}
    (b : Basis (Fin d) ℤ Gamma) (radius : Fin d → ℕ) :
    (centeredBasisGAP b radius).Homogeneous := by
  refine ⟨fun i ↦ -(radius i : ℤ), ?_⟩
  funext j
  simp only [centeredBasisGAP]
  simp

/-- Any coordinate estimate valid for signed coefficients in `[-radius,
radius]` bounds every point of the centered basis GAP. -/
theorem centeredBasisGAP_carrier_coordinate_le {d : ℕ}
    {Gamma : Sublattice d} (b : Basis (Fin d) ℤ Gamma)
    (radius : Fin d → ℕ) (bound : Fin d → ℤ)
    (hbound : ∀ (a : Fin d → ℤ),
      (∀ i, |a i| ≤ (radius i : ℤ)) →
      ∀ j,
        |((∑ i, a i • b i : Gamma) : LatticePoint d) j| ≤ bound j) :
    ∀ x ∈ (centeredBasisGAP b radius).carrier, ∀ j,
      |x j| ≤ bound j := by
  intro x hx j
  obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
  rw [centeredBasisGAP_coordPoint]
  apply hbound
  intro i
  have hn := (n i).isLt
  simp only [centeredBasisGAP_widths] at hn
  rw [abs_le]
  constructor <;> norm_num at ⊢ <;> omega

/-- Fully packaged arbitrary-width output: a proper homogeneous centered
basis GAP whose carrier lies in the required anisotropic axis box. -/
theorem exists_proper_centeredBasisGAP_contained {d : ℕ}
    {v w : Fin d → ℕ} (hv : ∀ i, 0 < v i)
    (Gamma : Sublattice d) (hrect : rectangularSubgroup v ≤ Gamma) :
    ∃ (sigma : Equiv.Perm (Fin d)) (b : Basis (Fin d) ℤ Gamma),
      Monotone (w ∘ sigma) ∧
      (centeredBasisGAP b (w ∘ sigma)).Proper ∧
      (centeredBasisGAP b (w ∘ sigma)).Homogeneous ∧
      ∀ x ∈ (centeredBasisGAP b (w ∘ sigma)).carrier, ∀ j,
        |x j| ≤ (d : ℤ) * (v j : ℤ) * (w j : ℤ) := by
  obtain ⟨sigma, b, hmono, hbound⟩ :=
    exists_widthAdapted_basis hv Gamma hrect
  refine ⟨sigma, b, hmono, centeredBasisGAP_proper b _,
    centeredBasisGAP_homogeneous b _, ?_⟩
  exact centeredBasisGAP_carrier_coordinate_le b (w ∘ sigma)
    (fun j ↦ (d : ℤ) * (v j : ℤ) * (w j : ℤ)) hbound

end Erdos186.CFP.AdaptedHNF
