/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Finite-index lattices and translated integer boxes

This file supplies the elementary lattice facts used in the lattice-intersection
step of the Pham--Zakharov argument.  A full-rank sublattice of `ℤ^d` is
represented by an additive subgroup of finite index, and its discrete
covolume is that index.

The intersection estimate is Mathlib's subgroup-index estimate, specialized
to integer lattices.  The box lemma is constructive: if `q` is the index of a
lattice `L`, then `q • z ∈ L` for every integer vector `z`.  Rounding each
coordinate of the lower corner upwards to a multiple of `q` therefore gives a
lattice point in the corresponding half-open box.  In positive dimension,
doubling the available side length lets us make that point nonzero as well.
-/

namespace Erdos186
namespace LatticeIntersection

open scoped BigOperators

/-- A sublattice of the standard integer lattice. -/
abbrev Sublattice (d : ℕ) := AddSubgroup (LatticePoint d)

/-- The discrete covolume of a sublattice is its additive-group index.

As usual for `Nat.card`, this is zero when the quotient is infinite. -/
noncomputable def covolume {d : ℕ} (L : Sublattice d) : ℕ :=
  L.index

/-- A sublattice is full-rank when it has finite index in `ℤ^d`. -/
def FullRank {d : ℕ} (L : Sublattice d) : Prop :=
  covolume L ≠ 0

/-- Membership in the half-open axis box with lower corner `a` and common
integer side length `Q`. -/
def MemHalfOpenBox {d : ℕ} (a : LatticePoint d) (Q : ℕ)
    (x : LatticePoint d) : Prop :=
  ∀ i, a i ≤ x i ∧ x i < a i + (Q : ℤ)

@[simp]
theorem fullRank_iff_index_ne_zero {d : ℕ} {L : Sublattice d} :
    FullRank L ↔ L.index ≠ 0 :=
  Iff.rfl

theorem fullRank_iff_finite_quotient {d : ℕ} {L : Sublattice d} :
    FullRank L ↔ Finite (LatticePoint d ⧸ L) := by
  rw [fullRank_iff_index_ne_zero, AddSubgroup.index_ne_zero_iff_finite]

/-- Intersecting two full-rank sublattices again gives a full-rank
sublattice. -/
theorem FullRank.inf {d : ℕ} {L K : Sublattice d}
    (hL : FullRank L) (hK : FullRank K) :
    FullRank (L ⊓ K) := by
  exact AddSubgroup.index_inf_ne_zero hL hK

/-- The covolume of an intersection is at most the product of the two
covolumes. -/
theorem covolume_inf_le {d : ℕ} (L K : Sublattice d) :
    covolume (L ⊓ K) ≤ covolume L * covolume K := by
  exact AddSubgroup.index_inf_le

/-- Bounded-covolume form of the binary intersection estimate. -/
theorem covolume_inf_le_mul {d C₁ C₂ : ℕ} {L K : Sublattice d}
    (hL : covolume L ≤ C₁) (hK : covolume K ≤ C₂) :
    covolume (L ⊓ K) ≤ C₁ * C₂ := by
  exact (covolume_inf_le L K).trans (Nat.mul_le_mul hL hK)

/-- In particular, intersecting two lattices of covolume at most `C` costs
at most a square. -/
theorem covolume_inf_le_sq {d C : ℕ} {L K : Sublattice d}
    (hL : covolume L ≤ C) (hK : covolume K ≤ C) :
    covolume (L ⊓ K) ≤ C ^ 2 := by
  simpa [pow_two] using covolume_inf_le_mul hL hK

/-- A finite intersection of full-rank sublattices is full-rank. -/
theorem fullRank_iInf {d : ℕ} {ι : Type*} [Finite ι]
    {L : ι → Sublattice d} (hL : ∀ i, FullRank (L i)) :
    FullRank (⨅ i, L i) := by
  exact AddSubgroup.index_iInf_ne_zero hL

/-- Covolume bound for a finite indexed intersection. -/
theorem covolume_iInf_le_prod {d : ℕ} {ι : Type*} [Fintype ι]
    (L : ι → Sublattice d) :
    covolume (⨅ i, L i) ≤ ∏ i, covolume (L i) := by
  exact AddSubgroup.index_iInf_le L

/-- If every member of a finite family has covolume at most `C`, their
intersection has covolume at most `C ^ |ι|`. -/
theorem covolume_iInf_le_pow {d C : ℕ} {ι : Type*} [Fintype ι]
    {L : ι → Sublattice d} (hL : ∀ i, covolume (L i) ≤ C) :
    covolume (⨅ i, L i) ≤ C ^ Fintype.card ι := by
  calc
    covolume (⨅ i, L i) ≤ ∏ i, covolume (L i) :=
      covolume_iInf_le_prod L
    _ ≤ ∏ _i : ι, C := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) fun i _ ↦ hL i
    _ = C ^ Fintype.card ι := by simp

/-- Every vector multiplied by the covolume belongs to the lattice. -/
theorem covolume_nsmul_mem {d : ℕ} (L : Sublattice d)
    (x : LatticePoint d) :
    covolume L • x ∈ L := by
  exact L.nsmul_index_mem x

/-- A translated half-open axis box of side at least the covolume contains a
lattice point. -/
theorem exists_mem_halfOpenBox_of_covolume_le {d Q : ℕ}
    (L : Sublattice d) (hfull : FullRank L)
    (hcov : covolume L ≤ Q) (a : LatticePoint d) :
    ∃ x : LatticePoint d, x ∈ L ∧ MemHalfOpenBox a Q x := by
  let q := covolume L
  have hq0 : q ≠ 0 := hfull
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hqpos' : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hqpos
  let r : LatticePoint d := fun i ↦ (-a i) % (q : ℤ)
  let x : LatticePoint d := a + r
  let z : LatticePoint d := fun i ↦ -((-a i) / (q : ℤ))
  have hx_eq : x = q • z := by
    funext i
    have hdiv := Int.ediv_mul_add_emod (-a i) (q : ℤ)
    simp only [x, r, z, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
    nlinarith
  refine ⟨x, ?_, ?_⟩
  · rw [hx_eq]
    exact covolume_nsmul_mem L z
  · intro i
    have hr0 : 0 ≤ r i := by
      exact Int.emod_nonneg _ (ne_of_gt hqpos')
    have hrq : r i < (q : ℤ) := by
      exact Int.emod_lt_of_pos _ hqpos'
    have hqQ : (q : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hcov
    dsimp only [x]
    rw [Pi.add_apply]
    constructor <;> dsimp only [r] at * <;> omega

/-- Exact-side version of `exists_mem_halfOpenBox_of_covolume_le`. -/
theorem exists_mem_halfOpenBox {d : ℕ} (L : Sublattice d)
    (hfull : FullRank L) (a : LatticePoint d) :
    ∃ x : LatticePoint d,
      x ∈ L ∧ MemHalfOpenBox a (covolume L) x := by
  exact exists_mem_halfOpenBox_of_covolume_le L hfull le_rfl a

/-- In positive dimension, a translated half-open box whose side is at
least twice the covolume contains a nonzero lattice point. -/
theorem exists_nonzero_mem_halfOpenBox_of_covolume_le {d Q : ℕ}
    (hd : 0 < d) (L : Sublattice d) (hfull : FullRank L)
    (hcov : covolume L ≤ Q) (a : LatticePoint d) :
    ∃ x : LatticePoint d,
      x ∈ L ∧ x ≠ 0 ∧ MemHalfOpenBox a (2 * Q) x := by
  obtain ⟨x, hxL, hxbox⟩ :=
    exists_mem_halfOpenBox_of_covolume_le L hfull hcov a
  by_cases hx0 : x = 0
  · let j : Fin d := ⟨0, hd⟩
    let e : LatticePoint d := fun i ↦ if i = j then 1 else 0
    let y : LatticePoint d := covolume L • e
    have hqpos : 0 < covolume L := Nat.pos_of_ne_zero hfull
    have hqQ : covolume L ≤ Q := hcov
    refine ⟨y, covolume_nsmul_mem L e, ?_, ?_⟩
    · intro hy0
      have := congrFun hy0 j
      simp [y, e] at this
      omega
    · intro i
      have hxi := hxbox i
      rw [hx0] at hxi
      simp only [Pi.zero_apply] at hxi
      have hqQ' : ((covolume L : ℕ) : ℤ) ≤ (Q : ℤ) := by
        exact_mod_cast hqQ
      by_cases hij : i = j
      · subst i
        have hyj : y j = (covolume L : ℤ) := by simp [y, e]
        rw [hyj]
        constructor <;> omega
      · have hyi : y i = 0 := by simp [y, e, hij]
        rw [hyi]
        constructor <;> omega
  · refine ⟨x, hxL, hx0, ?_⟩
    intro i
    have hxi := hxbox i
    have hQ : (0 : ℤ) ≤ (Q : ℤ) := by omega
    constructor
    · exact hxi.1
    · calc
        x i < a i + (Q : ℤ) := hxi.2
        _ ≤ a i + ((2 * Q : ℕ) : ℤ) := by omega

/-- A common point of two full-rank lattices occurs in every translated
axis box whose side is at least the product of their covolumes. -/
theorem exists_common_mem_halfOpenBox {d C₁ C₂ : ℕ}
    {L K : Sublattice d} (hLfull : FullRank L) (hKfull : FullRank K)
    (hLcov : covolume L ≤ C₁) (hKcov : covolume K ≤ C₂)
    (a : LatticePoint d) :
    ∃ x : LatticePoint d,
      x ∈ L ∧ x ∈ K ∧ MemHalfOpenBox a (C₁ * C₂) x := by
  have hfull : FullRank (L ⊓ K) := hLfull.inf hKfull
  have hcov : covolume (L ⊓ K) ≤ C₁ * C₂ :=
    covolume_inf_le_mul hLcov hKcov
  obtain ⟨x, hx, hbox⟩ :=
    exists_mem_halfOpenBox_of_covolume_le (L ⊓ K) hfull hcov a
  exact ⟨x, hx.1, hx.2, hbox⟩

/-- Nonzero common-point version.  Positive ambient dimension is necessary:
`ℤ^0` has no nonzero vector. -/
theorem exists_nonzero_common_mem_halfOpenBox {d C₁ C₂ : ℕ}
    (hd : 0 < d) {L K : Sublattice d}
    (hLfull : FullRank L) (hKfull : FullRank K)
    (hLcov : covolume L ≤ C₁) (hKcov : covolume K ≤ C₂)
    (a : LatticePoint d) :
    ∃ x : LatticePoint d,
      x ∈ L ∧ x ∈ K ∧ x ≠ 0 ∧
        MemHalfOpenBox a (2 * (C₁ * C₂)) x := by
  have hfull : FullRank (L ⊓ K) := hLfull.inf hKfull
  have hcov : covolume (L ⊓ K) ≤ C₁ * C₂ :=
    covolume_inf_le_mul hLcov hKcov
  obtain ⟨x, hx, hx0, hbox⟩ :=
    exists_nonzero_mem_halfOpenBox_of_covolume_le hd (L ⊓ K) hfull hcov a
  exact ⟨x, hx.1, hx.2, hx0, hbox⟩

end LatticeIntersection
end Erdos186
