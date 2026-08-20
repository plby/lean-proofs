/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos407.AdelicMinkowski
import ErdosProblems.Erdos407.PadicSubspaceDefs

/-!
# The integral congruence lattice behind the finite places

This file is deliberately independent of `AdelicSuccessiveMinima`.  Its first
part isolates the elementary piece of Smith-normal-form algebra used to turn
finitely many integral congruences into a full lattice.  The second part
records the rounding of positive real radii to powers of a prime.

The congruence lattice associated with an integral matrix `A` and row moduli
`q` is the kernel of

`z ↦ (sum_i A j i * z i mod q j)_j`.

It has a basis indexed by the ambient coordinates, its index is at most the
product of the row moduli, and membership in it is exactly rowwise
divisibility.  These statements are the algebraic core of the finite-place
lattice construction; rational local forms are reduced to this kernel after
clearing denominators and writing an S-integral point as `z / 6^K`.
-/

namespace Erdos407.PadicSubspace

open scoped BigOperators Matrix
open Module

namespace FinitePlaceLattice

/-! ## Rounding real radii -/

/-- A positive real number lies between two consecutive integral powers of
any natural base greater than one.  The lower power is the correct rounded
radius for a discretely valued norm. -/
theorem exists_primePower_floor (p : ℕ) (hp : 2 ≤ p) {r : ℝ} (hr : 0 < r) :
    ∃ a : ℤ, (p : ℝ) ^ a ≤ r ∧ r < (p : ℝ) ^ (a + 1) := by
  exact exists_mem_Ico_zpow hr (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hp))

/-- The upper endpoint in `exists_primePower_floor` is the lower endpoint
times the base. -/
theorem primePower_floor_lt_mul (p : ℕ) (hp : p ≠ 0) {r : ℝ} {a : ℤ}
    (hr : r < (p : ℝ) ^ (a + 1)) :
    r < (p : ℝ) * (p : ℝ) ^ a := by
  calc
    r < (p : ℝ) ^ (a + 1) := hr
    _ = (p : ℝ) ^ a * (p : ℝ) ^ (1 : ℤ) :=
      zpow_add₀ (by exact_mod_cast hp : (p : ℝ) ≠ 0) a 1
    _ = (p : ℝ) * (p : ℝ) ^ a := by rw [zpow_one, mul_comm]

/-- On rational numbers, replacing a positive real radius by its lower
`p`-power does not change a `p`-adic closed ball. -/
theorem padicNorm_le_iff_le_floor_power (p : ℕ) [Fact p.Prime]
    {r : ℝ} {a : ℤ} (hla : (p : ℝ) ^ a ≤ r)
    (hru : r < (p : ℝ) ^ (a + 1)) (q : ℚ) :
    (padicNorm p q : ℝ) ≤ r ↔ (padicNorm p q : ℝ) ≤ (p : ℝ) ^ a := by
  constructor
  · intro hq
    by_cases hq0 : q = 0
    · rw [hq0]
      simp only [padicNorm.zero, Rat.cast_zero, zero_le]
      exact zpow_nonneg (show (0 : ℝ) ≤ (p : ℝ) by positivity) a
    · have hnorm : (padicNorm p q : ℝ) = (p : ℝ) ^ (-(padicValRat p q)) := by
        rw [padicNorm.eq_zpow_of_nonzero hq0, Rat.cast_zpow]
        norm_num
      rw [hnorm] at hq ⊢
      have hp1 : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast (Fact.out : Nat.Prime p).one_lt
      by_contra hnot
      have hlt : (p : ℝ) ^ a < (p : ℝ) ^ (-(padicValRat p q)) :=
        lt_of_not_ge hnot
      have ha_lt : a < -(padicValRat p q) := by
        exact (zpow_lt_zpow_iff_right₀ hp1).mp hlt
      have ha1 : a + 1 ≤ -(padicValRat p q) := by omega
      have hpmono : (p : ℝ) ^ (a + 1) ≤ (p : ℝ) ^ (-(padicValRat p q)) :=
        (zpow_le_zpow_iff_right₀ hp1).mpr ha1
      exact (not_lt_of_ge (hpmono.trans hq)) hru
  · exact fun h => h.trans hla

/-! ## Integral congruence kernels -/

/-- Simultaneous rowwise reduction modulo a possibly varying family of
positive integers. -/
def congruenceMap {m n : ℕ} (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) :
    (Fin n → ℤ) →ₗ[ℤ] (∀ j : Fin m, ZMod (q j)) where
  toFun z j := ∑ i, (A j i : ZMod (q j)) * (z i : ZMod (q j))
  map_add' x y := by
    ext j
    simp only [Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext j
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [← Int.cast_smul_eq_zsmul (ZMod (q j)) c, Algebra.smul_def]
    change (∑ i, (A j i : ZMod (q j)) * ((c : ZMod (q j)) * (x i : ZMod (q j)))) =
      (c : ZMod (q j)) * ∑ i, (A j i : ZMod (q j)) * (x i : ZMod (q j))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem congruenceMap_apply {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (z : Fin n → ℤ) (j : Fin m) :
    congruenceMap A q z j =
      ∑ i, (A j i : ZMod (q j)) * (z i : ZMod (q j)) :=
  rfl

/-- The integral lattice cut out by the row congruences `A_j z = 0 mod q_j`. -/
def congruenceModule {m n : ℕ} (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) :
    Submodule ℤ (Fin n → ℤ) :=
  LinearMap.ker (congruenceMap A q)

@[simp] theorem mem_congruenceModule {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (z : Fin n → ℤ) :
    z ∈ congruenceModule A q ↔
      ∀ j, (q j : ℤ) ∣ ∑ i, A j i * z i := by
  rw [congruenceModule, LinearMap.mem_ker]
  constructor
  · intro hz j
    have hj := congrFun hz j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [congruenceMap_apply, Pi.zero_apply, Int.cast_sum, Int.cast_mul] using hj
  · intro hz
    funext j
    have hj := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hz j)
    simpa only [congruenceMap_apply, Pi.zero_apply, Int.cast_sum, Int.cast_mul] using hj

/-- The index of a simultaneous congruence kernel is at most the cardinality
of the full residue space. -/
theorem congruenceModule_index_le {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j) :
    (congruenceModule A q).toAddSubgroup.index ≤ ∏ j, q j := by
  letI (j : Fin m) : NeZero (q j) := ⟨(hq j).ne'⟩
  change (congruenceMap A q).toAddMonoidHom.ker.index ≤ _
  rw [AddSubgroup.index_ker]
  calc
    Nat.card (congruenceMap A q).toAddMonoidHom.range ≤
        Nat.card (∀ j : Fin m, ZMod (q j)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ = ∏ j, q j := by
      rw [Nat.card_pi]
      apply Finset.prod_congr rfl
      intro j _
      exact Nat.card_zmod (q j)

/-- Positive row moduli make the congruence kernel a full-rank free
`ℤ`-module.  This is the Smith-normal-form step. -/
theorem congruenceModule_index_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j) :
    (congruenceModule A q).toAddSubgroup.index ≠ 0 := by
  letI (j : Fin m) : NeZero (q j) := ⟨(hq j).ne'⟩
  change (congruenceMap A q).toAddMonoidHom.ker.index ≠ 0
  rw [AddSubgroup.index_ker]
  have hrange : Finite (congruenceMap A q).toAddMonoidHom.range := inferInstance
  let _ : Finite (congruenceMap A q).toAddMonoidHom.range := hrange
  exact (Nat.card_pos : 0 < Nat.card (congruenceMap A q).toAddMonoidHom.range).ne'

/-- A canonical (noncomputable) full-rank Smith basis of the simultaneous
congruence kernel. -/
noncomputable def congruenceBasis {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j) :
    Basis (Fin n) ℤ (congruenceModule A q) := by
  have hindex : (congruenceModule A q).toAddSubgroup.index ≠ 0 :=
    congruenceModule_index_ne_zero A q hq
  have he : Nonempty ((congruenceModule A q) ≃ₗ[ℤ] (Fin n → ℤ)) :=
    Int.submodule_toAddSubgroup_index_ne_zero_iff.mp hindex
  exact Basis.ofEquivFun he.some

/-- The chosen congruence basis really spans precisely the solutions of all
row divisibilities. -/
theorem mem_congruenceModule_iff_exists_basis_repr {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j)
    (z : Fin n → ℤ) :
    (∀ j, (q j : ℤ) ∣ ∑ i, A j i * z i) ↔
      ∃ c : Fin n → ℤ,
        z = ∑ i, c i • (congruenceBasis A q hq i : Fin n → ℤ) := by
  rw [← mem_congruenceModule A q]
  constructor
  · intro hz
    let z' : congruenceModule A q := ⟨z, hz⟩
    refine ⟨fun i => (congruenceBasis A q hq).repr z' i, ?_⟩
    change z = ∑ i, ((congruenceBasis A q hq).repr z') i •
      ((congruenceBasis A q hq i : congruenceModule A q) : Fin n → ℤ)
    apply funext
    intro j
    have hj := congrFun
      (congrArg (fun w : congruenceModule A q => (w : Fin n → ℤ))
        ((congruenceBasis A q hq).sum_repr z').symm) j
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using hj
  · rintro ⟨c, rfl⟩
    simpa using Submodule.sum_smul_mem (congruenceModule A q) c
      (fun i (_hi : i ∈ Finset.univ) => (congruenceBasis A q hq i).property)

/-- The determinant of the integral congruence basis is its subgroup index.
This exact statement is convenient when the basis is subsequently scaled by
`6⁻K` and embedded in `ℝ^n`. -/
theorem natAbs_det_congruenceBasis_eq_index {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j) :
    (Matrix.det (fun i j =>
      ((congruenceBasis A q hq j : congruenceModule A q) : Fin n → ℤ) i)).natAbs =
      (congruenceModule A q).toAddSubgroup.index := by
  classical
  rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin n))
    (congruenceModule A q).toAddSubgroup (congruenceBasis A q hq)]
  congr 1

/-- Consequently the determinant of the integral congruence basis is bounded
by the product of the row moduli. -/
theorem natAbs_det_congruenceBasis_le {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j) :
    (Matrix.det (fun i j =>
      ((congruenceBasis A q hq j : congruenceModule A q) : Fin n → ℤ) i)).natAbs ≤
      ∏ j, q j := by
  rw [natAbs_det_congruenceBasis_eq_index]
  exact congruenceModule_index_le A q hq

/-! ## Rational and real realizations -/

/-- Scale the integral Smith basis by a nonzero rational number. -/
noncomputable def scaledRationalBasis {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j)
    (s : ℚ) : Fin n → Fin n → ℚ :=
  fun i k => s *
    (((congruenceBasis A q hq i : congruenceModule A q) : Fin n → ℤ) k : ℚ)

/-- The scaled Smith family is a rational basis whenever the scale is
nonzero. -/
theorem scaledRationalBasis_linearIndependent {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j)
    {s : ℚ} (hs : s ≠ 0) :
    LinearIndependent ℚ (scaledRationalBasis A q hq s) := by
  let vZ : Fin n → Fin n → ℤ := fun i =>
    ((congruenceBasis A q hq i : congruenceModule A q) : Fin n → ℤ)
  have hvZ : LinearIndependent ℤ vZ := by
    exact (congruenceBasis A q hq).linearIndependent.map'
      (congruenceModule A q).subtype
      (LinearMap.ker_eq_bot.mpr (congruenceModule A q).subtype_injective)
  have hvQ : LinearIndependent ℚ (fun i => algebraMap ℤ ℚ ∘ vZ i) := by
    exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)).2 hvZ
  let u : ℚˣ := Units.mk0 s hs
  have hscaled := hvQ.units_smul (fun _ => u)
  convert hscaled using 1
  funext i k
  simp [scaledRationalBasis, vZ, u]

/-- The real basis obtained from the same scaled integral vectors. -/
noncomputable def scaledRealBasis {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j)
    (s : ℚ) (hs : s ≠ 0) : Basis (Fin n) ℝ (Fin n → ℝ) := by
  classical
  let vZ : Fin n → Fin n → ℤ := fun i =>
    ((congruenceBasis A q hq i : congruenceModule A q) : Fin n → ℤ)
  have hvZ : LinearIndependent ℤ vZ := by
    exact (congruenceBasis A q hq).linearIndependent.map'
      (congruenceModule A q).subtype
      (LinearMap.ker_eq_bot.mpr (congruenceModule A q).subtype_injective)
  have hvR : LinearIndependent ℝ (fun i => algebraMap ℤ ℝ ∘ vZ i) := by
    exact (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)).2 hvZ
  let u : ℝˣ := Units.mk0 (s : ℝ) (by exact_mod_cast hs)
  have hscaled := hvR.units_smul (fun _ => u)
  have hlin : LinearIndependent ℝ
      (fun i k => (s : ℝ) * (vZ i k : ℝ)) := by
    convert hscaled using 1
    funext i k
    simp [u]
  exact basisOfPiSpaceOfLinearIndependent hlin

@[simp] theorem scaledRealBasis_apply {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j)
    (s : ℚ) (hs : s ≠ 0) (i k : Fin n) :
    scaledRealBasis A q hq s hs i k =
      (scaledRationalBasis A q hq s i k : ℝ) := by
  classical
  simp only [scaledRealBasis, coe_basisOfPiSpaceOfLinearIndependent,
    scaledRationalBasis, Rat.cast_mul, Rat.cast_intCast]

/-- Exact rational map-back: the integer span of the scaled basis consists
precisely of scaled integer vectors satisfying the defining congruences. -/
theorem exists_scaledRationalBasis_repr_iff {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j)
    (s : ℚ) (x : Fin n → ℚ) :
    (∃ c : Fin n → ℤ,
        x = ∑ i, (c i : ℚ) • scaledRationalBasis A q hq s i) ↔
      ∃ z : Fin n → ℤ,
        (∀ j, (q j : ℤ) ∣ ∑ i, A j i * z i) ∧
        x = s • fun k => (z k : ℚ) := by
  constructor
  · rintro ⟨c, rfl⟩
    let z : Fin n → ℤ := ∑ i, c i •
      ((congruenceBasis A q hq i : congruenceModule A q) : Fin n → ℤ)
    refine ⟨z, ?_, ?_⟩
    · rw [← mem_congruenceModule A q]
      exact Submodule.sum_smul_mem (congruenceModule A q) c
        (fun i (_hi : i ∈ Finset.univ) => (congruenceBasis A q hq i).property)
    · funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        scaledRationalBasis, z, Int.cast_sum, Int.cast_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := (mem_congruenceModule_iff_exists_basis_repr A q hq z).1 hz
    refine ⟨c, ?_⟩
    funext k
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      scaledRationalBasis, Int.cast_sum, Int.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The Archimedean covolume determinant of the scaled basis is bounded by
the scale to the ambient dimension times the product of congruence moduli. -/
theorem abs_det_scaledRealBasis_le {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (q : Fin m → ℕ) (hq : ∀ j, 0 < q j)
    (s : ℚ) (hs : s ≠ 0) :
    |(Pi.basisFun ℝ (Fin n)).det (scaledRealBasis A q hq s hs)| ≤
      |(s : ℝ)| ^ n * (∏ j, q j : ℕ) := by
  classical
  rw [Basis.det_apply]
  have hmatrix : (Pi.basisFun ℝ (Fin n)).toMatrix
      (scaledRealBasis A q hq s hs) =
      fun i j => (s : ℝ) *
        (((congruenceBasis A q hq j : congruenceModule A q) : Fin n → ℤ) i : ℝ) := by
    ext i j
    simp [Basis.toMatrix_apply, scaledRealBasis_apply, scaledRationalBasis]
  rw [hmatrix]
  let U : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    (((congruenceBasis A q hq j : congruenceModule A q) : Fin n → ℤ) i : ℝ)
  rw [show (fun i j => (s : ℝ) *
      (((congruenceBasis A q hq j : congruenceModule A q) : Fin n → ℤ) i : ℝ)) =
      (s : ℝ) • U by
        ext i j
        change (s : ℝ) * _ = (s : ℝ) * U i j
        rfl]
  rw [Matrix.det_smul]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, abs_mul,
    abs_pow]
  gcongr
  change |Matrix.det U| ≤ _
  let V : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    ((congruenceBasis A q hq j : congruenceModule A q) : Fin n → ℤ) i
  have hUV : U = V.map (Int.castRingHom ℝ) := by
    ext i j
    rfl
  have hdet : (V.map (Int.castRingHom ℝ)).det = ((V.det : ℤ) : ℝ) := by
    exact (Int.cast_det V).symm
  rw [hUV, hdet]
  rw [← Int.cast_abs, ← Int.natCast_natAbs]
  norm_cast
  simpa [V] using natAbs_det_congruenceBasis_le A q hq

/-! ## Cleared rational rows -/

/-- A congruence for a denominator-cleared rational row gives the expected
`p`-adic bound after scaling.  This is the arithmetic map-back used for each
of the two finite places. -/
theorem padicNorm_scaled_intCast_le_of_dvd {n p e : ℕ} [Fact p.Prime]
    (f : RatLinearForm n) (A : Fin n → ℤ) (D : ℕ) (hD : D ≠ 0)
    (s : ℚ) (z : Fin n → ℤ) (r : ℝ)
    (hclear : (D : ℚ) * f (fun k ↦ (z k : ℚ)) =
      ((∑ k, A k * z k : ℤ) : ℚ))
    (hdvd : ((p ^ e : ℕ) : ℤ) ∣ ∑ k, A k * z k)
    (hround : ((padicNorm p (s / (D : ℚ)) *
      (p : ℚ) ^ (-(e : ℤ)) : ℚ) : ℝ) ≤ r) :
    (padicNorm p (f (s • fun k ↦ (z k : ℚ))) : ℝ) ≤ r := by
  have hform : f (s • fun k ↦ (z k : ℚ)) =
      (s / (D : ℚ)) * ((∑ k, A k * z k : ℤ) : ℚ) := by
    rw [map_smul]
    change s * f (fun k ↦ (z k : ℚ)) = _
    rw [← hclear]
    field_simp
  have hnorm : padicNorm p
      (((∑ k, A k * z k : ℤ) : ℚ)) ≤
      (p : ℚ) ^ (-(e : ℤ)) :=
    (padicNorm.dvd_iff_norm_le).mp hdvd
  have hnormR : (padicNorm p
      (((∑ k, A k * z k : ℤ) : ℚ)) : ℝ) ≤
      (((p : ℚ) ^ (-(e : ℤ)) : ℚ) : ℝ) := by
    exact_mod_cast hnorm
  have hround' : (padicNorm p (s / (D : ℚ)) : ℝ) *
      (((p : ℚ) ^ (-(e : ℤ)) : ℚ) : ℝ) ≤ r := by
    simpa only [Rat.cast_mul] using hround
  rw [hform, padicNorm.mul, Rat.cast_mul]
  exact (mul_le_mul_of_nonneg_left hnormR
    (by exact_mod_cast padicNorm.nonneg (s / (D : ℚ)))).trans hround'

/-! ## The two finite places -/

/-- A radius at most one lies between two consecutive nonpositive powers of
`p`, written with a natural exponent for the resulting congruence modulus. -/
theorem exists_inverse_primePower_floor (p : ℕ) (hp : 2 ≤ p)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ e : ℕ, (p : ℝ) ^ (-(e : ℤ)) ≤ r ∧
      r < (p : ℝ) * (p : ℝ) ^ (-(e : ℤ)) := by
  obtain ⟨a, ha, ha'⟩ := exists_primePower_floor p hp hr
  have ha0 : a ≤ 0 := by
    by_contra h
    have hpos : 0 < a := lt_of_not_ge h
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
    have : (1 : ℝ) < (p : ℝ) ^ a := by
      simpa using (zpow_lt_zpow_right₀ hp1 hpos)
    linarith
  have hae : a = -(a.natAbs : ℤ) := Int.eq_neg_natAbs_of_nonpos ha0
  refine ⟨a.natAbs, ?_, ?_⟩
  · rw [← hae]
    exact ha
  · rw [← hae]
    exact primePower_floor_lt_mul p (by omega) ha'

/-- The finite-place index `0` denotes `2`, and `1` denotes `3`. -/
def finitePlace (u : Fin 2) : Place23 :=
  Fin.cases Place23.two (fun _ ↦ Place23.three) u

/-- The rational prime belonging to a finite-place index. -/
def finitePrime (u : Fin 2) : ℕ :=
  Fin.cases 2 (fun _ ↦ 3) u

@[simp] theorem finitePlace_zero : finitePlace 0 = Place23.two := rfl
@[simp] theorem finitePlace_one : finitePlace 1 = Place23.three := rfl
@[simp] theorem finitePrime_zero : finitePrime 0 = 2 := rfl
@[simp] theorem finitePrime_one : finitePrime 1 = 3 := rfl

theorem finitePrime_pos (u : Fin 2) : 0 < finitePrime u := by
  fin_cases u <;> decide

/-- The `2n` finite rows, written as a rectangular rational coefficient
matrix. -/
def finiteFormMatrix {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    Matrix (Fin (2 * n)) (Fin n) ℚ := fun j k ↦
  let ui := finProdFinEquiv.symm j
  coefficientVector (L (finitePlace ui.1) ui.2) k

/-- A positive common denominator clearing all `2n·n` finite-form
coefficients. -/
def finiteFormDenominator {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : ℕ :=
  (finiteFormMatrix L).den

/-- The integral matrix obtained by clearing the common denominator. -/
def finiteIntegralFormMatrix {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    Fin (2 * n) → Fin n → ℤ :=
  (finiteFormMatrix L).num

theorem finiteFormDenominator_ne_zero {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    finiteFormDenominator L ≠ 0 :=
  Matrix.den_ne_zero (finiteFormMatrix L)

/-- The integral row really is the common denominator times the
corresponding rational linear form. -/
theorem finiteIntegralFormMatrix_clear {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (j : Fin (2 * n)) (z : Fin n → ℤ) :
    (finiteFormDenominator L : ℚ) *
        L (finitePlace (finProdFinEquiv.symm j).1)
          (finProdFinEquiv.symm j).2 (fun k ↦ (z k : ℚ)) =
      ((∑ k, finiteIntegralFormMatrix L j k * z k : ℤ) : ℚ) := by
  classical
  rw [linearForm_eq_dotProduct]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk := Matrix.num_div_den (finiteFormMatrix L) j k
  have hD : (finiteFormDenominator L : ℚ) ≠ 0 := by
    exact_mod_cast finiteFormDenominator_ne_zero L
  have hk' : (finiteIntegralFormMatrix L j k : ℚ) =
      (finiteFormDenominator L : ℚ) * finiteFormMatrix L j k := by
    simpa only [finiteIntegralFormMatrix, finiteFormDenominator, mul_comm] using
      (div_eq_iff hD).mp hk
  rw [hk']
  change (finiteFormDenominator L : ℚ) *
      (finiteFormMatrix L j k * (z k : ℚ)) = _
  ring

/-- The common `{2,3}`-integral scale `6⁻ᵏ`. -/
def finiteScale (K : ℕ) : ℚ := ((6 : ℚ) ^ K)⁻¹

theorem finiteScale_ne_zero (K : ℕ) : finiteScale K ≠ 0 := by
  simp [finiteScale]

theorem padicNorm_two_finiteScale (K : ℕ) :
    padicNorm 2 (finiteScale K) = (2 : ℚ) ^ K := by
  have hsix : padicNorm 2 (6 : ℚ) = (2 : ℚ)⁻¹ := by
    have h2 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ :=
      padicNorm.padicNorm_p_of_prime
    have h3 : padicNorm 2 (3 : ℚ) = 1 :=
      padicNorm.padicNorm_of_prime_of_ne (p := 2) (q := 3) (by omega)
    rw [show (6 : ℚ) = 2 * 3 by norm_num, padicNorm.mul, h2, h3]
    simp
  have hpow : padicNorm 2 ((6 : ℚ) ^ K) = ((2 : ℚ)⁻¹) ^ K := by
    induction K with
    | zero => simp
    | succ K ih => rw [pow_succ, padicNorm.mul, ih, hsix, pow_succ]
  rw [finiteScale, inv_eq_one_div, padicNorm.div, padicNorm.one, hpow]
  simp [inv_pow]

theorem padicNorm_three_finiteScale (K : ℕ) :
    padicNorm 3 (finiteScale K) = (3 : ℚ) ^ K := by
  have hsix : padicNorm 3 (6 : ℚ) = (3 : ℚ)⁻¹ := by
    have h2 : padicNorm 3 (2 : ℚ) = 1 :=
      padicNorm.padicNorm_of_prime_of_ne (p := 3) (q := 2) (by omega)
    have h3 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ :=
      padicNorm.padicNorm_p_of_prime
    rw [show (6 : ℚ) = 2 * 3 by norm_num, padicNorm.mul, h2, h3]
    simp
  have hpow : padicNorm 3 ((6 : ℚ) ^ K) = ((3 : ℚ)⁻¹) ^ K := by
    induction K with
    | zero => simp
    | succ K ih => rw [pow_succ, padicNorm.mul, ih, hsix, pow_succ]
  rw [finiteScale, inv_eq_one_div, padicNorm.div, padicNorm.one, hpow]
  simp [inv_pow]

/-- The norm of the common scale divided by the coefficient-clearing
denominator at one of the two finite places. -/
def finiteScaleNorm {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (K : ℕ) (u : Fin 2) : ℝ :=
  Fin.cases
    (padicNorm 2 (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ)
    (fun _ ↦
      (padicNorm 3 (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ)) u

theorem finiteScaleNorm_pos {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (K : ℕ) (u : Fin 2) :
    0 < finiteScaleNorm L K u := by
  fin_cases u
  · change 0 < (padicNorm 2
      (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ)
    have hDq : (finiteFormDenominator L : ℚ) ≠ 0 := by
      exact_mod_cast finiteFormDenominator_ne_zero L
    have hnz := padicNorm.nonzero (p := 2)
      (div_ne_zero (finiteScale_ne_zero K) hDq)
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hnz)
  · change 0 < (padicNorm 3
      (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ)
    have hDq : (finiteFormDenominator L : ℚ) ≠ 0 := by
      exact_mod_cast finiteFormDenominator_ne_zero L
    have hnz := padicNorm.nonzero (p := 3)
      (div_ne_zero (finiteScale_ne_zero K) hDq)
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hnz)

@[simp] theorem finiteScaleNorm_zero {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (K : ℕ) :
    finiteScaleNorm L K 0 =
      ((2 : ℝ) ^ K /
        (padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ)) := by
  change (padicNorm 2
      (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ) = _
  rw [padicNorm.div, padicNorm_two_finiteScale]
  norm_cast

@[simp] theorem finiteScaleNorm_one {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) (K : ℕ) :
    finiteScaleNorm L K 1 =
      ((3 : ℝ) ^ K /
        (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ)) := by
  change (padicNorm 3
      (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ) = _
  rw [padicNorm.div, padicNorm_three_finiteScale]
  norm_cast

/-- A sufficiently deep common `6`-power denominator makes every normalized
finite radius at most one. -/
theorem exists_finiteScale_normalizes {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (r : Fin 2 → Fin n → ℝ) (hr : ∀ u i, 0 < r u i) :
    ∃ K : ℕ, ∀ u i, r u i / finiteScaleNorm L K u ≤ 1 := by
  classical
  let d2 : ℝ := (padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ)
  let d3 : ℝ := (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ)
  let R2 : ℝ := (∑ i, r 0 i) * d2
  let R3 : ℝ := (∑ i, r 1 i) * d3
  let C : ℝ := max 1 (max R2 R3)
  have hC : (1 : ℝ) ≤ C := le_max_left _ _
  obtain ⟨k, _hk, hk'⟩ := exists_nat_pow_near hC (by norm_num : (1 : ℝ) < 2)
  refine ⟨k + 1, fun u i ↦ ?_⟩
  have hd2 : 0 < d2 := by
    have hDq : (finiteFormDenominator L : ℚ) ≠ 0 := by
      exact_mod_cast finiteFormDenominator_ne_zero L
    have hnz := padicNorm.nonzero (p := 2) hDq
    change 0 < (padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ)
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hnz)
  have hd3 : 0 < d3 := by
    have hDq : (finiteFormDenominator L : ℚ) ≠ 0 := by
      exact_mod_cast finiteFormDenominator_ne_zero L
    have hnz := padicNorm.nonzero (p := 3) hDq
    change 0 < (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ)
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hnz)
  have hsum (u : Fin 2) (i : Fin n) : r u i ≤ ∑ j, r u j :=
    Finset.single_le_sum (fun j _ ↦ (hr u j).le) (Finset.mem_univ i)
  fin_cases u
  · change r 0 i / finiteScaleNorm L (k + 1) 0 ≤ 1
    rw [finiteScaleNorm_zero]
    change r 0 i / ((2 : ℝ) ^ (k + 1) / d2) ≤ 1
    apply (div_le_one (div_pos (by positivity) hd2)).2
    apply (le_div_iff₀ hd2).2
    calc
      r 0 i * d2 ≤ R2 := mul_le_mul_of_nonneg_right (hsum 0 i) hd2.le
      _ ≤ max R2 R3 := le_max_left _ _
      _ ≤ C := le_max_right _ _
      _ ≤ (2 : ℝ) ^ (k + 1) := hk'.le
  · change r 1 i / finiteScaleNorm L (k + 1) 1 ≤ 1
    rw [finiteScaleNorm_one]
    change r 1 i / ((3 : ℝ) ^ (k + 1) / d3) ≤ 1
    apply (div_le_one (div_pos (by positivity) hd3)).2
    apply (le_div_iff₀ hd3).2
    calc
      r 1 i * d3 ≤ R3 := mul_le_mul_of_nonneg_right (hsum 1 i) hd3.le
      _ ≤ max R2 R3 := le_max_right _ _
      _ ≤ C := le_max_right _ _
      _ ≤ (2 : ℝ) ^ (k + 1) := hk'.le
      _ ≤ (3 : ℝ) ^ (k + 1) := by gcongr <;> norm_num

/-- Simultaneous rounding of all normalized radii to inverse prime powers.
The second inequality is the factor-`p` loss used in the index estimate. -/
theorem exists_finiteRoundingExponents {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (r : Fin 2 → Fin n → ℝ) (hr : ∀ u i, 0 < r u i)
    (hK : ∀ u i, r u i / finiteScaleNorm L K u ≤ 1) :
    ∃ e : Fin 2 → Fin n → ℕ, ∀ u i,
      finiteScaleNorm L K u *
          (finitePrime u : ℝ) ^ (-(e u i : ℤ)) ≤ r u i ∧
      r u i < (finitePrime u : ℝ) * finiteScaleNorm L K u *
          (finitePrime u : ℝ) ^ (-(e u i : ℤ)) := by
  classical
  have hex (u : Fin 2) (i : Fin n) :
      ∃ a : ℕ, (finitePrime u : ℝ) ^ (-(a : ℤ)) ≤
          r u i / finiteScaleNorm L K u ∧
        r u i / finiteScaleNorm L K u <
          (finitePrime u : ℝ) *
            (finitePrime u : ℝ) ^ (-(a : ℤ)) := by
    have hpos : 0 < r u i / finiteScaleNorm L K u :=
      div_pos (hr u i) (finiteScaleNorm_pos L K u)
    fin_cases u
    · exact exists_inverse_primePower_floor 2 (by omega) hpos (hK 0 i)
    · exact exists_inverse_primePower_floor 3 (by omega) hpos (hK 1 i)
  choose e he using hex
  refine ⟨e, fun u i ↦ ?_⟩
  have hN := finiteScaleNorm_pos L K u
  constructor
  · calc
      finiteScaleNorm L K u *
          (finitePrime u : ℝ) ^ (-(e u i : ℤ)) ≤
          finiteScaleNorm L K u *
            (r u i / finiteScaleNorm L K u) :=
        mul_le_mul_of_nonneg_left (he u i).1 hN.le
      _ = r u i := by field_simp
  · calc
      r u i = finiteScaleNorm L K u *
          (r u i / finiteScaleNorm L K u) := by field_simp
      _ < finiteScaleNorm L K u * ((finitePrime u : ℝ) *
          (finitePrime u : ℝ) ^ (-(e u i : ℤ))) :=
        mul_lt_mul_of_pos_left (he u i).2 hN
      _ = (finitePrime u : ℝ) * finiteScaleNorm L K u *
          (finitePrime u : ℝ) ^ (-(e u i : ℤ)) := by ring

/-- The row modulus attached to rounded exponents. -/
def finiteModuli {n : ℕ} (e : Fin 2 → Fin n → ℕ) :
    Fin (2 * n) → ℕ := fun j ↦
  let ui := finProdFinEquiv.symm j
  finitePrime ui.1 ^ e ui.1 ui.2

theorem finiteModuli_pos {n : ℕ} (e : Fin 2 → Fin n → ℕ) :
    ∀ j, 0 < finiteModuli e j := by
  intro j
  unfold finiteModuli
  exact pow_pos (finitePrime_pos _) _

/-- The actual rational basis of the finite-place approximation lattice. -/
noncomputable def finiteRationalBasis {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (e : Fin 2 → Fin n → ℕ) : Fin n → Fin n → ℚ :=
  scaledRationalBasis (finiteIntegralFormMatrix L) (finiteModuli e)
    (finiteModuli_pos e) (finiteScale K)

/-- The corresponding full real basis. -/
noncomputable def finiteRealBasis {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (e : Fin 2 → Fin n → ℕ) : Basis (Fin n) ℝ (Fin n → ℝ) :=
  scaledRealBasis (finiteIntegralFormMatrix L) (finiteModuli e)
    (finiteModuli_pos e) (finiteScale K) (finiteScale_ne_zero K)

@[simp] theorem finiteRealBasis_apply {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (e : Fin 2 → Fin n → ℕ) (i k : Fin n) :
    finiteRealBasis (K := K) L e i k =
      (finiteRationalBasis (K := K) L e i k : ℝ) := by
  exact scaledRealBasis_apply _ _ _ _ _ _ _

/-- Exact map-back for the finite-place basis, with one congruence for every
pair `(p,i)`, `p=2,3`. -/
theorem exists_finiteRationalBasis_repr_iff {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (e : Fin 2 → Fin n → ℕ) (x : Fin n → ℚ) :
    (∃ c : Fin n → ℤ,
        x = ∑ i, (c i : ℚ) • finiteRationalBasis (K := K) L e i) ↔
      ∃ z : Fin n → ℤ,
        (∀ u i, ((finitePrime u ^ e u i : ℕ) : ℤ) ∣
          ∑ k, finiteIntegralFormMatrix L (finProdFinEquiv (u, i)) k * z k) ∧
        x = finiteScale K • fun k ↦ (z k : ℚ) := by
  rw [show finiteRationalBasis (K := K) L e =
      scaledRationalBasis (finiteIntegralFormMatrix L) (finiteModuli e)
        (finiteModuli_pos e) (finiteScale K) by rfl]
  rw [exists_scaledRationalBasis_repr_iff]
  constructor
  · rintro ⟨z, hz, hx⟩
    refine ⟨z, fun u i ↦ ?_, hx⟩
    simpa [finiteModuli] using hz (finProdFinEquiv (u, i))
  · rintro ⟨z, hz, hx⟩
    refine ⟨z, fun j ↦ ?_, hx⟩
    let ui := finProdFinEquiv.symm j
    have hj := hz ui.1 ui.2
    have hback : finProdFinEquiv (ui.1, ui.2) = j := by
      simpa [ui] using finProdFinEquiv.apply_symm_apply j
    rw [hback] at hj
    simpa [finiteModuli, ui] using hj

/-- The real-valued `p`-adic norm at one of the two finite places. -/
def finitePadicNorm (u : Fin 2) (q : ℚ) : ℝ :=
  Fin.cases (padicNorm 2 q : ℝ) (fun _ ↦ (padicNorm 3 q : ℝ)) u

@[simp] theorem finitePadicNorm_zero (q : ℚ) :
    finitePadicNorm 0 q = (padicNorm 2 q : ℝ) := rfl

@[simp] theorem finitePadicNorm_one (q : ℚ) :
    finitePadicNorm 1 q = (padicNorm 3 q : ℝ) := rfl

/-- A scaled integral vector has denominator dividing `6ᵏ`, hence lies in
`ℤ[1/6]ⁿ`. -/
theorem finiteScale_smul_intCast_inZOneSix {n K : ℕ} (z : Fin n → ℤ) :
    AdelicMinkowski.InZOneSix
      (finiteScale K • fun k ↦ (z k : ℚ)) := by
  refine ⟨K, z, fun i ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, finiteScale,
    AdelicMinkowski.denominator]
  push_cast
  field_simp

/-- Every rational point in the integer span of the rounded basis is
`{2,3}`-integral and satisfies all prescribed finite-place row bounds. -/
theorem finiteRationalBasis_span_admissible {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (r : Fin 2 → Fin n → ℝ) (e : Fin 2 → Fin n → ℕ)
    (he : ∀ u i,
      finiteScaleNorm L K u *
          (finitePrime u : ℝ) ^ (-(e u i : ℤ)) ≤ r u i)
    (x : Fin n → ℚ)
    (hx : ∃ c : Fin n → ℤ,
      x = ∑ i, (c i : ℚ) • finiteRationalBasis (K := K) L e i) :
    AdelicMinkowski.InZOneSix x ∧
      ∀ u i, finitePadicNorm u (L (finitePlace u) i x) ≤ r u i := by
  obtain ⟨z, hz, rfl⟩ :=
    (exists_finiteRationalBasis_repr_iff L e x).1 hx
  refine ⟨finiteScale_smul_intCast_inZOneSix z, fun u i ↦ ?_⟩
  fin_cases u
  · change (padicNorm 2
      (L Place23.two i (finiteScale K • fun k ↦ (z k : ℚ))) : ℝ) ≤ r 0 i
    let j : Fin (2 * n) := finProdFinEquiv (0, i)
    apply padicNorm_scaled_intCast_le_of_dvd
      (f := L Place23.two i) (A := finiteIntegralFormMatrix L j)
      (D := finiteFormDenominator L) (hD := finiteFormDenominator_ne_zero L)
      (s := finiteScale K) (z := z) (e := e 0 i)
    · simpa [j] using finiteIntegralFormMatrix_clear L j z
    · simpa [j] using hz 0 i
    · have h := he (0 : Fin 2) i
      change (padicNorm 2
          (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ) *
        (2 : ℝ) ^ (-(e 0 i : ℤ)) ≤ r 0 i at h
      simpa [Rat.cast_zpow] using h
  · change (padicNorm 3
      (L Place23.three i (finiteScale K • fun k ↦ (z k : ℚ))) : ℝ) ≤ r 1 i
    let j : Fin (2 * n) := finProdFinEquiv (1, i)
    apply padicNorm_scaled_intCast_le_of_dvd
      (f := L Place23.three i) (A := finiteIntegralFormMatrix L j)
      (D := finiteFormDenominator L) (hD := finiteFormDenominator_ne_zero L)
      (s := finiteScale K) (z := z) (e := e 1 i)
    · simpa [j] using finiteIntegralFormMatrix_clear L j z
    · simpa [j] using hz 1 i
    · have h := he (1 : Fin 2) i
      change (padicNorm 3
          (finiteScale K / (finiteFormDenominator L : ℚ)) : ℝ) *
        (3 : ℝ) ^ (-(e 1 i : ℤ)) ≤ r 1 i at h
      simpa [Rat.cast_zpow] using h

/-- The determinant bound for the concrete finite-place basis before the
rounding-product estimate is inserted. -/
theorem abs_det_finiteRealBasis_le {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (e : Fin 2 → Fin n → ℕ) :
    |(Pi.basisFun ℝ (Fin n)).det (finiteRealBasis (K := K) L e)| ≤
      |(finiteScale K : ℝ)| ^ n *
        (∏ j, finiteModuli e j : ℕ) := by
  exact abs_det_scaledRealBasis_le (finiteIntegralFormMatrix L)
    (finiteModuli e) (finiteModuli_pos e) (finiteScale K)
    (finiteScale_ne_zero K)

/-- The factor-`p` rounding inequality bounds the corresponding congruence
modulus by `p` times the scale norm divided by the original radius. -/
theorem finitePrimePow_lt_scaleNorm_div_radius {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (r : Fin 2 → Fin n → ℝ) (hr : ∀ u i, 0 < r u i)
    (e : Fin 2 → Fin n → ℕ)
    (he : ∀ u i, r u i <
      (finitePrime u : ℝ) * finiteScaleNorm L K u *
        (finitePrime u : ℝ) ^ (-(e u i : ℤ)))
    (u : Fin 2) (i : Fin n) :
    (finitePrime u : ℝ) ^ e u i <
      (finitePrime u : ℝ) * finiteScaleNorm L K u / r u i := by
  have hp : 0 < (finitePrime u : ℝ) := by exact_mod_cast finitePrime_pos u
  have hq : 0 < (finitePrime u : ℝ) ^ e u i := pow_pos hp _
  apply (lt_div_iff₀ (hr u i)).2
  calc
    (finitePrime u : ℝ) ^ e u i * r u i <
        (finitePrime u : ℝ) ^ e u i *
          ((finitePrime u : ℝ) * finiteScaleNorm L K u *
            (finitePrime u : ℝ) ^ (-(e u i : ℤ))) :=
      mul_lt_mul_of_pos_left (he u i) hq
    _ = (finitePrime u : ℝ) * finiteScaleNorm L K u := by
      rw [zpow_neg, zpow_natCast]
      field_simp

/-- Reindexing the product of row moduli by the pair `(p,i)`. -/
theorem cast_prod_finiteModuli_eq {n : ℕ}
    (e : Fin 2 → Fin n → ℕ) :
    ((∏ j, finiteModuli e j : ℕ) : ℝ) =
      ∏ u, ∏ i, (finitePrime u : ℝ) ^ e u i := by
  push_cast
  rw [← finProdFinEquiv.prod_comp (fun j ↦ (finiteModuli e j : ℝ))]
  rw [Fintype.prod_prod_type]
  simp [finiteModuli]

/-- Product form of the pointwise modulus bound. -/
theorem cast_prod_finiteModuli_le {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (r : Fin 2 → Fin n → ℝ) (hr : ∀ u i, 0 < r u i)
    (e : Fin 2 → Fin n → ℕ)
    (he : ∀ u i, r u i <
      (finitePrime u : ℝ) * finiteScaleNorm L K u *
        (finitePrime u : ℝ) ^ (-(e u i : ℤ))) :
    ((∏ j, finiteModuli e j : ℕ) : ℝ) ≤
      ∏ u, ∏ i,
        ((finitePrime u : ℝ) * finiteScaleNorm L K u / r u i) := by
  rw [cast_prod_finiteModuli_eq]
  apply Finset.prod_le_prod
  · intro u _
    exact Finset.prod_nonneg fun i _ ↦ (pow_pos (by exact_mod_cast finitePrime_pos u) _).le
  · intro u _
    apply Finset.prod_le_prod
    · intro i _
      exact (pow_pos (by exact_mod_cast finitePrime_pos u) _).le
    · intro i _
      exact (finitePrimePow_lt_scaleNorm_div_radius L r hr e he u i).le

/-- The real scale and its two finite norms satisfy the restricted product
formula, with the fixed coefficient-denominator contribution left over. -/
theorem finiteScale_productFormula {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    |(finiteScale K : ℝ)| *
        ((2 : ℝ) * finiteScaleNorm L K 0) *
        ((3 : ℝ) * finiteScaleNorm L K 1) =
      6 / ((padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ) *
        (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ)) := by
  rw [finiteScaleNorm_zero, finiteScaleNorm_one]
  have hd2 : (padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ) ≠ 0 := by
    have hDq : (finiteFormDenominator L : ℚ) ≠ 0 := by
      exact_mod_cast finiteFormDenominator_ne_zero L
    exact_mod_cast padicNorm.nonzero (p := 2) hDq
  have hd3 : (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ) ≠ 0 := by
    have hDq : (finiteFormDenominator L : ℚ) ≠ 0 := by
      exact_mod_cast finiteFormDenominator_ne_zero L
    exact_mod_cast padicNorm.nonzero (p := 3) hDq
  have hs : |(finiteScale K : ℝ)| = (6 : ℝ) ^ (-K : ℤ) := by
    simp [finiteScale, zpow_neg, zpow_natCast]
  rw [hs]
  rw [zpow_neg, zpow_natCast]
  field_simp
  ring_nf
  rw [← mul_pow]
  norm_num

/-- The fixed finite-place covolume constant.  It depends only on the
rational coefficient matrix and the dimension, not on the radii. -/
noncomputable def finiteLatticeConstant {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) : ℝ :=
  (6 / ((padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ) *
    (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ))) ^ n

theorem finiteLatticeConstant_pos {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n) :
    0 < finiteLatticeConstant L := by
  unfold finiteLatticeConstant
  have hDq : (finiteFormDenominator L : ℚ) ≠ 0 := by
    exact_mod_cast finiteFormDenominator_ne_zero L
  have h2q := padicNorm.nonzero (p := 2) hDq
  have h3q := padicNorm.nonzero (p := 3) hDq
  have h2 : 0 < (padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm h2q)
  have h3 : 0 < (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm h3q)
  positivity

/-- Terminal covolume estimate: the concrete full real basis has determinant
at most a fixed constant times the reciprocal product of all `2n` finite
radii. -/
theorem abs_det_finiteRealBasis_le_constant_mul_inv_radii {n K : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (r : Fin 2 → Fin n → ℝ) (hr : ∀ u i, 0 < r u i)
    (e : Fin 2 → Fin n → ℕ)
    (he : ∀ u i, r u i <
      (finitePrime u : ℝ) * finiteScaleNorm L K u *
        (finitePrime u : ℝ) ^ (-(e u i : ℤ))) :
    |(Pi.basisFun ℝ (Fin n)).det (finiteRealBasis (K := K) L e)| ≤
      finiteLatticeConstant L * (∏ u, ∏ i, r u i)⁻¹ := by
  calc
    |(Pi.basisFun ℝ (Fin n)).det (finiteRealBasis (K := K) L e)| ≤
        |(finiteScale K : ℝ)| ^ n *
          ((∏ j, finiteModuli e j : ℕ) : ℝ) :=
      abs_det_finiteRealBasis_le L e
    _ ≤ |(finiteScale K : ℝ)| ^ n *
        (∏ u, ∏ i,
          ((finitePrime u : ℝ) * finiteScaleNorm L K u / r u i)) :=
      mul_le_mul_of_nonneg_left (cast_prod_finiteModuli_le L r hr e he)
        (pow_nonneg (abs_nonneg _) _)
    _ = finiteLatticeConstant L * (∏ u, ∏ i, r u i)⁻¹ := by
      simp_rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_pow]
      rw [← mul_div_assoc]
      rw [← mul_pow]
      have hscale := finiteScale_productFormula (K := K) L
      simp only [Fin.prod_univ_two, finitePrime_zero, finitePrime_one] at hscale ⊢
      have hscale' : |(finiteScale K : ℝ)| *
          ((2 : ℝ) * finiteScaleNorm L K 0 *
            ((3 : ℝ) * finiteScaleNorm L K 1)) =
          6 / ((padicNorm 2 (finiteFormDenominator L : ℚ) : ℝ) *
            (padicNorm 3 (finiteFormDenominator L : ℚ) : ℝ)) := by
        rw [← mul_assoc]
        exact hscale
      norm_num at hscale' ⊢
      rw [hscale']
      simp [finiteLatticeConstant, div_eq_mul_inv]

/-- Choose the common `S`-integral scale and all rounded prime-power
moduli at once.  The resulting basis is finite-place admissible and has the
terminal determinant bound needed by the Archimedean argument. -/
theorem exists_finiteLatticeBasis {n : ℕ}
    (L : Place23 → Fin n → RatLinearForm n)
    (r : Fin 2 → Fin n → ℝ) (hr : ∀ u i, 0 < r u i) :
    ∃ (K : ℕ) (e : Fin 2 → Fin n → ℕ),
      (∀ u i, finiteScaleNorm L K u *
          (finitePrime u : ℝ) ^ (-(e u i : ℤ)) ≤ r u i) ∧
      (∀ u i, r u i <
          (finitePrime u : ℝ) * finiteScaleNorm L K u *
            (finitePrime u : ℝ) ^ (-(e u i : ℤ))) ∧
      |(Pi.basisFun ℝ (Fin n)).det (finiteRealBasis (K := K) L e)| ≤
        finiteLatticeConstant L * (∏ u, ∏ i, r u i)⁻¹ := by
  obtain ⟨K, hK⟩ := exists_finiteScale_normalizes L r hr
  obtain ⟨e, he⟩ := exists_finiteRoundingExponents L r hr hK
  exact ⟨K, e, fun u i ↦ (he u i).1, fun u i ↦ (he u i).2,
    abs_det_finiteRealBasis_le_constant_mul_inv_radii
      L r hr e (fun u i ↦ (he u i).2)⟩

end FinitePlaceLattice

end Erdos407.PadicSubspace
