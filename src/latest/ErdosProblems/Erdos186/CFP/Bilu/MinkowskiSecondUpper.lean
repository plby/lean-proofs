/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondLower
import ErdosProblems.Erdos186.CFP.Bilu.SaturatedFlag
import Mathlib.Analysis.BoxIntegral.UnitPartition
import Mathlib.Data.Int.Log
import Mathlib.MeasureTheory.Group.GeometryOfNumbers

/-!
# Upper-volume infrastructure for Minkowski's second theorem

The sharp upper half of Minkowski's second theorem is not currently in
Mathlib.  This file develops the two ingredients needed for a direct
finite-dissection proof: strict sublevel vectors are contained in the
appropriate successive-minimum flag, and dyadic rounding produces nested
integer dilation factors while losing less than a factor two per direction.
-/

namespace Erdos186.CFP.Bilu.MinkowskiSecond

open scoped BigOperators Pointwise
open Erdos186.CFP.Bilu.Mahler
open Module Set

/-- The prefix of an independent family, indexed by the natural value of a
finite index. -/
def prefixFamily {n : ℕ} (x : Fin n → IntegralPoint n) (i : Fin n) :
    Fin i.val → (Fin n → ℝ) :=
  fun j ↦ integralEmbed (x (Fin.castLE i.isLt.le j))

theorem linearIndependent_prefixFamily {n : ℕ}
    (x : Fin n → IntegralPoint n)
    (hx : LinearIndependent ℝ (fun i ↦ integralEmbed (x i))) (i : Fin n) :
    LinearIndependent ℝ (prefixFamily x i) := by
  exact hx.comp (Fin.castLE i.isLt.le) (Fin.castLE_injective i.isLt.le)

theorem span_range_prefixFamily {n : ℕ}
    (x : Fin n → IntegralPoint n) (i : Fin n) :
    Submodule.span ℝ (Set.range (prefixFamily x i)) =
      Submodule.span ℝ ((fun j ↦ integralEmbed (x j)) '' Set.Iio i) := by
  congr 1
  ext y
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.castLE i.isLt.le j, j.isLt, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j.val, hj⟩, rfl⟩

/-- Every lattice vector strictly shorter than the `i`th successive
minimum lies in the real span of the preceding vectors of any compatible
successive-minimum family.

The plateau case is essential: when `lambda_(i-1) = lambda_i`, it reduces
to the induction hypothesis.  When the inequality is strict, adjoining a
new strict-short vector to the preceding family would contradict the
definition of `lambda_i`. -/
theorem strictShort_mem_span_preceding {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (x : Fin n → IntegralPoint n)
    (hxli : LinearIndependent ℝ (fun i ↦ integralEmbed (x i)))
    (hx : ∀ i, p (integralEmbed (x i)) ≤ successiveMinimum p i) :
    ∀ (i : Fin n) (y : IntegralPoint n),
      p (integralEmbed y) < successiveMinimum p i →
      integralEmbed y ∈
        Submodule.span ℝ ((fun j ↦ integralEmbed (x j)) '' Set.Iio i) := by
  cases n with
  | zero => exact fun i ↦ Fin.elim0 i
  | succ n =>
    intro i
    induction i using Fin.induction with
    | zero =>
        intro y hy
        have hy0 : y = 0 := by
          by_contra hne
          have hyli : LinearIndependent ℝ (fun _ : Fin 1 ↦ integralEmbed y) := by
            rw [linearIndependent_unique_iff]
            exact fun hzero ↦ hne (integralEmbed_injective (hzero.trans integralEmbed_zero.symm))
          have hadm : AdmitsIndependent p 1 (p (integralEmbed y)) :=
            ⟨fun _ ↦ y, hyli, fun _ ↦ le_rfl⟩
          exact (not_lt_of_ge (successiveMinimum_le_of_admits hadm)) hy
        subst y
        simp
    | succ i ih =>
        intro y hy
        by_cases heq : successiveMinimum p i.castSucc = successiveMinimum p i.succ
        · have hymem := ih y (by simpa [heq] using hy)
          apply Submodule.span_mono _ hymem
          rintro _ ⟨j, hj, rfl⟩
          exact ⟨j, hj.trans (show i.castSucc < i.succ from Fin.castSucc_lt_succ), rfl⟩
        · have hlt : successiveMinimum p i.castSucc < successiveMinimum p i.succ :=
            lt_of_le_of_ne
              (successiveMinimum_mono p
                (show i.castSucc ≤ i.succ from Fin.castSucc_lt_succ.le)) heq
          by_contra hymem
          have hprefixLI := linearIndependent_prefixFamily x hxli i.succ
          have hynot : integralEmbed y ∉
              Submodule.span ℝ (Set.range (prefixFamily x i.succ)) := by
            rwa [span_range_prefixFamily]
          have hallLI := hprefixLI.finSnoc hynot
          let r : ℝ := max (successiveMinimum p i.castSucc) (p (integralEmbed y))
          have hrlt : r < successiveMinimum p i.succ := max_lt hlt hy
          have hadm : AdmitsIndependent p (i.succ.val + 1) r := by
            let v : Fin (i.succ.val + 1) → IntegralPoint (n + 1) :=
              Fin.snoc
                (fun j : Fin i.succ.val ↦ x (Fin.castLE i.succ.isLt.le j)) y
            refine ⟨v, ?_, ?_⟩
            · have hvfun : (fun j ↦ integralEmbed (v j)) =
                  Fin.snoc (prefixFamily x i.succ) (integralEmbed y) := by
                funext j
                refine Fin.lastCases ?_ (fun k ↦ ?_) j
                · simp [v]
                · simp [v, prefixFamily]
              rw [hvfun]
              exact hallLI
            · intro j
              refine Fin.lastCases ?_ (fun k ↦ ?_) j
              · simpa [v, r] using
                  le_max_right (successiveMinimum p i.castSucc) (p (integralEmbed y))
              · have hk : Fin.castLE i.succ.isLt.le k ≤ i.castSucc := by
                  exact Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp k.isLt)
                rw [show v k.castSucc = x (Fin.castLE i.succ.isLt.le k) by
                  simp [v]]
                exact (hx _).trans <|
                  (successiveMinimum_mono p hk).trans (le_max_left _ _)
          exact (not_lt_of_ge (successiveMinimum_le_of_admits hadm)) hrlt

/-- There is a unimodular integral coordinate basis adapted to all strict
successive-minimum sublevels: a vector strictly shorter than `lambda_i`
has zero basis coordinates from `i` onwards. -/
theorem exists_prefixBasis_strictShort_repr_zero {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      ∀ (i : Fin n) (y : IntegralPoint n),
        p (integralEmbed y) < successiveMinimum p i →
          ∀ j, i ≤ j → b.repr y j = 0 := by
  obtain ⟨x, hxli, hx⟩ :=
    exists_independent_integralPoint_le_successiveMinimum p hp
  have hxli' : LinearIndependent ℝ
      (fun i ↦ Erdos186.CFP.Bilu.SaturatedFlag.realEmbed n (x i)) := by
    have hfun :
        (fun i ↦ Erdos186.CFP.Bilu.SaturatedFlag.realEmbed n (x i)) =
          (fun i ↦ integralEmbed (x i)) := by
      funext i
      ext j
      rfl
    rw [hfun]
    exact hxli
  obtain ⟨b, hbprefix, _hbtri, _hbpivot⟩ :=
    Erdos186.CFP.Bilu.SaturatedFlag.exists_prefix_adapted_basis_realPrefixLattice
      x hxli'
  refine ⟨b, ?_⟩
  intro i y hy j hij
  have hyspan := strictShort_mem_span_preceding p x hxli hx i y hy
  by_cases hi : i.val = 0
  · have hIio : Set.Iio i = ∅ := by
      ext k
      simp only [Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
      exact fun hki ↦ by omega
    have hyzero : integralEmbed y = 0 := by
      rw [hIio] at hyspan
      simpa using hyspan
    have : y = 0 := integralEmbed_injective (hyzero.trans integralEmbed_zero.symm)
    simp [this]
  · let ip : Fin n := ⟨i.val - 1, by omega⟩
    have hset : Set.Iic ip = Set.Iio i := by
      ext k
      simp only [Set.mem_Iic, Set.mem_Iio, Fin.le_iff_val_le_val,
        Fin.lt_iff_val_lt_val, ip]
      omega
    have hymem : y ∈ Erdos186.CFP.Bilu.SaturatedFlag.realPrefixLattice x ip := by
      rw [Erdos186.CFP.Bilu.SaturatedFlag.mem_realPrefixLattice]
      change integralEmbed y ∈
        Submodule.span ℝ ((fun z ↦ integralEmbed z) '' (x '' Set.Iic ip))
      simpa [Set.image_image, Function.comp_def, hset] using hyspan
    have hymem' : y ∈ Submodule.span ℤ (b '' Set.Iic ip) := by
      rwa [← hbprefix ip]
    apply Erdos186.CFP.Bilu.SaturatedFlag.repr_eq_zero_of_mem_span_image
      b (Set.Iic ip) hymem'
    intro hj
    have hjle : j ≤ ip := Set.mem_Iic.mp hj
    have hjval : j.val ≤ i.val - 1 := hjle
    omega

/-! ## Dyadic scales -/

/-- The largest integral power of two not exceeding a positive real number. -/
noncomputable def dyadicFloor (r : ℝ) : ℝ :=
  (2 : ℝ) ^ (Int.log 2 r)

theorem dyadicFloor_pos {r : ℝ} (hr : 0 < r) : 0 < dyadicFloor r := by
  exact zpow_pos (by norm_num) _

theorem dyadicFloor_le {r : ℝ} (hr : 0 < r) : dyadicFloor r ≤ r := by
  exact Int.zpow_log_le_self (R := ℝ) (by norm_num : 1 < (2 : ℕ)) hr

theorem half_lt_dyadicFloor {r : ℝ} (hr : 0 < r) : r / 2 < dyadicFloor r := by
  have h := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2)
    (by norm_num : 1 < (2 : ℕ)) r
  calc
    r / 2 < ((2 : ℝ) ^ (Int.log 2 r + 1)) / 2 :=
      div_lt_div_of_pos_right h (by norm_num)
    _ = dyadicFloor r := by
      rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp [dyadicFloor]

theorem dyadicFloor_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    dyadicFloor a ≤ dyadicFloor b := by
  apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact Int.log_mono_right ha hab

/-- Ratios of ordered dyadic floors are nonnegative integral powers of two. -/
theorem exists_nat_mul_dyadicFloor_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) * dyadicFloor a = dyadicFloor b := by
  let za : ℤ := Int.log 2 a
  let zb : ℤ := Int.log 2 b
  have hz : za ≤ zb := Int.log_mono_right ha hab
  let k : ℕ := (zb - za).toNat
  have hk : (k : ℤ) = zb - za := by
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hz)]
  refine ⟨2 ^ k, pow_pos (by norm_num : 0 < (2 : ℕ)) k, ?_⟩
  rw [Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast]
  simp only [dyadicFloor]
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), hk]
  congr 1
  omega

/-! ## Unimodular coordinates -/

/-- The real matrix whose columns are an integral basis. -/
noncomputable def integralBasisMatrix {n : ℕ} (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  (integralColumns fun i ↦ b i).map (Int.castRingHom ℝ)

@[simp]
theorem integralBasisMatrix_apply {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (r c : Fin n) :
    integralBasisMatrix b r c = (b c r : ℝ) := rfl

/-- Multiplication by the basis matrix sends the cast of integral basis
coordinates back to the embedded integral vector. -/
theorem mulVec_integralBasisMatrix_repr {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (z : IntegralPoint n) :
    (integralBasisMatrix b).mulVec (fun i ↦ (b.repr z i : ℝ)) =
      integralEmbed z := by
  classical
  ext r
  have hr := congrFun (b.sum_repr z) r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hr
  change (∑ i, (b i r : ℝ) * (b.repr z i : ℝ)) = (z r : ℝ)
  exact_mod_cast (by simpa [mul_comm] using hr)

/-- An integral basis matrix is unimodular, hence its real determinant has
absolute value one. -/
theorem abs_det_integralBasisMatrix {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    |(integralBasisMatrix b).det| = 1 := by
  classical
  let A : Matrix (Fin n) (Fin n) ℤ := integralColumns fun i ↦ b i
  let R : Matrix (Fin n) (Fin n) ℤ :=
    fun row col ↦ b.repr (standardIntegralPoint col) row
  have hAR : A * R = 1 := by
    ext row col
    have hcoord := congrFun (b.sum_repr (standardIntegralPoint col)) row
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
    change (∑ k, b k row * b.repr (standardIntegralPoint col) k) =
      (1 : Matrix (Fin n) (Fin n) ℤ) row col
    calc
      (∑ k, b k row * b.repr (standardIntegralPoint col) k) =
          standardIntegralPoint col row := by simpa [mul_comm] using hcoord
      _ = (1 : Matrix (Fin n) (Fin n) ℤ) row col := by
        by_cases h : row = col
        · subst col
          simp [standardIntegralPoint]
        · have h' : col ≠ row := Ne.symm h
          simp [standardIntegralPoint, h, h']
  have hdetmul : A.det * R.det = 1 := by
    rw [← Matrix.det_mul, hAR, Matrix.det_one]
  have hdetunit : IsUnit A.det := by
    refine ⟨⟨A.det, R.det, hdetmul, ?_⟩, rfl⟩
    simpa [mul_comm] using hdetmul
  have habsZ : |A.det| = 1 := by
    rcases Int.isUnit_iff.mp hdetunit with h | h
    · simp [h]
    · simp [h]
  have hcast : (integralBasisMatrix b).det = (A.det : ℝ) := by
    simpa [integralBasisMatrix, A] using (Int.cast_det (R := ℝ) A).symm
  rw [hcast, ← Int.cast_abs, habsZ]
  norm_num

theorem integralBasisMatrix_isUnit {n : ℕ}
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    IsUnit (integralBasisMatrix b) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  exact isUnit_iff_ne_zero.mpr fun hzero ↦ by
    have := abs_det_integralBasisMatrix b
    rw [hzero, abs_zero] at this
    norm_num at this

/-- Pull a seminorm back to the real coordinates of an integral basis. -/
noncomputable def inBasisSeminorm {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    Seminorm ℝ (Fin n → ℝ) :=
  p.comp (Matrix.toLin' (integralBasisMatrix b))

@[simp]
theorem inBasisSeminorm_apply {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (c : Fin n → ℝ) :
    inBasisSeminorm p b c = p ((integralBasisMatrix b).mulVec c) := by
  rfl

@[simp]
theorem inBasisSeminorm_integral_repr {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (z : IntegralPoint n) :
    inBasisSeminorm p b (fun i ↦ (b.repr z i : ℝ)) = p (integralEmbed z) := by
  rw [inBasisSeminorm_apply, mulVec_integralBasisMatrix_repr]

theorem inBasisSeminorm_integral_coords {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) (c : IntegralPoint n) :
    inBasisSeminorm p b (integralEmbed c) =
      p (integralEmbed (b.equivFun.symm c)) := by
  have h := inBasisSeminorm_integral_repr p b (b.equivFun.symm c)
  have hcoords :
      (fun i ↦ (b.repr (b.equivFun.symm c) i : ℝ)) = integralEmbed c := by
    funext i
    have hi := congrFun (b.equivFun.apply_symm_apply c) i
    have hiz : b.repr (b.equivFun.symm c) i = c i := by
      simpa [Basis.equivFun_apply] using hi
    change ((b.repr (b.equivFun.symm c) i : ℤ) : ℝ) = (c i : ℝ)
    exact_mod_cast hiz
  rw [← hcoords]
  exact h

/-- Coordinate form of `exists_prefixBasis_strictShort_repr_zero`. -/
theorem exists_inBasisSeminorm_strictShort_coordinate_zero {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ b : Basis (Fin n) ℤ (IntegralPoint n),
      ∀ (i : Fin n) (c : IntegralPoint n),
        inBasisSeminorm p b (integralEmbed c) < successiveMinimum p i →
          ∀ j, i ≤ j → c j = 0 := by
  obtain ⟨b, hb⟩ := exists_prefixBasis_strictShort_repr_zero p hp
  refine ⟨b, ?_⟩
  intro i c hc j hij
  let y : IntegralPoint n := b.equivFun.symm c
  have hpy : p (integralEmbed y) < successiveMinimum p i := by
    rw [inBasisSeminorm_integral_coords] at hc
    exact hc
  have hz := hb i y hpy j hij
  have hj : b.repr y j = c j := by
    have hj' := congrFun (b.equivFun.apply_symm_apply c) j
    exact hj'
  rwa [hj] at hz

/-! ## Dyadic diagonal compression -/

/-- A strictly smaller dyadic scale. -/
noncomputable def coarseScale {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) : ℝ :=
  dyadicFloor (successiveMinimum p i) / 2

theorem coarseScale_pos {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ))
    (hp : IsDefinite p) (i : Fin n) : 0 < coarseScale p i := by
  exact div_pos (dyadicFloor_pos (successiveMinimum_pos p hp i)) (by norm_num)

theorem coarseScale_lt_successiveMinimum {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    coarseScale p i < successiveMinimum p i := by
  have hpos := dyadicFloor_pos (successiveMinimum_pos p hp i)
  have hle := dyadicFloor_le (successiveMinimum_pos p hp i)
  dsimp [coarseScale]
  nlinarith

theorem successiveMinimum_le_four_mul_coarseScale {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    successiveMinimum p i ≤ 4 * coarseScale p i := by
  have h := half_lt_dyadicFloor (successiveMinimum_pos p hp i)
  dsimp [coarseScale]
  linarith

theorem exists_nat_mul_coarseScale_eq {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    {i j : Fin n} (hij : i ≤ j) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) * coarseScale p i = coarseScale p j := by
  obtain ⟨q, hq, hscale⟩ := exists_nat_mul_dyadicFloor_eq
    (successiveMinimum_pos p hp i) (successiveMinimum_mono p hij)
  refine ⟨q, hq, ?_⟩
  dsimp [coarseScale]
  linarith

end Erdos186.CFP.Bilu.MinkowskiSecond
