/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondUpper
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiUpper

/-!
# A coarse upper half of Minkowski's second theorem

This file uses nested dyadic coordinate dilations and Minkowski's first
theorem.  The dyadic rounding and the use of a closed convex body cost a
factor `4` per direction, giving the unconditional dimension-only bound
`8^n`.
-/

namespace Erdos186.CFP.Bilu.MinkowskiSecond

open scoped BigOperators Pointwise
open Erdos186.CFP.Bilu.Mahler
open Module Set MeasureTheory

namespace Direct

open Erdos186.CFP.Bilu.MinkowskiUpper

/-- Pull a coordinate seminorm back by division by its diagonal scales. -/
noncomputable def diagonalPullbackSeminorm {n : ℕ}
    (q : Seminorm ℝ (Fin n → ℝ)) (d : Fin n → ℝ) :
    Seminorm ℝ (Fin n → ℝ) :=
  q.comp (Matrix.toLin' (Matrix.diagonal fun i ↦ (d i)⁻¹))

@[simp]
theorem diagonalPullbackSeminorm_apply {n : ℕ}
    (q : Seminorm ℝ (Fin n → ℝ)) (d : Fin n → ℝ) (z : Fin n → ℝ) :
    diagonalPullbackSeminorm q d z = q (fun i ↦ (d i)⁻¹ * z i) := by
  classical
  rw [diagonalPullbackSeminorm, Seminorm.comp_apply, Matrix.toLin'_apply]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

/-- Highest nonzero coordinate of a nonzero finite vector. -/
theorem exists_last_ne_zero {n : ℕ} (z : Fin n → ℤ) (hz : z ≠ 0) :
    ∃ i, z i ≠ 0 ∧ ∀ j, i < j → z j = 0 := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i ↦ z i ≠ 0
  have hs : s.Nonempty := by
    by_contra hsempty
    have hall : ∀ i, z i = 0 := by
      intro i
      have hi : i ∉ s := by
        intro his
        exact hsempty ⟨i, his⟩
      simpa [s] using hi
    exact hz (funext hall)
  let i : Fin n := s.max' hs
  refine ⟨i, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (s.max'_mem hs)).2
  · intro j hij
    by_contra hj
    have hjs : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    exact (not_le_of_gt hij) (s.le_max' j hjs)

/-- Nested integral ratios make the diagonally pulled-back unit ball
lattice-point-free when strict short vectors vanish in the corresponding
coordinate flag. -/
theorem diagonalPullback_no_nonzero_integralPoint {n : ℕ}
    (q : Seminorm ℝ (Fin n → ℝ)) (lambda d : Fin n → ℝ)
    (hdpos : ∀ i, 0 < d i) (hdlt : ∀ i, d i < lambda i)
    (hdiv : ∀ {i j}, i ≤ j →
      ∃ a : ℕ, 0 < a ∧ (a : ℝ) * d i = d j)
    (hshort : ∀ (i : Fin n) (w : IntegralPoint n),
      q (integralEmbed w) < lambda i → ∀ j, i ≤ j → w j = 0) :
    ∀ z : IntegralPoint n, z ≠ 0 →
      ¬ diagonalPullbackSeminorm q d (integralEmbed z) ≤ 1 := by
  classical
  intro z hz hzd
  obtain ⟨i, hzi, hlast⟩ := exists_last_ne_zero z hz
  let a : Fin n → ℕ := fun j ↦ if h : j ≤ i then (hdiv h).choose else 0
  have ha_pos {j : Fin n} (hji : j ≤ i) : 0 < a j := by
    simp only [a, dif_pos hji]
    exact (hdiv hji).choose_spec.1
  have ha_scale {j : Fin n} (hji : j ≤ i) :
      (a j : ℝ) * d j = d i := by
    simp only [a, dif_pos hji]
    exact (hdiv hji).choose_spec.2
  let w : IntegralPoint n := fun j ↦ if j ≤ i then (a j : ℤ) * z j else 0
  have hwreal : integralEmbed w =
      d i • (fun j ↦ (d j)⁻¹ * (z j : ℝ)) := by
    ext j
    by_cases hji : j ≤ i
    · have hdj : d j ≠ 0 := (hdpos j).ne'
      simp only [w, hji, ↓reduceIte, integralEmbed, Pi.smul_apply, smul_eq_mul]
      rw [Int.cast_mul, Int.cast_natCast, ← ha_scale hji]
      field_simp
    · have hij : i < j := lt_of_not_ge hji
      have hzj : z j = 0 := hlast j hij
      simp [w, hji, hzj, integralEmbed]
  have hwi : w i ≠ 0 := by
    have hai : (a i : ℤ) ≠ 0 := by exact_mod_cast (ha_pos le_rfl).ne'
    simpa [w] using mul_ne_zero hai hzi
  have hwq : q (integralEmbed w) < lambda i := by
    rw [hwreal, map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos (hdpos i), ← diagonalPullbackSeminorm_apply]
    exact (mul_le_mul_of_nonneg_left hzd (hdpos i).le).trans_lt (by
      simpa using hdlt i)
  exact hwi (hshort i w hwq i le_rfl)

/-- Pulling a definite seminorm back by an integral basis matrix preserves
definiteness. -/
theorem isDefinite_inBasisSeminorm {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    IsDefinite (inBasisSeminorm p b) := by
  intro x hx
  have hAx : (integralBasisMatrix b).mulVec x = 0 := hp _ (by simpa using hx)
  exact (Matrix.mulVec_injective_of_isUnit (integralBasisMatrix_isUnit b))
    (by simpa using hAx)

/-- Pullback by a positive diagonal matrix preserves definiteness. -/
theorem isDefinite_diagonalPullbackSeminorm {n : ℕ}
    (q : Seminorm ℝ (Fin n → ℝ)) (hq : IsDefinite q)
    (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    IsDefinite (diagonalPullbackSeminorm q d) := by
  intro x hx
  have hdiag : (fun i ↦ (d i)⁻¹ * x i) = 0 := hq _ (by simpa using hx)
  funext i
  have hi := congrFun hdiag i
  simp only [Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (inv_ne_zero (hd i).ne')

/-- The unit ball of the diagonal pullback is the diagonal image of the
original unit ball. -/
theorem unitBall_diagonalPullback_eq_image {n : ℕ}
    (q : Seminorm ℝ (Fin n → ℝ)) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) :
    unitBall (diagonalPullbackSeminorm q d) =
      Matrix.toLin' (Matrix.diagonal d) '' unitBall q := by
  classical
  ext z
  constructor
  · intro hz
    refine ⟨fun i ↦ (d i)⁻¹ * z i, ?_, ?_⟩
    · simpa [unitBall] using hz
    · ext i
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.diagonal,
        (hd i).ne']
  · rintro ⟨x, hx, rfl⟩
    change diagonalPullbackSeminorm q d
      ((Matrix.diagonal d).mulVec x) ≤ 1
    rw [diagonalPullbackSeminorm_apply]
    have heq : (fun i ↦ (d i)⁻¹ * ((Matrix.diagonal d).mulVec x) i) = x := by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal, (hd i).ne']
    rw [heq]
    exact hx

/-- Exact volume change under a positive diagonal pullback. -/
theorem volume_unitBall_diagonalPullback {n : ℕ}
    (q : Seminorm ℝ (Fin n → ℝ)) (d : Fin n → ℝ)
    (hd : ∀ i, 0 < d i) :
    volume (unitBall (diagonalPullbackSeminorm q d)) =
      ENNReal.ofReal (∏ i, d i) * volume (unitBall q) := by
  classical
  rw [unitBall_diagonalPullback_eq_image q d hd,
    MeasureTheory.Measure.addHaar_image_linearMap]
  congr 1
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  change ENNReal.ofReal |(LinearMap.toMatrix'
    (Matrix.toLin' (Matrix.diagonal d))).det| = _
  rw [LinearMap.toMatrix'_toLin', Matrix.det_diagonal,
    abs_of_pos (Finset.prod_pos fun i _ ↦ hd i)]

/-- Membership in the standard real lattice means that all coordinates are
integer, hence comes from an `IntegralPoint`. -/
theorem exists_integralPoint_eq_of_mem_standardRealLattice {n : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ standardRealLattice n) :
    ∃ z : IntegralPoint n, integralEmbed z = x := by
  classical
  have hc := ((Pi.basisFun ℝ (Fin n)).mem_span_iff_repr_mem ℤ x).mp hx
  choose z hz using hc
  refine ⟨z, ?_⟩
  funext i
  change (z i : ℝ) = x i
  simpa using hz i

/-- First Minkowski for the standard lattice, contraposed: a definite
seminorm ball without a nonzero integral point has volume at most `2^n`. -/
theorem volume_unitBall_le_two_pow_of_no_nonzero_integralPoint {n : ℕ}
    [Nonempty (Fin n)] (r : Seminorm ℝ (Fin n → ℝ)) (hr : IsDefinite r)
    (hno : ∀ z : IntegralPoint n, z ≠ 0 → ¬ r (integralEmbed z) ≤ 1) :
    volume (unitBall r) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
  classical
  by_contra hle
  have hbig : ENNReal.ofReal ((2 : ℝ) ^ n) < volume (unitBall r) :=
    lt_of_not_ge hle
  let F : Set (Fin n → ℝ) := ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n))
  have hfund : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup F volume := by
    simpa [F] using
      (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume)
  have : Countable
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n))))
    infer_instance
  have hsymm : ∀ x ∈ unitBall r, -x ∈ unitBall r := by
    intro x hx
    simpa [unitBall] using hx
  have hcpt : IsCompact (unitBall r) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_unitBall r, isBounded_unitBall r hr⟩
  have hM : volume F * 2 ^ finrank ℝ (Fin n → ℝ) ≤ volume (unitBall r) := by
    have hF : volume F = 1 := by
      rw [show F = ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)) from rfl,
        ZSpan.volume_fundamentalDomain]
      have hmatrix : Matrix.of (Pi.basisFun ℝ (Fin n)) = 1 := by
        ext i j
        simp [Matrix.of_apply, Pi.basisFun_apply, Pi.single_apply,
          Matrix.one_apply, eq_comm]
      rw [hmatrix, Matrix.det_one, abs_one, ENNReal.ofReal_one]
    rw [hF, one_mul, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    simpa [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)] using hbig.le
  obtain ⟨x, hxne, hxball⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      hfund hsymm (convex_unitBall r) hcpt hM
  have hxL : (x : Fin n → ℝ) ∈ standardRealLattice n := by
    exact x.property
  obtain ⟨z, hz⟩ := exists_integralPoint_eq_of_mem_standardRealLattice hxL
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hxne
    apply Subtype.ext
    change (x : Fin n → ℝ) = 0
    rw [← hz, hzero]
    exact integralEmbed_zero
  apply hno z hz0
  simpa [unitBall, hz] using hxball

/-- An integral change of basis does not change the volume of a seminorm
unit ball. -/
theorem volume_unitBall_inBasisSeminorm {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ))
    (b : Basis (Fin n) ℤ (IntegralPoint n)) :
    volume (unitBall (inBasisSeminorm p b)) = volume (unitBall p) := by
  classical
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    Matrix.toLin' (integralBasisMatrix b)
  have hAinj : Function.Injective A := by
    exact Matrix.mulVec_injective_of_isUnit (integralBasisMatrix_isUnit b)
  have hAsurj : Function.Surjective A := A.surjective_of_injective hAinj
  have himage : A '' unitBall (inBasisSeminorm p b) = unitBall p := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hAsurj y
      exact ⟨x, hy, rfl⟩
  have hvol := MeasureTheory.Measure.addHaar_image_linearMap volume A
    (unitBall (inBasisSeminorm p b))
  rw [himage] at hvol
  have hdet : |LinearMap.det A| = 1 := by
    rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
    change |(LinearMap.toMatrix' (Matrix.toLin'
      (integralBasisMatrix b))).det| = 1
    simpa using abs_det_integralBasisMatrix b
  rw [hdet, ENNReal.ofReal_one, one_mul] at hvol
  exact hvol.symm

end Direct

open Direct
open Erdos186.CFP.Bilu.MinkowskiUpper

/-- A dimension-only upper half of Minkowski's second theorem.  The direct
dyadic argument loses a factor four on each successive minimum, so first
Minkowski gives the explicit constant `8^n`. -/
theorem minkowskiSecond_upper_eight_pow_ennreal {n : ℕ} [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ENNReal.ofReal (∏ i, successiveMinimum p i) * volume (unitBall p) ≤
      ENNReal.ofReal ((8 : ℝ) ^ n) := by
  classical
  obtain ⟨b, hshort⟩ := exists_inBasisSeminorm_strictShort_coordinate_zero p hp
  let q : Seminorm ℝ (Fin n → ℝ) := inBasisSeminorm p b
  let d : Fin n → ℝ := coarseScale p
  let r : Seminorm ℝ (Fin n → ℝ) := diagonalPullbackSeminorm q d
  have hdpos : ∀ i, 0 < d i := fun i ↦ coarseScale_pos p hp i
  have hno : ∀ z : IntegralPoint n, z ≠ 0 → ¬ r (integralEmbed z) ≤ 1 := by
    exact diagonalPullback_no_nonzero_integralPoint q
      (fun i ↦ successiveMinimum p i) d hdpos
      (fun i ↦ coarseScale_lt_successiveMinimum p hp i)
      (fun {i j} hij ↦ by
        simpa [d] using exists_nat_mul_coarseScale_eq p hp hij) hshort
  have hqdef : IsDefinite q := isDefinite_inBasisSeminorm p hp b
  have hrdef : IsDefinite r := isDefinite_diagonalPullbackSeminorm q hqdef d hdpos
  have hvolr : volume (unitBall r) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) :=
    volume_unitBall_le_two_pow_of_no_nonzero_integralPoint r hrdef hno
  have hdvol : ENNReal.ofReal (∏ i, d i) * volume (unitBall p) ≤
      ENNReal.ofReal ((2 : ℝ) ^ n) := by
    rw [show r = diagonalPullbackSeminorm q d from rfl,
      volume_unitBall_diagonalPullback q d hdpos,
      show q = inBasisSeminorm p b from rfl,
      volume_unitBall_inBasisSeminorm p b] at hvolr
    exact hvolr
  have hprod : (∏ i, successiveMinimum p i) ≤
      (4 : ℝ) ^ n * ∏ i, d i := by
    calc
      (∏ i, successiveMinimum p i) ≤ ∏ i, (4 : ℝ) * d i :=
        Finset.prod_le_prod
          (fun i _ ↦ (successiveMinimum_pos p hp i).le)
          (fun i _ ↦ successiveMinimum_le_four_mul_coarseScale p hp i)
      _ = (4 : ℝ) ^ n * ∏ i, d i := by
        rw [Finset.prod_mul_distrib]
        simp
  have hofprod : ENNReal.ofReal (∏ i, successiveMinimum p i) ≤
      ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (∏ i, d i) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ n)]
    exact ENNReal.ofReal_le_ofReal hprod
  calc
    ENNReal.ofReal (∏ i, successiveMinimum p i) * volume (unitBall p) ≤
        (ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (∏ i, d i)) *
          volume (unitBall p) := by gcongr
    _ = ENNReal.ofReal ((4 : ℝ) ^ n) *
          (ENNReal.ofReal (∏ i, d i) * volume (unitBall p)) := by ac_rfl
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal ((2 : ℝ) ^ n) :=
      by gcongr
    _ = ENNReal.ofReal ((8 : ℝ) ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ n)]
      congr 1
      rw [← mul_pow]
      norm_num

/-- Real-valued form of the coarse upper bound, convenient for subsequent
convex-geometric estimates. -/
theorem minkowskiSecond_upper_eight_pow_real {n : ℕ} [Nonempty (Fin n)]
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    (∏ i, successiveMinimum p i) * volume.real (unitBall p) ≤ (8 : ℝ) ^ n := by
  have h := minkowskiSecond_upper_eight_pow_ennreal p hp
  have hreal := ENNReal.toReal_mono (by simp) h
  have hprod : 0 ≤ ∏ i, successiveMinimum p i :=
    Finset.prod_nonneg fun i _ ↦ (successiveMinimum_pos p hp i).le
  simpa [measureReal_def, ENNReal.toReal_ofReal hprod,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (8 : ℝ) ^ n)] using hreal

end Erdos186.CFP.Bilu.MinkowskiSecond
