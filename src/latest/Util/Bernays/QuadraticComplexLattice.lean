import Util.Bernays.QuadraticOrder
import Util.Bernays.LatticePointAsymptotic

/-!
# The complex lattice of a negative-discriminant quadratic order

We use twice the usual complex embedding, so that the norm-square identity
has no denominators. Its covolume need not be explicitly evaluated.
-/

open MeasureTheory Module Submodule Metric Set
open scoped Classical

namespace Bernays

noncomputable def quadraticComplexMap (d b : ℤ) : QuadraticAlgebra ℤ d b →ₗ[ℤ] ℂ where
  toFun z := ⟨2 * z.re + b * z.im, Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ) * z.im⟩
  map_add' z w := by apply Complex.ext <;> simp <;> ring
  map_smul' n z := by apply Complex.ext <;> simp <;> ring

theorem quadraticComplexMap_norm_sq {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (z : QuadraticAlgebra ℤ d b) : ‖quadraticComplexMap d b z‖ ^ 2 = 4 * (z.norm : ℝ) := by
  have hD' : (0 : ℝ) < -(b ^ 2 + 4 * d : ℤ) := by exact_mod_cast neg_pos.mpr hD
  rw [Complex.sq_norm, Complex.normSq_apply]
  change (2 * (z.re : ℝ) + (b : ℝ) * z.im) * (2 * z.re + b * z.im) +
    (Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ) * z.im) *
      (Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ) * z.im) = _
  have hi : (4 : ℝ) * z.norm = (2 * (z.re : ℝ) + (b : ℝ) * z.im) ^ 2 -
      (b ^ 2 + 4 * d : ℤ) * (z.im : ℝ) ^ 2 := by
    exact_mod_cast four_mul_quadraticNorm d b z
  rw [hi]
  nlinarith [Real.sq_sqrt hD'.le]

theorem quadraticComplexMap_injective {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    Function.Injective (quadraticComplexMap d b) := by
  suffices hzero : ∀ z, quadraticComplexMap d b z = 0 → z = 0 by
    intro z w hzw
    have hsub : quadraticComplexMap d b (z - w) = 0 := by rw [map_sub, hzw, sub_self]
    exact sub_eq_zero.mp (hzero _ hsub)
  intro z hz
  have hn := quadraticComplexMap_norm_sq hD z
  rw [hz, norm_zero, zero_pow (by decide), zero_eq_mul] at hn
  have hzNorm : z.norm = 0 := by exact_mod_cast hn.resolve_left (by norm_num)
  exact (quadraticNorm_eq_zero_iff hD z).mp hzNorm

noncomputable def quadraticIdealLattice (d b : ℤ) (I : Ideal (QuadraticAlgebra ℤ d b)) :
    Submodule ℤ ℂ := (I.restrictScalars ℤ).map (quadraticComplexMap d b)

theorem mem_quadraticIdealLattice (d b : ℤ) (I : Ideal (QuadraticAlgebra ℤ d b)) (w : ℂ) :
    w ∈ quadraticIdealLattice d b I ↔ ∃ z ∈ I, quadraticComplexMap d b z = w := Iff.rfl

theorem quadraticIdealLattice_discrete {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) : DiscreteTopology (quadraticIdealLattice d b I) := by
  apply discreteTopology_iff_isOpen_singleton_zero.mpr
  refine ⟨ball 0 1, isOpen_ball, ?_⟩
  ext w
  simp only [Set.mem_preimage, mem_ball, dist_zero_right, Set.mem_singleton_iff]
  constructor
  · intro hw
    obtain ⟨z, hz, hzw⟩ := (mem_quadraticIdealLattice d b I w).mp w.2
    have heq : z = 0 := by
      by_contra hzero
      have hn : 0 < z.norm := lt_of_le_of_ne (quadraticNorm_nonneg hD z)
        (Ne.symm ((quadraticNorm_eq_zero_iff hD z).not.mpr hzero))
      have hnR : (1 : ℝ) ≤ z.norm := by exact_mod_cast hn
      have hnorm := quadraticComplexMap_norm_sq hD z
      rw [hzw] at hnorm
      nlinarith [norm_nonneg (w : ℂ)]
    apply Subtype.ext
    change (w : ℂ) = 0
    simpa only [heq, map_zero] using hzw.symm
  · rintro rfl
    simp

theorem quadraticIdealLattice_full {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) :
    letI := quadraticIdealLattice_discrete hD I
    IsZLattice ℝ (quadraticIdealLattice d b I) := by
  let := quadraticOrderIsDomain hD
  let := quadraticIdealLattice_discrete hD I
  let O := QuadraticAlgebra ℤ d b
  let : Finite (O ⧸ I) := Ring.HasFiniteQuotients.finiteQuotient hI
  let m := I.cardQuot
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.card_pos (α := O ⧸ I))
  let s := Real.sqrt (-(b ^ 2 + 4 * d : ℤ) : ℝ)
  have hs : 0 < s := Real.sqrt_pos.mpr (by exact_mod_cast neg_pos.mpr hD)
  have hmI : (m : O) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  have hzI : (⟨0, (m : ℤ)⟩ : O) ∈ I := by
    have h := I.mul_mem_left (⟨0, 1⟩ : O) hmI
    have heq : (⟨0, 1⟩ : O) * (m : O) = ⟨0, (m : ℤ)⟩ := by
      apply QuadraticAlgebra.ext <;>
        simp only [O, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
          QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, zero_mul,
          mul_zero, zero_add, add_zero, one_mul]
    rwa [heq] at h
  let L := quadraticIdealLattice d b I
  have hv₀ : quadraticComplexMap d b (m : O) ∈ Submodule.span ℝ (L : Set ℂ) :=
    Submodule.subset_span ((mem_quadraticIdealLattice d b I _).mpr ⟨_, hmI, rfl⟩)
  have hv₁ : quadraticComplexMap d b (⟨0, (m : ℤ)⟩ : O) ∈ Submodule.span ℝ (L : Set ℂ) :=
    Submodule.subset_span ((mem_quadraticIdealLattice d b I _).mpr ⟨_, hzI, rfl⟩)
  refine ⟨eq_top_iff.mpr ?_⟩
  intro w _
  have hmem := (Submodule.span ℝ (L : Set ℂ)).add_mem
    ((Submodule.span ℝ (L : Set ℂ)).smul_mem ((w.re - (b : ℝ) * w.im / s) / (2 * m)) hv₀)
    ((Submodule.span ℝ (L : Set ℂ)).smul_mem (w.im / (s * m)) hv₁)
  have heq : ((w.re - (b : ℝ) * w.im / s) / (2 * m)) • quadraticComplexMap d b (m : O) +
      (w.im / (s * m)) • quadraticComplexMap d b (⟨0, (m : ℤ)⟩ : O) = w := by
    apply Complex.ext
    · simp only [O, Complex.add_re, Complex.smul_re, quadraticComplexMap, LinearMap.coe_mk,
        AddHom.coe_mk, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        Int.cast_natCast, Int.cast_zero, smul_eq_mul]
      change ((w.re - (b : ℝ) * w.im / s) / (2 * m)) * (2 * m + (b : ℝ) * 0) +
        (w.im / (s * m)) * (2 * 0 + (b : ℝ) * m) = w.re
      field_simp
      ring
    · simp only [O, Complex.add_im, Complex.smul_im, quadraticComplexMap, LinearMap.coe_mk,
        AddHom.coe_mk, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        Int.cast_natCast, Int.cast_zero, smul_eq_mul]
      change ((w.re - (b : ℝ) * w.im / s) / (2 * m)) * (s * 0) +
        (w.im / (s * m)) * (s * m) = w.im
      simp only [mul_zero, zero_add, div_mul_cancel₀ _ (mul_ne_zero hs.ne' hm.ne')]
  exact heq ▸ hmem

end Bernays
