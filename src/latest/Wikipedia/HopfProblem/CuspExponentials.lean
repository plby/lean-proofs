import Wikipedia.HopfProblem.CuspQuotient
import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Exponential coordinates on the nonzero cusp fibres

The normalized exponential has precisely the integer periods. Its two
coordinates parametrize each nonzero fibre of the toric space, before
taking the twisted lattice quotient.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace

def exponential (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

theorem exponential_factor_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    Complex.I_ne_zero

@[simp] theorem exponential_ne_zero (z : ℂ) : exponential z ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem exponential_zero : exponential 0 = 1 := by simp [exponential]

theorem exponential_add (z w : ℂ) : exponential (z + w) = exponential z * exponential w := by
  simp only [exponential, mul_add, Complex.exp_add]

@[simp] theorem exponential_int (n : ℤ) : exponential n = 1 := by
  simpa only [exponential, mul_comm] using Complex.exp_int_mul_two_pi_mul_I n

theorem exponential_eq_iff (z w : ℂ) :
    exponential z = exponential w ↔ ∃ n : ℤ, z = w + n := by
  rw [exponential, exponential, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, mul_left_cancel₀ exponential_factor_ne_zero ?_⟩
    calc
      (2 * Real.pi * Complex.I : ℂ) * z = _ := hn
      _ = (2 * Real.pi * Complex.I : ℂ) * (w + n) := by ring
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

def logarithm (t : ℂ) : ℂ := Complex.log t / (2 * Real.pi * Complex.I)

theorem exponential_logarithm {t : ℂ} (ht : t ≠ 0) : exponential (logarithm t) = t := by
  rw [exponential, logarithm, mul_div_cancel₀ _ exponential_factor_ne_zero]
  exact Complex.exp_log ht

theorem exponential_holomorphic : ContDiff ℂ ω exponential :=
  (contDiff_const.mul contDiff_id).cexp

theorem log_norm_exponential (s : ℂ) : Real.log ‖exponential s‖ = -2 * Real.pi * s.im := by
  simp [exponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

def torusPoint (w : CoordinateSpace 3) : Space :=
  inclusion referenceTriangle (monomial referenceTriangle.dual w)

theorem torusPoint_mem {w : CoordinateSpace 3} (hw : w ∈ torus) : torusPoint w ∈ openTorus :=
  inclusion_torus_subset _ ⟨_, monomial_mapsTo_torus _ hw, rfl⟩

theorem torusCoordinates_torusPoint {w : CoordinateSpace 3} (hw : w ∈ torus) :
    torusCoordinates (torusPoint w) = w := by
  rw [torusPoint, torusCoordinates_inclusion _ (monomial_mapsTo_torus _ hw),
    monomial_mul_on_torus _ _ hw, Triangle.rays_dual, monomial_one]

theorem torusPoint_torusCoordinates {x : Space} (hx : x ∈ openTorus) :
    torusPoint (torusCoordinates x) = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [torusCoordinates_inclusion _ hz, torusPoint,
    monomial_mul_on_torus _ _ hz, Triangle.dual_rays, monomial_one]

theorem torusCoordinates_injective : Set.InjOn torusCoordinates openTorus := by
  intro x hx y hy he
  rw [← torusPoint_torusCoordinates hx, ← torusPoint_torusCoordinates hy, he]

def exponentialCoordinates (t : ℂ) (z : ComplexPlane₂) : CoordinateSpace 3 :=
  ![exponential (z 0), exponential (z 1), t]

theorem exponentialCoordinates_mem {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    exponentialCoordinates t z ∈ torus := by
  intro i
  fin_cases i
  · exact exponential_ne_zero _
  · exact exponential_ne_zero _
  · exact ht

theorem exponentialCoordinates_holomorphic (t : ℂ) : ContDiff ℂ ω (exponentialCoordinates t) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact exponential_holomorphic.comp (contDiff_apply ℂ ℂ 0)
  · exact exponential_holomorphic.comp (contDiff_apply ℂ ℂ 1)
  · exact contDiff_const

def exponentialPoint (t : ℂ) : ComplexPlane₂ → Space := torusPoint ∘ exponentialCoordinates t

theorem exponentialPoint_mem {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    exponentialPoint t z ∈ openTorus := torusPoint_mem (exponentialCoordinates_mem ht z)

theorem torusCoordinates_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    torusCoordinates (exponentialPoint t z) = exponentialCoordinates t z :=
  torusCoordinates_torusPoint (exponentialCoordinates_mem ht z)

theorem time_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    time (exponentialPoint t z) = t := by
  simpa [exponentialCoordinates] using congrFun (torusCoordinates_exponentialPoint ht z) 2

theorem exponentialPoint_holomorphic {t : ℂ} (ht : t ≠ 0) :
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ (CoordinateSpace 3))
      ω (exponentialPoint t) := by
  apply (inclusion_holomorphic referenceTriangle).comp
  apply ContDiff.contMDiff
  apply contDiffOn_univ.mp
  exact (monomial_contDiffOn referenceTriangle.dual ω).comp
    (exponentialCoordinates_holomorphic t).contDiffOn
    (fun z _ => torus_subset_domain _ (exponentialCoordinates_mem ht z))

theorem exponentialPoint_surjective_fibre {t : ℂ} (ht : t ≠ 0) {x : Space}
    (hx : time x = t) : ∃ z : ComplexPlane₂, exponentialPoint t z = x := by
  have hxT : x ∈ openTorus := (mem_openTorus_iff _).mpr (hx ▸ ht)
  let z : ComplexPlane₂ := fun i => logarithm (torusCoordinates x i.castSucc)
  refine ⟨z, torusCoordinates_injective (exponentialPoint_mem ht z) hxT ?_⟩
  rw [torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i
  · exact exponential_logarithm (torusCoordinates_nonzero hxT 0)
  · exact exponential_logarithm (torusCoordinates_nonzero hxT 1)
  · simpa [exponentialCoordinates] using hx.symm

theorem exponentialPoint_eq_iff {t : ℂ} (ht : t ≠ 0) (z w : ComplexPlane₂) :
    exponentialPoint t z = exponentialPoint t w ↔
      ∃ m : Fin 2 → ℤ, z = w + (fun i => (m i : ℂ)) := by
  constructor
  · intro he
    have hec := congrArg torusCoordinates he
    rw [torusCoordinates_exponentialPoint ht, torusCoordinates_exponentialPoint ht] at hec
    have hi (i : Fin 2) : ∃ n : ℤ, z i = w i + n := by
      apply (exponential_eq_iff _ _).mp
      have hi := congrFun hec i.castSucc
      fin_cases i <;> exact hi
    choose m hm using hi
    exact ⟨m, funext hm⟩
  · rintro ⟨m, rfl⟩
    apply torusCoordinates_injective (exponentialPoint_mem ht _) (exponentialPoint_mem ht _)
    rw [torusCoordinates_exponentialPoint ht, torusCoordinates_exponentialPoint ht]
    ext i
    fin_cases i
    · exact (exponential_eq_iff _ _).mpr ⟨m 0, rfl⟩
    · exact (exponential_eq_iff _ _).mpr ⟨m 1, rfl⟩
    · rfl

end Wikipedia.HopfProblem.CuspUniformization
