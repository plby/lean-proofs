import Wikipedia.HopfProblem.CuspExponentials
import Wikipedia.HopfProblem.MatrixPeriodTori
import Wikipedia.HopfProblem.ToricReduction

/-!
# The logarithmic period lattice of a cusp fibre

For `t = exp(2πis)`, the period matrix is `Z(s) = s B₀ + C(t)`.
The small-drift estimate proves that its imaginary part is invertible.
Exponentiating a `Z(s)`-period gives exactly the constructed twisted action.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace

def logarithmicPeriod (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := s • B₀.map (Int.castRingHom ℂ) + C (exponential s)

theorem logarithmicPeriod_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    (logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i =
      s * (cuspVector v i : ℂ) + (C (exponential s) *ᵥ (fun j => (v j : ℂ))) i := by
  fin_cases i <;>
    simp [logarithmicPeriod, B₀, cuspVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, smul_eq_mul] <;> ring

theorem imaginary_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (ht : Real.log ‖exponential s‖ ≠ 0) (v : Fin 2 → ℝ) :
    Real.log ‖exponential s‖ • displacement C (exponential s) v =
      (-2 * Real.pi) • ((logarithmicPeriod C s).map Complex.im *ᵥ v) := by
  change Real.log ‖exponential s‖ • (realCuspVector v +
    (Real.log ‖exponential s‖)⁻¹ • (driftMatrix C (exponential s) *ᵥ v)) = _
  rw [smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul]
  ext i
  fin_cases i <;>
    simp [logarithmicPeriod, B₀, realCuspVector, driftMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, smul_eq_mul, log_norm_exponential, Complex.mul_im] <;> ring

theorem logarithmicPeriod_nondegenerate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (ht : Real.log ‖exponential s‖ < 0)
    (hR : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4) :
    Function.Bijective ((logarithmicPeriod C s).map Complex.im).mulVecLin := by
  have hinj : Function.Injective ((logarithmicPeriod C s).map Complex.im).mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have he := imaginary_displacement C s ht.ne v
    change (logarithmicPeriod C s).map Complex.im *ᵥ v = 0 at hv
    rw [hv, smul_zero] at he
    have hd : displacement C (exponential s) v = 0 := (smul_eq_zero.mp he).resolve_left ht.ne
    exact (displacement_bijective C ht hR).injective (hd.trans (map_zero _).symm)
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

def periodData (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (ht : Real.log ‖exponential s‖ < 0)
    (hR : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4) :
    FullPeriodMatrix := ⟨logarithmicPeriod C s, logarithmicPeriod_nondegenerate C s ht hR⟩

theorem exponential_logarithmicPeriod (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    exponential ((logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i) =
      (exponentialMultiplier C v (exponential s) i : ℂ) * exponential s ^ cuspVector v i := by
  rw [logarithmicPeriod_apply, exponential_add]
  have he : exponential (s * (cuspVector v i : ℂ)) = exponential s ^ cuspVector v i := by
    unfold exponential
    rw [show (2 * Real.pi * Complex.I : ℂ) * (s * (cuspVector v i : ℂ)) =
      (cuspVector v i : ℂ) * (2 * Real.pi * Complex.I * s) by ring, Complex.exp_int_mul]
  rw [he]
  exact mul_comm _ _

theorem twistedTranslate_exponentialPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (v : Fin 2 → ℤ) (z : ComplexPlane₂) :
    twistedTranslate C v (exponentialPoint (exponential s) z) =
      exponentialPoint (exponential s)
        (z + logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) := by
  have ht := exponential_ne_zero s
  have hx := exponentialPoint_mem ht z
  have hx' : twistedTranslate C v (exponentialPoint (exponential s) z) ∈ openTorus := by
    simpa only [mem_openTorus_iff, time_twistedTranslate] using hx
  apply torusCoordinates_injective hx' (exponentialPoint_mem ht _)
  have hi (i : Fin 2) :
      torusCoordinates (twistedTranslate C v (exponentialPoint (exponential s) z)) i.castSucc =
        exponential (z i + (logarithmicPeriod C s *ᵥ (fun j => (v j : ℂ))) i) := by
    rw [torusCoordinates_twistedTranslate_apply C v hx, time_exponentialPoint ht]
    have hz : torusCoordinates (exponentialPoint (exponential s) z) i.castSucc =
        exponential (z i) := by
      rw [torusCoordinates_exponentialPoint ht]
      fin_cases i <;> rfl
    rw [hz, exponential_add, exponential_logarithmicPeriod]
    ring
  rw [torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i
  · exact hi 0
  · exact hi 1
  · simp [exponentialCoordinates, time_twistedTranslate, time_exponentialPoint ht]

end Wikipedia.HopfProblem.CuspUniformization
