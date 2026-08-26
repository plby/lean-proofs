/- Adapted from the checked repository proof in Erdos1148/PadicLatticeRepresentatives.lean. -/
import ErdosProblems.Erdos941.PairLocal.PadicPrimitiveMatrix
import ErdosProblems.Erdos941.PairLocal.PadicTriangularMatrices
import ErdosProblems.Erdos941.PairLocal.NormalizedIntegralAction
import ErdosProblems.Erdos941.PairLocal.ProjectiveAction

/-!
# Enumerating p-adic coefficient lattices

Every coefficient lattice has a triangular representative, with a natural
depth, one residue modulo `p^n`, and one of two coordinate charts.
-/

namespace Erdos941.PairLocal

lemma map_neighborMatrix {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (π z : R) : (neighborMatrix π z).map φ = neighborMatrix (φ π) (φ z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neighborMatrix]

lemma map_swapMatrix {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    (swapMatrix : Matrix (Fin 2) (Fin 2) R).map φ = (swapMatrix : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMatrix]

noncomputable def padicChartMatrix (p : ℕ) [Fact p.Prime] (n : ℕ) (z : ZMod (p ^ n))
    (flipped : Bool) : Matrix (Fin 2) (Fin 2) (Padic p) :=
  if flipped then neighborMatrix ((p : Padic p) ^ n) (z.val : Padic p) * swapMatrix
  else neighborMatrix ((p : Padic p) ^ n) (z.val : Padic p)

lemma det_padicChartMatrix_ne_zero (p : ℕ) [Fact p.Prime] (n : ℕ)
    (z : ZMod (p ^ n)) (flipped : Bool) : (padicChartMatrix p n z flipped).det ≠ 0 := by
  have hp : (p : Padic p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  cases flipped <;> simp [padicChartMatrix, Matrix.det_mul, det_neighborMatrix, det_swapMatrix, hp]

noncomputable def padicChartIsometry (p : ℕ) [Fact p.Prime] (n : ℕ)
    (z : ZMod (p ^ n)) (flipped : Bool) : specialDiscrGroup (Padic p) :=
  normalizedTransformIsometry (padicChartMatrix p n z flipped)
    (det_padicChartMatrix_ne_zero p n z flipped)

def padicChartLattice (p : ℕ) [Fact p.Prime] (n : ℕ) (z : ZMod (p ^ n))
    (flipped : Bool) : Set (Padic p × Padic p × Padic p) :=
  coefficientLattice (algebraMap (PadicInt p) (Padic p)) (padicChartIsometry p n z flipped)⁻¹

lemma unit_matrix_map_det_ne_zero {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (U : Matrix (Fin 2) (Fin 2) R) (hU : IsUnit U.det) :
    (U.map φ).det ≠ 0 := by
  change (φ.mapMatrix U).det ≠ 0
  rw [← φ.map_det]
  exact (hU.map φ).ne_zero

lemma scaled_matrix_det_ne_zero {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (c : K) (hc : c ≠ 0) :
    (c • M).det ≠ 0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hM

lemma normalizedTransformIsometry_eq_of_scaled {K : Type*} [Field K]
    (M A : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (hA : A.det ≠ 0)
    (c : K) (hc : c ≠ 0) (heq : A = c • M) :
    normalizedTransformIsometry A hA = normalizedTransformIsometry M hM := by
  subst A
  exact normalizedTransformIsometry_smul M hM c hc _

lemma integral_triangular_chart {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (U A : Matrix (Fin 2) (Fin 2) R) (π z : R)
    (heq : U * A = neighborMatrix π z ∨ U * A * swapMatrix = neighborMatrix π z) :
    U.map φ * A.map φ = neighborMatrix (φ π) (φ z) ∨
      U.map φ * A.map φ = neighborMatrix (φ π) (φ z) * swapMatrix := by
  rcases heq with heq | heq
  · left
    change φ.mapMatrix U * φ.mapMatrix A = _
    rw [← map_mul, heq]
    exact map_neighborMatrix φ π z
  · right
    have hUA : U * A = neighborMatrix π z * swapMatrix := by
      rw [← heq, Matrix.mul_assoc, swapMatrix_mul_self, Matrix.mul_one]
    change φ.mapMatrix U * φ.mapMatrix A = _
    rw [← map_mul, hUA, map_mul]
    change (neighborMatrix π z).map φ * (swapMatrix : Matrix (Fin 2) (Fin 2) R).map φ = _
    rw [map_neighborMatrix, map_swapMatrix]

/-- Every p-adic coefficient lattice occurs in the two explicit triangular charts. -/
theorem exists_padicChartLattice (p : ℕ) [Fact p.Prime]
    (g : specialDiscrGroup (Padic p)) :
    ∃ (n : ℕ) (z : ZMod (p ^ n)) (flipped : Bool),
      coefficientLattice (algebraMap (PadicInt p) (Padic p)) g =
        padicChartLattice p n z flipped := by
  let φ := algebraMap (PadicInt p) (Padic p)
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective (PadicInt p) (Padic p)
  obtain ⟨M, hM, hg⟩ := exists_normalizedTransformIsometry g⁻¹
  obtain ⟨c, A, hc, hAM, i, j, hij⟩ := exists_padic_primitive_matrix p M hM
  have hAK : (A.map φ).det ≠ 0 := by
    rw [hAM]
    exact scaled_matrix_det_ne_zero M hM c hc
  have hA : A.det ≠ 0 := by
    intro hzero
    apply hAK
    change (φ.mapMatrix A).det = 0
    rw [← φ.map_det, hzero, map_zero]
  have hnorm : normalizedTransformIsometry (A.map φ) hAK = g⁻¹ :=
    (normalizedTransformIsometry_eq_of_scaled M (A.map φ) hM hAK c hc hAM).trans hg
  have hlattice : coefficientLattice φ g =
      coefficientLattice φ (normalizedTransformIsometry (A.map φ) hAK)⁻¹ := by
    rw [hnorm, inv_inv]
  have ha : ∃ i j, IsUnit (A i j) := ⟨i, j, hij ▸ isUnit_one⟩
  obtain ⟨U, n, z, hU, heq⟩ := padic_triangular_representatives p A hA ha
  have hUK := unit_matrix_map_det_ne_zero φ U hU
  have hprod : (U.map φ * A.map φ).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hUK hAK
  have hrow := image_lattice_normalized_left_unit φ hφ U hU hUK (A.map φ) hAK
  have hcharts := integral_triangular_chart φ U A ((p : PadicInt p) ^ n) (z.val : PadicInt p) heq
  simp only [map_pow, map_natCast] at hcharts
  rcases hcharts with hchart | hchart
  · refine ⟨n, z, false, ?_⟩
    rw [hlattice, ← hrow]
    have hisom : normalizedTransformIsometry (U.map φ * A.map φ) hprod =
        padicChartIsometry p n z false := by
      unfold padicChartIsometry padicChartMatrix
      congr 1
    exact congrArg (fun k : specialDiscrGroup (Padic p) => coefficientLattice φ k⁻¹) hisom
  · refine ⟨n, z, true, ?_⟩
    rw [hlattice, ← hrow]
    have hisom : normalizedTransformIsometry (U.map φ * A.map φ) hprod =
        padicChartIsometry p n z true := by
      unfold padicChartIsometry padicChartMatrix
      congr 1
    exact congrArg (fun k : specialDiscrGroup (Padic p) => coefficientLattice φ k⁻¹) hisom

end Erdos941.PairLocal
