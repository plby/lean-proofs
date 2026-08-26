import ErdosProblems.Erdos1148.IntegralFormEmbedding

/-! # The standard integral lattice in a rational two-dimensional vector space -/

namespace Erdos1148.DukeArithmetic

def intVectorCast : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℚ) where
  toFun v i := v i
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

def standardRationalLattice : Submodule ℤ (Fin 2 → ℚ) := intVectorCast.range

lemma mem_standardRationalLattice_iff (v : Fin 2 → ℚ) :
    v ∈ standardRationalLattice ↔ ∃ u : Fin 2 → ℤ, intVectorCast u = v := Iff.rfl

lemma intVectorCast_mulVec (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    intVectorCast (M.mulVec v) = (M.map (Int.castRingHom ℚ)).mulVec (intVectorCast v) := by
  ext i
  fin_cases i <;>
    simp [intVectorCast, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply]

theorem matrix_preserves_standardRationalLattice_iff (M : Matrix (Fin 2) (Fin 2) ℚ) :
    (∀ v ∈ standardRationalLattice, M.mulVec v ∈ standardRationalLattice) ↔
      M ∈ integralRationalMatrices := by
  classical
  constructor
  · intro h
    have hcol (j : Fin 2) : ∃ u : Fin 2 → ℤ,
        intVectorCast u = M.mulVec (Pi.single j 1) := by
      apply h
      refine ⟨Pi.single j 1, ?_⟩
      ext i
      by_cases hij : i = j <;> simp [intVectorCast, hij]
    choose u hu using hcol
    rw [mem_integralRationalMatrices_iff]
    refine ⟨fun i j => u j i, ?_⟩
    ext i j
    change (u j i : ℚ) = M i j
    have h := congrFun (hu j) i
    simpa [intVectorCast, Matrix.mulVec_single, Matrix.col] using h
  · rintro ⟨N, hN⟩ v ⟨u, rfl⟩
    refine ⟨N.mulVec u, ?_⟩
    rw [intVectorCast_mulVec]
    rw [show N.map (Int.castRingHom ℚ) = M from hN]

end Erdos1148.DukeArithmetic
