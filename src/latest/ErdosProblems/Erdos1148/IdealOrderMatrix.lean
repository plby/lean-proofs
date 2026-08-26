import ErdosProblems.Erdos1148.FormOfOrderMatrix
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # The integral matrix of the quadratic order acting on an ideal -/

namespace Erdos1148.DukeArithmetic

noncomputable def quadraticOrderGeneratorElem (d : ℤ) : quadraticOrder d :=
  ⟨quadraticOrderGenerator d, quadraticOrderGenerator_mem d⟩

noncomputable def quadraticOrderRoot (d : ℤ) : quadraticOrder d :=
  (2 : ℤ) • quadraticOrderGeneratorElem d - d • (1 : quadraticOrder d)

lemma quadraticOrderRoot_val (d : ℤ) :
    (quadraticOrderRoot d : QuadraticDiscrAlgebra d) = ⟨0, 1⟩ := by
  change (2 : ℤ) • quadraticOrderGenerator d - d • (1 : QuadraticDiscrAlgebra d) = _
  rw [zsmul_eq_mul, zsmul_eq_mul]
  ext <;> norm_num [quadraticOrderGenerator, QuadraticAlgebra.re_ofNat,
    QuadraticAlgebra.im_ofNat] <;> ring

lemma quadraticOrderRoot_mul_self (d : ℤ) :
    quadraticOrderRoot d * quadraticOrderRoot d = d • (1 : quadraticOrder d) := by
  apply Subtype.ext
  change (quadraticOrderRoot d : QuadraticDiscrAlgebra d) *
    (quadraticOrderRoot d : QuadraticDiscrAlgebra d) = d • (1 : QuadraticDiscrAlgebra d)
  rw [quadraticOrderRoot_val]
  ext <;> simp [zsmul_eq_mul]

noncomputable def idealOrderRepresentation {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) :
    quadraticOrder d →ₐ[ℤ] Matrix (Fin 2) (Fin 2) ℤ :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.comp (Algebra.lsmul ℤ ℤ I)

noncomputable def idealOrderMatrix {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) : Matrix (Fin 2) (Fin 2) ℤ :=
  idealOrderRepresentation I b (quadraticOrderGeneratorElem d)

lemma idealOrderRepresentation_apply {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) (w : quadraticOrder d) (i j : Fin 2) :
    idealOrderRepresentation I b w i j = b.repr (w • b j) i := by
  simp [idealOrderRepresentation, LinearMap.toMatrixAlgEquiv_apply, Algebra.lsmul_apply]

lemma idealOrderRepresentation_root {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) :
    idealOrderRepresentation I b (quadraticOrderRoot d) =
      orderRootMatrix d (idealOrderMatrix I b) := by
  simp only [quadraticOrderRoot, map_sub, map_smul, map_one, orderRootMatrix, idealOrderMatrix]

theorem idealOrderMatrix_root_square {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) :
    orderRootMatrix d (idealOrderMatrix I b) * orderRootMatrix d (idealOrderMatrix I b) =
      d • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [← idealOrderRepresentation_root, ← map_mul, quadraticOrderRoot_mul_self,
    map_smul, map_one]

noncomputable def formOfIdealBasis {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) : ℤ × ℤ × ℤ :=
  formOfOrderMatrix d (idealOrderMatrix I b)

theorem formOfIdealBasis_discr {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) : discr (formOfIdealBasis I b) = d :=
  formOfOrderMatrix_discr (idealOrderMatrix_root_square I b)

theorem formOfIdealBasis_fst_ne_zero {d : ℤ} [hns : Fact (¬IsSquare d)]
    (I : Ideal (quadraticOrder d)) (b : Module.Basis (Fin 2) ℤ I) :
    (formOfIdealBasis I b).1 ≠ 0 :=
  formOfOrderMatrix_fst_ne_zero hns.out (idealOrderMatrix_root_square I b)

end Erdos1148.DukeArithmetic
