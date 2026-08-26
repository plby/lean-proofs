import ErdosProblems.Erdos1148.IdealOrderMatrix
import ErdosProblems.Erdos1148.FormIdealGenerators

/-! # Recovering the lattice of an ideal from its action matrix -/

namespace Erdos1148.DukeArithmetic

open scoped nonZeroDivisors

noncomputable def idealBasisValue {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) (i : Fin 2) : QuadraticDiscrAlgebra d :=
  ((b i : quadraticOrder d) : QuadraticDiscrAlgebra d)

lemma idealBasisValue_ne_zero {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) (i : Fin 2) : idealBasisValue I b i ≠ 0 := by
  intro h
  apply b.ne_zero i
  apply Subtype.ext
  exact Subtype.ext h

lemma idealBasisValue_repr {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) (x : I) :
    ((x : quadraticOrder d) : QuadraticDiscrAlgebra d) =
      (b.repr x 0 : QuadraticDiscrAlgebra d) * idealBasisValue I b 0 +
      (b.repr x 1 : QuadraticDiscrAlgebra d) * idealBasisValue I b 1 := by
  have h := b.sum_repr x
  rw [Fin.sum_univ_two] at h
  have h' := congrArg (fun z : I => ((z : quadraticOrder d) : QuadraticDiscrAlgebra d)) h
  change (b.repr x 0) • idealBasisValue I b 0 +
    (b.repr x 1) • idealBasisValue I b 1 = _ at h'
  simpa only [zsmul_eq_mul] using h'.symm

lemma idealBasisValue_mul_root {d : ℤ} [hns : Fact (¬IsSquare d)]
    (I : Ideal (quadraticOrder d)) (b : Module.Basis (Fin 2) ℤ I) :
    (quadraticOrderRoot d : QuadraticDiscrAlgebra d) * idealBasisValue I b 0 =
      -(formOfIdealBasis I b).2.1 * idealBasisValue I b 0 +
      (2 * (formOfIdealBasis I b).1 : QuadraticDiscrAlgebra d) * idealBasisValue I b 1 := by
  have h := idealBasisValue_repr I b (quadraticOrderRoot d • b 0)
  rw [← idealOrderRepresentation_apply, ← idealOrderRepresentation_apply,
    idealOrderRepresentation_root] at h
  rw [← formRootMatrix_formOfOrderMatrix hns.out (idealOrderMatrix_root_square I b)] at h
  simpa [formRootMatrix, pellFormMatrix, formOfIdealBasis, idealBasisValue, smul_eq_mul] using h

lemma twice_leading_mul_formIdealGenerator {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    (2 * t.1 : QuadraticDiscrAlgebra d) * formIdealGenerator t =
      (t.2.1 : QuadraticDiscrAlgebra d) + (quadraticOrderRoot d : QuadraticDiscrAlgebra d) := by
  have haQ : (t.1 : ℚ) ≠ 0 := by exact_mod_cast ha
  rw [quadraticOrderRoot_val]
  ext <;> simp [formIdealGenerator, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    field_simp

theorem idealBasisValue_one_eq_generator {d : ℤ} [Fact (¬IsSquare d)]
    (I : Ideal (quadraticOrder d)) (b : Module.Basis (Fin 2) ℤ I) :
    idealBasisValue I b 1 = idealBasisValue I b 0 * formIdealGenerator (formOfIdealBasis I b) := by
  have ha := formOfIdealBasis_fst_ne_zero I b
  have haK : ((formOfIdealBasis I b).1 : QuadraticDiscrAlgebra d) ≠ 0 := by exact_mod_cast ha
  have hroot := idealBasisValue_mul_root I b
  have hgen := twice_leading_mul_formIdealGenerator (d := d) (formOfIdealBasis I b) ha
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : QuadraticDiscrAlgebra d) ≠ 0) haK)
  linear_combination -hroot - idealBasisValue I b 0 * hgen

lemma idealBasisValue_int_combination {d : ℤ} (I : Ideal (quadraticOrder d))
    (b : Module.Basis (Fin 2) ℤ I) (x y : ℤ) :
    (((x • b 0 + y • b 1 : I) : quadraticOrder d) : QuadraticDiscrAlgebra d) =
      (x : QuadraticDiscrAlgebra d) * idealBasisValue I b 0 +
      (y : QuadraticDiscrAlgebra d) * idealBasisValue I b 1 := by
  change x • idealBasisValue I b 0 + y • idealBasisValue I b 1 = _
  simp only [zsmul_eq_mul]

theorem coeIdeal_eq_span_mul_formFractionalIdeal {d : ℤ} [Fact (¬IsSquare d)]
    (I : Ideal (quadraticOrder d)) (b : Module.Basis (Fin 2) ℤ I) :
    (I : FractionalIdeal (quadraticOrder d)⁰ (QuadraticDiscrAlgebra d)) =
      FractionalIdeal.spanSingleton (quadraticOrder d)⁰ (idealBasisValue I b 0) *
        formFractionalIdeal (formOfIdealBasis_discr I b) (formOfIdealBasis_fst_ne_zero I b) := by
  apply FractionalIdeal.eq_spanSingleton_mul.mpr
  constructor
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (FractionalIdeal.mem_coeIdeal (quadraticOrder d)⁰).mp hz
    let xI : I := ⟨x, hx⟩
    refine ⟨(b.repr xI 0 : QuadraticDiscrAlgebra d) +
      (b.repr xI 1 : QuadraticDiscrAlgebra d) * formIdealGenerator (formOfIdealBasis I b), ?_, ?_⟩
    · change _ ∈ formIdealLattice (formOfIdealBasis I b) (formOfIdealBasis_fst_ne_zero I b)
      exact (formIdealLattice_int_coordinates_iff _ _ _).mpr ⟨_, _, rfl⟩
    · have h := idealBasisValue_repr I b xI
      rw [idealBasisValue_one_eq_generator] at h
      change idealBasisValue I b 0 * _ = (x : QuadraticDiscrAlgebra d)
      change (x : QuadraticDiscrAlgebra d) = _ at h
      linear_combination -h
  · intro z hz
    obtain ⟨x, y, rfl⟩ := formIdealLattice_int_coordinates _ _ hz
    let zI : I := x • b 0 + y • b 1
    refine (FractionalIdeal.mem_coeIdeal (quadraticOrder d)⁰).mpr
      ⟨(zI : quadraticOrder d), zI.2, ?_⟩
    change (zI : QuadraticDiscrAlgebra d) = _
    have h := idealBasisValue_int_combination I b x y
    rw [idealBasisValue_one_eq_generator] at h
    change (zI : QuadraticDiscrAlgebra d) = _ at h
    linear_combination h

end Erdos1148.DukeArithmetic
