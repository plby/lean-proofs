import ErdosProblems.Erdos1148.QuadraticOrderFractionField

/-! # An integral basis of the discriminant order -/

namespace Erdos1148.DukeArithmetic

def monicCompanionForm (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (1, t.2.1, t.1 * t.2.2)

lemma discr_monicCompanionForm (t : ℤ × ℤ × ℤ) :
    discr (monicCompanionForm t) = discr t := by dsimp [monicCompanionForm, discr]; ring

lemma primitive_monicCompanionForm (t : ℤ × ℤ × ℤ) :
    PrimitiveIntegralForm (monicCompanionForm t) := primitiveIntegralForm_of_monic rfl

noncomputable def quadraticOrderParam (d : ℤ) : (Fin 2 → ℤ) →ₗ[ℤ] quadraticOrder d where
  toFun v := ⟨(v 0 : QuadraticDiscrAlgebra d) +
    (v 1 : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d,
    int_combination_mem_quadraticOrder d (v 0) (v 1)⟩
  map_add' v w := by
    apply Subtype.ext
    change ((v 0 + w 0 : ℤ) : QuadraticDiscrAlgebra d) +
      ((v 1 + w 1 : ℤ) : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d = _
    push_cast
    ring
  map_smul' r v := by
    apply Subtype.ext
    change ((r * v 0 : ℤ) : QuadraticDiscrAlgebra d) +
      ((r * v 1 : ℤ) : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d =
      r • ((v 0 : QuadraticDiscrAlgebra d) +
        (v 1 : QuadraticDiscrAlgebra d) * quadraticOrderGenerator d)
    rw [zsmul_eq_mul]
    push_cast
    ring

lemma quadraticOrderParam_re (d : ℤ) (v : Fin 2 → ℤ) :
    (quadraticOrderParam d v).1.re = (v 0 : ℚ) + (v 1 : ℚ) * d / 2 := by
  simp [quadraticOrderParam, quadraticOrderGenerator]
  ring

lemma quadraticOrderParam_im (d : ℤ) (v : Fin 2 → ℤ) :
    (quadraticOrderParam d v).1.im = (v 1 : ℚ) / 2 := by
  simp [quadraticOrderParam, quadraticOrderGenerator]
  ring

lemma quadraticOrderParam_injective (d : ℤ) : Function.Injective (quadraticOrderParam d) := by
  intro v w hvw
  have hre := congrArg (fun z : quadraticOrder d => z.1.re) hvw
  have him := congrArg (fun z : quadraticOrder d => z.1.im) hvw
  rw [quadraticOrderParam_re, quadraticOrderParam_re] at hre
  rw [quadraticOrderParam_im, quadraticOrderParam_im] at him
  have h1Q : (v 1 : ℚ) = (w 1 : ℚ) := by linarith
  have h0Q : (v 0 : ℚ) = (w 0 : ℚ) := by rw [h1Q] at hre; linarith
  ext i
  fin_cases i
  · exact Int.cast_injective h0Q
  · exact Int.cast_injective h1Q

lemma quadraticOrderParam_surjective {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Function.Surjective (quadraticOrderParam d) := by
  intro w
  obtain ⟨x, y, hxy⟩ := (mem_quadraticOrder_iff_coordinates
    ((discr_monicCompanionForm t).trans ht) (primitive_monicCompanionForm t) w.1).mp w.2
  refine ⟨![x, y], Subtype.ext ?_⟩
  exact hxy.symm

noncomputable def quadraticOrderBasis {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Module.Basis (Fin 2) ℤ (quadraticOrder d) :=
  (Pi.basisFun ℤ (Fin 2)).map (LinearEquiv.ofBijective (quadraticOrderParam d)
    ⟨quadraticOrderParam_injective d, quadraticOrderParam_surjective ht⟩)

lemma quadraticOrder_moduleFinite {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Module.Finite ℤ (quadraticOrder d) := Module.Finite.of_basis (quadraticOrderBasis ht)

lemma quadraticOrder_moduleFree {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    Module.Free ℤ (quadraticOrder d) := Module.Free.of_basis (quadraticOrderBasis ht)

lemma quadraticOrder_isNoetherianRing {d : ℤ} {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    IsNoetherianRing (quadraticOrder d) := by
  let := quadraticOrder_moduleFinite ht
  exact IsNoetherianRing.of_finite ℤ (quadraticOrder d)

end Erdos1148.DukeArithmetic
