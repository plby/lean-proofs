import Wikipedia.HopfProblem.CuspNormalizationGermsBasic

/-!
# Centering actual analytic germs by translation

Pullback by `z ↦ a + z` identifies actual analytic germs at `a` with
actual analytic germs at zero.  The inverse is pullback by `z ↦ z - a`.
The two maps compose to the identity on analytic representatives, and
the resulting ring equivalence preserves the value of a germ at its
base point.  No topology or ring structure is transported by definition.
-/

noncomputable section

open Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.SheafManifoldStalk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem addTranslation_analyticAt (a x : E) :
    AnalyticAt ℂ (fun z : E => a + z) x :=
  analyticAt_const.add analyticAt_id

theorem subTranslation_analyticAt (a x : E) :
    AnalyticAt ℂ (fun z : E => z - a) x :=
  analyticAt_id.sub analyticAt_const

/-- Actual analytic pullback from a germ at `a` to its centered germ. -/
def translateToZeroHom (a : E) : Germs.AnalyticGerm a →+* Germs.AnalyticGerm (0 : E) :=
  Germs.pullbackAt (fun z : E => a + z) (addTranslation_analyticAt a 0) (add_zero a)

/-- Actual analytic pullback undoing the centering translation. -/
def translateFromZeroHom (a : E) : Germs.AnalyticGerm (0 : E) →+* Germs.AnalyticGerm a :=
  Germs.pullbackAt (fun z : E => z - a) (subTranslation_analyticAt a a) (sub_self a)

theorem translateToZeroHom_ofAnalytic (a : E) (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    translateToZeroHom a (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (fun z => f (a + z))
        (hf.comp_of_eq (addTranslation_analyticAt a 0) (add_zero a)) :=
  Germs.pullbackAt_ofAnalytic ..

theorem translateFromZeroHom_ofAnalytic (a : E) (f : E → ℂ)
    (hf : AnalyticAt ℂ f (0 : E)) :
    translateFromZeroHom a (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (fun z => f (z - a))
        (hf.comp_of_eq (subTranslation_analyticAt a a) (sub_self a)) :=
  Germs.pullbackAt_ofAnalytic ..

@[simp] theorem translateFromZeroHom_translateToZeroHom (a : E) (φ : Germs.AnalyticGerm a) :
    translateFromZeroHom a (translateToZeroHom a φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  rw [translateToZeroHom_ofAnalytic, translateFromZeroHom_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => by
    change f (a + (z - a)) = f z
    rw [← add_sub_assoc, add_sub_cancel_left]

@[simp] theorem translateToZeroHom_translateFromZeroHom (a : E)
    (φ : Germs.AnalyticGerm (0 : E)) :
    translateToZeroHom a (translateFromZeroHom a φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  rw [translateFromZeroHom_ofAnalytic, translateToZeroHom_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => by
    change f (a + z - a) = f z
    rw [add_sub_cancel_left]

/-- Translation to zero is an equivalence of the original analytic-germ
rings, with explicit analytic pullbacks in both directions. -/
def translateToZero (a : E) : Germs.AnalyticGerm a ≃+* Germs.AnalyticGerm (0 : E) :=
  { translateToZeroHom a with
    invFun := translateFromZeroHom a
    left_inv := translateFromZeroHom_translateToZeroHom a
    right_inv := translateToZeroHom_translateFromZeroHom a }

@[simp] theorem translateToZero_toRingHom (a : E) :
    (translateToZero a).toRingHom = translateToZeroHom a := rfl

@[simp] theorem translateToZero_ofAnalytic (a : E) (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    translateToZero a (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (fun z => f (a + z))
        (hf.comp_of_eq (addTranslation_analyticAt a 0) (add_zero a)) :=
  translateToZeroHom_ofAnalytic a f hf

@[simp] theorem translateToZero_symm_ofAnalytic (a : E) (f : E → ℂ)
    (hf : AnalyticAt ℂ f (0 : E)) :
    (translateToZero a).symm (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (fun z => f (z - a))
        (hf.comp_of_eq (subTranslation_analyticAt a a) (sub_self a)) :=
  translateFromZeroHom_ofAnalytic a f hf

/-- Evaluation at the new origin equals evaluation at the old base point. -/
@[simp] theorem eval_translateToZero (a : E) (φ : Germs.AnalyticGerm a) :
    Germs.eval (0 : E) (translateToZero a φ) = Germs.eval a φ :=
  Germs.eval_pullbackAt _ _ _ φ

@[simp] theorem eval_translateToZero_symm (a : E) (φ : Germs.AnalyticGerm (0 : E)) :
    Germs.eval a ((translateToZero a).symm φ) = Germs.eval (0 : E) φ :=
  Germs.eval_pullbackAt _ _ _ φ

@[simp] theorem translateToZero_constant (a : E) (c : ℂ) :
    translateToZero a (Germs.constant a c) = Germs.constant (0 : E) c := by
  change translateToZero a (Germs.ofAnalytic (fun _ => c) analyticAt_const) = _
  rw [translateToZero_ofAnalytic]
  rfl

@[simp] theorem translateToZero_symm_constant (a : E) (c : ℂ) :
    (translateToZero a).symm (Germs.constant (0 : E) c) = Germs.constant a c := by
  change (translateToZero a).symm (Germs.ofAnalytic (fun _ => c) analyticAt_const) = _
  rw [translateToZero_symm_ofAnalytic]
  rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafManifoldStalk
