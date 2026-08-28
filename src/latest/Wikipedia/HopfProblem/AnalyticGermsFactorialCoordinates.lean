import Wikipedia.HopfProblem.CuspNormalizationGermsBasic

/-!
# Actual analytic germs under coordinate changes

An analytic equivalence with analytic inverse induces an equivalence of actual
analytic-germ rings by composition. In particular, complex continuous linear
equivalences, translations, and affine coordinate changes preserve the actual
germ rings. Their action on representatives is ordinary composition.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.Coordinates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- An actual analytic equivalence with analytic inverse acts contravariantly
on the actual analytic-germ rings. -/
def analyticEquivPullbackAt (e : E ≃ F) {a : E} {b : F}
    (he : AnalyticAt ℂ e a) (hinv : AnalyticAt ℂ e.symm b) (hab : e a = b) :
    AnalyticGerm b ≃+* AnalyticGerm a :=
  { pullbackAt e he hab with
    toFun := pullbackAt e he hab
    invFun := pullbackAt e.symm hinv (by rw [← hab, e.symm_apply_apply])
    left_inv := by
      intro φ
      obtain ⟨f, hf, rfl⟩ := exists_representative φ
      rw [pullbackAt_ofAnalytic, pullbackAt_ofAnalytic]
      apply (ofAnalytic_eq_iff _ _ _ _).mpr
      exact Eventually.of_forall fun x => by simp
    right_inv := by
      intro φ
      obtain ⟨f, hf, rfl⟩ := exists_representative φ
      rw [pullbackAt_ofAnalytic, pullbackAt_ofAnalytic]
      apply (ofAnalytic_eq_iff _ _ _ _).mpr
      exact Eventually.of_forall fun x => by simp }

@[simp] theorem analyticEquivPullbackAt_ofAnalytic (e : E ≃ F) {a : E} {b : F}
    (he : AnalyticAt ℂ e a) (hinv : AnalyticAt ℂ e.symm b) (hab : e a = b)
    (f : F → ℂ) (hf : AnalyticAt ℂ f b) :
    analyticEquivPullbackAt e he hinv hab (ofAnalytic f hf) =
      ofAnalytic (f ∘ e) (hf.comp_of_eq he hab) :=
  pullbackAt_ofAnalytic e he hab f hf

@[simp] theorem eval_analyticEquivPullbackAt (e : E ≃ F) {a : E} {b : F}
    (he : AnalyticAt ℂ e a) (hinv : AnalyticAt ℂ e.symm b) (hab : e a = b)
    (φ : AnalyticGerm b) :
    eval a (analyticEquivPullbackAt e he hinv hab φ) = eval b φ :=
  eval_pullbackAt e he hab φ

/-- A continuous linear coordinate change, with its base point left explicit. -/
def linearPullbackEquivAt (e : E ≃L[ℂ] F) (a : E) :
    AnalyticGerm (e a) ≃+* AnalyticGerm a :=
  analyticEquivPullbackAt e.toEquiv (e.analyticAt a) (e.symm.analyticAt (e a)) rfl

@[simp] theorem linearPullbackEquivAt_ofAnalytic (e : E ≃L[ℂ] F) (a : E)
    (f : F → ℂ) (hf : AnalyticAt ℂ f (e a)) :
    linearPullbackEquivAt e a (ofAnalytic f hf) =
      ofAnalytic (f ∘ e) (hf.comp (e.analyticAt a)) := rfl

@[simp] theorem eval_linearPullbackEquivAt (e : E ≃L[ℂ] F) (a : E)
    (φ : AnalyticGerm (e a)) :
    eval a (linearPullbackEquivAt e a φ) = eval (e a) φ :=
  eval_pullbackAt e (e.analyticAt a) rfl φ

/-- Continuous linear coordinate changes preserve the actual germ rings at zero. -/
def linearPullbackEquiv (e : E ≃L[ℂ] F) :
    AnalyticGerm (0 : F) ≃+* AnalyticGerm (0 : E) :=
  analyticEquivPullbackAt e.toEquiv (e.analyticAt 0) (e.symm.analyticAt 0) (map_zero e)

@[simp] theorem linearPullbackEquiv_ofAnalytic (e : E ≃L[ℂ] F)
    (f : F → ℂ) (hf : AnalyticAt ℂ f 0) :
    linearPullbackEquiv e (ofAnalytic f hf) =
      ofAnalytic (f ∘ e) (hf.comp_of_eq (e.analyticAt 0) (map_zero e)) :=
  pullbackAt_ofAnalytic _ _ _ _ _

@[simp] theorem linearPullbackEquiv_symm_ofAnalytic (e : E ≃L[ℂ] F)
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    (linearPullbackEquiv e).symm (ofAnalytic f hf) =
      ofAnalytic (f ∘ e.symm) (hf.comp_of_eq (e.symm.analyticAt 0) (map_zero e.symm)) :=
  pullbackAt_ofAnalytic _ _ _ _ _

@[simp] theorem eval_linearPullbackEquiv (e : E ≃L[ℂ] F)
    (φ : AnalyticGerm (0 : F)) :
    eval (0 : E) (linearPullbackEquiv e φ) = eval (0 : F) φ :=
  eval_pullbackAt e (e.analyticAt 0) (map_zero e) φ

@[simp] theorem linearPullbackEquiv_ne_zero_iff (e : E ≃L[ℂ] F)
    (φ : AnalyticGerm (0 : F)) : linearPullbackEquiv e φ ≠ 0 ↔ φ ≠ 0 := by
  simp

private def translationEquiv (a : E) : E ≃ E where
  toFun x := a + x
  invFun x := x - a
  left_inv x := by simp
  right_inv x := by simp

/-- Translation to the origin, by the actual map `x ↦ a + x`. -/
def translationPullbackEquiv (a : E) : AnalyticGerm a ≃+* AnalyticGerm (0 : E) :=
  analyticEquivPullbackAt (translationEquiv a)
    (analyticAt_const.add analyticAt_id) (analyticAt_id.sub analyticAt_const) (add_zero a)

@[simp] theorem translationPullbackEquiv_ofAnalytic (a : E)
    (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    translationPullbackEquiv a (ofAnalytic f hf) =
      ofAnalytic (fun x => f (a + x))
        (hf.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero a)) :=
  pullbackAt_ofAnalytic _ _ _ _ _

@[simp] theorem translationPullbackEquiv_symm_ofAnalytic (a : E)
    (f : E → ℂ) (hf : AnalyticAt ℂ f 0) :
    (translationPullbackEquiv a).symm (ofAnalytic f hf) =
      ofAnalytic (fun x => f (x - a))
        (hf.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self a)) :=
  pullbackAt_ofAnalytic _ _ _ _ _

@[simp] theorem eval_translationPullbackEquiv (a : E) (φ : AnalyticGerm a) :
    eval (0 : E) (translationPullbackEquiv a φ) = eval a φ :=
  eval_pullbackAt _ _ _ φ

@[simp] theorem eval_translationPullbackEquiv_symm (a : E)
    (φ : AnalyticGerm (0 : E)) :
    eval a ((translationPullbackEquiv a).symm φ) = eval (0 : E) φ :=
  eval_pullbackAt _ _ _ φ

@[simp] theorem translationPullbackEquiv_ne_zero_iff (a : E) (φ : AnalyticGerm a) :
    translationPullbackEquiv a φ ≠ 0 ↔ φ ≠ 0 := by
  simp

/-- The affine coordinate map `x ↦ b + e (x - a)` is analytic at `a`. -/
theorem affine_analyticAt (e : E ≃L[ℂ] F) (a : E) (b : F) :
    AnalyticAt ℂ (fun x : E => b + e (x - a)) a := by
  have ht : AnalyticAt ℂ (fun x : E => x - a) a := analyticAt_id.sub analyticAt_const
  exact analyticAt_const.add ((e.analyticAt 0).comp_of_eq ht (sub_self a))

/-- Actual affine coordinate changes preserve analytic-germ rings. -/
def affinePullbackEquiv (e : E ≃L[ℂ] F) (a : E) (b : F) :
    AnalyticGerm b ≃+* AnalyticGerm a :=
  ((translationPullbackEquiv b).trans (linearPullbackEquiv e)).trans
    (translationPullbackEquiv a).symm

@[simp] theorem affinePullbackEquiv_ofAnalytic (e : E ≃L[ℂ] F) (a : E) (b : F)
    (f : F → ℂ) (hf : AnalyticAt ℂ f b) :
    affinePullbackEquiv e a b (ofAnalytic f hf) =
      ofAnalytic (fun x => f (b + e (x - a)))
        (hf.comp_of_eq (affine_analyticAt e a b) (by simp)) := by
  simp only [affinePullbackEquiv, RingEquiv.trans_apply, translationPullbackEquiv_ofAnalytic,
    linearPullbackEquiv_ofAnalytic, translationPullbackEquiv_symm_ofAnalytic]
  rfl

@[simp] theorem affinePullbackEquiv_symm_ofAnalytic (e : E ≃L[ℂ] F) (a : E) (b : F)
    (f : E → ℂ) (hf : AnalyticAt ℂ f a) :
    (affinePullbackEquiv e a b).symm (ofAnalytic f hf) =
      ofAnalytic (fun y => f (a + e.symm (y - b)))
        (hf.comp_of_eq (affine_analyticAt e.symm b a) (by simp)) := by
  simp only [affinePullbackEquiv, RingEquiv.symm_trans_apply,
    RingEquiv.symm_symm, translationPullbackEquiv_ofAnalytic,
    linearPullbackEquiv_symm_ofAnalytic, translationPullbackEquiv_symm_ofAnalytic]
  rfl

@[simp] theorem eval_affinePullbackEquiv (e : E ≃L[ℂ] F) (a : E) (b : F)
    (φ : AnalyticGerm b) : eval a (affinePullbackEquiv e a b φ) = eval b φ := by
  simp [affinePullbackEquiv]

@[simp] theorem affinePullbackEquiv_ne_zero_iff (e : E ≃L[ℂ] F) (a : E) (b : F)
    (φ : AnalyticGerm b) : affinePullbackEquiv e a b φ ≠ 0 ↔ φ ≠ 0 := by
  simp

end Wikipedia.HopfProblem.CuspNormalization.Germs.Coordinates
