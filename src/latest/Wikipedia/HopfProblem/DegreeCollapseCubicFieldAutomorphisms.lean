import Wikipedia.HopfProblem.DegreeCollapseCubicDescent

/-!
# Absorbing diagonal blocks by actual cubic-field automorphisms

Any invertible change within equal-rate transverse eigenspaces commutes
with the cubic model vector field. It need not preserve the quadratic
function. This distinction permits arbitrary diagonal blocks from the
holonomy reduction to be absorbed into field charts, without asserting
an orientation normalization or a function-preserving coordinate change.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

def transverseFieldChange (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) : Model m ≃L[ℝ] Model m :=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr T

theorem transverseFieldChange_apply (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) (p : Model m) :
    transverseFieldChange T p = (p.1, T p.2) := rfl

/-- The actual model field is unchanged by a transverse linear map commuting
with its rate operator; no preservation of the model function is claimed. -/
theorem transverseFieldChange_cubicDescent (σ : Fin m → ℝ)
    (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hcomm : ∀ z, T (fun i => σ i * z i) = fun i => σ i * T z i)
    (t : ℝ) (p : Model m) :
    transverseFieldChange T (cubicDescent σ t p) =
      cubicDescent σ t (transverseFieldChange T p) := by
  apply Prod.ext
  · rfl
  · change T (fun i => -σ i * p.2 i) = fun i => -σ i * T p.2 i
    have hleft : (fun i => -σ i * p.2 i) = -(fun i => σ i * p.2 i) := by
      funext i
      simp only [Pi.neg_apply, neg_mul]
    rw [hleft, map_neg, hcomm]
    funext i
    simp only [Pi.neg_apply, neg_mul]

/-- These are actual transformations of ODE solutions, with the same time parameter. -/
theorem hasDerivAt_transverseFieldChange (σ : Fin m → ℝ)
    (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hcomm : ∀ z, T (fun i => σ i * z i) = fun i => σ i * T z i)
    {t r : ℝ} {γ : ℝ → Model m} (hγ : HasDerivAt γ (cubicDescent σ t (γ r)) r) :
    HasDerivAt (transverseFieldChange T ∘ γ)
      (cubicDescent σ t (transverseFieldChange T (γ r))) r := by
  have hh := (transverseFieldChange T).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hγ
  have he := transverseFieldChange_cubicDescent σ T hcomm t (γ r)
  exact he ▸ hh

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

def splitTransverseChange (e : (Fin m → ℝ) ≃L[ℝ] (A × B))
    (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  (e.trans (P.prodCongr S)).trans e.symm

/-- Arbitrary invertible changes within the two rate spaces commute with
the transverse rate operator, including changes of either determinant sign. -/
theorem splitTransverseChange_commutes (σ : Fin m → ℝ)
    (e : (Fin m → ℝ) ≃L[ℝ] (A × B)) (α β : ℝ)
    (he : ∀ z, e (fun i => σ i * z i) = (α • (e z).1, β • (e z).2))
    (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B) (z : Fin m → ℝ) :
    splitTransverseChange e P S (fun i => σ i * z i) =
      fun i => σ i * splitTransverseChange e P S z i := by
  apply e.injective
  simp only [splitTransverseChange, ContinuousLinearEquiv.trans_apply,
    e.apply_symm_apply, he, ContinuousLinearEquiv.prodCongr_apply, map_smul]

/-- The actual diagonal holonomy blocks give an actual native model
diffeomorphism preserving the cubic field and its entire longitudinal axis. -/
theorem splitTransverseChange_field_automorphism (σ : Fin m → ℝ)
    (e : (Fin m → ℝ) ≃L[ℝ] (A × B)) (α β : ℝ)
    (he : ∀ z, e (fun i => σ i * z i) = (α • (e z).1, β • (e z).2))
    (P : A ≃L[ℝ] A) (S : B ≃L[ℝ] B) :
    ∃ D : Diffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, Model m) (Model m) (Model m) ∞,
      (∀ p : Model m, D p = (p.1, e.symm (P (e p.2).1, S (e p.2).2))) ∧
      (∀ s : ℝ, D (s, 0) = (s, 0)) ∧
      ∀ t p, fderiv ℝ D p (cubicDescent σ t p) = cubicDescent σ t (D p) := by
  let T := splitTransverseChange e P S
  let L := transverseFieldChange T
  refine ⟨L.toDiffeomorph, fun p => rfl, ?_, ?_⟩
  · intro s
    change (s, T 0) = (s, 0)
    rw [map_zero]
  · intro t p
    change fderiv ℝ L p (cubicDescent σ t p) = cubicDescent σ t (L p)
    rw [L.fderiv]
    exact transverseFieldChange_cubicDescent σ T
      (splitTransverseChange_commutes σ e α β he P S) t p

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
