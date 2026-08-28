import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Ring

/-!
# Continuous symmetric bilinear forms for the smooth Morse lemma

Symmetric forms form an actual real submodule of continuous bilinear
forms. Symmetrization is a continuous linear projection onto this
submodule. Congruence is the literal operation of applying one linear
operator in both arguments of the given form.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Bilinear := E →L[ℝ] E →L[ℝ] ℝ

/-- The actual submodule of symmetric continuous real bilinear forms. -/
def symmetricForms : Submodule ℝ (Bilinear E) where
  carrier := {B | ∀ u v, B u v = B v u}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro B C hB hC u v
    change B u v + C u v = B v u + C v u
    rw [hB u v, hC u v]
  smul_mem' := by
    intro c B hB u v
    change c * B u v = c * B v u
    rw [hB u v]

abbrev SymmetricForm := symmetricForms E

@[ext] theorem symmetricForm_ext {S T : SymmetricForm E}
    (h : ∀ u v, S.val u v = T.val u v) : S = T :=
  Subtype.ext (ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => h u v)

/-- Flipping the arguments as an actual continuous linear map. -/
def flipBilinear : Bilinear E →L[ℝ] Bilinear E :=
  (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem flipBilinear_apply (B : Bilinear E) (u v : E) :
    flipBilinear E B u v = B v u := rfl

/-- The continuous linear projection from all forms to symmetric forms. -/
def symmetrize : Bilinear E →L[ℝ] SymmetricForm E :=
  (((2 : ℝ)⁻¹) • (ContinuousLinearMap.id ℝ (Bilinear E) + flipBilinear E)).codRestrict
    (symmetricForms E) (fun B u v => by
      change (2 : ℝ)⁻¹ * (B u v + B v u) = (2 : ℝ)⁻¹ * (B v u + B u v)
      ring)

@[simp] theorem symmetrize_apply (B : Bilinear E) (u v : E) :
    (symmetrize E B).val u v = (2 : ℝ)⁻¹ * (B u v + B v u) := rfl

@[simp] theorem symmetrize_coe (S : SymmetricForm E) : symmetrize E S.val = S := by
  apply symmetricForm_ext
  intro u v
  rw [symmetrize_apply, S.property u v]
  ring

variable {E}

/-- Literal congruence of a continuous bilinear form by a linear operator. -/
def congruence (B : Bilinear E) (L : E →L[ℝ] E) : Bilinear E := B.bilinearComp L L

@[simp] theorem congruence_apply (B : Bilinear E) (L : E →L[ℝ] E) (u v : E) :
    congruence B L u v = B (L u) (L v) := rfl

theorem congruence_symmetric (B : Bilinear E) (hB : ∀ u v, B u v = B v u)
    (L : E →L[ℝ] E) : congruence B L ∈ symmetricForms E :=
  fun u v => hB (L u) (L v)

@[simp] theorem congruence_id (B : Bilinear E) :
    congruence B (ContinuousLinearMap.id ℝ E) = B := by
  ext u v
  rfl

@[simp] theorem congruence_zero (B : Bilinear E) : congruence B (0 : E →L[ℝ] E) = 0 := by
  ext u v
  simp [congruence]

/-- Congruence is a globally smooth polynomial in the operator. -/
theorem contDiff_congruence (B : Bilinear E) : ContDiff ℝ ∞ (congruence B) := by
  have h₁ : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => B.comp L) :=
    contDiff_const.clm_comp contDiff_id
  have h₂ : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => (B.comp L).flip) :=
    (flipBilinear E).contDiff.comp h₁
  exact (flipBilinear E).contDiff.comp (h₂.clm_comp contDiff_id)

/-- Raising one index using the actual nondegenerate reference form. -/
def raiseIndex (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) : Bilinear E →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E H.symm.toContinuousLinearMap

@[simp] theorem raiseIndex_apply (H : E ≃L[ℝ] (E →L[ℝ] ℝ)) (B : Bilinear E) (u : E) :
    raiseIndex H B u = H.symm (B u) := rfl

@[simp] theorem apply_raiseIndex (H : E ≃L[ℝ] (E →L[ℝ] ℝ))
    (B : Bilinear E) (u v : E) : H (raiseIndex H B u) v = B u v := by
  rw [raiseIndex_apply, H.apply_symm_apply]

end Wikipedia.HopfProblem.SmoothMorseLemma
