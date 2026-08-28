import Wikipedia.HopfProblem.CuspNormalizationGermsBasic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Local rings of actual analytic germs

An analytic germ is a unit exactly when its value at the base point is
nonzero.  The inverse is the germ of the actual analytic reciprocal of a
representative.  Thus evaluation identifies the unique maximal ideal with
the germs vanishing at the base point, and analytic pullbacks are local
ring homomorphisms.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a : E}

/-- The actual analytic reciprocal represents an inverse near a point
where the original representative is nonzero. -/
theorem ofAnalytic_mul_reciprocal (f : E → ℂ) (hf : AnalyticAt ℂ f a)
    (hfa : f a ≠ 0) :
    ofAnalytic f hf * ofAnalytic (fun x => (f x)⁻¹) (hf.inv hfa) = 1 := by
  change ofAnalytic (f * fun x => (f x)⁻¹) (hf.mul (hf.inv hfa)) =
    ofAnalytic (fun _ => 1) analyticAt_const
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  filter_upwards [hf.continuousAt.eventually_ne hfa] with x hx
  exact mul_inv_cancel₀ hx

/-- The unit attached to an actual analytic representative nonzero at its
base point. Its inverse is its ordinary reciprocal germ. -/
def unitOfAnalytic (f : E → ℂ) (hf : AnalyticAt ℂ f a) (hfa : f a ≠ 0) :
    (AnalyticGerm a)ˣ where
  val := ofAnalytic f hf
  inv := ofAnalytic (fun x => (f x)⁻¹) (hf.inv hfa)
  val_inv := ofAnalytic_mul_reciprocal f hf hfa
  inv_val := by rw [mul_comm]; exact ofAnalytic_mul_reciprocal f hf hfa

@[simp] theorem unitOfAnalytic_val (f : E → ℂ) (hf : AnalyticAt ℂ f a)
    (hfa : f a ≠ 0) :
    (unitOfAnalytic f hf hfa : AnalyticGerm a) = ofAnalytic f hf := rfl

@[simp] theorem unitOfAnalytic_inv_val (f : E → ℂ) (hf : AnalyticAt ℂ f a)
    (hfa : f a ≠ 0) :
    ((unitOfAnalytic f hf hfa)⁻¹).val =
      ofAnalytic (fun x => (f x)⁻¹) (hf.inv hfa) := rfl

/-- Units in the actual analytic-germ ring are precisely the germs whose
evaluation is nonzero. -/
@[simp] theorem isUnit_iff_eval_ne_zero (φ : AnalyticGerm a) :
    IsUnit φ ↔ eval a φ ≠ 0 := by
  constructor
  · intro hφ
    exact (hφ.map (eval a)).ne_zero
  · obtain ⟨f, hf, rfl⟩ := exists_representative φ
    intro hf0
    exact (unitOfAnalytic f hf hf0).isUnit

/-- Evaluation reflects units because the reciprocal remains analytic. -/
instance eval_isLocalHom (a : E) : IsLocalHom (eval a) where
  map_nonunit φ hφ := (isUnit_iff_eval_ne_zero φ).mpr hφ.ne_zero

/-- The genuine ring of analytic germs is a local ring. -/
instance analyticGerm_isLocalRing (a : E) : IsLocalRing (AnalyticGerm a) :=
  (eval a).domain_isLocalRing

/-- The unique maximal ideal consists exactly of germs evaluating to zero. -/
theorem maximalIdeal_eq_ker_eval (a : E) :
    IsLocalRing.maximalIdeal (AnalyticGerm a) = RingHom.ker (eval a) :=
  (IsLocalRing.ker_eq_maximalIdeal (eval a) (eval_surjective a)).symm

@[simp] theorem mem_maximalIdeal_iff_eval_eq_zero (φ : AnalyticGerm a) :
    φ ∈ IsLocalRing.maximalIdeal (AnalyticGerm a) ↔ eval a φ = 0 := by
  rw [maximalIdeal_eq_ker_eval]
  rfl

section Pullback

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Actual analytic pullback is a local homomorphism of analytic-germ rings. -/
instance pullback_isLocalHom (g : E → F) (hg : AnalyticAt ℂ g a) :
    IsLocalHom (pullback g hg) where
  map_nonunit φ hφ := by
    apply (isUnit_iff_eval_ne_zero φ).mpr
    have h := (isUnit_iff_eval_ne_zero (pullback g hg φ)).mp hφ
    simpa only [eval_pullback] using h

/-- The named-target version of analytic pullback is also a local homomorphism. -/
instance pullbackAt_isLocalHom {b : F} (g : E → F) (hg : AnalyticAt ℂ g a)
    (hab : g a = b) : IsLocalHom (pullbackAt g hg hab) where
  map_nonunit φ hφ := by
    apply (isUnit_iff_eval_ne_zero φ).mpr
    have h := (isUnit_iff_eval_ne_zero (pullbackAt g hg hab φ)).mp hφ
    simpa only [eval_pullbackAt] using h

end Pullback

end Wikipedia.HopfProblem.CuspNormalization.Germs
