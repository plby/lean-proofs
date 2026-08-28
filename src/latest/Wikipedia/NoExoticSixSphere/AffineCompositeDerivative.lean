import Wikipedia.NoExoticSixSphere.AffineJetParameter

/-!
# Spatial derivatives of actual affine perturbations followed by a smooth map

An affine parameter variation vanishing at a specified source point keeps
the argument of the final map fixed there. Consequently its effect on the
actual spatial derivative is exactly linear, even if the final map is nonlinear.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.AffineComposite

open AffinePerturbation

variable {X V E W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def ambient (g : X → E) (i : X → V) (a : ℝ) (p : Parameters V E) (x : X) : E :=
  g x + a • value p (i x)

def composite (g : X → E) (i : X → V) (r : E → W) (a : ℝ)
    (p : Parameters V E) (x : X) : W := r (ambient g i a p x)

theorem hasFDerivAt_ambient (g : X → E) (i : X → V) (a : ℝ) (p : Parameters V E)
    (x : X) (hg : DifferentiableAt ℝ g x) (hi : DifferentiableAt ℝ i x) :
    HasFDerivAt (ambient g i a p)
      (fderiv ℝ g x + a • p.1.comp (fderiv ℝ i x)) x :=
  hg.hasFDerivAt.add (((p.1.hasFDerivAt.comp x hi.hasFDerivAt).add_const p.2).const_smul a)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem ambient_add_smul (g : X → E) (i : X → V) (a : ℝ)
    (p q : Parameters V E) (t : ℝ) (x : X) :
    ambient g i a (p + t • q) x = ambient g i a p x + a • (t • value q (i x)) := by
  have he : value (p + t • q) (i x) = value p (i x) + t • value q (i x) :=
    (evaluation (F := E) (i x)).map_add p (t • q) |>.trans
      (congrArg (value p (i x) + ·) ((evaluation (F := E) (i x)).map_smul t q))
  rw [ambient, he, smul_add]
  change g x + (a • value p (i x) + a • (t • value q (i x))) = _
  exact (add_assoc _ _ _).symm

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem ambient_eq_of_zero_value (g : X → E) (i : X → V) (a : ℝ)
    (p q : Parameters V E) (x : X) (hq : value q (i x) = 0) (t : ℝ) :
    ambient g i a (p + t • q) x = ambient g i a p x := by
  rw [ambient_add_smul, hq, smul_zero, smul_zero, add_zero]

theorem fderiv_composite (g : X → E) (i : X → V) (r : E → W) (a : ℝ)
    (p : Parameters V E) (x : X) (hg : DifferentiableAt ℝ g x)
    (hi : DifferentiableAt ℝ i x) (hr : DifferentiableAt ℝ r (ambient g i a p x)) :
    fderiv ℝ (composite g i r a p) x =
      (fderiv ℝ r (ambient g i a p x)).comp
        (fderiv ℝ g x + a • p.1.comp (fderiv ℝ i x)) :=
  (hr.hasFDerivAt.comp x (hasFDerivAt_ambient g i a p x hg hi)).fderiv

theorem fderiv_composite_add_smul_of_zero (g : X → E) (i : X → V) (r : E → W) (a : ℝ)
    (p q : Parameters V E) (x : X) (hg : DifferentiableAt ℝ g x)
    (hi : DifferentiableAt ℝ i x) (hr : DifferentiableAt ℝ r (ambient g i a p x))
    (hq : value q (i x) = 0) (t : ℝ) :
    fderiv ℝ (composite g i r a (p + t • q)) x =
      fderiv ℝ (composite g i r a p) x +
        t • (fderiv ℝ r (ambient g i a p x)).comp (a • q.1.comp (fderiv ℝ i x)) := by
  have he := ambient_eq_of_zero_value g i a p q x hq t
  have hr' : DifferentiableAt ℝ r (ambient g i a (p + t • q) x) := he.symm ▸ hr
  rw [fderiv_composite g i r a (p + t • q) x hg hi hr', he,
    fderiv_composite g i r a p x hg hi hr]
  ext v
  change fderiv ℝ r (ambient g i a p x)
      (fderiv ℝ g x v + a • (p.1 (fderiv ℝ i x v) + t • q.1 (fderiv ℝ i x v))) =
    fderiv ℝ r (ambient g i a p x) (fderiv ℝ g x v + a • p.1 (fderiv ℝ i x v)) +
      t • fderiv ℝ r (ambient g i a p x) (a • q.1 (fderiv ℝ i x v))
  simp only [map_add, map_smul, smul_add, smul_smul]
  rw [mul_comm a t]
  abel

end NoExoticSixSphere.AffineComposite
