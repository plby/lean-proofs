import Wikipedia.NoExoticSixSphere.AffineJetParameter

/-!
# Spatially weighted affine variations and their actual derivatives

A source-dependent cutoff contributes its derivative to the spatial jet.
For an affine variation with zero value at the chosen point, that extra term
vanishes. The nonlinear target map therefore has the same exact linear jet
variation as in the constant-weight case, with the actual cutoff value.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.WeightedAffineComposite

open AffinePerturbation

variable {X V E W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def ambient (g : X → E) (i : X → V) (a : X → ℝ) (p : Parameters V E) (x : X) : E :=
  g x + a x • value p (i x)

def composite (g : X → E) (i : X → V) (r : E → W) (a : X → ℝ)
    (p : Parameters V E) (x : X) : W := r (ambient g i a p x)

theorem hasFDerivAt_ambient (g : X → E) (i : X → V) (a : X → ℝ)
    (p : Parameters V E) (x : X) (hg : DifferentiableAt ℝ g x)
    (hi : DifferentiableAt ℝ i x) (ha : DifferentiableAt ℝ a x) :
    HasFDerivAt (ambient g i a p)
      (fderiv ℝ g x + (a x • p.1.comp (fderiv ℝ i x) +
        (fderiv ℝ a x).smulRight (value p (i x)))) x :=
  hg.hasFDerivAt.add (ha.hasFDerivAt.smul
    ((p.1.hasFDerivAt.comp x hi.hasFDerivAt).add_const p.2))

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem ambient_add_smul (g : X → E) (i : X → V) (a : X → ℝ)
    (p q : Parameters V E) (t : ℝ) (x : X) :
    ambient g i a (p + t • q) x = ambient g i a p x + a x • (t • value q (i x)) := by
  have he : value (p + t • q) (i x) = value p (i x) + t • value q (i x) :=
    (evaluation (F := E) (i x)).map_add p (t • q) |>.trans
      (congrArg (value p (i x) + ·) ((evaluation (F := E) (i x)).map_smul t q))
  rw [ambient, he, smul_add]
  exact (add_assoc _ _ _).symm

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem ambient_eq_of_zero_value (g : X → E) (i : X → V) (a : X → ℝ)
    (p q : Parameters V E) (x : X) (hq : value q (i x) = 0) (t : ℝ) :
    ambient g i a (p + t • q) x = ambient g i a p x := by
  rw [ambient_add_smul, hq, smul_zero, smul_zero, add_zero]

theorem fderiv_composite (g : X → E) (i : X → V) (r : E → W) (a : X → ℝ)
    (p : Parameters V E) (x : X) (hg : DifferentiableAt ℝ g x)
    (hi : DifferentiableAt ℝ i x) (ha : DifferentiableAt ℝ a x)
    (hr : DifferentiableAt ℝ r (ambient g i a p x)) :
    fderiv ℝ (composite g i r a p) x =
      (fderiv ℝ r (ambient g i a p x)).comp
        (fderiv ℝ g x + (a x • p.1.comp (fderiv ℝ i x) +
          (fderiv ℝ a x).smulRight (value p (i x)))) :=
  (hr.hasFDerivAt.comp x (hasFDerivAt_ambient g i a p x hg hi ha)).fderiv

theorem fderiv_composite_add_smul_of_zero (g : X → E) (i : X → V) (r : E → W) (a : X → ℝ)
    (p q : Parameters V E) (x : X) (hg : DifferentiableAt ℝ g x)
    (hi : DifferentiableAt ℝ i x) (ha : DifferentiableAt ℝ a x)
    (hr : DifferentiableAt ℝ r (ambient g i a p x))
    (hq : value q (i x) = 0) (t : ℝ) :
    fderiv ℝ (composite g i r a (p + t • q)) x =
      fderiv ℝ (composite g i r a p) x +
        t • (fderiv ℝ r (ambient g i a p x)).comp (a x • q.1.comp (fderiv ℝ i x)) := by
  have he := ambient_eq_of_zero_value g i a p q x hq t
  have hv : value (p + t • q) (i x) = value p (i x) := by
    change evaluation (i x) (p + t • q) = evaluation (i x) p
    rw [map_add, map_smul]
    change value p (i x) + t • value q (i x) = value p (i x)
    rw [hq, smul_zero, add_zero]
  have hr' : DifferentiableAt ℝ r (ambient g i a (p + t • q) x) := he.symm ▸ hr
  rw [fderiv_composite g i r a (p + t • q) x hg hi ha hr', he, hv,
    fderiv_composite g i r a p x hg hi ha hr]
  apply ContinuousLinearMap.ext
  intro v
  change fderiv ℝ r (ambient g i a p x)
      (fderiv ℝ g x v + (a x • (p.1 (fderiv ℝ i x v) + t • q.1 (fderiv ℝ i x v)) +
        fderiv ℝ a x v • value p (i x))) =
    fderiv ℝ r (ambient g i a p x)
      (fderiv ℝ g x v + (a x • p.1 (fderiv ℝ i x v) +
        fderiv ℝ a x v • value p (i x))) +
      t • fderiv ℝ r (ambient g i a p x) (a x • q.1 (fderiv ℝ i x v))
  simp only [map_add, map_smul, smul_add, smul_smul]
  rw [mul_comm (a x) t]
  abel

end NoExoticSixSphere.WeightedAffineComposite
