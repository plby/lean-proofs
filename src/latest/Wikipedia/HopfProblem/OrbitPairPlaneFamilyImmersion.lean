import Wikipedia.SmoothSixDPoincare.PlaneImmersionPerturbation
import Wikipedia.SmoothSixDPoincare.MorseOpenDomain

/-!
# Simultaneous immersion repair for a one-parameter family of plane maps

For a smooth family ℝ×ℝ²→F, the two added affine columns can be chosen
arbitrarily small so that every spatial slice is immersive. All singular
parameters lie in two smooth images of dimension dim(F)+4 inside a
parameter space of dimension 2·dim(F). Thus dimension at least five is
enough, including the actual quotient dimension.

This is the local analytic input for regularizing a two-sphere homotopy.
It does not yet localize the perturbation, keep endpoint collars fixed,
or eliminate slice double points.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold ENNReal

namespace Wikipedia.HopfProblem.OrbitPair.PlaneFamily

open Wikipedia.SmoothSixDPoincare
open PlaneImmersion (Plane)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def badFirst (f : ℝ × Plane → F) (q : (ℝ × Plane) × (ℝ × F)) : F × F :=
  (-fderiv ℝ (fun x => f (q.1.1, x)) q.1.2 (1, q.2.1) - q.2.1 • q.2.2, q.2.2)

def badSecond (f : ℝ × Plane → F) (q : (ℝ × Plane) × (ℝ × F)) : F × F :=
  (q.2.2, -fderiv ℝ (fun x => f (q.1.1, x)) q.1.2 (q.2.1, 1) - q.2.1 • q.2.2)

theorem contDiff_spatialDerivative {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => fderiv ℝ (fun x => f (p.1, x)) p.2) :=
  contDiffOn_univ.mp (MorsePerturbation.contDiffOn_spatialDerivative
    (f := fun t x => f (t, x)) isOpen_univ hf.contDiffOn)

theorem contDiff_badFirst {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (badFirst f) := by
  have hd := contDiff_spatialDerivative hf
  have he : ContDiff ℝ ∞ (fun q : (ℝ × Plane) × (ℝ × F) =>
      fderiv ℝ (fun x => f (q.1.1, x)) q.1.2 (1, q.2.1)) :=
    (hd.comp contDiff_fst).clm_apply (contDiff_const.prodMk (contDiff_fst.comp contDiff_snd))
  exact (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul
    (contDiff_snd.comp contDiff_snd))).prodMk (contDiff_snd.comp contDiff_snd)

theorem contDiff_badSecond {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (badSecond f) := by
  have hd := contDiff_spatialDerivative hf
  have he : ContDiff ℝ ∞ (fun q : (ℝ × Plane) × (ℝ × F) =>
      fderiv ℝ (fun x => f (q.1.1, x)) q.1.2 (q.2.1, 1)) :=
    (hd.comp contDiff_fst).clm_apply ((contDiff_fst.comp contDiff_snd).prodMk contDiff_const)
  exact (contDiff_snd.comp contDiff_snd).prodMk
    (he.neg.sub ((contDiff_fst.comp contDiff_snd).smul (contDiff_snd.comp contDiff_snd)))

theorem dimH_bad_parameters_le {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (range (badFirst f) ∪ range (badSecond f)) ≤
      (Module.finrank ℝ ((ℝ × Plane) × (ℝ × F)) : ℝ≥0∞) := by
  have h₁ : dimH (range (badFirst f)) ≤
      (Module.finrank ℝ ((ℝ × Plane) × (ℝ × F)) : ℝ≥0∞) := by
    rw [← image_univ]
    exact GeneralPosition.dimH_image_manifold_le isOpen_univ
      (contDiff_badFirst hf).contMDiff.contMDiffOn
  have h₂ : dimH (range (badSecond f)) ≤
      (Module.finrank ℝ ((ℝ × Plane) × (ℝ × F)) : ℝ≥0∞) := by
    rw [← image_univ]
    exact GeneralPosition.dimH_image_manifold_le isOpen_univ
      (contDiff_badSecond hf).contMDiff.contMDiffOn
  rw [dimH_union]
  exact max_le h₁ h₂

theorem dense_good_parameters {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 5 ≤ Module.finrank ℝ F) : Dense (range (badFirst f) ∪ range (badSecond f))ᶜ := by
  have hd : Module.finrank ℝ ((ℝ × Plane) × (ℝ × F)) < Module.finrank ℝ (F × F) := by
    simp only [Plane, Module.finrank_prod, Module.finrank_self]
    omega
  exact dense_compl_of_dimH_lt_finrank
    ((dimH_bad_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd))

theorem not_bad_on_slice (f : ℝ × Plane → F) {A : F × F}
    (hA : A ∉ range (badFirst f) ∪ range (badSecond f)) (t : ℝ) :
    A ∉ range (PlaneImmersion.badFirst (fun x => f (t, x))) ∪
      range (PlaneImmersion.badSecond (fun x => f (t, x))) := by
  rintro (⟨q, hq⟩ | ⟨q, hq⟩)
  · exact hA (Or.inl ⟨((t, q.1), q.2), hq⟩)
  · exact hA (Or.inr ⟨((t, q.1), q.2), hq⟩)

def perturb (f : ℝ × Plane → F) (A : F × F) (p : ℝ × Plane) : F :=
  f p + PlaneImmersion.linearMap A p.2

theorem contDiff_perturb {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f) (A : F × F) :
    ContDiff ℝ ∞ (perturb f A) :=
  hf.add ((PlaneImmersion.linearMap A).contDiff.comp contDiff_snd)

theorem exists_small_affine_family_immersion {f : ℝ × Plane → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 5 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F, ‖A‖ < ε ∧ ContDiff ℝ ∞ (perturb f A) ∧
      ∀ t x, Function.Injective (fderiv ℝ (fun y => perturb f A (t, y)) x) := by
  obtain ⟨A, hA, hnorm⟩ := (dense_good_parameters hf hdim).exists_dist_lt 0 hε
  refine ⟨A, ?_, contDiff_perturb hf A, ?_⟩
  · simpa only [dist_zero_left] using hnorm
  · intro t x
    change Function.Injective (fderiv ℝ (PlaneImmersion.perturb (fun y => f (t, y)) A) x)
    have hft : ContDiff ℝ ∞ (fun y : Plane => f (t, y)) :=
      hf.comp (contDiff_const.prodMk contDiff_id)
    rw [PlaneImmersion.fderiv_perturb hft A x]
    exact PlaneImmersion.injective_add_linearMap_of_not_bad _ (not_bad_on_slice f hA t) x

end Wikipedia.HopfProblem.OrbitPair.PlaneFamily
