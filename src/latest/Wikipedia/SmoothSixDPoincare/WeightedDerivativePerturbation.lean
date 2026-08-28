import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Small weighted perturbations repair derivatives along a low-dimensional locus

The perturbation `f x + β x • a` preserves every zero of `β`, but its derivative
there may change in the transverse direction. Along a smooth locus of small
enough dimension, generic parameters leave exactly the common kernel of the
original derivatives of `f` and `β`. This is the local analytic input for
repairing a radially constant disk filling at its fixed boundary.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.WeightedPerturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def perturb (f : E → F) (β : E → ℝ) (a : F) (x : E) : F := f x + β x • a

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem perturb_eq_of_zero (f : E → F) {β : E → ℝ} (a : F) {x : E} (hx : β x = 0) :
    perturb f β a x = f x := by simp only [perturb, hx, zero_smul, add_zero]

theorem contDiff_perturb {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) :
    ContDiff ℝ ∞ (perturb f β a) := hf.add (hβ.smul contDiff_const)

theorem fderiv_perturb {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) (a : F) (x : E) :
    fderiv ℝ (perturb f β a) x = fderiv ℝ f x + (fderiv ℝ β x).smulRight a :=
  ((hf.differentiable (by simp) x).hasFDerivAt.add
    ((hβ.differentiable (by simp) x).hasFDerivAt.smul_const a)).fderiv

variable {B H X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace X] [ChartedSpace H X]

def badDomain (b : X → E) (β : E → ℝ) : Set (X × E) :=
  {q | fderiv ℝ β (b q.1) q.2 ≠ 0}

def badParameter (b : X → E) (f : E → F) (β : E → ℝ) (q : X × E) : F :=
  (fderiv ℝ β (b q.1) q.2)⁻¹ • (-(fderiv ℝ f (b q.1) q.2))

theorem contMDiff_scalarDerivative {b : X → E} {β : E → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun q : X × E => fderiv ℝ β (b q.1) q.2) :=
  ((hβ.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd

theorem isOpen_badDomain {b : X → E} {β : E → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hβ : ContDiff ℝ ∞ β) :
    IsOpen (badDomain b β) :=
  isOpen_ne_fun (contMDiff_scalarDerivative hb hβ).continuous continuous_const

theorem contMDiffOn_badParameter {b : X → E} {f : E → F} {β : E → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) :
    ContMDiffOn (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ (badParameter b f β) (badDomain b β) := by
  have hdf : ContMDiff (I.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
      (fun q : X × E => fderiv ℝ f (b q.1) q.2) :=
    ((hf.fderiv_right (by simp)).contMDiff.comp (hb.comp contMDiff_fst)).clm_apply contMDiff_snd
  intro q hq
  exact (((contMDiff_scalarDerivative hb hβ).contMDiffAt.inv₀ hq).smul
    hdf.contMDiffAt.neg).contMDiffWithinAt

omit [TopologicalSpace X] in
/-- For a good parameter, the new derivative kernel is exactly the common kernel of the
original map and scalar-weight derivatives at every point of the prescribed locus. -/
theorem kernel_iff_of_not_bad {b : X → E} {f : E → F} {β : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β) {a : F}
    (hgood : a ∉ badParameter b f β '' badDomain b β) (x : X) (v : E) :
    fderiv ℝ (perturb f β a) (b x) v = 0 ↔
      fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  rw [fderiv_perturb hf hβ]
  change fderiv ℝ f (b x) v + fderiv ℝ β (b x) v • a = 0 ↔ _
  constructor
  · intro hker
    have hbzero : fderiv ℝ β (b x) v = 0 := by
      by_contra hn
      apply hgood
      refine ⟨(x, v), hn, ?_⟩
      have heq : fderiv ℝ β (b x) v • a = -(fderiv ℝ f (b x) v) :=
        eq_neg_of_add_eq_zero_right hker
      change (fderiv ℝ β (b x) v)⁻¹ • (-(fderiv ℝ f (b x) v)) = a
      rw [← heq, inv_smul_smul₀ hn]
    exact ⟨by simpa only [hbzero, zero_smul, add_zero] using hker, hbzero⟩
  · rintro ⟨hfzero, hbzero⟩
    simp only [hfzero, hbzero, zero_smul, add_zero]

variable [FiniteDimensional ℝ B] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ X] [LindelofSpace (X × E)]

/-- Arbitrarily small parameters repair every transverse derivative along a low-dimensional
smooth locus, while the map remains fixed at every zero of the scalar weight. -/
theorem exists_small_parameter_with_common_kernel {b : X → E} {f : E → F} {β : E → ℝ}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hf : ContDiff ℝ ∞ f) (hβ : ContDiff ℝ ∞ β)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ ContDiff ℝ ∞ (perturb f β a) ∧
      ∀ x v, fderiv ℝ (perturb f β a) (b x) v = 0 ↔
        fderiv ℝ f (b x) v = 0 ∧ fderiv ℝ β (b x) v = 0 := by
  have hd : Module.finrank ℝ (B × E) < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense := GeneralPosition.dense_compl_manifold_image (isOpen_badDomain hb hβ)
    (contMDiffOn_badParameter hb hf hβ) hd
  obtain ⟨a, hgood, hnorm⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨a, by simpa only [dist_zero_left] using hnorm, contDiff_perturb hf hβ a,
    kernel_iff_of_not_bad hf hβ hgood⟩

end Wikipedia.SmoothSixDPoincare.WeightedPerturbation
