import Wikipedia.NoExoticSixSphere.DoublePointLinearPerturbation
import Wikipedia.NoExoticSixSphere.FamilyDoublePointClosure
import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential
import Wikipedia.NoExoticSixSphere.Transport

/-!
# Smooth manifolds on the actual off-diagonal double-point locus

The regular zero atlas on the open distinct-pair domain transfers to the
original ordered double-point subtype. Its inclusion is smooth and immersive.
Small linear perturbations construct the required regularity, in particular
giving a one-dimensional locus for three-dimensional slices in six-space.
-/

noncomputable section

open Set Function Module Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DoublePointPerturbation

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

def zeroHomeomorph (f : ℝ → E → F) :
    FamilyEmbedding.doublePoints f ≃ₜ
      {q : distinctDomain E // baseDifference f q.val = 0} where
  toFun q := ⟨⟨q.val, q.property.1⟩, sub_eq_zero.mpr q.property.2⟩
  invFun q := ⟨q.val.val, q.val.property, sub_eq_zero.mp q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply IsInducing.subtypeVal.continuous_iff.mpr
    apply IsInducing.subtypeVal.continuous_iff.mpr
    exact continuous_subtype_val
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem exists_doublePoint_manifold (f : ℝ → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hr : ∀ q : ℝ × (E × E), q.2.1 ≠ q.2.2 → baseDifference f q = 0 →
      Surjective (fderiv ℝ (baseDifference f) q))
    (k : ℕ) (hd : 1 + (finrank ℝ E + finrank ℝ E) = finrank ℝ F + k) :
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin k)) (FamilyEmbedding.doublePoints f),
      letI := c;
      IsManifold (𝓡 k) ∞ (FamilyEmbedding.doublePoints f) ∧
      ContMDiff (𝓡 k) 𝓘(ℝ, ℝ × (E × E)) ∞
        (Subtype.val : FamilyEmbedding.doublePoints f → ℝ × (E × E)) ∧
      ∀ x : FamilyEmbedding.doublePoints f,
        Injective (mfderiv (𝓡 k) 𝓘(ℝ, ℝ × (E × E)) Subtype.val x) := by
  let X := distinctDomain E
  let g : X → F := fun q ↦ baseDifference f q.val
  have hg : ContMDiff 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, F) ∞ g :=
    (contDiff_baseDifference f hf).contMDiff.comp contMDiff_subtype_val
  have hv : ContMDiff 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, ℝ × (E × E)) ∞
      (Subtype.val : X → ℝ × (E × E)) := contMDiff_subtype_val
  have hreg : ∀ q : X, g q = 0 →
      Surjective (mfderiv 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, F) g q) := by
    intro q hq
    have h := mfderiv_comp q
      ((contDiff_baseDifference f hf).contMDiff.mdifferentiable (by simp) q.val)
      (hv.mdifferentiable (by simp) q)
    rw [mfderiv_eq_fderiv] at h
    rw [show mfderiv 𝓘(ℝ, ℝ × (E × E)) 𝓘(ℝ, F) g q = _ from h]
    exact (hr q.val q.property hq).comp
      (mfderiv_openSubset_val_bijective (I := 𝓘(ℝ, ℝ × (E × E))) X q).surjective
  have hdim : finrank ℝ (ℝ × (E × E)) = finrank ℝ F + k := by
    simpa only [finrank_prod, finrank_self] using hd
  obtain ⟨A⟩ := nonempty_regularLevelAtlas isOpen_univ hg.contMDiffOn
    (subset_univ _) hreg k hdim
  let := A.chartedSpace
  let := A.isManifold
  let e := zeroHomeomorph f
  let c := pullbackAtlas (n := k) e
  refine ⟨c, ?_⟩
  let := c
  have he : ContMDiff (𝓡 k) (𝓡 k) ∞ e := pullback_contMDiff e
  have hl := A.contMDiff_subtype_val
  refine ⟨pullback_isManifold e, hv.comp (hl.comp he), ?_⟩
  intro x
  let d := pullbackDiffeomorph (n := k) e
  have heinj := (d.mfderivToContinuousLinearEquiv (by simp) x).injective
  have hlinj := A.injective_mfderiv_subtype_val (e x)
  have hvinj := (mfderiv_openSubset_val_bijective
    (I := 𝓘(ℝ, ℝ × (E × E))) X (e x).val).injective
  have hde := he.mdifferentiable (by simp) x
  have hdl := hl.mdifferentiable (by simp) (e x)
  have hdv := hv.mdifferentiable (by simp) (e x).val
  change Injective (mfderiv (𝓡 k) 𝓘(ℝ, ℝ × (E × E))
    ((Subtype.val : X → ℝ × (E × E)) ∘
      ((Subtype.val : {q : X // g q = 0} → X) ∘ e)) x)
  rw [mfderiv_comp x hdv (hdl.comp x hde), mfderiv_comp x hdl hde]
  exact hvinj.comp (hlinj.comp heinj)

theorem exists_small_doublePoint_manifold (f : ℝ → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f)) (k : ℕ)
    (hd : 1 + (finrank ℝ E + finrank ℝ E) = finrank ℝ F + k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ A : E →L[ℝ] F, ‖A‖ < ε ∧
      ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin k))
          (FamilyEmbedding.doublePoints (perturb f A)),
        letI := c;
        IsManifold (𝓡 k) ∞ (FamilyEmbedding.doublePoints (perturb f A)) ∧
        ContMDiff (𝓡 k) 𝓘(ℝ, ℝ × (E × E)) ∞
          (Subtype.val : FamilyEmbedding.doublePoints (perturb f A) → ℝ × (E × E)) ∧
        ∀ x : FamilyEmbedding.doublePoints (perturb f A),
          Injective (mfderiv (𝓡 k) 𝓘(ℝ, ℝ × (E × E)) Subtype.val x) := by
  obtain ⟨A, hsmall, hr⟩ := exists_small_regular_operator f hf hε
  refine ⟨A, hsmall, exists_doublePoint_manifold (perturb f A) (contDiff_perturb f hf A)
    ?_ k hd⟩
  have he : baseDifference (perturb f A) = difference f A :=
    funext (fun q ↦ (difference_eq f A q).symm)
  rw [he]
  exact hr

end NoExoticSixSphere.DoublePointPerturbation
