import Wikipedia.NoExoticSixSphere.ChartFiber
import Wikipedia.NoExoticSixSphere.RegularLevelManifold

/-!
# Regularity survives valid domain and target chart restrictions

The domain inclusion and target chart have invertible differentials. Thus
the centered chart-coordinate map has surjective differential along its zero
fiber whenever the original manifold-valued map is regular at the specified
value. The existing regular-level construction then supplies its actual atlas.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere.ChartFiber

variable {B H M C H' N F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (f : ContinuousMap M N) (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞)

theorem mfderiv_coordinates_surjective (hf : ContMDiff I J ∞ f) (b : N)
    (x : domain f c) (hreg : Function.Surjective (mfderiv I J f x.val)) :
    Function.Surjective (mfderiv I 𝓘(ℝ, F) (coordinates f c b) x) := by
  have hc : IsLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ c (f x.val) :=
    ⟨c, x.property, fun _ _ ↦ rfl⟩
  have hcs : Function.Surjective (mfderiv J 𝓘(ℝ, F) c (f x.val)) :=
    (hc.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hvs := (mfderiv_openSubset_val_bijective (I := I) (domain f c) x).surjective
  have hdc := hc.mdifferentiableAt (by simp)
  have hdf := hf.mdifferentiable (by simp) x.val
  have hdv := (contMDiff_subtype_val (I := I) (U := domain f c) (n := ∞)).mdifferentiable
    (by simp) x
  have hdcf := hdc.comp x (hdf.comp x hdv)
  change Function.Surjective
    (mfderiv I 𝓘(ℝ, F)
      ((c ∘ (f ∘ (Subtype.val : domain f c → M))) - fun _ ↦ c b) x)
  rw [mfderiv_sub hdcf mdifferentiableAt_const, mfderiv_const]
  let D : B →L[ℝ] F :=
    mfderiv I 𝓘(ℝ, F) (c ∘ (f ∘ (Subtype.val : domain f c → M))) x
  change Function.Surjective (D - (0 : B →L[ℝ] F))
  rw [sub_zero]
  change Function.Surjective
    (mfderiv I 𝓘(ℝ, F) (c ∘ (f ∘ (Subtype.val : domain f c → M))) x)
  rw [mfderiv_comp x hdc (hdf.comp x hdv), mfderiv_comp x hdf hdv]
  exact hcs.comp (hreg.comp hvs)

variable [FiniteDimensional ℝ B] [FiniteDimensional ℝ F]
  [I.Boundaryless] [IsManifold I ∞ M]

theorem nonempty_levelAtlas (hf : ContMDiff I J ∞ f) (b : N) (hb : b ∈ c.source)
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x))
    (k : ℕ) (hd : finrank ℝ B = finrank ℝ F + k) :
    Nonempty (RegularLevelAtlas (K := EuclideanSpace ℝ (Fin k)) I (coordinates f c b)) := by
  apply nonempty_regularLevelAtlas isOpen_univ (contMDiff_coordinates f c hf b).contMDiffOn
    (subset_univ _) _ k hd
  intro x hx
  exact mfderiv_coordinates_surjective f c hf b x
    (hreg x.val ((coordinates_zero_iff f c b hb x).mp hx))

end NoExoticSixSphere.ChartFiber
