import Wikipedia.NoExoticSixSphere.SardTriangularDerivative
import Wikipedia.NoExoticSixSphere.SardCriticalLocus
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The Fubini step in Sard's theorem

For a smooth map preserving its first coordinate on an open set, every
section of its critical-value set is contained in the critical values of
the corresponding vertical map. Lower-dimensional Sard therefore implies
that the whole critical-value set has product measure zero. Measurability
is proved from smoothness and finite dimensionality, not assumed.
-/

open scoped ContDiff Topology
open Set MeasureTheory MeasureTheory.Measure

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem criticalValues_slice_subset {g : ℝ × E → ℝ × F} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hfirst : ∀ p ∈ U, (g p).1 = p.1) (t : ℝ) :
    Prod.mk t ⁻¹' (g '' {p | p ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g p)}) ⊆
      (fun v : E ↦ (g (t, v)).2) ''
        {v | (t, v) ∈ U ∧
          ¬ Function.Surjective (fderiv ℝ (fun v : E ↦ (g (t, v)).2) v)} := by
  rintro w ⟨p, hp, he⟩
  have ht : p.1 = t := (hfirst p hp.1).symm.trans (congrArg Prod.fst he)
  have hp' : (t, p.2) ∈ U := by simpa only [← ht, Prod.eta] using hp.1
  refine ⟨p.2, ⟨hp', ?_⟩, ?_⟩
  · intro hs
    have hd := (hg.contDiffAt (hU.mem_nhds hp.1)).differentiableAt (by simp)
    have hf : (fun q ↦ (g q).1) =ᶠ[𝓝 p] (Prod.fst : ℝ × E → ℝ) := by
      filter_upwards [hU.mem_nhds hp.1] with q hq
      exact hfirst q hq
    apply hp.2
    apply (surjective_fderiv_iff_vertical hd hf).mpr
    simpa only [ht] using hs
  · simpa only [← ht, Prod.eta] using congrArg Prod.snd he

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem measure_criticalValues_of_preserves_fst
    (μ : Measure ℝ) (ν : Measure F)
    (hSard : ∀ (f : E → F) (V : Set E), IsOpen V → ContDiffOn ℝ ∞ f V →
      ν (f '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ f x)}) = 0)
    {g : ℝ × E → ℝ × F} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hfirst : ∀ p ∈ U, (g p).1 = p.1) :
    μ.prod ν (g '' {p | p ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g p)}) = 0 := by
  apply measure_prod_null_of_ae_null (measurableSet_criticalValues hU hg)
  apply Filter.Eventually.of_forall
  intro t
  apply measure_mono_null (criticalValues_slice_subset hU hg hfirst t)
  apply hSard (fun v : E ↦ (g (t, v)).2) (Prod.mk t ⁻¹' U)
  · exact hU.preimage (continuous_const.prodMk continuous_id)
  · exact hg.snd.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ hv ↦ hv)

end NoExoticSixSphere.Sard
