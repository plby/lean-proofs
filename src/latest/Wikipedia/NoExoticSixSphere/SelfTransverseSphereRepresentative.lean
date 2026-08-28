import Wikipedia.NoExoticSixSphere.GenericSphereRegularTimes
import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularities
import Wikipedia.NoExoticSixSphere.SphereDoublePointParity
import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Self-transverse immersed representatives in the original homotopy class

A generic family has at most countably many singular times and has spatially
transverse double points at almost every time. An interior time satisfying
both conditions supplies a genuine smooth self-transverse immersion. The
actual family, not just its homotopy class, connects it to the original map.
No embedding or double-point removal is asserted.
-/

noncomputable section

open Set Function Topology
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization ManifoldAffineSphereFamily SphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_selfTransverse_immersed_homotopic_of_smooth (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) ∧
      ∀ s t, s ≠ t → g s = g t → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g s).coprod (mfderiv (𝓡 3) (𝓡 6) g t)) := by
  let f₀ : ℝ → Sphere 3 → M := fun _ s ↦ f s
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  obtain ⟨S, C, p, hSfin, hS, hCfin, hC, _, hgen, hmem, hP, hend⟩ :=
    exists_small_generic_manifold_family e r f₀ hf₀ rfl (by norm_num : (0 : ℝ) < 1)
  let G := ManifoldAffineSphereFamily.map e r f₀ p
  let A := {q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1} ∩ singularParameters (n := 6) G
  have hdis : IsDiscrete A :=
    isDiscrete_interior_singularParameters e r f₀ hf₀ p hP S C hS hC hmem hgen
  have hcount : A.Countable :=
    (HereditarilyLindelofSpace.isLindelof A).countable_of_isDiscrete hdis
  have hreg := ae_regular_time_in_charts e r f₀ hf₀ p volume
    S hSfin.countable C hCfin.countable hgen
  have hdense := Measure.dense_of_ae (hreg.and ((hcount.image Prod.fst).ae_notMem volume))
  obtain ⟨t, ⟨htreg, hta⟩, ht⟩ :=
    hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (by norm_num : (0 : ℝ) < 1))
  have hg : ContMDiff (𝓡 3) (𝓡 6) ∞ (G t) :=
    hP.comp (contMDiff_const.prodMk contMDiff_id)
  let g : C(Sphere 3, M) := ⟨G t, hg.continuous⟩
  have H : f.Homotopic g := by
    refine ⟨{
      toFun := fun q ↦ G ((q.1 : ℝ) * t) q.2
      continuous_toFun := hP.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
      map_zero_left := ?_
      map_one_left := ?_
    }⟩
    · intro s
      change G ((0 : ℝ) * t) s = f s
      rw [zero_mul]
      exact hend 0 (Or.inl le_rfl) s
    · intro s
      change G ((1 : ℝ) * t) s = G t s
      rw [one_mul]
  refine ⟨g, hg, H, ?_, ?_⟩
  · intro s
    by_contra hs
    exact hta ⟨(t, s), ⟨ht, hs⟩, rfl⟩
  · exact self_transverse_of_regular_time e r f₀ hf₀ p hP S C hS hC t ht (hmem t) htreg

include e r in
theorem exists_selfTransverse_immersed_homotopic (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) ∧
      ∀ s t, s ≠ t → g s = g t → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g s).coprod (mfderiv (𝓡 3) (𝓡 6) g t)) := by
  obtain ⟨F, hF, HF⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) f
  obtain ⟨g, hg, H, hd, ht⟩ := e.exists_selfTransverse_immersed_homotopic_of_smooth r F hF
  exact ⟨g, hg, HF.trans H, hd, ht⟩

include e r in
theorem exists_finite_selfTransverse_immersed_homotopic [T2Space M]
    (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) ∧
      (∀ s t, s ≠ t → g s = g t → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g s).coprod (mfderiv (𝓡 3) (𝓡 6) g t))) ∧
      (SphereSelfIntersections.pairs g).Finite ∧ Even (SphereSelfIntersections.pairs g).ncard := by
  obtain ⟨g, hg, H, hi, ht⟩ := e.exists_selfTransverse_immersed_homotopic r f
  have hfin := SphereSelfIntersections.finite_pairs hg ht hi
  exact ⟨g, hg, H, hi, ht, hfin, SphereSelfIntersections.even_ncard g hfin⟩

end NoExoticSixSphere.EuclideanEmbedding
