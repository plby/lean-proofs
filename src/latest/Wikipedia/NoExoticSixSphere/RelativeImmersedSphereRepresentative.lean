import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereSingularities
import Wikipedia.NoExoticSixSphere.SpatiallyRelativeSphereRegularTimes
import Wikipedia.NoExoticSixSphere.SphereDoublePointParity
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Immersed self-transverse representatives preserving prescribed local data

For a smooth map already immersive and self-transverse on the protected set,
a constructed relative family supplies an actual globally immersed and
self-transverse sphere in the same relative homotopy class. Its values and
native derivatives are unchanged on that set. Center avoidance outside the
set turns a prescribed unique local fiber into a unique global fiber.

Constructing the initial protected local models for arbitrary classes, and
simultaneous mutual transversality of two representatives, remain separate.
-/

noncomputable section

open Set Function Topology
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SpatiallyRelativeSphereFamily SphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_selfTransverse_immersed_relative_of_smooth
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (χ : Sphere 3 → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hn : ∀ s, 0 ≤ χ s) (hbound : ∀ s, ‖χ s‖ ≤ 1)
    (hi : ∀ s, χ s = 0 → Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (ht : ∀ s z, χ s = 0 → χ z = 0 → s ≠ z → f s = f z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f s).coprod (mfderiv (𝓡 3) (𝓡 6) f z)))
    (b : M) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧
      f.HomotopicRel g {s | χ s = 0} ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) ∧
      (∀ s z, s ≠ z → g s = g z → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g s).coprod (mfderiv (𝓡 3) (𝓡 6) g z))) ∧
      (∀ s, χ s = 0 → mfderiv (𝓡 3) (𝓡 6) g s = mfderiv (𝓡 3) (𝓡 6) f s) ∧
      ∀ s, χ s ≠ 0 → g s ≠ b := by
  let f₀ : ℝ → Sphere 3 → M := fun _ s ↦ f s
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  obtain ⟨S, C, p, hSfin, hS, hCfin, hC, _, hgen, hmem, hP, hfix, hend, havoid⟩ :=
    exists_small_generic_avoiding_manifold_family e r f₀ χ hf₀ hχ hbound rfl b
      (by norm_num : (0 : ℝ) < 1)
  let G := SpatiallyRelativeSphereFamily.map e r f₀ χ p
  let A := {q : ℝ × Sphere 3 | q.1 ∈ Ioo (0 : ℝ) 1} ∩ singularParameters (n := 6) G
  have hdis : IsDiscrete A :=
    isDiscrete_interior_singularParameters e r f₀ χ hf₀ hχ p hn hP S C hS hC hmem hgen
      (fun _ _ s hs ↦ hi s hs)
  have hcount : A.Countable :=
    (HereditarilyLindelofSpace.isLindelof A).countable_of_isDiscrete hdis
  have hreg := ae_regular_time_in_charts e r f₀ χ hf₀ hχ p volume
    S hSfin.countable C hCfin.countable hgen
  have hdense := Measure.dense_of_ae (hreg.and ((hcount.image Prod.fst).ae_notMem volume))
  obtain ⟨t, ⟨htreg, hta⟩, htime⟩ :=
    hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr (by norm_num : (0 : ℝ) < 1))
  have hg : ContMDiff (𝓡 3) (𝓡 6) ∞ (G t) :=
    hP.comp (contMDiff_const.prodMk contMDiff_id)
  let g : C(Sphere 3, M) := ⟨G t, hg.continuous⟩
  have H : f.HomotopicRel g {s | χ s = 0} := by
    refine ⟨{
      toFun := fun q ↦ G ((q.1 : ℝ) * t) q.2
      continuous_toFun := hP.continuous.comp
        (((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk continuous_snd)
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_
    }⟩
    · intro s
      change G ((0 : ℝ) * t) s = f s
      rw [zero_mul]
      exact hend 0 (Or.inl le_rfl) s
    · intro s
      change G ((1 : ℝ) * t) s = G t s
      rw [one_mul]
    · exact fun u s hs ↦ hfix ((u : ℝ) * t) s hs
  refine ⟨g, hg, H, ?_, ?_, ?_, ?_⟩
  · intro s
    by_contra hs
    exact hta ⟨(t, s), ⟨htime, hs⟩, rfl⟩
  · exact self_transverse_of_regular_time e r f₀ χ hf₀ hχ hn p hP S C hS hC
      t htime (hmem t) htreg ht
  · exact fun s hs ↦ mfderiv_map_of_zero_cutoff e r f₀ χ hf₀ hχ hn p t s hs
  · exact havoid t htime

include e r in
theorem exists_selfTransverse_immersed_relative_unique_center
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (χ : Sphere 3 → ℝ) (hχ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ χ)
    (hn : ∀ s, 0 ≤ χ s) (hbound : ∀ s, ‖χ s‖ ≤ 1)
    (hi : ∀ s, χ s = 0 → Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (ht : ∀ s z, χ s = 0 → χ z = 0 → s ≠ z → f s = f z → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f s).coprod (mfderiv (𝓡 3) (𝓡 6) f z)))
    (x : Sphere 3) (hx : χ x = 0) (hu : ∀ s, χ s = 0 → f s = f x → s = x) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧
      f.HomotopicRel g {s | χ s = 0} ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) g s)) ∧
      (∀ s z, s ≠ z → g s = g z → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g s).coprod (mfderiv (𝓡 3) (𝓡 6) g z))) ∧
      (∀ s, χ s = 0 → mfderiv (𝓡 3) (𝓡 6) g s = mfderiv (𝓡 3) (𝓡 6) f s) ∧
      ∀ s, g s = f x ↔ s = x := by
  obtain ⟨g, hg, H, hgi, hgt, hD, ha⟩ :=
    e.exists_selfTransverse_immersed_relative_of_smooth r f hf χ hχ hn hbound hi ht (f x)
  refine ⟨g, hg, H, hgi, hgt, hD, ?_⟩
  intro s
  constructor
  · intro hs
    by_cases hz : χ s = 0
    · exact hu s hz ((H.fst_eq_snd hz).trans hs)
    · exact (ha s hz hs).elim
  · rintro rfl
    exact (H.fst_eq_snd hx).symm

end NoExoticSixSphere.EuclideanEmbedding
