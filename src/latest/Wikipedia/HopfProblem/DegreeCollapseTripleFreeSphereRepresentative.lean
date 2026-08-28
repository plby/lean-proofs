import Wikipedia.HopfProblem.DegreeCollapseTripleFreeManifoldFamily
import Wikipedia.HopfProblem.DegreeCollapseFiniteDoublePointReduction
import Wikipedia.NoExoticSixSphere.SelfTransverseSphereRepresentative

/-!
# Actual smooth self-transverse representatives with simple double fibers

Choose one interior time of the constructed triple-free generic family
outside its countable singular-time set and its null exceptional set for
spatial transversality. This gives a genuine native immersion in the original
homotopy class without assuming a fiber condition. In a simply connected
target the constructed Whitney reduction then leaves at most one double point.
-/

noncomputable section

open Set Function Topology
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding ManifoldAffineSphereFamily SphereFamily DoublePointCounting

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r in
theorem exists_tripleFree_immersed_homotopic_of_smooth (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      HasOnlyDoubleFibers g := by
  let f₀ : ℝ → Sphere 3 → M := fun _ x ↦ f x
  have hf₀ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f₀) :=
    hf.comp contMDiff_snd
  obtain ⟨S, C, p, hSfin, hS, hCfin, hC, _, hgen, hfree, hmem, hP, hend⟩ :=
    exists_small_tripleFree_generic_manifold_family e r f₀ hf₀ (by norm_num : (0 : ℝ) < 1)
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
    · intro x
      change G ((0 : ℝ) * t) x = f x
      rw [zero_mul]
      exact hend 0 (Or.inl le_rfl) x
    · intro x
      change G ((1 : ℝ) * t) x = G t x
      rw [one_mul]
  refine ⟨g, hg, H, ?_, ?_, hfree t ht⟩
  · intro x
    by_contra hx
    exact hta ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  · exact self_transverse_of_regular_time e r f₀ hf₀ p hP S C hS hC t ht (hmem t) htreg

include e r in
theorem exists_tripleFree_immersed_homotopic (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      HasOnlyDoubleFibers g := by
  obtain ⟨F, hF, HF⟩ :=
    Wikipedia.SmoothSixDPoincare.ManifoldSmoothing.exists_smooth_map_homotopic
      (I := 𝓡 3) (J := 𝓡 6) f
  obtain ⟨g, hg, H, hi, ht, hd⟩ := exists_tripleFree_immersed_homotopic_of_smooth e r F hF
  exact ⟨g, hg, HF.trans H, hi, ht, hd⟩

include e r in
theorem exists_at_most_one_double_representative [T2Space M] [SimplyConnectedSpace M]
    (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      HasOnlyDoubleFibers g ∧ Nat.card (SphereSelfIntersections.Unordered g) ≤ 1 := by
  obtain ⟨F, hF, HF, hi, ht, hd⟩ := exists_tripleFree_immersed_homotopic e r f
  obtain ⟨g, hg, H, hgi, hgt, hgd, _, hcard, _⟩ :=
    ImmersedSource.exists_reduction_to_at_most_one_double_point F hF hi ht hd
  exact ⟨g, hg, HF.trans H, hgi, hgt, hgd, hcard⟩

omit r in
theorem exists_reduced_representative_of_normalFrame [T2Space M] [SimplyConnectedSpace M]
    (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (f : C(Sphere 3, M)) :
    ∃ g : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ g ∧ f.Homotopic g ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) g x).coprod (mfderiv (𝓡 3) (𝓡 6) g y))) ∧
      HasOnlyDoubleFibers g ∧ Nat.card (SphereSelfIntersections.Unordered g) ≤ 1 := by
  let x : Sphere 3 := Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
  let : Nonempty M := ⟨f x⟩
  obtain ⟨r⟩ := e.nonempty_tubularRetraction a
  exact exists_at_most_one_double_representative e r f

end Wikipedia.HopfProblem.DegreeCollapse.TripleParameters
