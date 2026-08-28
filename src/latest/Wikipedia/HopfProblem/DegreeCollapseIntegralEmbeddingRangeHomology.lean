import Wikipedia.HopfProblem.DegreeCollapseIntegralEmbeddingRange
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Exact homology of the original embedding-range pair

The actual range homeomorphism retains the source map in the pair
sequence. Adjacent surjectivity and injectivity give relative vanishing.
When ambient next homology vanishes, the original connecting map is
injective; an original cyclic inclusion kernel then gives an original
generator of the relative group.
-/

noncomputable section

open Function Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralEmbeddingRange

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open NoExoticSixSphere.RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem rangeMap_homology_bijective (f : C(X, Y)) (hf : IsEmbedding f) (n : ℕ) :
    Bijective (singularHomologyMap (rangeMap f) n) :=
  (homeomorphHomologyEquiv hf.toHomeomorph n).bijective

theorem inclusion_rangeMap_homology (f : C(X, Y)) (n : ℕ) (a : SingularHomology X n) :
    singularHomologyMap (subtypeInclusion (Set.range f)) n
      (singularHomologyMap (rangeMap f) n a) = singularHomologyMap f n a := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, inclusion_rangeMap]

theorem range_inclusion_homology_injective (f : C(X, Y)) (hf : IsEmbedding f) (n : ℕ)
    (hi : Injective (singularHomologyMap f n)) :
    Injective (singularHomologyMap (subtypeInclusion (Set.range f)) n) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := (rangeMap_homology_bijective f hf n).2 a
  obtain ⟨y, rfl⟩ := (rangeMap_homology_bijective f hf n).2 b
  rw [inclusion_rangeMap_homology, inclusion_rangeMap_homology] at hab
  exact congrArg (singularHomologyMap (rangeMap f) n) (hi hab)

theorem relative_homology_subsingleton (f : C(X, Y)) (hf : IsEmbedding f) (n : ℕ)
    (hs : Surjective (singularHomologyMap f (n + 1)))
    (hi : Injective (singularHomologyMap f n)) :
    Subsingleton (Homology (Set.range f) (n + 1)) := by
  have hincl := range_inclusion_homology_injective f hf n hi
  have hproj (a : SingularHomology Y (n + 1)) : toRelative (Set.range f) (n + 1) a = 0 := by
    obtain ⟨b, rfl⟩ := hs a
    apply (NoExoticSixSphere.RelativeSingularHomology.exact_at_ambient
      (Set.range f) (n + 1)).le
    exact ⟨singularHomologyMap (rangeMap f) (n + 1) b, inclusion_rangeMap_homology f (n + 1) b⟩
  have hz (a : Homology (Set.range f) (n + 1)) : a = 0 := by
    have ha : connecting (Set.range f) n a = 0 := by
      apply hincl
      rw [map_zero]
      exact (exact_at_subspace (Set.range f) n).le ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := (exact_at_relative (Set.range f) n).ge ha
    exact hb.symm.trans (hproj b)
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

theorem connecting_injective (U : Set Y) (n : ℕ)
    [Subsingleton (SingularHomology Y (n + 1))] : Injective (connecting U n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨b, hb⟩ := (exact_at_relative U n).ge ha
  exact hb.symm.trans ((congrArg (toRelative U (n + 1)) (Subsingleton.elim b 0)).trans (map_zero _))

theorem relative_class_multiple (f : C(X, Y)) (hf : IsEmbedding f) (n : ℕ)
    [Subsingleton (SingularHomology Y (n + 1))]
    (μ : SingularHomology X n)
    (hker : (singularHomologyMap f n).toAddMonoidHom.ker = AddSubgroup.zmultiples μ)
    (w : Homology (Set.range f) (n + 1))
    (hw : connecting (Set.range f) n w = singularHomologyMap (rangeMap f) n μ)
    (a : Homology (Set.range f) (n + 1)) : ∃ k : ℤ, k • w = a := by
  obtain ⟨b, hb⟩ := (rangeMap_homology_bijective f hf n).2 (connecting (Set.range f) n a)
  have hq : singularHomologyMap f n b = 0 := by
    rw [← inclusion_rangeMap_homology f n b, hb]
    exact (exact_at_subspace (Set.range f) n).le ⟨a, rfl⟩
  have hm : b ∈ AddSubgroup.zmultiples μ := by
    rw [← hker]
    exact hq
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  refine ⟨k, connecting_injective (Set.range f) n ?_⟩
  rw [map_zsmul, hw, ← map_zsmul, hk]
  exact hb

end Wikipedia.HopfProblem.DegreeCollapse.IntegralEmbeddingRange
