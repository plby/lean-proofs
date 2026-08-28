import Wikipedia.NoExoticSixSphere.ManifoldImageDimension
import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Nullhomotopies of lower-dimensional sphere maps

Smooth approximation gives a smooth representative. A lower-dimensional smooth
manifold image omits a point of the target sphere, and stereographic coordinates
then give an explicit contraction. This is a sphere-connectivity result, not an
orthogonal-group homotopy computation or a smooth-sphere classification.
-/

open scoped Manifold ContDiff Topology
open Set Module

namespace NoExoticSixSphere

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

section ChartContraction

open unitInterval

/-- A map with image inside a full Euclidean chart is nullhomotopic. -/
noncomputable def chartContractionHomotopy (f : C(X, Y)) (c : OpenPartialHomeomorph Y E)
    (ht : c.target = univ) (hf : ∀ x, f x ∈ c.source) :
    f.Homotopy (ContinuousMap.const _ (c.symm 0)) where
  toFun p := c.symm ((1 - (p.1 : ℝ)) • c (f p.2))
  continuous_toFun := by
    have hc : Continuous (fun x ↦ c (f x)) := c.continuousOn.comp_continuous f.continuous hf
    have hci : Continuous c.symm := by
      apply continuousOn_univ.mp
      rw [← ht]
      exact c.symm.continuousOn
    exact hci.comp ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (hc.comp continuous_snd))
  map_zero_left x := by
    change c.symm ((1 - (0 : ℝ)) • c (f x)) = f x
    rw [sub_zero, one_smul]
    exact c.left_inv (hf x)
  map_one_left x := by
    change c.symm ((1 - (1 : ℝ)) • c (f x)) = c.symm 0
    rw [sub_self, zero_smul]

/-- An actual omitted sphere point gives a nullhomotopy through stereographic coordinates. -/
theorem sphereMap_nullhomotopic_of_omitted_point (n : ℕ) (f : C(X, Sphere n))
    (p : Sphere n) (hp : ∀ x, f x ≠ p) : ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let c := stereographic' n p
  have hf : ∀ x, f x ∈ c.source := by
    intro x
    simpa only [c, stereographic'_source, mem_compl_iff, mem_singleton_iff] using hp x
  exact ⟨c.symm 0, ⟨chartContractionHomotopy f c (stereographic'_target (n := n) p) hf⟩⟩

end ChartContraction

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I in
/-- Every continuous map from a compact smooth manifold to a higher-dimensional sphere
is nullhomotopic. The original continuous map need not have any differentiability. -/
theorem sphereMap_nullhomotopic_of_dim_lt (n : ℕ) (f : C(M, Sphere n))
    (hd : finrank ℝ B < n) : ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  classical
  obtain ⟨g, hg, hfg⟩ := exists_smoothSphereRepresentative (I := I) n f
  let : Nonempty (Sphere n) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  have hn : ¬ Function.Surjective g := not_surjective_contMDiff_of_dim_lt hg
    (by simpa only [finrank_euclideanSpace_fin] using hd)
  obtain ⟨p, hp⟩ : ∃ p, ∀ x, g x ≠ p := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  obtain ⟨c, hgc⟩ := sphereMap_nullhomotopic_of_omitted_point n g p hp
  exact ⟨c, hfg.trans hgc⟩

/-- Every continuous map from a lower-dimensional standard sphere to a higher-dimensional
standard sphere is nullhomotopic. -/
theorem sphere_sphere_nullhomotopic {m n : ℕ} (hmn : m < n) (f : C(Sphere m, Sphere n)) :
    ∃ c, f.Homotopic (ContinuousMap.const _ c) :=
  sphereMap_nullhomotopic_of_dim_lt (I := 𝓡 m) n f
    (by simpa only [finrank_euclideanSpace_fin] using hmn)

end NoExoticSixSphere
