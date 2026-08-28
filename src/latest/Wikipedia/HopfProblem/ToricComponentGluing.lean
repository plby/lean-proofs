import Wikipedia.HopfProblem.ToricComponentTopology

/-!
# Gluing maps on a toric ray surface

Compatible maps on the affine charts descend to the actual surface.
For continuous maps to a Hausdorff space, compatibility can be checked
on the dense two-dimensional torus, including when chart overlaps
contain boundary points.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

theorem zeroCount_insertZero_eq_one_iff (j : Fin 3) (z : CoordinateSpace 2) :
    zeroCount (insertZero j z) = 1 ↔ z ∈ torus := by
  constructor
  · intro h i hi
    have htwo : 2 ≤ zeroCount (insertZero j z) :=
      (zeroCount_ge_two_iff _).mpr ⟨j, j.succAbove i, (Fin.succAbove_ne j i).symm,
        insertZero_at j z, by simpa only [insertZero, Fin.insertNth_apply_succAbove] using hi⟩
    omega
  · intro hz
    rw [← vanishingIndices_card]
    have he : vanishingIndices (insertZero j z) = {j} := by
      ext k
      rw [mem_vanishingIndices, Finset.mem_singleton]
      constructor
      · intro hk
        by_contra hkj
        exact insertZero_ne_of_ne j hz hkj hk
      · rintro rfl
        exact insertZero_at _ _
    rw [he, Finset.card_singleton]

variable {v : Fin 2 → ℤ}

theorem torus_of_affineInclusion_eq (c d : ChartIndex v) {z w : CoordinateSpace 2}
    (hz : z ∈ torus) (he : affineInclusion c z = affineInclusion d w) : w ∈ torus := by
  apply (zeroCount_insertZero_eq_one_iff d.coordinate w).mp
  have h := congrArg (fun x : rayDivisor v => branchCount (x : Space)) he
  simp only [affineInclusion_coe, branchCount_inclusion] at h
  rw [← h]
  exact (zeroCount_insertZero_eq_one_iff c.coordinate z).mpr hz

variable {Y : Type*} (f : ChartIndex v → CoordinateSpace 2 → Y)
    (hf : ∀ c d z w, affineInclusion c z = affineInclusion d w → f c z = f d w)

def descend (x : rayDivisor v) : Y :=
  f (preferredIndex v x) ((parametrization (preferredIndex v x)).symm x)

include hf

theorem descend_affineInclusion (c : ChartIndex v) (z : CoordinateSpace 2) :
    descend f (affineInclusion c z) = f c z := by
  apply hf
  exact (parametrization (preferredIndex v (affineInclusion c z))).right_inv
    (by rw [parametrization_target]; exact preferred_mem v (affineInclusion c z))

theorem descend_holomorphic {F H : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    (I : ModelWithCorners ℂ F H)
    (hhol : ∀ c, ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω (f c)) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω (descend f) := by
  apply contMDiff_of_comp_affineInclusions
  intro c
  have he : descend f ∘ affineInclusion c = f c := by
    funext z
    exact descend_affineInclusion f hf c z
  rw [he]
  exact hhol c

omit hf

variable [TopologicalSpace Y] [T2Space Y]

theorem compatible_of_torus (hcont : ∀ c, Continuous (f c))
    (htorus : ∀ c d z w, z ∈ torus → w ∈ torus →
      affineInclusion c z = affineInclusion d w → f c z = f d w)
    (c d : ChartIndex v) (z w : CoordinateSpace 2)
    (he : affineInclusion c z = affineInclusion d w) : f c z = f d w := by
  let U := affineInclusion c ⁻¹' range (affineInclusion d)
  let g := f d ∘ (parametrization d).symm ∘ affineInclusion c
  have hU : IsOpen U := (affineInclusion_openEmbedding d).isOpen_range.preimage
    (affineInclusion_openEmbedding c).continuous
  have hg : ContinuousOn g U := (hcont d).comp_continuousOn
    ((parametrization d).symm.continuousOn.comp
      (affineInclusion_openEmbedding c).continuous.continuousOn (fun x hx => by
        change affineInclusion c x ∈ (parametrization d).target
        rw [parametrization_target]
        exact hx))
  have htor : EqOn (f c) g (U ∩ torus) := by
    intro x hx
    obtain ⟨y, hy⟩ := hx.1
    have hi : (parametrization d).symm (affineInclusion c x) = y := by
      rw [← hy]
      exact (parametrization d).left_inv (mem_univ y)
    change f c x = f d ((parametrization d).symm (affineInclusion c x))
    rw [hi]
    exact htorus c d x y hx.2 (torus_of_affineInclusion_eq c d hx.2 hy.symm) hy.symm
  have hall : EqOn (f c) g U := htor.of_subset_closure
    (hcont c).continuousOn hg inter_subset_left (torus_dense.open_subset_closure_inter hU)
  have hi : (parametrization d).symm (affineInclusion c z) = w := by
    rw [he]
    exact (parametrization d).left_inv (mem_univ w)
  have h := hall (show z ∈ U from ⟨w, he.symm⟩)
  change f c z = f d ((parametrization d).symm (affineInclusion c z)) at h
  rwa [hi] at h

theorem compatible_of_reference_torus (c₀ : ChartIndex v)
    (hcont : ∀ c, Continuous (f c))
    (href : ∀ c z, z ∈ torus →
      f c z = f c₀ ((parametrization c₀).symm (affineInclusion c z)))
    (c d : ChartIndex v) (z w : CoordinateSpace 2)
    (he : affineInclusion c z = affineInclusion d w) : f c z = f d w := by
  apply compatible_of_torus f hcont ?_ c d z w he
  intro c d z w hz hw he
  rw [href c z hz, href d w hw, he]

end Wikipedia.HopfProblem.ToricComponent
