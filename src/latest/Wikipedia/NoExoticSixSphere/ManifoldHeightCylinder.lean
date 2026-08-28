import Wikipedia.NoExoticSixSphere.ManifoldHeightNormalFrame

/-!
# The original manifold cylinder in the stabilized ambient space

The cylinder keeps the original Euclidean embedding, uses the distinguished
height coordinate, and has zero graph coordinates. The whole cylinder and
its closed slabs are closed embedded, without a compactness assumption on
the original manifold or any change to its topology or atlas.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization StabilizedSpanningDisk

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)

def heightCylinder (p : M × ℝ) : Vector (e.ambientDimension + 6) :=
  coordinates e.ambientDimension 4 ((e.toFun p.1, p.2), 0)

theorem continuous_heightCylinder : Continuous e.heightCylinder :=
  (coordinates e.ambientDimension 4).continuous.comp
    (((e.closedEmbedding.continuous.comp continuous_fst).prodMk continuous_snd).prodMk
      continuous_const)

theorem injective_heightCylinder : Injective e.heightCylinder := by
  intro p q h
  have he := (coordinates e.ambientDimension 4).injective h
  have hm : e.toFun p.1 = e.toFun q.1 := congrArg (fun z ↦ z.1.1) he
  have ht : p.2 = q.2 := congrArg (fun z ↦ z.1.2) he
  exact Prod.ext (e.closedEmbedding.injective hm) ht

theorem isEmbedding_heightCylinder : IsEmbedding e.heightCylinder :=
  (coordinates e.ambientDimension 4).toHomeomorph.isEmbedding.comp
    ((isEmbedding_prodMkLeft (0 : ℝ × Vector 4)).comp
      (e.closedEmbedding.isEmbedding.prodMap (IsEmbedding.id : IsEmbedding (id : ℝ → ℝ))))

theorem heightCylinder_zero (m : M) :
    e.heightCylinder (m, 0) = appendZeroMap e.ambientDimension 6 (e.toFun m) :=
  coordinates_old e.ambientDimension 4 (e.toFun m)

theorem isClosedEmbedding_heightCylinder : IsClosedEmbedding e.heightCylinder := by
  have hz : IsClosedEmbedding
      (fun p : Vector e.ambientDimension × ℝ ↦ (p, (0 : ℝ × Vector 4))) := by
    refine ⟨isEmbedding_prodMkLeft _, ?_⟩
    have he : range (fun p : Vector e.ambientDimension × ℝ ↦ (p, (0 : ℝ × Vector 4))) =
        {p : (Vector e.ambientDimension × ℝ) × (ℝ × Vector 4) | p.2 = 0} := by
      ext p
      constructor
      · rintro ⟨q, rfl⟩
        rfl
      · intro hp
        exact ⟨p.1, Prod.ext rfl hp.symm⟩
    rw [he]
    exact isClosed_eq continuous_snd continuous_const
  exact (coordinates e.ambientDimension 4).toHomeomorph.isClosedEmbedding.comp
    (hz.comp (e.closedEmbedding.prodMap (IsClosedEmbedding.id :
      IsClosedEmbedding (id : ℝ → ℝ))))

theorem closedEmbedding_heightCylinder_slab (l u : ℝ) :
    IsClosedEmbedding (fun p : M × Icc l u ↦ e.heightCylinder (p.1, p.2.val)) :=
  e.isClosedEmbedding_heightCylinder.comp
    ((IsClosedEmbedding.id : IsClosedEmbedding (id : M → M)).prodMap
      isClosed_Icc.isClosedEmbedding_subtypeVal)

theorem isClosedEmbedding_heightSlice (t : ℝ) :
    IsClosedEmbedding (fun m : M ↦ e.heightCylinder (m, t)) := by
  have hj : IsClosedEmbedding (fun m : M ↦ (m, t)) := by
    refine ⟨isEmbedding_prodMkLeft _, ?_⟩
    have he : range (fun m : M ↦ (m, t)) = {p : M × ℝ | p.2 = t} := by
      ext p
      constructor
      · rintro ⟨m, rfl⟩
        rfl
      · intro hp
        exact ⟨p.1, Prod.ext rfl hp.symm⟩
    rw [he]
    exact isClosed_eq continuous_snd continuous_const
  exact e.isClosedEmbedding_heightCylinder.comp hj

end NoExoticSixSphere.EuclideanEmbedding
