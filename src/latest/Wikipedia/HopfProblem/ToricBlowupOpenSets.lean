import Wikipedia.HopfProblem.ToricBlowupCharts
import Wikipedia.HopfProblem.AffineBlowupGluing
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Three open affine blow-ups covering the central toric surface

Each pair of adjacent charts is the actual incidence-model blow-up of
the affine plane. The maps are holomorphic open embeddings, and their
three images cover the compact ray component. This records the local
blow-up geometry without assuming a global projective-plane blow-down.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace

def blowupMap (k : Fin 3) : AffineBlowup.Space → rayDivisor 0 :=
  AffineBlowup.descend (blowupAffine k)

@[simp] theorem blowupMap_affineMap (k : Fin 3) (b : Bool) (z : CoordinateSpace 2) :
    blowupMap k (AffineBlowup.affineMap b z) = blowupAffine k b z :=
  AffineBlowup.descend_affineMap (blowupAffine k) (blowupAffine_crossCoordinates k) b z

theorem blowupMap_injective (k : Fin 3) : Function.Injective (blowupMap k) := by
  apply AffineBlowup.descend_injective (blowupAffine k) (blowupAffine_crossCoordinates k)
  intro b c z w h
  by_cases hbc : b = c
  · subst c
    exact congrArg (AffineBlowup.affineMap b) ((blowupAffine_isOpenEmbedding k b).injective h)
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    exact (AffineBlowup.affineMap_cross_eq_iff b z w).mpr
      ((blowupAffine_cross_eq_iff k b z w).mp h)

theorem blowupMap_holomorphic (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (blowupMap k) :=
  AffineBlowup.descend_holomorphic (blowupAffine k) (blowupAffine_crossCoordinates k) _
    (blowupAffine_holomorphic k)

theorem blowupMap_continuous (k : Fin 3) : Continuous (blowupMap k) :=
  (blowupMap_holomorphic k).continuous

theorem blowupMap_isOpenMap (k : Fin 3) : IsOpenMap (blowupMap k) :=
  AffineBlowup.descend_isOpenMap (blowupAffine k) (blowupAffine_crossCoordinates k)
    (fun b => (blowupAffine_isOpenEmbedding k b).isOpenMap)

theorem blowupMap_isOpenEmbedding (k : Fin 3) : IsOpenEmbedding (blowupMap k) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (blowupMap_continuous k) (blowupMap_injective k) (blowupMap_isOpenMap k)

theorem blowupMap_range (k : Fin 3) : range (blowupMap k) = ⋃ b, range (blowupAffine k b) :=
  AffineBlowup.descend_range (blowupAffine k) (blowupAffine_crossCoordinates k)

theorem blowupMap_jointly_surjective (x : rayDivisor 0) : ∃ k y, blowupMap k y = x := by
  obtain ⟨k, b, z, rfl⟩ := blowupAffine_jointly_surjective x
  exact ⟨k, AffineBlowup.affineMap b z, blowupMap_affineMap k b z⟩

theorem blowupMap_cover : (⋃ k : Fin 3, range (blowupMap k)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨k, y, rfl⟩ := blowupMap_jointly_surjective x
  exact mem_iUnion.mpr ⟨k, mem_range_self y⟩

def blowupOpenSet (k : Fin 3) : TopologicalSpace.Opens (rayDivisor 0) :=
  ⟨range (blowupMap k), (blowupMap_isOpenEmbedding k).isOpen_range⟩

def blowupHomeomorph (k : Fin 3) : AffineBlowup.Space ≃ₜ blowupOpenSet k :=
  (blowupMap_isOpenEmbedding k).isEmbedding.toHomeomorph

@[simp] theorem blowupHomeomorph_apply (k : Fin 3) (x : AffineBlowup.Space) :
    (blowupHomeomorph k x : rayDivisor 0) = blowupMap k x := rfl

def blowupParametrization (k : Fin 3) :
    OpenPartialHomeomorph AffineBlowup.Space (rayDivisor 0) :=
  (blowupMap_isOpenEmbedding k).toOpenPartialHomeomorph (blowupMap k)

@[simp] theorem blowupParametrization_apply (k : Fin 3) (x : AffineBlowup.Space) :
    blowupParametrization k x = blowupMap k x := rfl

@[simp] theorem blowupParametrization_source (k : Fin 3) :
    (blowupParametrization k).source = univ := rfl

@[simp] theorem blowupParametrization_target (k : Fin 3) :
    (blowupParametrization k).target = range (blowupMap k) := by
  simp [blowupParametrization]

@[simp] theorem blowupParametrization_symm_affine (k : Fin 3) (b : Bool)
    (z : CoordinateSpace 2) :
    (blowupParametrization k).symm (blowupAffine k b z) = AffineBlowup.affineMap b z := by
  rw [← blowupMap_affineMap]
  exact (blowupParametrization k).left_inv (mem_univ _)

theorem blowupParametrization_symm_inclusion (k : Fin 3) (b : Bool)
    (z : CoordinateSpace 2) :
    (blowupParametrization k).symm (affineInclusion (zeroChart (blowupIndex k b)) z) =
      AffineBlowup.affineMap b (reorder k b z) := by
  have he : blowupAffine k b (reorder k b z) =
      affineInclusion (zeroChart (blowupIndex k b)) z := by
    unfold blowupAffine
    rw [reorder_involutive]
  rw [← he, blowupParametrization_symm_affine]

theorem blowupParametrization_symm_holomorphic (k : Fin 3) :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (blowupParametrization k).symm
      (range (blowupMap k)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨b, z, rfl⟩ := AffineBlowup.affineMap_jointly_surjective y
  rw [blowupMap_affineMap]
  let c := zeroChart (blowupIndex k b)
  have hc : (parametrization c).symm ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (rayDivisor 0) :=
    IsManifold.subset_maximalAtlas (mem_range_self c)
  have hchart : ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (parametrization c).symm
      (range (affineInclusion c)) := by
    simpa only [OpenPartialHomeomorph.symm_source, parametrization_target] using
      contMDiffOn_of_mem_maximalAtlas hc
  have hcomp := ((AffineBlowup.affineMap_holomorphic b).comp
    (reorder_holomorphic k b).contMDiff).comp_contMDiffOn hchart
  have he : EqOn (blowupParametrization k).symm
      (AffineBlowup.affineMap b ∘ reorder k b ∘ (parametrization c).symm)
      (range (affineInclusion c)) := by
    rintro _ ⟨w, rfl⟩
    change (blowupParametrization k).symm (affineInclusion c w) =
      AffineBlowup.affineMap b (reorder k b ((parametrization c).symm (affineInclusion c w)))
    have hw : (parametrization c).symm (affineInclusion c w) = w :=
      (parametrization c).left_inv (mem_univ w)
    rw [hw]
    exact blowupParametrization_symm_inclusion k b w
  exact ((hcomp.congr he).contMDiffAt
    ((affineInclusion_openEmbedding c).isOpen_range.mem_nhds
      (mem_range_self (reorder k b z)))).contMDiffWithinAt

instance blowupOpenSet_nonempty (k : Fin 3) : Nonempty (blowupOpenSet k) :=
  ⟨⟨blowupMap k (AffineBlowup.left 0), mem_range_self _⟩⟩

theorem blowupHomeomorph_holomorphic (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (blowupHomeomorph k) := by
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω
      (fun y => (blowupHomeomorph k y : rayDivisor 0)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (blowupHomeomorph k) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (blowupMap_holomorphic k x)

theorem blowupHomeomorph_symm_holomorphic (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (blowupHomeomorph k).symm := by
  intro x
  have hEq : (blowupHomeomorph k).symm =
      (blowupParametrization k).symm ∘ (Subtype.val : blowupOpenSet k → rayDivisor 0) := by
    funext y
    obtain ⟨w, rfl⟩ := (blowupHomeomorph k).surjective y
    rw [Homeomorph.symm_apply_apply]
    exact ((blowupParametrization k).left_inv (mem_univ w)).symm
  rw [hEq]
  exact ((blowupParametrization_symm_holomorphic k).contMDiffAt
    ((blowupOpenSet k).isOpen.mem_nhds x.2)).comp _ contMDiff_subtype_val.contMDiffAt

def blowupBiholomorph (k : Fin 3) :
    Diffeomorph (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) AffineBlowup.Space (blowupOpenSet k) ω where
  toEquiv := (blowupHomeomorph k).toEquiv
  contMDiff_toFun := blowupHomeomorph_holomorphic k
  contMDiff_invFun := blowupHomeomorph_symm_holomorphic k

end Wikipedia.HopfProblem.ToricComponent
