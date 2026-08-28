import Wikipedia.HopfProblem.DegreeCollapseSevenHalfExteriorQuotients

/-!
# The actual twisted surgery homology and its integral meridian relation

The old half is the common exterior modulo its meridian class. The new
half for a column multiplier j is the same exterior modulo epsilon+j*mu.
Both quotient maps are the genuine geometric maps on singular homology.
An annihilator of the actual old attaching class supplies the integral
relation l*epsilon+l'*mu=0 and its exact change under the twist.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist

open NoExoticSixSphere GLOrthonormalization OrthogonalPaths
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

theorem sphere_linear_range {H : Type} [AddCommGroup H] [Module ℤ H]
    (L : SingularHomology (Sphere 3) 3 →ₗ[ℤ] H) :
    LinearMap.range L = Submodule.span ℤ {L (unitSphereTopClass 2)} := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨k, rfl⟩ := unitSphereTopClass_generates 2 c
    rw [map_zsmul]
    exact Submodule.mem_span_singleton.mpr
      ⟨k, int_smul_eq_zsmul (inferInstance : Module ℤ H) k (L (unitSphereTopClass 2))⟩
  · intro hx
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨k • unitSphereTopClass 2, ?_⟩
    rw [map_zsmul]
    exact (int_smul_eq_zsmul (inferInstance : Module ℤ H) k (L (unitSphereTopClass 2))).symm.trans hk

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hA : A.radius = 2) (T : TimeData A)

def halfSectionClass (v : Sphere 3) : SingularHomology (HalfExterior A hA T) 3 :=
  singularHomologyMap (halfSectionMap A hA T v) 3 (unitSphereTopClass 2)

def halfMeridianClass (s : Sphere 3) : SingularHomology (HalfExterior A hA T) 3 :=
  singularHomologyMap (halfMeridianMap A hA T s) 3 (unitSphereTopClass 2)

theorem halfOld_kernel_span (s : Sphere 3) :
    LinearMap.ker (singularHomologyMap (halfOldInclusion A hA T) 3) =
      Submodule.span ℤ {halfMeridianClass A hA T s} := by
  rw [← halfMeridian_range_eq_old_kernel A hA T s]
  exact sphere_linear_range _

theorem halfNew_kernel_span (v : Sphere 3) :
    LinearMap.ker (singularHomologyMap (halfNewInclusion A hA T) 3) =
      Submodule.span ℤ {halfSectionClass A hA T v} := by
  rw [← halfSection_range_eq_new_kernel A hA T v]
  exact sphere_linear_range _

theorem exists_meridian_relation (v s : Sphere 3) (l : ℤ)
    (hl : l • singularHomologyMap (halfBoundaryPair A hA T).attachingSphere 3
      (unitSphereTopClass 2) = 0) :
    ∃ l' : ℤ, l • halfSectionClass A hA T v + l' • halfMeridianClass A hA T s = 0 := by
  have he : l • halfSectionClass A hA T v ∈
      LinearMap.ker (singularHomologyMap (halfOldInclusion A hA T) 3) := by
    change singularHomologyMap (halfOldInclusion A hA T) 3
      (l • singularHomologyMap (halfSectionMap A hA T v) 3 (unitSphereTopClass 2)) = 0
    rw [map_zsmul, halfOldInclusion_section]
    exact hl
  rw [halfOld_kernel_span A hA T s] at he
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp he
  refine ⟨-k, ?_⟩
  have hk' : k • halfMeridianClass A hA T s = l • halfSectionClass A hA T v :=
    (int_smul_eq_zsmul (SingularHomology (HalfExterior A hA T) 3).isModule k _).symm.trans hk
  rw [neg_zsmul, ← hk', add_neg_cancel]

variable (B : FramedAttachingProduct e a f) (hB : B.radius = 2)
  (ρ : C(Sphere 3, OrthogonalOperators 4))
  (ht : ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w))

def halfTwistedNewMap : SingularHomology (HalfExterior A hA T) 3 →ₗ[ℤ]
    SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3 :=
  (singularHomologyMap (halfNewInclusion B hB (twistTimeData A hA B hB ρ ht T)) 3).comp
    (homeomorphHomologyEquiv (halfExteriorHomeomorph A hA B hB ρ ht T) 3).symm.toLinearMap

theorem halfTwistedNewMap_surjective : Surjective (halfTwistedNewMap A hA T B hB ρ ht) :=
  (halfNewInclusion_surjective B hB (twistTimeData A hA B hB ρ ht T)).comp
    (homeomorphHomologyEquiv (halfExteriorHomeomorph A hA B hB ρ ht T) 3).symm.surjective

theorem halfSectionClass_twist (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3, singularHomologyMap (column v ρ) 3 c = j • c) :
    homeomorphHomologyEquiv (halfExteriorHomeomorph A hA B hB ρ ht T) 3
      (halfSectionClass B hB (twistTimeData A hA B hB ρ ht T) v) =
        halfSectionClass A hA T v + j • halfMeridianClass A hA T s :=
  halfSection_homology_twist_of_multiplier A hA B hB ρ ht T v s j hρ (unitSphereTopClass 2)

theorem halfTwistedNewMap_kernel (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3, singularHomologyMap (column v ρ) 3 c = j • c) :
    LinearMap.ker (halfTwistedNewMap A hA T B hB ρ ht) =
      Submodule.span ℤ {halfSectionClass A hA T v + j • halfMeridianClass A hA T s} := by
  let H := homeomorphHomologyEquiv (halfExteriorHomeomorph A hA B hB ρ ht T) 3
  have hg : H (halfSectionClass B hB (twistTimeData A hA B hB ρ ht T) v) =
      halfSectionClass A hA T v + j • halfMeridianClass A hA T s :=
    halfSectionClass_twist A hA T B hB ρ ht v s j hρ
  ext x
  change singularHomologyMap (halfNewInclusion B hB (twistTimeData A hA B hB ρ ht T)) 3
    (H.symm x) = 0 ↔ _
  constructor
  · intro hx
    have hx' : H.symm x ∈ LinearMap.ker
        (singularHomologyMap (halfNewInclusion B hB (twistTimeData A hA B hB ρ ht T)) 3) := hx
    rw [halfNew_kernel_span B hB (twistTimeData A hA B hB ρ ht T) v] at hx'
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx'
    apply Submodule.mem_span_singleton.mpr
    refine ⟨k, ?_⟩
    have h := congrArg H hk
    rw [H.map_smul, hg, LinearEquiv.apply_symm_apply] at h
    exact h
  · intro hx
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hx
    have hx' : H.symm x ∈ Submodule.span ℤ
        {halfSectionClass B hB (twistTimeData A hA B hB ρ ht T) v} := by
      apply Submodule.mem_span_singleton.mpr
      refine ⟨k, ?_⟩
      apply H.injective
      rw [H.map_smul, hg, LinearEquiv.apply_symm_apply]
      exact hk
    rw [← halfNew_kernel_span B hB (twistTimeData A hA B hB ρ ht T) v] at hx'
    exact hx'

def halfTwistedNewQuotientEquiv (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3, singularHomologyMap (column v ρ) 3 c = j • c) :
    (SingularHomology (HalfExterior A hA T) 3 ⧸
      Submodule.span ℤ {halfSectionClass A hA T v + j • halfMeridianClass A hA T s}) ≃ₗ[ℤ]
        SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3 := by
  let q := (Submodule.quotEquivOfEq _ _ (halfTwistedNewMap_kernel A hA T B hB ρ ht v s j hρ).symm).trans
    ((halfTwistedNewMap A hA T B hB ρ ht).quotKerEquivOfSurjective
      (halfTwistedNewMap_surjective A hA T B hB ρ ht))
  let qa : (SingularHomology (HalfExterior A hA T) 3 ⧸
      Submodule.span ℤ {halfSectionClass A hA T v + j • halfMeridianClass A hA T s}) ≃+
        SingularHomology (PositiveHalf B hB (twistTimeData A hA B hB ρ ht T)) 3 :=
    { toEquiv := q.toEquiv, map_add' := fun x y ↦ q.map_add' x y }
  exact qa.toIntLinearEquiv

theorem halfTwistedNewQuotientEquiv_mk (v s : Sphere 3) (j : ℤ)
    (hρ : ∀ c : SingularHomology (Sphere 3) 3, singularHomologyMap (column v ρ) 3 c = j • c)
    (x : SingularHomology (HalfExterior A hA T) 3) :
    halfTwistedNewQuotientEquiv A hA T B hB ρ ht v s j hρ (Submodule.Quotient.mk x) =
      halfTwistedNewMap A hA T B hB ρ ht x := by
  change (halfTwistedNewMap A hA T B hB ρ ht).quotKerEquivOfSurjective
    (halfTwistedNewMap_surjective A hA T B hB ρ ht)
    (Submodule.quotEquivOfEq _ _ (halfTwistedNewMap_kernel A hA T B hB ρ ht v s j hρ).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem twisted_meridian_relation (v s : Sphere 3) (l l' j : ℤ)
    (h : l • halfSectionClass A hA T v + l' • halfMeridianClass A hA T s = 0) :
    l • (halfSectionClass A hA T v + j • halfMeridianClass A hA T s) +
      (l' - l * j) • halfMeridianClass A hA T s = 0 := by
  calc
    _ = l • halfSectionClass A hA T v + l' • halfMeridianClass A hA T s := by
      rw [zsmul_add, sub_zsmul, mul_zsmul]
      abel
    _ = 0 := h

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery.ExteriorTwist
