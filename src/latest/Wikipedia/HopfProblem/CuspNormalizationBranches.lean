import Wikipedia.HopfProblem.ToricComponentManifold

/-!
# Affine branches of the cusp normalization map

Translating a coordinate plane in an arbitrary toric chart to the component
at the origin gives an analytic affine chart of that component. On the
central fibre the multiplier is frozen at zero, so these charts need no
regularity assumption on the matrix-valued function `C`. The actual cusp
quotient projection on each chart is the corresponding coordinate-plane
map in the original toric chart.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace ToricComponent

/-- Insert the vanishing coordinate of an affine branch of the central fibre. -/
def centralPlane (j : Fin 3) (z : CoordinateSpace 2) : centralAffine :=
  ⟨insertZero j z, by
    change Triangle.time (insertZero j z) = 0
    have h := time_eq_zero_of_mem_rayDivisor
      ((mem_rayDivisor_vertex (⟨0, 0, false⟩ : Triangle) j (insertZero j z)).mpr
        (insertZero_at j z))
    simpa only [time_inclusion] using h⟩

@[simp] theorem centralPlane_coe (j : Fin 3) (z : CoordinateSpace 2) :
    (centralPlane j z : CoordinateSpace 3) = insertZero j z := rfl

theorem centralPlane_continuous (j : Fin 3) : Continuous (centralPlane j) :=
  (insertZero_holomorphic j).continuous.subtype_mk _

@[simp] theorem time_insertZero (j : Fin 3) (z : CoordinateSpace 2) :
    Triangle.time (insertZero j z) = 0 := (centralPlane j z).2

/-- The translated toric chart in which the selected ray is the origin. -/
def branchChartIndex (s : Triangle) (j : Fin 3) : ChartIndex 0 where
  triangle := s.shift (-s.vertex j)
  coordinate := j
  vertex_eq := by simp

def branchFactors (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) : CoordinateSpace 2 :=
  fun k => factors (s.shift (-s.vertex j))
    (fibreMultiplier (exponentialMultiplier C (cuspVector (s.vertex j)) 0)) (j.succAbove k)

theorem branchFactors_nonzero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (k : Fin 2) : branchFactors C s j k ≠ 0 :=
  factors_nonzero _ _ _

def branchScale (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  branchFactors C s j * z

def branchScaleInv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  fun k => (branchFactors C s j k)⁻¹ * z k

theorem branchScale_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) : ContDiff ℂ ω (branchScale C s j) := by
  apply contDiff_pi.mpr
  intro k
  exact contDiff_const.mul (contDiff_apply ℂ ℂ k)

theorem branchScaleInv_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) : ContDiff ℂ ω (branchScaleInv C s j) := by
  apply contDiff_pi.mpr
  intro k
  exact contDiff_const.mul (contDiff_apply ℂ ℂ k)

def branchScaleHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) : CoordinateSpace 2 ≃ₜ CoordinateSpace 2 where
  toFun := branchScale C s j
  invFun := branchScaleInv C s j
  left_inv z := by
    ext k
    simp [branchScale, branchScaleInv, branchFactors_nonzero]
  right_inv z := by
    ext k
    simp [branchScale, branchScaleInv, branchFactors_nonzero]
  continuous_toFun := (branchScale_holomorphic C s j).continuous
  continuous_invFun := (branchScaleInv_holomorphic C s j).continuous

/-- The actual affine branch, translated by the twisted lattice action to `E₀`. -/
def branchAffine (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) : rayDivisor 0 :=
  affineInclusion (branchChartIndex s j) (branchScale C s j z)

theorem branchAffine_openEmbedding (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) : IsOpenEmbedding (branchAffine C s j) :=
  (affineInclusion_openEmbedding _).comp (branchScaleHomeomorph C s j).isOpenEmbedding

theorem branchAffine_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) : Continuous (branchAffine C s j) :=
  (branchAffine_openEmbedding C s j).continuous

theorem branchAffine_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (branchAffine C s j) :=
  (affineInclusion_holomorphic _).comp (branchScale_holomorphic C s j).contMDiff

theorem branchAffine_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) :
    (branchAffine C s j z : Space) =
      twistedTranslate C (cuspVector (s.vertex j)) (inclusion s (insertZero j z)) := by
  rw [twistedTranslate, translate_inclusion, variableMultiplier_inclusion,
    cuspVector_cuspVector, time_insertZero]
  change inclusion (s.shift (-s.vertex j)) (insertZero j (branchScale C s j z)) =
    inclusion (s.shift (-s.vertex j)) (scale (s.shift (-s.vertex j))
      (fibreMultiplier (exponentialMultiplier C (cuspVector (s.vertex j)) 0)) (insertZero j z))
  congr 1
  ext k
  obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · simp [scale]
  · simp [insertZero, branchScale, branchFactors, scale, Fin.insertNth_apply_succAbove]

theorem branchAffine_coe_centralTranslation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) :
    (branchAffine C s j z : Space) =
      centralTranslationHomeomorph C (cuspVector (s.vertex j))
        (inclusion s (insertZero j z)) := by
  rw [centralTranslationHomeomorph_eq_twistedTranslate C _ _
    (by rw [time_inclusion, time_insertZero])]
  exact branchAffine_coe C s j z

def branchParametrization (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    OpenPartialHomeomorph (CoordinateSpace 2) (rayDivisor 0) :=
  (branchScaleHomeomorph C s j).toOpenPartialHomeomorph.trans
    (ToricComponent.parametrization (branchChartIndex s j))

@[simp] theorem branchParametrization_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) :
    branchParametrization C s j z = branchAffine C s j z := rfl

@[simp] theorem branchParametrization_source (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) : (branchParametrization C s j).source = univ := by
  simp [branchParametrization]

theorem branchAffine_range (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    range (branchAffine C s j) = range (affineInclusion (branchChartIndex s j)) := by
  change range (affineInclusion (branchChartIndex s j) ∘ branchScaleHomeomorph C s j) = _
  rw [Set.range_comp, (branchScaleHomeomorph C s j).surjective.range_eq, Set.image_univ]

@[simp] theorem branchParametrization_target (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    (branchParametrization C s j).target = range (branchAffine C s j) := by
  simp [branchParametrization, branchAffine_range]

theorem branchAffine_mem_range_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) (x : rayDivisor 0) :
    x ∈ range (branchAffine C s j) ↔
      (x : Space) ∈ centralTranslationHomeomorph C (cuspVector (s.vertex j)) ''
        range (inclusion s) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨inclusion s (insertZero j z), mem_range_self _,
      (branchAffine_coe_centralTranslation C s j z).symm⟩
  · rintro ⟨_, ⟨w, rfl⟩, hw⟩
    have hx : 0 ∈ branchVertices
        (centralTranslationHomeomorph C (cuspVector (s.vertex j)) (inclusion s w)) := by
      rw [hw]
      exact x.2
    rw [branchVertices_centralTranslationHomeomorph, cuspVector_cuspVector] at hx
    obtain ⟨v, hv, he⟩ := hx
    have hve : v = s.vertex j := by simpa only [add_neg_eq_zero] using he
    have hwj : w j = 0 := (mem_rayDivisor_vertex s j w).mp (by rwa [← hve])
    refine ⟨removeCoordinate j w, Subtype.ext ?_⟩
    rw [branchAffine_coe_centralTranslation, insertZero_removeCoordinate j w hwj]
    exact hw

theorem branchParametrization_target_image (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    (branchParametrization C s j).target =
      (Subtype.val : rayDivisor 0 → Space) ⁻¹'
        (centralTranslationHomeomorph C (cuspVector (s.vertex j)) '' range (inclusion s)) := by
  rw [branchParametrization_target]
  ext x
  exact branchAffine_mem_range_iff C s j x

theorem branchParametrization_symm_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (branchParametrization C s j).symm
      (range (branchAffine C s j)) := by
  change ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
    (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω
    (branchScaleInv C s j ∘ (ToricComponent.parametrization (branchChartIndex s j)).symm)
    (range (branchAffine C s j))
  have hc : (ToricComponent.parametrization (branchChartIndex s j)).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (rayDivisor 0) :=
    IsManifold.subset_maximalAtlas (mem_range_self (branchChartIndex s j))
  have hh := (branchScaleInv_holomorphic C s j).contMDiff.comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas hc)
  simpa only [OpenPartialHomeomorph.symm_source, ToricComponent.parametrization_target,
    branchAffine_range] using hh

theorem branchChart_mem_maximalAtlas (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : Triangle) (j : Fin 3) :
    (branchParametrization C s j).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (rayDivisor 0) := by
  apply (branchParametrization C s j).symm.mem_maximalAtlas_of_contMDiffOn
  · simpa only [OpenPartialHomeomorph.symm_source, branchParametrization_target] using
      branchParametrization_symm_holomorphic C s j
  · exact (branchAffine_holomorphic C s j).contMDiffOn

theorem componentLift_branchAffine (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) :
    componentLift ε hε (branchAffine C s j z) =
      tubeTranslate C (disc ε) (cuspVector (s.vertex j))
        (centralLift ε hε s (centralPlane j z)) :=
  Subtype.ext (branchAffine_coe C s j z)

@[simp] theorem componentProjection_branchAffine (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (s : Triangle) (j : Fin 3) (z : CoordinateSpace 2) :
    componentProjection C ε hε (branchAffine C s j z) =
      centralChartMap C ε hε s (centralPlane j z) := by
  change quotientMap C ε (componentLift ε hε (branchAffine C s j z)) = _
  rw [componentLift_branchAffine, quotientMap_translate]
  rfl

end Wikipedia.HopfProblem.CuspQuotient
