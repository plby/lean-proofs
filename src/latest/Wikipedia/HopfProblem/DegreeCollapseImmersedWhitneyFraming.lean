import Wikipedia.HopfProblem.DegreeCollapseImmersedCornerOrientation
import Wikipedia.SmoothSixDPoincare.TubularBigonAdaptedChart

/-!
# The actual Whitney normal framing from opposite native crossing signs

The source-coordinate and forward-tube orientation factors have positive
endpoint products. Their exact determinant identity transfers opposite
original crossing signs to the actual tubular corner Jacobians. The
existing frame extension then constructs a genuine normal-adapted chart
for both original branch strips. The opposite native sign condition is
explicit; complementarity alone is not substituted for it.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner

open Wikipedia.SmoothSixDPoincare WhitneyPairModel ImmersedSource
open OrbitPair.DeterminantSignCover OrbitPair.OrientationWeights

variable {G E M N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, G) N))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (J : Sheet ≃L[ℝ] G) (K : (G × G) ≃L[ℝ] E)
  {F : N → M} {U V : Set N} {α β : C(ℝ, N)}
  {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) (F '' U) (F '' V) (F ∘ α) k₀ k₁}
  {l : CleanStripPatch (E := E) (F '' V) (F '' U) (F ∘ β) l₀ l₁}
  (tube : TubularBigon (E := E) (F '' U) (F '' V) (F ∘ α) (F ∘ β) k.map l.map h)
  (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' U) k.map)
  (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (F '' V) l.map)

include J

theorem opposite_native_signs_imply_opposite_corner_determinants
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hα : MapsTo α (Icc (0 : ℝ) 1) (interior U))
    (hβ : MapsTo β (Icc (0 : ℝ) 1) (interior V))
    (ht : ∀ t : ℝ, t = 0 ∨ t = 1 → Surjective
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (β t)).coprod
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (α t))))
    (hsign : intersectionSign oN oM K F (α 0) (β 0) ≠
      intersectionSign oN oM K F (α 1) (β 1)) :
    tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0 := by
  have hαD : MapsTo (F ∘ α) (Icc (0 : ℝ) 1) d.chart.target := by
    intro t htI
    have hh := d.center_mem_target htI
    rwa [k.center t htI] at hh
  have hβD : MapsTo (F ∘ β) (Icc (0 : ℝ) 1) e.chart.target := by
    intro t htI
    have hh := e.center_mem_target htI
    rwa [l.center t htI] at hh
  have hαK (t : ℝ) (htI : t ∈ Icc (0 : ℝ) 1) : U ∈ 𝓝 (α t) :=
    mem_of_superset (isOpen_interior.mem_nhds (hα htI)) interior_subset
  have hβK (t : ℝ) (htI : t ∈ Icc (0 : ℝ) 1) : V ∈ 𝓝 (β t) :=
    mem_of_superset (isOpen_interior.mem_nhds (hβ htI)) interior_subset
  have hαpos := weighted_patch_source_determinants_pos oN d.chart F J hF hi
    isOpen_interior interior_subset d.sheet α.continuous hα hαD
  have hβpos := weighted_patch_source_determinants_pos oN e.chart F J hF hi
    isOpen_interior interior_subset e.sheet β.continuous hβ hβD
  have hTpos := weighted_tube_determinants_pos oM J K tube
  have hnegative := (action_ne_iff_product_neg _ _
    (originalJointFrame_det_ne_zero K (ht 0 (Or.inl rfl)))
    (originalJointFrame_det_ne_zero K (ht 1 (Or.inr rfl)))
    (intersectionBit oN oM F (α 0) (β 0))
    (intersectionBit oN oM F (α 1) (β 1))).mp hsign
  exact negative_product_of_source_comparison
    (weighted_actual_corner_determinant_factor oN oM J K tube d e hF (Or.inl rfl)
      (hαK 0 (by simp)) (hβK 0 (by simp)) rfl rfl)
    (weighted_actual_corner_determinant_factor oN oM J K tube d e hF (Or.inr rfl)
      (hαK 1 (by simp)) (hβK 1 (by simp)) rfl rfl)
    (coordinateScale_ne_zero J K) hTpos hβpos hαpos hnegative

/-- Both original boundary frames extend to an actual normal-adapted tubular chart. -/
theorem nonempty_normalAdaptedChart_of_opposite_native_signs
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hα : MapsTo α (Icc (0 : ℝ) 1) (interior U))
    (hβ : MapsTo β (Icc (0 : ℝ) 1) (interior V))
    (ht : ∀ t : ℝ, t = 0 ∨ t = 1 → Surjective
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (β t)).coprod
        (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (α t))))
    (hsign : intersectionSign oN oM K F (α 0) (β 0) ≠
      intersectionSign oN oM K F (α 1) (β 1)) :
    Nonempty (TubularBigon.NormalAdaptedChart tube d e) :=
  tube.nonempty_normalAdaptedChart_of_opposite_corner_signs d e
    (opposite_native_signs_imply_opposite_corner_determinants oN oM J K tube d e
      hF hi hα hβ ht hsign)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedCorner
