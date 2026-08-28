import Wikipedia.HopfProblem.DegreeCollapseMutualSheetSigns

/-!
# The actual Whitney corner condition also detects opposite intrinsic signs

Use the exact native determinant comparison in the reverse direction.
All coordinate factors have positive endpoint products, so a negative
corner product forces the original two ordered intersection signs to
differ. Together with the earlier implication this is an equivalence.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare WhitneyPairModel ImmersedSource ImmersedCorner
open OrbitPair.DeterminantSignCover OrbitPair.OrientationWeights

theorem source_product_negative_of_corner_product
    {m₀ m₁ c₀ c₁ a₀ a₁ b₀ b₁ d₀ d₁ k : ℝ}
    (h₀ : m₀ * c₀ * a₀ * b₀ * k = d₀) (h₁ : m₁ * c₁ * a₁ * b₁ * k = d₁)
    (hk : k ≠ 0) (hc : 0 < c₀ * c₁) (ha : 0 < a₀ * a₁) (hb : 0 < b₀ * b₁)
    (hm : m₀ * m₁ < 0) : d₀ * d₁ < 0 := by
  have he : (m₀ * m₁) * ((c₀ * c₁) * (a₀ * a₁) * (b₀ * b₁) * k ^ 2) = d₀ * d₁ := by
    calc
      _ = (m₀ * c₀ * a₀ * b₀ * k) * (m₁ * c₁ * a₁ * b₁ * k) := by ring
      _ = _ := congrArg₂ (· * ·) h₀ h₁
  have hs : 0 < (c₀ * c₁) * (a₀ * a₁) * (b₀ * b₁) * k ^ 2 :=
    mul_pos (mul_pos (mul_pos hc ha) hb) (sq_pos_of_ne_zero hk)
  exact he ▸ mul_neg_of_neg_of_pos hm hs

variable {D E M N P : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  (oN : Orientation (tangentBundleCore 𝓘(ℝ, D) N))
  (oP : Orientation (tangentBundleCore 𝓘(ℝ, D) P))
  (oM : Orientation (tangentBundleCore 𝓘(ℝ, E) M))
  (J : Sheet ≃L[ℝ] D) (K : (D × D) ≃L[ℝ] E)

include J in
theorem opposite_corners_imply_opposite_signs
    {F : N → M} {G : P → M} {α : C(ℝ, N)} {β : C(ℝ, P)}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : CleanStripPatch (E := E) (range F) (range G) (F ∘ α) k₀ k₁}
    {l : CleanStripPatch (E := E) (range G) (range F) (G ∘ β) l₀ l₁}
    (tube : TubularBigon (E := E) (range F) (range G) (F ∘ α) (G ∘ β) k.map l.map h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) k.map)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range G) l.map)
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G)
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (ht : ∀ t : ℝ, t = 0 ∨ t = 1 → Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G (β t)).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (α t))))
    (hcorner : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    intersectionSign oN oP oM K F G (α 0) (β 0) ≠
      intersectionSign oN oP oM K F G (α 1) (β 1) := by
  have hαD : MapsTo (F ∘ α) (Icc (0 : ℝ) 1) d.chart.target := by
    intro t htI
    have hh := d.center_mem_target htI
    rwa [k.center t htI] at hh
  have hβD : MapsTo (G ∘ β) (Icc (0 : ℝ) 1) e.chart.target := by
    intro t htI
    have hh := e.center_mem_target htI
    rwa [l.center t htI] at hh
  have hdclean : ∀ q ∈ d.chart.source, d.chart q ∈ F '' (univ : Set N) ↔ q.2 = 0 := by
    simpa only [image_univ] using d.sheet
  have heclean : ∀ q ∈ e.chart.source, e.chart q ∈ G '' (univ : Set P) ↔ q.2 = 0 := by
    simpa only [image_univ] using e.sheet
  have hαpos := weighted_patch_source_determinants_pos oN d.chart F J hF hiF
    isOpen_univ (Subset.refl univ) hdclean α.continuous (mapsTo_univ _ _) hαD
  have hβpos := weighted_patch_source_determinants_pos oP e.chart G J hG hiG
    isOpen_univ (Subset.refl univ) heclean β.continuous (mapsTo_univ _ _) hβD
  have hTpos := ImmersedCorner.weighted_tube_determinants_pos oM J K tube
  have hnegative := source_product_negative_of_corner_product
    (weighted_actual_corner_determinant_factor oN oP oM J K tube d e hF hG
      (Or.inl rfl) rfl rfl)
    (weighted_actual_corner_determinant_factor oN oP oM J K tube d e hF hG
      (Or.inr rfl) rfl rfl)
    (coordinateScale_ne_zero J K) hTpos hβpos hαpos hcorner
  exact (action_ne_iff_product_neg _ _
    (jointFrame_det_ne_zero K (ht 0 (Or.inl rfl)))
    (jointFrame_det_ne_zero K (ht 1 (Or.inr rfl)))
    (intersectionBit oN oP oM F (α 0) (β 0))
    (intersectionBit oN oP oM F (α 1) (β 1))).mpr hnegative

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets
