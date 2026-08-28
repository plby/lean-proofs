import Wikipedia.HopfProblem.DegreeCollapseMutualSheetDeterminants
import Wikipedia.HopfProblem.DegreeCollapseImmersedWhitneyFraming

/-!
# Opposite intrinsic signs for two independent native sheets

Both source orientations and the target orientation are retained. The
actual source-coordinate and forward-tube determinant factors have
positive endpoint products. Thus opposite ordered mutual intersection
signs give the genuine Whitney corner condition. The proof never swaps
one branch at only one endpoint.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare WhitneyPairModel ImmersedSource ImmersedCorner
open OrbitPair.DeterminantSignCover OrbitPair.OrientationWeights

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

def intersectionBit (F : N → M) (x : N) (y : P) : Bool :=
  Bool.xor (Bool.xor (oP.rawSign y) (oN.rawSign x)) (oM.rawSign (F x))

def intersectionSign (F : N → M) (G : P → M) (x : N) (y : P) : Bool :=
  action (jointFrame K F G x y).det (intersectionBit oN oP oM F x y)

theorem weighted_actual_corner_determinant_factor
    {F : N → M} {G : P → M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (tube : TubularBigon (E := E) (range F) (range G) a b k l h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) k)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range G) l)
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G)
    {t : ℝ} (ht : t = 0 ∨ t = 1) {x : N} {y : P}
    (hx : F x = a t) (hy : G y = b t) :
    tube.sheetPairDet d e t *
        (weight (oM.rawSign (F x)) * (forwardTubeFrame J K tube.chart ((2 * t - 1, 0), 0)).det) *
        (weight (oP.rawSign y) * (sourceFrame J e.chart G y).det) *
        (weight (oN.rawSign x) * (sourceFrame J d.chart F x).det) * coordinateScale J K =
      weight (intersectionBit oN oP oM F x y) * (jointFrame K F G x y).det :=
  normalize_source_comparison (oP.rawSign y) (oN.rawSign x) (oM.rawSign (F x))
    (actual_corner_determinant_factor J K tube d e hF hG ht hx hy)

include J in
theorem opposite_signs_imply_opposite_corner_determinants
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
    (hsign : intersectionSign oN oP oM K F G (α 0) (β 0) ≠
      intersectionSign oN oP oM K F G (α 1) (β 1)) :
    tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0 := by
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
  have hnegative := (action_ne_iff_product_neg _ _
    (jointFrame_det_ne_zero K (ht 0 (Or.inl rfl)))
    (jointFrame_det_ne_zero K (ht 1 (Or.inr rfl)))
    (intersectionBit oN oP oM F (α 0) (β 0))
    (intersectionBit oN oP oM F (α 1) (β 1))).mp hsign
  exact negative_product_of_source_comparison
    (weighted_actual_corner_determinant_factor oN oP oM J K tube d e hF hG
      (Or.inl rfl) rfl rfl)
    (weighted_actual_corner_determinant_factor oN oP oM J K tube d e hF hG
      (Or.inr rfl) rfl rfl)
    (coordinateScale_ne_zero J K) hTpos hβpos hαpos hnegative

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets
