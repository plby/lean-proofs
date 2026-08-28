import Wikipedia.NoExoticSixSphere.NormalizedFramedCollapseData
import Wikipedia.NoExoticSixSphere.OnePointProductMap

/-!
# Actual collapse data for an affine product stabilization

Explicit ambient and normal coordinates identify the new embedding and
frame with the old ones plus a Euclidean factor. The resulting map is the
literal product compactification of the radius-normalized old collapse,
conjugated by these coordinates. The geometric coordinate identities are
explicit inputs to this general construction.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.AffineProductCollapse

abbrev V (j : ℕ) := EuclideanSpace ℝ (Fin j)

variable {n q : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (V n) M]
  {e e' : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  {a' : SmoothRangeFrame (𝓡 n) e'.normalProjection e'.NormalModel}
  (d : e.FramedCollapseData a)
  (S : V e'.ambientDimension ≃L[ℝ] (V e.ambientDimension × V q))
  (C : e'.NormalModel ≃L[ℝ] (e.NormalModel × V q)) (b : V e'.ambientDimension)

def ambientCoordinates : V e'.ambientDimension ≃ₜ (V e.ambientDimension × V q) :=
  (Homeomorph.addRight (-b)).trans S.toHomeomorph

theorem ambientCoordinates_apply (y : V e'.ambientDimension) :
    ambientCoordinates S b y = S (y - b) := by simp [ambientCoordinates, sub_eq_add_neg]

def productMap : C(OnePoint (V e'.ambientDimension), OnePoint e'.NormalModel) :=
  C.symm.toHomeomorph.onePointCongr.toHomotopyEquiv.toFun.comp
    ((OnePointProduct.productMap d.normalizedMap (ContinuousMap.id (OnePoint (V q)))
      d.normalizedMap_infty rfl).comp
        (ambientCoordinates S b).onePointCongr.toHomotopyEquiv.toFun)

theorem productMap_infty : productMap d S C b OnePoint.infty = OnePoint.infty := by
  change C.symm.toHomeomorph.onePointCongr
    (OnePointProduct.productMap d.normalizedMap (ContinuousMap.id (OnePoint (V q)))
      d.normalizedMap_infty rfl OnePoint.infty) = OnePoint.infty
  exact congrArg C.symm.toHomeomorph.onePointCongr
    (OnePointProduct.productMap_infty d.normalizedMap
      (ContinuousMap.id (OnePoint (V q))) d.normalizedMap_infty rfl)

theorem productMap_coe (y : V e'.ambientDimension) :
    productMap d S C b (↑y) = C.symm.toHomeomorph.onePointCongr
      (OnePointProduct.map (d.normalizedMap (↑((S (y - b)).1)), ↑((S (y - b)).2))) := by
  change C.symm.toHomeomorph.onePointCongr
    (OnePointProduct.productMap d.normalizedMap (ContinuousMap.id (OnePoint (V q)))
      d.normalizedMap_infty rfl (↑(ambientCoordinates S b y))) = _
  rw [ambientCoordinates_apply]
  exact congrArg C.symm.toHomeomorph.onePointCongr
    (OnePointProduct.productMap_coe _ _ _ _ _ _)

def coordinates (y : V e'.ambientDimension) : e'.NormalModel :=
  C.symm (d.normalizedCoordinates (S (y - b)).1, (S (y - b)).2)

def neighborhood : Set (V e'.ambientDimension) :=
  (fun y ↦ (S (y - b)).1) ⁻¹' d.neighborhood

theorem contDiff_ambient : ContDiff ℝ ∞ (fun y : V e'.ambientDimension ↦ S (y - b)) :=
  S.contDiff.comp (contDiff_id.sub contDiff_const)

theorem isOpen_neighborhood : IsOpen (neighborhood d S b) :=
  d.open_neighborhood.preimage (contDiff_ambient S b).continuous.fst

theorem contDiffOn_coordinates :
    ContDiffOn ℝ ∞ (coordinates d S C b) (neighborhood d S b) := by
  apply C.symm.contDiff.comp_contDiffOn
  exact (d.contDiffOn_normalizedCoordinates.comp (contDiff_ambient S b).fst.contDiffOn
    (fun _ hy ↦ hy)).prodMk (contDiff_ambient S b).snd.contDiffOn

theorem hasFDerivAt_coordinates {y : V e'.ambientDimension} (hy : y ∈ neighborhood d S b) :
    HasFDerivAt (coordinates d S C b)
      (C.symm.toContinuousLinearMap.comp
        (((fderiv ℝ d.normalizedCoordinates (S (y - b)).1).comp
          ((ContinuousLinearMap.fst ℝ _ _).comp S.toContinuousLinearMap)).prod
          ((ContinuousLinearMap.snd ℝ _ _).comp S.toContinuousLinearMap))) y := by
  have hd₀ := d.contDiffOn_normalizedCoordinates.contDiffAt (d.open_neighborhood.mem_nhds hy)
  have hd : DifferentiableAt ℝ d.normalizedCoordinates (S (y - b)).1 :=
    hd₀.differentiableAt (by simp)
  have hs : HasFDerivAt (fun y ↦ S (y - b)) S.toContinuousLinearMap y := by
    have hb : HasFDerivAt (fun z : V e'.ambientDimension ↦ z - b)
        (ContinuousLinearMap.id ℝ _) y := (hasFDerivAt_id y).sub_const b
    exact (S.hasFDerivAt.comp y hb).congr_fderiv (ContinuousLinearMap.comp_id _)
  have hfst := hd.hasFDerivAt.comp y hs.fst
  have hpair := hfst.prodMk hs.snd
  exact C.symm.hasFDerivAt.comp y hpair

theorem surjective_fderiv_coordinates {y : V e'.ambientDimension}
    (hy : y ∈ neighborhood d S b) :
    Function.Surjective (fderiv ℝ (coordinates d S C b) y) := by
  rw [(hasFDerivAt_coordinates d S C b hy).fderiv]
  intro v
  obtain ⟨w, hw⟩ := d.normalized.surjective_differential (S (y - b)).1 hy (C v).1
  refine ⟨S.symm (w, (C v).2), ?_⟩
  change C.symm (fderiv ℝ d.normalizedCoordinates (S (y - b)).1
    (S (S.symm (w, (C v).2))).1, (S (S.symm (w, (C v).2))).2) = v
  rw [S.apply_symm_apply]
  change C.symm (fderiv ℝ d.normalized.coordinates (S (y - b)).1 w, (C v).2) = v
  rw [hw, Prod.mk.eta, C.symm_apply_apply]

theorem productMap_local_formula (y : V e'.ambientDimension)
    (hy : y ∈ neighborhood d S b) :
    productMap d S C b (↑y) = (↑(coordinates d S C b y) : OnePoint _) := by
  rw [productMap_coe, d.normalizedMap_local_formula _ hy, OnePointProduct.map_coe]
  rfl

variable (he : ∀ x, S (e'.toFun x - b) = (e.toFun x, 0))

include he in
theorem range_subset_neighborhood : range e'.toFun ⊆ neighborhood d S b := by
  rintro _ ⟨x, rfl⟩
  change (S (e'.toFun x - b)).1 ∈ d.neighborhood
  rw [he]
  exact d.range_subset ⟨x, rfl⟩

include he in
theorem productMap_zero_fiber (y : OnePoint (V e'.ambientDimension)) :
    productMap d S C b y = (↑(0 : e'.NormalModel)) ↔
      ∃ x, (e'.toFun x : OnePoint (V e'.ambientDimension)) = y := by
  induction y using OnePoint.rec with
  | infty => simp [productMap_infty]
  | coe y =>
    rw [productMap_coe]
    have hz : C.symm.toHomeomorph.onePointCongr (↑(0 : e.NormalModel × V q)) =
        (↑(0 : e'.NormalModel)) := congrArg OnePoint.some (map_zero C.symm)
    rw [← hz, C.symm.toHomeomorph.onePointCongr.injective.eq_iff,
      OnePointProduct.map_eq_coe_iff]
    change d.normalizedMap (↑((S (y - b)).1)) = (↑(0 : e.NormalModel)) ∧
      (↑((S (y - b)).2) : OnePoint (V q)) = ↑(0 : V q) ↔ _
    rw [d.normalizedMap_zero_fiber, OnePoint.coe_injective.eq_iff]
    constructor
    · rintro ⟨⟨x, hx⟩, hy⟩
      refine ⟨x, congrArg OnePoint.some ?_⟩
      have hs : S (e'.toFun x - b) = S (y - b) :=
        (he x).trans (Prod.ext (OnePoint.coe_injective hx) hy.symm)
      simpa only [sub_add_cancel] using congrArg (fun z ↦ z + b) (S.injective hs)
    · rintro ⟨x, hx⟩
      have hxy : e'.toFun x = y := OnePoint.coe_injective hx
      have h := he x
      rw [hxy] at h
      exact ⟨⟨x, congrArg OnePoint.some (congrArg Prod.fst h).symm⟩, congrArg Prod.snd h⟩

variable (ha : ∀ x v, S (a'.ambient x v) = (a.ambient x (C v).1, (C v).2))

include he ha in
theorem fderiv_coordinates_frame (x : M) (v : e'.NormalModel) :
    fderiv ℝ (coordinates d S C b) (e'.toFun x) (a'.ambient x v) = v := by
  rw [(hasFDerivAt_coordinates d S C b
    (range_subset_neighborhood d S b he ⟨x, rfl⟩)).fderiv]
  change C.symm (fderiv ℝ d.normalizedCoordinates (S (e'.toFun x - b)).1
    (S (a'.ambient x v)).1, (S (a'.ambient x v)).2) = v
  rw [he, ha]
  have h := congrArg (fun L : e.NormalModel →L[ℝ] e.NormalModel ↦ L (C v).1)
    (d.normalizedCoordinates_differential_frame x)
  change fderiv ℝ d.normalizedCoordinates (e.toFun x) (a.ambient x (C v).1) = (C v).1 at h
  rw [h, Prod.mk.eta, C.symm_apply_apply]

def collapseData : e'.FramedCollapseData a' where
  radius := 1
  radius_pos := zero_lt_one
  neighborhood := neighborhood d S b
  open_neighborhood := isOpen_neighborhood d S b
  range_subset := range_subset_neighborhood d S b he
  coordinates := coordinates d S C b
  smooth_coordinates := contDiffOn_coordinates d S C b
  surjective_differential := fun _ hy ↦ surjective_fderiv_coordinates d S C b hy
  differential_frame := fun x v ↦ by
    rw [one_smul]
    exact fderiv_coordinates_frame d S C b he ha x v
  map := productMap d S C b
  map_infty := productMap_infty d S C b
  zero_fiber := productMap_zero_fiber d S C b he
  local_formula := productMap_local_formula d S C b

end NoExoticSixSphere.EuclideanEmbedding.AffineProductCollapse
