import Wikipedia.NoExoticSixSphere.LinearProjectionCharts

/-!
# Generic linear projections preserve compact smooth embeddings

When the target dimension is strictly greater than twice the manifold
dimension, one actual linear map simultaneously avoids every nonzero
secant and tangent vector. The resulting map is a closed smooth embedding
of the original manifold with its original atlas. Good linear maps are
dense, not merely assumed to exist.
-/

noncomputable section

open Set Function Module MeasureTheory
open MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.LinearProjection

open GLOrthonormalization ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {q : ℕ}

def Good (L : Vector e.ambientDimension →L[ℝ] Vector q) : Prop :=
  Injective (L ∘ e.toFun) ∧
    ∀ x, Injective (mfderiv (𝓡 n) (𝓡 q) (L ∘ e.toFun) x)

theorem projectedDerivative_eq (L : Vector e.ambientDimension →L[ℝ] Vector q) (x : M) :
    mfderiv (𝓡 n) (𝓡 q) (L ∘ e.toFun) x =
      L.comp (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x) := by
  have hL : MDifferentiableAt (𝓡 e.ambientDimension) (𝓡 q) L (e.toFun x) :=
    L.differentiableAt.mdifferentiableAt
  rw [mfderiv_comp x hL
    (e.smooth.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, L.fderiv]
  rfl

theorem good_of_chart_avoidance (C : Set (TargetChart n M))
    (hcover : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (L : Vector e.ambientDimension →L[ℝ] Vector q)
    (hs : ∀ c ∈ C, ∀ d ∈ C, ∀ z ∈ secantDomain e c d, L (secant e c d z) ≠ 0)
    (ht : ∀ c ∈ C, ∀ z ∈ tangentDomain c, L (tangent e c z) ≠ 0) : Good e L := by
  constructor
  · intro x y hxy
    by_contra hne
    obtain ⟨c, hc, hx⟩ := hcover x
    obtain ⟨d, hd, hy⟩ := hcover y
    have hcx : c.symm (c x) = x := c.left_inv hx
    have hdy : d.symm (d y) = y := d.left_inv hy
    have hval : secant e c d (c x, d y) = e.toFun x - e.toFun y := by
      change e.toFun (c.symm (c x)) - e.toFun (d.symm (d y)) = _
      rw [hcx, hdy]
    have hz : (c x, d y) ∈ secantDomain e c d := by
      refine ⟨⟨c.map_source hx, d.map_source hy⟩, ?_⟩
      change secant e c d (c x, d y) ≠ 0
      rw [hval]
      exact sub_ne_zero.mpr (e.closedEmbedding.injective.ne hne)
    apply hs c hc d hd (c x, d y) hz
    rw [hval, map_sub]
    exact sub_eq_zero.mpr hxy
  · intro x
    obtain ⟨c, hc, hx⟩ := hcover x
    have hcx : c.symm (c x) = x := c.left_inv hx
    have hi : Injective (L.comp (fderiv ℝ (chartMap e c) (c x))) := by
      intro u v huv
      by_contra hne
      have hz : (c x, u - v) ∈ tangentDomain c :=
        ⟨c.map_source hx, sub_ne_zero.mpr hne⟩
      apply ht c hc (c x, u - v) hz
      change L (fderiv ℝ (chartMap e c) (c x) (u - v)) = 0
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr huv
    rw [chartDerivative_eq e c (c.map_source hx)] at hi
    have hl : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c.symm (c x) :=
      ⟨c.symm, c.map_source hx, fun _ _ ↦ rfl⟩
    have hfinal : Injective (mfderiv (𝓡 n) (𝓡 q) (L ∘ e.toFun) (c.symm (c x))) := by
      rw [projectedDerivative_eq]
      exact Function.Injective.of_comp_right (g := mfderiv (𝓡 n) (𝓡 n) c.symm (c x)) hi
        (hl.mfderivToContinuousLinearEquiv (by simp)).surjective
    exact hcx ▸ hfinal

theorem ae_good [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    [MeasurableSpace (Vector e.ambientDimension →L[ℝ] Vector q)]
    [BorelSpace (Vector e.ambientDimension →L[ℝ] Vector q)]
    (μ : Measure (Vector e.ambientDimension →L[ℝ] Vector q)) [IsAddHaarMeasure μ]
    (hd : 2 * n < q) : ∀ᵐ L ∂μ, Good e L := by
  obtain ⟨C, hC, hcover⟩ := exists_finite_chart_cover n M
  let : Countable C := hC.countable.to_subtype
  have hdim : finrank ℝ (Vector n × Vector n) < finrank ℝ (Vector q) := by
    simpa only [finrank_prod, finrank_euclideanSpace_fin, two_mul] using hd
  have hs : ∀ᵐ L ∂μ, ∀ c : C, ∀ d : C, ∀ z ∈ secantDomain e c.val d.val,
      L (secant e c.val d.val z) ≠ 0 :=
    ae_all_iff.mpr fun c ↦ ae_all_iff.mpr fun d ↦
      GenericLinearAvoidance.ae_avoids_zero μ (secant e c.val d.val)
        (secantDomain e c.val d.val) ((contDiffOn_secant e c.val d.val).mono inter_subset_left)
        (secant_nonzero e c.val d.val) hdim
  have ht : ∀ᵐ L ∂μ, ∀ c : C, ∀ z ∈ tangentDomain c.val,
      L (tangent e c.val z) ≠ 0 :=
    ae_all_iff.mpr fun c ↦ GenericLinearAvoidance.ae_avoids_zero μ (tangent e c.val)
      (tangentDomain c.val) (contDiffOn_tangent e c.val) (tangent_nonzero e c.val) hdim
  exact (hs.and ht).mono fun L h ↦ good_of_chart_avoidance e C hcover L
    (fun c hc d hd ↦ h.1 ⟨c, hc⟩ ⟨d, hd⟩) (fun c hc ↦ h.2 ⟨c, hc⟩)

theorem dense_good [IsManifold (𝓡 n) ∞ M] [CompactSpace M] (hd : 2 * n < q) :
    Dense {L : Vector e.ambientDimension →L[ℝ] Vector q | Good e L} := by
  let : MeasurableSpace (Vector e.ambientDimension →L[ℝ] Vector q) := borel _
  let : BorelSpace (Vector e.ambientDimension →L[ℝ] Vector q) := ⟨rfl⟩
  exact Measure.dense_of_ae (ae_good e addHaar hd)

theorem exists_good_near [IsManifold (𝓡 n) ∞ M] [CompactSpace M] (hd : 2 * n < q)
    (L₀ : Vector e.ambientDimension →L[ℝ] Vector q) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Vector e.ambientDimension →L[ℝ] Vector q, Good e L ∧ dist L₀ L < ε :=
  (dense_good e hd).exists_dist_lt L₀ hε

def embedding [CompactSpace M] (L : Vector e.ambientDimension →L[ℝ] Vector q)
    (hL : Good e L) : EuclideanEmbedding n M where
  ambientDimension := q
  toFun := L ∘ e.toFun
  smooth := L.contDiff.contMDiff.comp e.smooth
  closedEmbedding := (L.continuous.comp e.smooth.continuous).isClosedEmbedding hL.1
  injective_mfderiv := hL.2

end NoExoticSixSphere.LinearProjection
