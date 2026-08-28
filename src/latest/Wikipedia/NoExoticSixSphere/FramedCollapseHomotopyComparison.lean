import Wikipedia.NoExoticSixSphere.FramedCollapseNormalComparison
import Wikipedia.NoExoticSixSphere.SphereLocalFiberHomotopy
import Wikipedia.NoExoticSixSphere.LocalSphereCollapse
import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension

/-!
# Homotopy uniqueness of collapse data for the same compact framed embedding

The smooth defining equations, exact zero fiber, and specified positive
normal derivative suffice to construct a homotopy. The input maps need
not be chosen from the same tube, and equality of their germs is not an
additional hypothesis. The comparison persists through every specified
finite suspension.
-/

noncomputable section

open Set Topology
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [Nonempty M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel}
  (d d' : e.FramedCollapseData a)

theorem sphereMap_homotopic : d.sphereMap.Homotopic d'.sphereMap := by
  obtain ⟨V, hV, hcore, hsub, hblend⟩ := d.exists_open_coordinate_comparison d'
  let U := (fun y : EuclideanSpace ℝ (Fin e.ambientDimension) ↦
    (y : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension)))) '' V
  have hU : IsOpen U := OnePoint.isOpenEmbedding_coe.isOpenMap V hV
  let p : U → EuclideanSpace ℝ (Fin e.ambientDimension) :=
    fun x ↦ OnePointFiberGerm.finitePart x.val
  have hpV (x : U) : p x ∈ V := by
    obtain ⟨y, hy, hxy⟩ := x.property
    change OnePointFiberGerm.finitePart x.val ∈ V
    rw [← hxy]
    exact hy
  have hpcoe (x : U) : ((p x : EuclideanSpace ℝ (Fin e.ambientDimension)) : OnePoint _) =
      x.val := by
    apply OnePointFiberGerm.coe_finitePart
    obtain ⟨y, _, hxy⟩ := x.property
    rw [← hxy]
    exact OnePoint.coe_ne_infty y
  have hp : Continuous p := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx : x.val ≠ OnePoint.infty := by
      rw [← hpcoe x]
      exact OnePoint.coe_ne_infty _
    exact (OnePointFiberGerm.continuousAt_finitePart hx).comp
      continuous_subtype_val.continuousAt
  let q := euclideanOnePointSphere (e.ambientDimension - n)
  let F : C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension)),
      Sphere (e.ambientDimension - n)) :=
    ⟨fun z ↦ q (d.map z), q.continuous.comp d.map.continuous⟩
  let G : C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension)),
      Sphere (e.ambientDimension - n)) :=
    ⟨fun z ↦ q (d'.map z), q.continuous.comp d'.map.continuous⟩
  let b := q ((0 : e.NormalModel) : OnePoint _)
  have hK : ∀ z, F z = b ↔ G z = b := by
    intro z
    change q (d.map z) = q (↑(0 : e.NormalModel)) ↔
      q (d'.map z) = q (↑(0 : e.NormalModel))
    rw [q.injective.eq_iff, q.injective.eq_iff, d.zero_fiber, d'.zero_fiber]
  have hKU : F ⁻¹' {b} ⊆ U := by
    intro z hz
    have hh : d.map z = (↑(0 : e.NormalModel) : OnePoint _) := q.injective hz
    obtain ⟨x, rfl⟩ := (d.zero_fiber z).mp hh
    exact ⟨e.toFun x, hcore ⟨x, rfl⟩, rfl⟩
  have hF (x : U) : F x.val = q (↑(d.coordinates (p x)) : OnePoint _) := by
    change q (d.map x.val) = _
    rw [← hpcoe x, d.local_formula _ (hsub (hpV x)).1]
  have hG (x : U) : G x.val = q (↑(d'.coordinates (p x)) : OnePoint _) := by
    change q (d'.map x.val) = _
    rw [← hpcoe x, d'.local_formula _ (hsub (hpV x)).2]
  have hc : Continuous (fun x : U ↦ d.coordinates (p x)) :=
    d.smooth_coordinates.continuousOn.comp_continuous hp (fun x ↦ (hsub (hpV x)).1)
  have hc' : Continuous (fun x : U ↦ d'.coordinates (p x)) :=
    d'.smooth_coordinates.continuousOn.comp_continuous hp (fun x ↦ (hsub (hpV x)).2)
  let L : C(I × U, Sphere (e.ambientDimension - n)) := by
    refine ⟨fun z ↦ q (↑((1 - (z.1 : ℝ)) • d.coordinates (p z.2) +
      (z.1 : ℝ) • d'.coordinates (p z.2)) : OnePoint _), ?_⟩
    have ht : Continuous (fun z : I × U ↦ (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact q.continuous.comp (OnePoint.continuous_coe.comp
      (((continuous_const.sub ht).smul (hc.comp continuous_snd)).add
        (ht.smul (hc'.comp continuous_snd))))
  have hLzero (x : U) : L (0, x) = F x.val := by
    change q (↑((1 - (0 : ℝ)) • d.coordinates (p x) +
      (0 : ℝ) • d'.coordinates (p x)) : OnePoint _) = F x.val
    rw [sub_zero, one_smul, zero_smul, add_zero, hF]
  have hLone (x : U) : L (1, x) = G x.val := by
    change q (↑((1 - (1 : ℝ)) • d.coordinates (p x) +
      (1 : ℝ) • d'.coordinates (p x)) : OnePoint _) = G x.val
    rw [sub_self, zero_smul, one_smul, zero_add, hG]
  have hLfiber (t : I) (x : U) : L (t, x) = b ↔ F x.val = b := by
    rw [hF]
    change q (↑((1 - (t : ℝ)) • d.coordinates (p x) +
      (t : ℝ) • d'.coordinates (p x)) : OnePoint _) = q (↑(0 : e.NormalModel)) ↔
        q (↑(d.coordinates (p x)) : OnePoint _) = q (↑(0 : e.NormalModel))
    rw [q.injective.eq_iff, q.injective.eq_iff,
      OnePoint.coe_injective.eq_iff, OnePoint.coe_injective.eq_iff,
      hblend (p x) (hpV x) t t.property]
    have hh := hblend (p x) (hpV x) 0 (by simp)
    simpa only [sub_zero, one_smul, zero_smul, add_zero] using hh.symm
  obtain ⟨H⟩ := SphereFiberGerm.homotopic_of_local_fiber_homotopy F G b hK U hU hKU
    L hLzero hLone hLfiber
  let s := euclideanOnePointSphere e.ambientDimension
  refine ⟨{
    toFun := fun z ↦ H (z.1, s.symm z.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (s.symm.continuous.comp continuous_snd))
    map_zero_left := fun y ↦ H.apply_zero (s.symm y)
    map_one_left := fun y ↦ H.apply_one (s.symm y) }⟩

theorem iterate_sphereMap_nullhomotopic_iff (r : ℕ) :
    (SphereMapSuspension.iterate d.sphereMap r).Nullhomotopic ↔
      (SphereMapSuspension.iterate d'.sphereMap r).Nullhomotopic := by
  have H := SphereMapSuspension.iterate_homotopic (d.sphereMap_homotopic d') r
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, H.symm.trans hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, H.trans hb⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
