import Wikipedia.HopfProblem.AffineBlowup
import Mathlib.Topology.LocalAtTarget

/-!
# Topology of the incidence blow-up

The incidence condition is closed in `ℂ² × ℙ¹`.  Consequently the blow-down
is proper.  The actual exceptional fibre, with its subspace topology, is
homeomorphic to the Riemann sphere.  Second countability follows from the
two affine charts, without imposing it on a newly constructed topology.
-/

noncomputable section

open Set Topology OnePoint

namespace Wikipedia.HopfProblem.AffineBlowup

open ToricCharts

private def ambientMap (b : Bool) : CoordinateSpace 2 × ℂ →
    CoordinateSpace 2 × RiemannSphere :=
  Prod.map id (RiemannSphere.standardCharts.affineMap b)

private theorem ambientMap_isOpenMap (b : Bool) : IsOpenMap (ambientMap b) :=
  IsOpenMap.id.prodMap
    (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).isOpenMap

private theorem ambientMap_preimage_closed (b : Bool) :
    IsClosed (ambientMap b ⁻¹' incidenceSet) := by
  cases b
  · change IsClosed {p : CoordinateSpace 2 × ℂ | p.1 0 = p.2 * p.1 1}
    exact isClosed_eq (by fun_prop) (by fun_prop)
  · have h : ambientMap true ⁻¹' incidenceSet =
        {p : CoordinateSpace 2 × ℂ | p.1 1 = p.2 * p.1 0} := by
      ext p
      exact incidence_infinityParametrization p.1 p.2
    rw [h]
    exact isClosed_eq (by fun_prop) (by fun_prop)

private theorem ambientMap_jointly_surjective (p : CoordinateSpace 2 × RiemannSphere) :
    ∃ b : Bool, ∃ q : CoordinateSpace 2 × ℂ, ambientMap b q = p := by
  obtain ⟨z, hz⟩ | ⟨z, hz⟩ := RiemannSphere.standardCharts.covered p.2
  · exact ⟨false, (p.1, z), Prod.ext rfl hz⟩
  · exact ⟨true, (p.1, z), Prod.ext rfl hz⟩

/-- The incidence blow-up is a closed subspace of `ℂ² × ℙ¹`. -/
theorem incidenceSet_isClosed : IsClosed incidenceSet := by
  have he : incidenceSetᶜ = ⋃ b : Bool,
      ambientMap b '' (ambientMap b ⁻¹' incidenceSetᶜ) := by
    ext p
    constructor
    · intro hp
      obtain ⟨b, q, rfl⟩ := ambientMap_jointly_surjective p
      exact mem_iUnion.mpr ⟨b, ⟨q, hp, rfl⟩⟩
    · intro hp
      obtain ⟨b, q, hq, rfl⟩ := mem_iUnion.mp hp
      exact hq
  apply isOpen_compl_iff.mp
  rw [he]
  apply isOpen_iUnion
  intro b
  apply ambientMap_isOpenMap
  exact (ambientMap_preimage_closed b).isOpen_compl

/-- Hausdorffness is inherited from the actual ambient product. -/
theorem space_t2 : T2Space Space := inferInstance

instance secondCountableTopology : SecondCountableTopology Space := by
  let (b : Bool) : SecondCountableTopology (affineTarget b) :=
    (parametrization b).symm.secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover affineTarget_isOpen
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨b, z, rfl⟩ := affineMap_jointly_surjective x
  exact ⟨b, affineMap_mem_target b z⟩

/-- Properness is proved by restricting the product projection to the closed
incidence subset; the second factor is the compact Riemann sphere. -/
theorem projection_isProperMap : IsProperMap projection :=
  isProperMap_fst_of_compactSpace.restrict incidenceSet_isClosed

theorem projection_isClosedMap : IsClosedMap projection :=
  projection_isProperMap.isClosedMap

theorem projection_preimage_isCompact {K : Set (CoordinateSpace 2)} (hK : IsCompact K) :
    IsCompact (projection ⁻¹' K) :=
  projection_isProperMap.isCompact_preimage hK

@[simp] theorem incidence_zero (l : RiemannSphere) : Incidence 0 l := by
  induction l using OnePoint.rec with
  | infty => rfl
  | coe z => simp

/-- The exceptional divisor is the fibre of the blow-down over the origin. -/
def exceptionalSet : Set Space := projection ⁻¹' {0}

def exceptionalInclusion (l : RiemannSphere) : Space :=
  ⟨(0, l), incidence_zero l⟩

@[simp] theorem projection_exceptionalInclusion (l : RiemannSphere) :
    projection (exceptionalInclusion l) = 0 := rfl

@[simp] theorem direction_exceptionalInclusion (l : RiemannSphere) :
    direction (exceptionalInclusion l) = l := rfl

theorem continuous_exceptionalInclusion : Continuous exceptionalInclusion :=
  (continuous_const.prodMk continuous_id).subtype_mk _

@[simp] theorem exceptionalInclusion_mem (l : RiemannSphere) :
    exceptionalInclusion l ∈ exceptionalSet := rfl

/-- An explicit homeomorphism onto the exceptional fibre with its induced topology. -/
def exceptionalHomeomorph : RiemannSphere ≃ₜ exceptionalSet where
  toFun l := ⟨exceptionalInclusion l, exceptionalInclusion_mem l⟩
  invFun x := direction x.1
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact x.2.symm
    · rfl
  continuous_toFun := continuous_exceptionalInclusion.subtype_mk _
  continuous_invFun := continuous_direction.comp continuous_subtype_val

@[simp] theorem exceptionalHomeomorph_apply (l : RiemannSphere) :
    (exceptionalHomeomorph l).1 = exceptionalInclusion l := rfl

@[simp] theorem exceptionalHomeomorph_symm_apply (x : exceptionalSet) :
    exceptionalHomeomorph.symm x = direction x.1 := rfl

theorem exceptionalSet_isClosed : IsClosed exceptionalSet :=
  isClosed_singleton.preimage continuous_projection

theorem exceptionalSet_isCompact : IsCompact exceptionalSet :=
  projection_preimage_isCompact isCompact_singleton

theorem range_exceptionalInclusion : range exceptionalInclusion = exceptionalSet := by
  ext x
  constructor
  · rintro ⟨l, rfl⟩
    exact exceptionalInclusion_mem l
  · intro hx
    exact ⟨direction x, congrArg Subtype.val
      (exceptionalHomeomorph.apply_symm_apply ⟨x, hx⟩)⟩

/-- Every vector lies on at least one projective line through the origin. -/
theorem projection_surjective : Function.Surjective projection := by
  intro v
  by_cases h : v 1 = 0
  · exact ⟨⟨(v, ∞), h⟩, rfl⟩
  · refine ⟨⟨(v, ((v 0 / v 1 : ℂ) : RiemannSphere)), ?_⟩, rfl⟩
    exact (div_mul_cancel₀ (v 0) h).symm

/-- A nonzero vector determines its unique projective direction. -/
theorem incidence_direction_unique {v : CoordinateSpace 2} (hv : v ≠ 0)
    {l m : RiemannSphere} (hl : Incidence v l) (hm : Incidence v m) : l = m := by
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i
      fin_cases i <;> assumption
    have hd (d : RiemannSphere) (hd : Incidence v d) : d = ∞ := by
      induction d using OnePoint.rec with
      | infty => rfl
      | coe z =>
          have hz : v 0 = 0 := by simpa [h1] using hd
          exact (h0 hz).elim
    exact (hd l hl).trans (hd m hm).symm
  · induction l using OnePoint.rec with
    | infty => exact (h1 hl).elim
    | coe z =>
        induction m using OnePoint.rec with
        | infty => exact (h1 hm).elim
        | coe w =>
            apply congrArg ((↑) : ℂ → RiemannSphere)
            exact mul_right_cancel₀ h1 (hl.symm.trans hm)

/-- The ordinary punctured affine plane, bundled as an open subset. -/
def puncturedBase : TopologicalSpace.Opens (CoordinateSpace 2) :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

/-- The complement of the exceptional divisor, bundled as an open subset. -/
def puncturedSpace : TopologicalSpace.Opens Space :=
  ⟨projection ⁻¹' {0}ᶜ, isClosed_singleton.isOpen_compl.preimage continuous_projection⟩

@[simp] theorem mem_puncturedBase (v : CoordinateSpace 2) :
    v ∈ puncturedBase ↔ v ≠ 0 := Iff.rfl

@[simp] theorem mem_puncturedSpace (x : Space) :
    x ∈ puncturedSpace ↔ projection x ≠ 0 := Iff.rfl

theorem puncturedSpace_eq_compl_exceptionalSet :
    (puncturedSpace : Set Space) = exceptionalSetᶜ := rfl

def puncturedProjection : puncturedSpace → puncturedBase :=
  (puncturedBase : Set (CoordinateSpace 2)).restrictPreimage projection

@[simp] theorem puncturedProjection_coe (x : puncturedSpace) :
    (puncturedProjection x).1 = projection x.1 := rfl

theorem puncturedProjection_isProperMap : IsProperMap puncturedProjection :=
  projection_isProperMap.restrictPreimage (puncturedBase : Set (CoordinateSpace 2))

theorem puncturedProjection_bijective : Function.Bijective puncturedProjection := by
  constructor
  · intro x y h
    have hxy : projection x.1 = projection y.1 := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext hxy
    apply incidence_direction_unique x.2 (incidence_point x.1)
    rw [hxy]
    exact incidence_point y.1
  · intro v
    obtain ⟨x, hx⟩ := projection_surjective v.1
    exact ⟨⟨x, by change projection x ≠ 0; rw [hx]; exact v.2⟩, Subtype.ext hx⟩

/-- Blow-down is a homeomorphism away from the exceptional divisor.  Both
spaces are genuine open subspaces, so they inherit their analytic atlases. -/
def puncturedHomeomorph : puncturedSpace ≃ₜ puncturedBase :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective puncturedProjection puncturedProjection_bijective)
    puncturedProjection_isProperMap.continuous puncturedProjection_isProperMap.isClosedMap

@[simp] theorem puncturedHomeomorph_apply (x : puncturedSpace) :
    puncturedHomeomorph x = puncturedProjection x := rfl

@[simp] theorem projection_puncturedHomeomorph_symm (v : puncturedBase) :
    projection (puncturedHomeomorph.symm v).1 = v.1 :=
  congrArg Subtype.val (puncturedHomeomorph.apply_symm_apply v)

end Wikipedia.HopfProblem.AffineBlowup
