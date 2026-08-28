import Wikipedia.HopfProblem.OrbitPairScalarHopf
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspNeighborhoodEquivariance

/-!
# The radial quotient of the actual round normal product

The domain is the existing injective normal neighborhood of the actual
fixed curve. The projection below is an open quotient map onto the
product of the original Riemann sphere and a Euclidean three-ball. Its
fibres are exactly the original period-one circle orbits.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold
open CuspCircleNormalTrivialization
open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

local notation "Circle" => AddCircle (1 : ℝ)

/-- A product neighborhood of the fixed sphere in radial orbit coordinates. -/
def normalOrbitTube : TopologicalSpace.Opens (RiemannSphere × Transverse) :=
  ⟨{p | ‖p.2‖ < injectiveRadius},
    isOpen_lt (continuous_norm.comp continuous_snd) continuous_const⟩

theorem scalarHopfMap_mem_normalOrbitTube (p : roundNormalProduct) :
    (p.val.1, scalarHopfMap p.val.2) ∈ normalOrbitTube := by
  change ‖scalarHopfMap p.val.2‖ < injectiveRadius
  apply (sq_lt_sq₀ (norm_nonneg _) injectiveRadius_pos.le).mp
  rw [norm_scalarHopfMap_sq]
  exact p.property

/-- The original base coordinate and the explicit radial normal invariant. -/
def normalTubeProjection (p : roundNormalProduct) : normalOrbitTube :=
  ⟨(p.val.1, scalarHopfMap p.val.2), scalarHopfMap_mem_normalOrbitTube p⟩

@[simp] theorem normalTubeProjection_coe (p : roundNormalProduct) :
    (normalTubeProjection p : RiemannSphere × Transverse) =
      (p.val.1, scalarHopfMap p.val.2) := rfl

theorem normalTubeProjection_surjective : Function.Surjective normalTubeProjection := by
  intro y
  obtain ⟨v, hv⟩ := scalarHopfMap_surjective y.val.2
  have hr : radiusSq v < injectiveRadius ^ 2 := by
    change Complex.normSq v.1 + Complex.normSq v.2 < injectiveRadius ^ 2
    rw [← norm_scalarHopfMap_sq, hv]
    exact (sq_lt_sq₀ (norm_nonneg _) injectiveRadius_pos.le).mpr y.property
  exact ⟨⟨(y.val.1, v), hr⟩, Subtype.ext (Prod.ext rfl hv)⟩

theorem normalTubeProjection_continuous : Continuous normalTubeProjection :=
  (continuous_subtype_val.fst.prodMk
    (continuous_scalarHopfMap.comp continuous_subtype_val.snd)).subtype_mk _

theorem normalTubeProjection_isOpenMap : IsOpenMap normalTubeProjection := by
  have h : IsOpenMap (Prod.map (id : RiemannSphere → RiemannSphere) scalarHopfMap) :=
    IsOpenMap.id.prodMap scalarHopfMap_isOpenQuotientMap.isOpenMap
  exact (h.domRestrict roundNormalProduct.isOpen).subtype_mk _

theorem normalTubeProjection_isOpenQuotientMap : IsOpenQuotientMap normalTubeProjection :=
  ⟨normalTubeProjection_surjective, normalTubeProjection_continuous,
    normalTubeProjection_isOpenMap⟩

theorem normalTubeProjection_circleAction (t : Circle) (p : roundNormalProduct) :
    normalTubeProjection (roundCircleAction t p) = normalTubeProjection p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact scalarHopfMap_smul _ (circleParameter_norm t) p.val.2

/-- These are the actual circle fibres on the existing round normal domain. -/
theorem normalTubeProjection_eq_iff (p q : roundNormalProduct) :
    normalTubeProjection p = normalTubeProjection q ↔
      ∃ t : Circle, roundCircleAction t p = q := by
  constructor
  · intro he
    have hb := congrArg (fun y : normalOrbitTube => y.val.1) he
    have hv := congrArg (fun y : normalOrbitTube => y.val.2) he
    obtain ⟨u, hu, huv⟩ := (scalarHopfMap_eq_iff p.val.2 q.val.2).mp hv
    obtain ⟨t, ht⟩ := exists_circleParameter_of_norm_eq_one u hu
    refine ⟨t, Subtype.ext ?_⟩
    change (p.val.1, (Homology.DeltaSweep.circleParameter t : ℂ) • p.val.2) = q.val
    rw [ht]
    exact Prod.ext hb huv
  · rintro ⟨t, rfl⟩
    exact (normalTubeProjection_circleAction t p).symm

/-- The zero normal vector downstairs detects exactly the original zero section. -/
theorem normalTubeProjection_normal_zero_iff (p : roundNormalProduct) :
    (normalTubeProjection p).val.2 = 0 ↔ p.val.2 = 0 :=
  scalarHopfMap_eq_zero_iff p.val.2

end Wikipedia.HopfProblem.OrbitPair
