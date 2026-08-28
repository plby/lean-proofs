import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspNeighborhood

/-!
# A compact round normal disk inside the actual smooth neighborhood

Half the proved injectivity radius gives a closed round disk entirely
inside the original real-analytic product chart. Its image is a genuine
compact embedded neighborhood of the original curve. The map is the
restriction of the already proved native real-analytic diffeomorphism;
no new smooth structure on a closed subset is introduced.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.space_t2Space Threefold.chartedSpace

/-- The closed disk stays strictly inside the actual injective open normal chart. -/
def closedRadius : ℝ := injectiveRadius / 2

theorem closedRadius_pos : 0 < closedRadius := half_pos injectiveRadius_pos

theorem closedRadius_lt_injectiveRadius : closedRadius < injectiveRadius :=
  half_lt_self injectiveRadius_pos

/-- Closed Euclidean normal sublevel sets are compact in the original normed fibre. -/
theorem isCompact_radiusSq_sublevel (r : ℝ) :
    IsCompact {v : Fibre | radiusSq v ≤ r ^ 2} := by
  have hc : IsClosed {v : Fibre | radiusSq v ≤ r ^ 2} :=
    isClosed_le (contDiff_radiusSq (n := ω)).continuous continuous_const
  have hs : {v : Fibre | radiusSq v ≤ r ^ 2} ⊆ closedBall (0 : Fibre) |r| := by
    intro v hv
    have hv' : ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 ≤ r ^ 2 := by
      simpa only [mem_ofPred_eq, radiusSq, Complex.normSq_eq_norm_sq] using hv
    rw [mem_closedBall, dist_zero_right, norm_prod_le_iff]
    constructor
    · apply (sq_le_sq₀ (norm_nonneg v.1) (abs_nonneg r)).mp
      rw [sq_abs]
      nlinarith only [hv', sq_nonneg ‖v.2‖]
    · apply (sq_le_sq₀ (norm_nonneg v.2) (abs_nonneg r)).mp
      rw [sq_abs]
      nlinarith only [hv', sq_nonneg ‖v.1‖]
  exact isCompact_of_isClosed_isBounded hc ((isBounded_closedBall).subset hs)

/-- The actual closed round normal disk, using the positive half-radius. -/
abbrev ClosedNormalDisk := {v : Fibre // radiusSq v ≤ closedRadius ^ 2}

instance closedNormalDiskCompactSpace : CompactSpace ClosedNormalDisk :=
  isCompact_iff_compactSpace.mp (isCompact_radiusSq_sublevel closedRadius)

/-- The original base sphere times the closed round normal disk. -/
abbrev ClosedNormalProduct := RiemannSphere × ClosedNormalDisk

/-- Inclusion of the closed disk product in the actual open normal-coordinate domain. -/
def closedProductIntoRound (p : ClosedNormalProduct) : roundNormalProduct :=
  ⟨(p.1, p.2.val), by
    change radiusSq p.2.val < injectiveRadius ^ 2
    have hsq : closedRadius ^ 2 < injectiveRadius ^ 2 :=
      (sq_lt_sq₀ closedRadius_pos.le injectiveRadius_pos.le).mpr
        closedRadius_lt_injectiveRadius
    exact p.2.property.trans_lt hsq⟩

@[simp] theorem closedProductIntoRound_coe (p : ClosedNormalProduct) :
    (closedProductIntoRound p : RiemannSphere × Fibre) = (p.1, p.2.val) := rfl

theorem closedProductIntoRound_continuous : Continuous closedProductIntoRound :=
  (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem closedProductIntoRound_injective : Function.Injective closedProductIntoRound := by
  intro p q hpq
  have he : (p.1, p.2.val) = (q.1, q.2.val) :=
    congrArg (fun x : roundNormalProduct => x.val) hpq
  apply Prod.ext
  · exact congrArg (fun x : RiemannSphere × Fibre => x.1) he
  · apply Subtype.ext
    exact congrArg (fun x : RiemannSphere × Fibre => x.2) he

/-- The actual compact-disk map is the restriction of the native analytic normal chart. -/
def closedProductMap : ClosedNormalProduct → Threefold.Space :=
  roundProductMap ∘ closedProductIntoRound

@[simp] theorem closedProductMap_eq_round (p : ClosedNormalProduct) :
    closedProductMap p = roundProductMap (closedProductIntoRound p) := rfl

theorem closedProductMap_continuous : Continuous closedProductMap :=
  roundProductMap_contMDiff.continuous.comp closedProductIntoRound_continuous

theorem closedProductMap_injective : Function.Injective closedProductMap :=
  roundProductMap_injective.comp closedProductIntoRound_injective

/-- The compact product is embedded in the original Hausdorff threefold. -/
theorem closedProductMap_isClosedEmbedding : IsClosedEmbedding closedProductMap :=
  closedProductMap_continuous.isClosedEmbedding closedProductMap_injective

/-- The literal compact disk image in the original threefold. -/
def closedDiskNeighborhood : Set Threefold.Space := range closedProductMap

theorem closedDiskNeighborhood_isCompact : IsCompact closedDiskNeighborhood :=
  isCompact_range closedProductMap_continuous

theorem closedDiskNeighborhood_subset_open : closedDiskNeighborhood ⊆ fixedCurveNeighborhood := by
  rintro _ ⟨p, rfl⟩
  exact mem_range_self (closedProductIntoRound p)

/-- The compact disk image has the proved actual product topology. -/
def closedDiskNeighborhoodHomeomorph : ClosedNormalProduct ≃ₜ closedDiskNeighborhood :=
  closedProductMap_isClosedEmbedding.isEmbedding.toHomeomorph

@[simp] theorem closedDiskNeighborhoodHomeomorph_coe (p : ClosedNormalProduct) :
    (closedDiskNeighborhoodHomeomorph p : Threefold.Space) = closedProductMap p := rfl

/-- The zero normal vector of the actual closed disk. -/
def closedZero : ClosedNormalDisk := ⟨0, by simp [sq_nonneg]⟩

theorem closedProductMap_zeroSection (p : RiemannSphere) :
    closedProductMap (p, closedZero) = CuspGeometry.doubleCurveParametrization 1 p :=
  globalProductMap_zeroSection p

theorem doubleCurve_subset_closedDiskNeighborhood :
    CuspGeometry.doubleCurve 1 ⊆ closedDiskNeighborhood := by
  rw [← CuspGeometry.doubleCurveParametrization_range]
  rintro _ ⟨p, rfl⟩
  exact ⟨(p, closedZero), closedProductMap_zeroSection p⟩

/-- The compact disk image really is a neighborhood of the entire original curve. -/
theorem doubleCurve_subset_interior_closedDiskNeighborhood :
    CuspGeometry.doubleCurve 1 ⊆ interior closedDiskNeighborhood := by
  let U : Set roundNormalProduct := {p | radiusSq p.val.2 < closedRadius ^ 2}
  have hU : IsOpen U := isOpen_lt
    ((contDiff_radiusSq (n := ω)).continuous.comp continuous_subtype_val.snd) continuous_const
  have ho : IsOpen (roundProductMap '' U) := roundProductMap_isOpenMap U hU
  have hs : roundProductMap '' U ⊆ closedDiskNeighborhood := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(p.val.1, ⟨p.val.2, le_of_lt hp⟩), ?_⟩
    apply congrArg roundProductMap
    apply Subtype.ext
    rfl
  rw [← CuspGeometry.doubleCurveParametrization_range]
  rintro _ ⟨a, rfl⟩
  apply interior_mono hs
  rw [ho.interior_eq]
  refine ⟨⟨(a, 0), zero_mem_roundNormalProduct a⟩, ?_, roundProductMap_zeroSection a⟩
  change radiusSq (0 : Fibre) < closedRadius ^ 2
  rw [radiusSq_zero]
  exact sq_pos_of_pos closedRadius_pos

theorem closedProductMap_mem_doubleCurve_iff (p : ClosedNormalProduct) :
    closedProductMap p ∈ CuspGeometry.doubleCurve 1 ↔ p.2.val = 0 :=
  roundProductMap_mem_doubleCurve_iff (closedProductIntoRound p)

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
