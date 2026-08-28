import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticRestriction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocalDiffeomorph

/-!
# Holomorphic restriction of the original ambient elliptic canonical bundle

The canonical bundle of the genuine small elliptic piece is biholomorphic,
fibrewise linearly, to the restriction of the original full-filling
canonical bundle to that piece.  The target is the ordinary open inverse
image of the actual `pieceDomain` in the native full bundle total space.
No topology or atlas is transported along a set-theoretic identification.

Both directions use the previously constructed derivative pullback on
ambient three-covectors.  The inverse map is identified explicitly, and
the biholomorphism commutes with the actual projection to the small piece.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

local instance restrictionHolomorphicFullManifold (j : Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance restrictionHolomorphicPieceManifold (j : Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

/-- The original full ambient canonical bundle restricted to the actual
small-filling domain, with its natural open-subspace topology and atlas. -/
def fullBundleRestriction (j : Kind) : TopologicalSpace.Opens (fullBundle j).TotalSpace :=
  ⟨(Bundle.TotalSpace.proj : (fullBundle j).TotalSpace → SpecialFullFilling j) ⁻¹'
      (pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
        specialBaseCover j : Set (SpecialFullFilling j)),
    (pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
      specialBaseCover j).isOpen.preimage (fullBundle j).continuous_proj⟩

/-- The actual base projection of the restricted full bundle. -/
def fullBundleRestrictionProjection (j : Kind) (p : fullBundleRestriction j) :
    SpecialEllipticPiece j := ⟨p.val.proj, p.property⟩

@[simp] theorem fullBundleRestrictionProjection_val (j : Kind)
    (p : fullBundleRestriction j) :
    (fullBundleRestrictionProjection j p).val = p.val.proj := rfl

/-- The genuine map of canonical total spaces induced by the native
open-subset inclusion, using inverse derivative pullback on each fibre. -/
def restrictionPushforward (j : Kind) : (bundle j).TotalSpace → (fullBundle j).TotalSpace :=
  Pullback.forwardMap (pieceInclusion_isLocalDiffeomorph j)

@[simp] theorem restrictionPushforward_proj (j : Kind) (p : (bundle j).TotalSpace) :
    (restrictionPushforward j p).proj = p.proj.val := rfl

@[simp] theorem restrictionPushforward_mk (j : Kind) (x : SpecialEllipticPiece j)
    (v : (bundle j).Fiber x) :
    restrictionPushforward j ⟨x, v⟩ = ⟨x.val, (restriction j x).symm v⟩ := rfl

/-- Its scalar in preferred native coordinates is unchanged because the
actual inclusion differential is identity, as previously proved. -/
theorem restrictionPushforward_preferred_coefficient (j : Kind) (p : (bundle j).TotalSpace) :
    id (α := ℂ) (restrictionPushforward j p).2 = id (α := ℂ) p.2 := by
  change id (α := ℂ) ((restriction j p.proj).symm p.2) = id (α := ℂ) p.2
  have h := restriction_preferred_coefficient j p.proj ((restriction j p.proj).symm p.2)
  exact h.symm.trans (congrArg (id (α := ℂ)) ((restriction j p.proj).apply_symm_apply p.2))

theorem restrictionPushforward_holomorphic (j : Kind) :
    ContMDiff Iᴷ Iᴷ ω (restrictionPushforward j) :=
  Pullback.forwardMap_holomorphic (pieceInclusion_isLocalDiffeomorph j)

theorem restrictionPushforward_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph Iᴷ Iᴷ ω (restrictionPushforward j) :=
  Pullback.forwardMap_isLocalDiffeomorph (pieceInclusion_isLocalDiffeomorph j)

theorem restrictionPushforward_injective (j : Kind) :
    Function.Injective (restrictionPushforward j) := by
  intro p q h
  obtain ⟨x, v⟩ := p
  obtain ⟨y, w⟩ := q
  have hb : x.val = y.val := congrArg Bundle.TotalSpace.proj h
  have hxy : x = y := Subtype.ext hb
  subst y
  have hv : (restriction j x).symm v = (restriction j x).symm w :=
    congrArg (fun r : (fullBundle j).TotalSpace => id (α := ℂ) r.2) h
  have hvw := (restriction j x).symm.injective hv
  subst w
  rfl

/-- The full image is exactly the natural restricted bundle, not merely
an unspecified open image of the small bundle. -/
theorem restrictionPushforward_range (j : Kind) :
    range (restrictionPushforward j) =
      (fullBundleRestriction j : Set (fullBundle j).TotalSpace) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.proj.property
  · intro hp
    obtain ⟨x, v⟩ := p
    let a : SpecialEllipticPiece j := ⟨x, hp⟩
    refine ⟨⟨a, restriction j a v⟩, ?_⟩
    change (⟨x, (restriction j a).symm (restriction j a v)⟩ : (fullBundle j).TotalSpace) =
      ⟨x, v⟩
    rw [ContinuousLinearEquiv.symm_apply_apply]

def restrictionPushforwardToPiece (j : Kind) (p : (bundle j).TotalSpace) :
    fullBundleRestriction j := ⟨restrictionPushforward j p, p.proj.property⟩

@[simp] theorem restrictionPushforwardToPiece_val (j : Kind) (p : (bundle j).TotalSpace) :
    (restrictionPushforwardToPiece j p : (fullBundle j).TotalSpace) =
      restrictionPushforward j p := rfl

theorem restrictionPushforwardToPiece_bijective (j : Kind) :
    Function.Bijective (restrictionPushforwardToPiece j) := by
  constructor
  · intro p q h
    exact restrictionPushforward_injective j (congrArg Subtype.val h)
  · intro p
    have hp : p.val ∈ range (restrictionPushforward j) := by
      rw [restrictionPushforward_range]
      exact p.property
    obtain ⟨q, hq⟩ := hp
    exact ⟨q, Subtype.ext hq⟩

theorem restrictionPushforwardToPiece_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph Iᴷ Iᴷ ω (restrictionPushforwardToPiece j) :=
  isLocalDiffeomorph_codRestrictOpens Iᴷ Iᴷ
    (restrictionPushforward_isLocalDiffeomorph j) (fullBundleRestriction j)
    (fun p => p.proj.property)

/-- The actual restriction isomorphism of native canonical bundle total
spaces; both directions are holomorphic in the original bundle atlases. -/
def restrictionBundleBiholomorph (j : Kind) :
    Diffeomorph Iᴷ Iᴷ (bundle j).TotalSpace (fullBundleRestriction j) ω :=
  (restrictionPushforwardToPiece_isLocalDiffeomorph j).diffeomorphOfBijective
    (restrictionPushforwardToPiece_bijective j)

@[simp] theorem restrictionBundleBiholomorph_val (j : Kind) (p : (bundle j).TotalSpace) :
    (restrictionBundleBiholomorph j p : (fullBundle j).TotalSpace) =
      restrictionPushforward j p := rfl

@[simp] theorem restrictionBundleBiholomorph_proj (j : Kind) (p : (bundle j).TotalSpace) :
    (restrictionBundleBiholomorph j p).val.proj = p.proj.val := rfl

/-- The base comparison is literally the identity on the actual small piece. -/
theorem restrictionBundleBiholomorph_projection (j : Kind) (p : (bundle j).TotalSpace) :
    fullBundleRestrictionProjection j (restrictionBundleBiholomorph j p) = p.proj :=
  Subtype.ext rfl

@[simp] theorem restrictionBundleBiholomorph_mk (j : Kind) (x : SpecialEllipticPiece j)
    (v : (bundle j).Fiber x) :
    (restrictionBundleBiholomorph j ⟨x, v⟩ : (fullBundle j).TotalSpace) =
      ⟨x.val, (restriction j x).symm v⟩ := rfl

/-- The inverse map is the previously proved actual derivative pullback
on each fibre, at the actual point of the small open domain. -/
def restrictionTotalPullback (j : Kind) (p : fullBundleRestriction j) : (bundle j).TotalSpace :=
  ⟨fullBundleRestrictionProjection j p,
    restriction j (fullBundleRestrictionProjection j p) p.val.2⟩

@[simp] theorem restrictionTotalPullback_proj (j : Kind) (p : fullBundleRestriction j) :
    (restrictionTotalPullback j p).proj = fullBundleRestrictionProjection j p := rfl

theorem restrictionTotalPullback_leftInverse (j : Kind) :
    Function.LeftInverse (restrictionTotalPullback j) (restrictionPushforwardToPiece j) := by
  rintro ⟨x, v⟩
  change (⟨x, restriction j x ((restriction j x).symm v)⟩ : (bundle j).TotalSpace) = ⟨x, v⟩
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem restrictionTotalPullback_rightInverse (j : Kind) :
    Function.RightInverse (restrictionTotalPullback j) (restrictionPushforwardToPiece j) := by
  rintro ⟨⟨x, v⟩, hx⟩
  apply Subtype.ext
  let a : SpecialEllipticPiece j := ⟨x, hx⟩
  change (⟨x, (restriction j a).symm (restriction j a v)⟩ : (fullBundle j).TotalSpace) = ⟨x, v⟩
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem restrictionBundleBiholomorph_symm_apply (j : Kind) (p : fullBundleRestriction j) :
    (restrictionBundleBiholomorph j).symm p = restrictionTotalPullback j p := by
  apply (restrictionBundleBiholomorph j).injective
  exact ((restrictionBundleBiholomorph j).apply_symm_apply p).trans
    (restrictionTotalPullback_rightInverse j p).symm

theorem restrictionTotalPullback_holomorphic (j : Kind) :
    ContMDiff Iᴷ Iᴷ ω (restrictionTotalPullback j) := by
  have h : restrictionTotalPullback j =
      ((restrictionBundleBiholomorph j).symm :
        fullBundleRestriction j → (bundle j).TotalSpace) :=
    funext fun p => (restrictionBundleBiholomorph_symm_apply j p).symm
  rw [h]
  exact (restrictionBundleBiholomorph j).symm.contMDiff

theorem restrictionBundleBiholomorph_symm_proj (j : Kind) (p : fullBundleRestriction j) :
    ((restrictionBundleBiholomorph j).symm p).proj = fullBundleRestrictionProjection j p := by
  rw [restrictionBundleBiholomorph_symm_apply]
  rfl

/-- Fibrewise linearity is the genuine linearity of inverse derivative pullback. -/
theorem restrictionBundleBiholomorph_fiber_add (j : Kind) (x : SpecialEllipticPiece j)
    (v w : (bundle j).Fiber x) :
    id (α := (fullBundle j).Fiber x.val) (restrictionBundleBiholomorph j ⟨x, v + w⟩).val.2 =
      id (α := (fullBundle j).Fiber x.val) (restrictionBundleBiholomorph j ⟨x, v⟩).val.2 +
        id (α := (fullBundle j).Fiber x.val) (restrictionBundleBiholomorph j ⟨x, w⟩).val.2 :=
  (restriction j x).symm.map_add v w

theorem restrictionBundleBiholomorph_fiber_smul (j : Kind) (x : SpecialEllipticPiece j)
    (c : ℂ) (v : (bundle j).Fiber x) :
    id (α := (fullBundle j).Fiber x.val) (restrictionBundleBiholomorph j ⟨x, c • v⟩).val.2 =
      c • id (α := (fullBundle j).Fiber x.val) (restrictionBundleBiholomorph j ⟨x, v⟩).val.2 :=
  (restriction j x).symm.map_smul c v

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic
