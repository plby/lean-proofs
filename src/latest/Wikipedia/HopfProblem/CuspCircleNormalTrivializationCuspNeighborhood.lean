import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspRadius

/-!
# An actual injective normal-product neighborhood of the original fixed curve

The round normal domain maps diffeomorphically onto an open subset of
the original threefold, using its original smooth atlas. Its zero
section is exactly the preexisting double-curve parametrization. The
inverse identifies the zero normal vector with the actual named curve.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold

local notation "IP" => 𝓘(ℝ, Model)
local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace

theorem roundToSmall_isLocalDiffeomorph : IsLocalDiffeomorph IP IP ω roundToSmall :=
  OpenRestriction.isLocalDiffeomorph_restrictOpens IP IP
    (Diffeomorph.refl IP (RiemannSphere × Fibre) ω).isLocalDiffeomorph
    roundNormalProduct smallNormalProduct (fun _ hx => roundNormalProduct_subset_small hx)

theorem roundProductMap_isLocalDiffeomorph :
    IsLocalDiffeomorph IP IX ω roundProductMap := by
  intro p
  exact (roundToSmall_isLocalDiffeomorph p).comp (K := IX) (P := Threefold.Space)
    (globalProductMap_isLocalDiffeomorph (roundToSmall p))

theorem roundProductMap_contMDiff : ContMDiff IP IX ω roundProductMap :=
  roundProductMap_isLocalDiffeomorph.contMDiff

theorem roundProductMap_isOpenMap : IsOpenMap roundProductMap :=
  roundProductMap_isLocalDiffeomorph.isOpenMap

/-- The actual open image in the original glued threefold. -/
def fixedCurveNeighborhood : TopologicalSpace.Opens Threefold.Space :=
  roundProductMap_isLocalDiffeomorph.image

@[simp] theorem fixedCurveNeighborhood_coe :
    (fixedCurveNeighborhood : Set Threefold.Space) = range roundProductMap := rfl

/-- The unchanged product map with codomain restricted to its actual image. -/
def roundProductIntoNeighborhood (p : roundNormalProduct) : fixedCurveNeighborhood :=
  ⟨roundProductMap p, mem_range_self p⟩

@[simp] theorem roundProductIntoNeighborhood_coe (p : roundNormalProduct) :
    (roundProductIntoNeighborhood p : Threefold.Space) = roundProductMap p := rfl

theorem roundProductIntoNeighborhood_isLocalDiffeomorph :
    IsLocalDiffeomorph IP IX ω roundProductIntoNeighborhood :=
  OpenRestriction.isLocalDiffeomorph_codRestrictOpens IP IX
    roundProductMap_isLocalDiffeomorph fixedCurveNeighborhood (fun p => mem_range_self p)

theorem roundProductIntoNeighborhood_bijective :
    Function.Bijective roundProductIntoNeighborhood := by
  constructor
  · intro p q hpq
    exact roundProductMap_injective (congrArg Subtype.val hpq)
  · rintro ⟨x, p, rfl⟩
    exact ⟨p, rfl⟩

/-- A real-analytic normal-product diffeomorphism onto the actual open neighborhood. -/
def normalNeighborhoodDiffeomorph :
    Diffeomorph IP IX roundNormalProduct fixedCurveNeighborhood ω :=
  roundProductIntoNeighborhood_isLocalDiffeomorph.diffeomorphOfBijective
    roundProductIntoNeighborhood_bijective

@[simp] theorem normalNeighborhoodDiffeomorph_coe (p : roundNormalProduct) :
    (normalNeighborhoodDiffeomorph p : Threefold.Space) = roundProductMap p := rfl

@[simp] theorem normalNeighborhoodDiffeomorph_zeroSection (p : RiemannSphere) :
    (normalNeighborhoodDiffeomorph ⟨(p, 0), zero_mem_roundNormalProduct p⟩ : Threefold.Space) =
      CuspGeometry.doubleCurveParametrization 1 p :=
  roundProductMap_zeroSection p

theorem doubleCurve_subset_fixedCurveNeighborhood :
    CuspGeometry.doubleCurve 1 ⊆ fixedCurveNeighborhood := by
  rw [← CuspGeometry.doubleCurveParametrization_range]
  rintro _ ⟨p, rfl⟩
  exact ⟨⟨(p, 0), zero_mem_roundNormalProduct p⟩, roundProductMap_zeroSection p⟩

/-- The actual named fixed curve is exactly the zero section in the injective neighborhood. -/
theorem roundProductMap_mem_doubleCurve_iff (p : roundNormalProduct) :
    roundProductMap p ∈ CuspGeometry.doubleCurve 1 ↔ p.val.2 = 0 := by
  rw [← CuspGeometry.doubleCurveParametrization_range]
  constructor
  · rintro ⟨a, ha⟩
    have he : p = (⟨(a, 0), zero_mem_roundNormalProduct a⟩ : roundNormalProduct) := by
      apply roundProductMap_injective
      exact ha.symm.trans (roundProductMap_zeroSection a).symm
    rw [he]
  · intro hp
    have he : p =
        (⟨(p.val.1, 0), zero_mem_roundNormalProduct p.val.1⟩ : roundNormalProduct) := by
      apply Subtype.ext
      exact Prod.ext rfl hp
    refine ⟨p.val.1, ?_⟩
    conv_rhs => rw [he]
    exact (roundProductMap_zeroSection p.val.1).symm

/-- The inverse coordinates detect the original curve, not just an auxiliary zero locus. -/
theorem normalNeighborhoodDiffeomorph_inverse_fibre_zero_iff (x : fixedCurveNeighborhood) :
    (normalNeighborhoodDiffeomorph.symm x).val.2 = 0 ↔
      (x : Threefold.Space) ∈ CuspGeometry.doubleCurve 1 := by
  rw [← roundProductMap_mem_doubleCurve_iff]
  have he : roundProductMap (normalNeighborhoodDiffeomorph.symm x) =
      (x : Threefold.Space) := by
    change (normalNeighborhoodDiffeomorph (normalNeighborhoodDiffeomorph.symm x) :
      Threefold.Space) = (x : Threefold.Space)
    rw [normalNeighborhoodDiffeomorph.apply_symm_apply]
  rw [he]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
