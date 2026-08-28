import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspRadius
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationProductOpen
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationProductDiffeomorph
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFourOpenSmooth
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealSphere
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRadial

/-!
# Standard sphere and open-ball coordinates on the actual round normal domain

Only native product and open-submanifold atlases are used. The real
sphere diffeomorphism, literal real/imaginary fibre coordinates, and
positive radial scaling turn the proved normal domain into the standard
unit two-sphere times the standard open unit four-ball.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

local notation "IP" => 𝓘(ℝ, Model)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "IF" => 𝓘(ℝ, Fibre)
local notation "I₄" => 𝓘(ℝ, RealFour.Space)
local notation "IS" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, RealFour.Space)

/-- The open normal product is literally the product with its round normal factor. -/
def roundProductSplitDiffeomorph :
    Diffeomorph IP ((IC).prod IF) roundNormalProduct
      (RiemannSphere × RealFour.roundFibreBall injectiveRadius) ω where
  toEquiv := (ProductOpen.diffeomorph IC IF ω
    (RealFour.roundFibreBall injectiveRadius)).toEquiv
  contMDiff_toFun := by
    have hf : ContMDiff IP IC ω (fun p : RiemannSphere × Fibre => p.1) := by
      simpa only [← modelWithCornersSelf_prod] using
        (contMDiff_fst (I := IC) (J := IF) (n := ω) (M := RiemannSphere) (N := Fibre))
    have hs : ContMDiff IP IF ω (fun p : RiemannSphere × Fibre => p.2) := by
      simpa only [← modelWithCornersSelf_prod] using
        (contMDiff_snd (I := IC) (J := IF) (n := ω) (M := RiemannSphere) (N := Fibre))
    have ht : ContMDiff IP IF ω (fun p : roundNormalProduct =>
        (⟨p.val.2, p.property⟩ : RealFour.roundFibreBall injectiveRadius)) := by
      intro p
      apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
      exact (hs.comp contMDiff_subtype_val) p
    exact (hf.comp contMDiff_subtype_val).prodMk ht
  contMDiff_invFun := by
    have h : ContMDiff ((IC).prod IF) IP ω
        (fun p : RiemannSphere × RealFour.roundFibreBall injectiveRadius => (p.1, p.2.val)) := by
      conv =>
        arg 2
        rw [modelWithCornersSelf_prod]
      change ContMDiff ((IC).prod IF) ((IC).prod IF) ω
        (fun p : RiemannSphere × RealFour.roundFibreBall injectiveRadius => (p.1, p.2.val))
      exact contMDiff_fst.prodMk (contMDiff_subtype_val.comp contMDiff_snd)
    intro p
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact h p

@[simp] theorem roundProductSplitDiffeomorph_apply (p : roundNormalProduct) :
    roundProductSplitDiffeomorph p = (p.val.1, ⟨p.val.2, p.property⟩) := rfl

@[simp] theorem roundProductSplitDiffeomorph_symm_coe
    (p : RiemannSphere × RealFour.roundFibreBall injectiveRadius) :
    (roundProductSplitDiffeomorph.symm p : RiemannSphere × Fibre) = (p.1, p.2.val) := rfl

/-- Native standard coordinates at the chosen, positive physical normal radius. -/
def roundProductStandardDiffeomorph :
    Diffeomorph IP IS roundNormalProduct
      (RealSphere.UnitTwoSphere × RealFour.standardFibreBall injectiveRadius) ω :=
  let e := productDiffeomorph RealSphere.sphereDiffeomorph
    (RealFour.openBallDiffeomorph injectiveRadius injectiveRadius_pos.le)
  roundProductSplitDiffeomorph.trans e

@[simp] theorem roundProductStandardDiffeomorph_apply (p : roundNormalProduct) :
    roundProductStandardDiffeomorph p =
      (RealSphere.sphereDiffeomorph p.val.1,
        RealFour.openBallDiffeomorph injectiveRadius injectiveRadius_pos.le
          ⟨p.val.2, p.property⟩) := rfl

/-- The literal standard two-sphere times the standard open unit four-ball. -/
abbrev StandardOpenNormalProduct :=
  RealSphere.UnitTwoSphere × Radial.ballOpen (E := RealFour.Space) 1

/-- Positive physical-radius scaling, followed by the genuine native inverse coordinates. -/
def standardUnitToNormalDiffeomorph :
    Diffeomorph IS IP StandardOpenNormalProduct roundNormalProduct ω :=
  ((Diffeomorph.refl (𝓡 2) RealSphere.UnitTwoSphere ω).prodCongr
      (Radial.ballDiffeomorph (E := RealFour.Space) injectiveRadius injectiveRadius_pos)).trans
    roundProductStandardDiffeomorph.symm

@[simp] theorem standardUnitToNormalDiffeomorph_coe (p : StandardOpenNormalProduct) :
    (standardUnitToNormalDiffeomorph p : RiemannSphere × Fibre) =
      (RealSphere.sphereDiffeomorph.symm p.1,
        RealFour.coordinateEquiv.symm (injectiveRadius • (p.2 : RealFour.Space))) := rfl

/-- The zero vector of the literal standard open unit four-ball. -/
def standardOpenZero : Radial.ballOpen (E := RealFour.Space) 1 :=
  ⟨0, by
    change (0 : RealFour.Space) ∈ ball (0 : RealFour.Space) 1
    simp⟩

@[simp] theorem standardUnitToNormalDiffeomorph_zeroSection (p : RealSphere.UnitTwoSphere) :
    standardUnitToNormalDiffeomorph (p, standardOpenZero) =
      (⟨(RealSphere.sphereDiffeomorph.symm p, 0),
        zero_mem_roundNormalProduct (RealSphere.sphereDiffeomorph.symm p)⟩ :
          roundNormalProduct) := by
  apply Subtype.ext
  rw [standardUnitToNormalDiffeomorph_coe]
  change (RealSphere.sphereDiffeomorph.symm p,
    RealFour.coordinateEquiv.symm (injectiveRadius • (0 : RealFour.Space))) = _
  rw [smul_zero, map_zero]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
