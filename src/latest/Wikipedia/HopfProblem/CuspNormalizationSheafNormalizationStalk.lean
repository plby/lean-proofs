import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalkBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalkBranches

/-!
# The actual normalization sheaf stalk as actual branch analytic germs

This is the composite of the proved finite-pushforward stalk equivalence,
the actual fibre enumeration by active branches, and the genuine analytic
branch-chart stalk comparisons. Its formula on actual section germs is
literal composition with the actual translated affine branch maps.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk

open CuspQuotient ToricCharts ToricSpace ToricComponent ToricFan SheafResolution

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : CoordinateSpace 3)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- Reindex the actual fibre stalks and use the actual centered chart at
each branch centre. This is an equivalence of their existing rings. -/
def branchProductEquiv (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) :
    (∀ y : normalizationMap C ε hε ⁻¹' {x},
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)).stalk
        y.val) ≃+* (Germs.activeBranches b → Germs.BranchGerm) :=
  (RingEquiv.piCongrLeft'
    (fun y : normalizationMap C ε hε ⁻¹' {x} =>
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)).stalk y.val)
    (actualFibreEquiv C ε hε hε1 hC hR a s b hb x hxb).symm).trans
      (RingEquiv.piCongrRight fun j : Germs.activeBranches b =>
        branchStalkEquiv C s j (removeCoordinate j b))

@[simp] theorem branchProductEquiv_apply (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b)
    (φ : ∀ y : normalizationMap C ε hε ⁻¹' {x},
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)).stalk y.val)
    (j : Germs.activeBranches b) :
    branchProductEquiv C ε hε hε1 hC hR a s b hb x hxb φ j =
      branchStalkEquiv C s j (removeCoordinate j b)
        (φ (actualFibreEquiv C ε hε hε1 hC hR a s b hb x hxb j)) := rfl

/-- The actual additive stalk of the normalization direct image is the
product of actual two-variable analytic-germ rings in the active branches. -/
def normalizationStalkEquiv (hb : b ∈ (e).target) (x : CentralSpace C ε)
    (hxb : (x : QuotientSpace C ε) = (e).symm b) :
    (normalizationSheaf C ε hε).presheaf.stalk x ≃+
      (Germs.activeBranches b → Germs.BranchGerm) :=
  (finiteStalkEquiv C ε hε hε1 hC hR x).trans
    (branchProductEquiv C ε hε hε1 hC hR a s b hb x hxb).toAddEquiv

@[simp] theorem normalizationStalkEquiv_apply (hb : b ∈ (e).target)
    (x : CentralSpace C ε) (hxb : (x : QuotientSpace C ε) = (e).symm b)
    (φ : (normalizationSheaf C ε hε).presheaf.stalk x) (j : Germs.activeBranches b) :
    normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb φ j =
      branchStalkEquiv C s j (removeCoordinate j b)
        (finiteStalkEquiv C ε hε hε1 hC hR x φ
          (actualFibreEquiv C ε hε hε1 hC hR a s b hb x hxb j)) := rfl

/-- On actual section germs, the branch representative is the literal
section composed with `branchAffine C s j (removeCoordinate j b + z)`. -/
@[simp] theorem normalizationStalkEquiv_germ (hb : b ∈ (e).target)
    (x : CentralSpace C ε) (hxb : (x : QuotientSpace C ε) = (e).symm b)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) (j : Germs.activeBranches b) :
    normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb
        ((normalizationSheaf C ε hε).presheaf.germ U x hxU f) j =
      Germs.ofAnalytic
        (branchSectionRepresentative C s j (removeCoordinate j b)
          ((Opens.map (normalizationMap C ε hε)).obj U) f)
        (branchSectionRepresentative_analyticAt C s j (removeCoordinate j b)
          ((Opens.map (normalizationMap C ε hε)).obj U) f
          (branch_mem_preimage C ε hε hε1 hC hR a s b hb x hxb U hxU j)) :=
  (congrArg (branchStalkEquiv C s j (removeCoordinate j b))
    (finiteStalkEquiv_germ C ε hε hε1 hC hR x U hxU f
      (actualFibreEquiv C ε hε hε1 hC hR a s b hb x hxb j))).trans
    (branchStalkEquiv_germ C s j (removeCoordinate j b)
      ((Opens.map (normalizationMap C ε hε)).obj U)
      (branch_mem_preimage C ε hε hε1 hC hR a s b hb x hxb U hxU j) f)

@[simp] theorem normalizationStalkEquiv_germ_eval (hb : b ∈ (e).target)
    (x : CentralSpace C ε) (hxb : (x : QuotientSpace C ε) = (e).symm b)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0)
      ((Opens.map (normalizationMap C ε hε)).obj U)) (j : Germs.activeBranches b) :
    Germs.eval (0 : CoordinateSpace 2)
        (normalizationStalkEquiv C ε hε hε1 hC hR a s b hb x hxb
          ((normalizationSheaf C ε hε).presheaf.germ U x hxU f) j) =
      f ⟨branchAffine C s j (removeCoordinate j b),
        branch_mem_preimage C ε hε hε1 hC hR a s b hb x hxb U hxU j⟩ := by
  rw [normalizationStalkEquiv_germ, Germs.eval_ofAnalytic, branchSectionRepresentative_zero]

omit b in
/-- The same equivalence with the chart coordinate of the actual point
selected automatically, as used in the local resolution diagram. -/
def normalizationStalkEquivAt (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    (normalizationSheaf C ε hε).presheaf.stalk x ≃+
      (Germs.activeBranches ((e) x.val) → Germs.BranchGerm) :=
  normalizationStalkEquiv C ε hε hε1 hC hR a s ((e) x.val) ((e).map_source hx)
    x ((e).left_inv hx).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk
