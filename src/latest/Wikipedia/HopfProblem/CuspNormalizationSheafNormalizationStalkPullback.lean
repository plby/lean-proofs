import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafNormalizationStalkPullbackFunctions
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspStalkAmbient
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspStalkBranchRepresentatives

/-!
# The actual first normalization arrow in analytic-germ coordinates

The morphism is the stalk map of the actual reduced-function pullback.
Its expression in the independently constructed stalk comparisons is
the existing coordinate-plane restriction map. This is checked on
actual ambient holomorphic representatives, which generate every
actual reduced-function stalk, rather than assumed as local exactness.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk

open CuspQuotient ToricCharts ToricSpace ToricComponent ToricFan SheafResolution

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3
local notation "I₂" => 𝓘(ℂ, CoordinateSpace 2)
local notation "I₃" => 𝓘(ℂ, CoordinateSpace 3)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Forgetting multiplication identifies the genuine additive reduced
stalk with the additive group of its genuine commutative-ring stalk. -/
def reducedStalkAddEquiv (x : CentralSpace C ε) :
    (reducedSheaf C ε hε hε1 hC hR).presheaf.stalk x ≃+
      (reducedRingSheaf C ε hε hε1 hC hR).presheaf.stalk x :=
  SheafForgetStalk.sheafStalkAddEquiv (reducedRingSheaf C ε hε hε1 hC hR) x

/-- The actual first sheaf arrow, evaluated by the actual stalk functor. -/
def normalizationStalkMap (x : CentralSpace C ε) :
    (reducedSheaf C ε hε hε1 hC hR).presheaf.stalk x →+
      (normalizationSheaf C ε hε).presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor (X := TopCat.of (CentralSpace C ε)) AddCommGrpCat x).map
    (normalizationPullback C ε hε hε1 hC hR).hom).hom

variable (a : Tube (disc ε)) (s : Triangle)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The actual additive reduced-function stalk in active-plane coordinates. -/
def reducedStalkEquiv (x : CentralSpace C ε) (hx : x.val ∈ (e).source) :
    (reducedSheaf C ε hε hε1 hC hR).presheaf.stalk x ≃+
      Germs.RestrictedAnalyticGerm (Germs.activeBranches ((e) x.val)) :=
  (reducedStalkAddEquiv C ε hε hε1 hC hR x).trans
    (cuspStalkEquiv C ε hε hε1 hC hR a s x hx).toAddEquiv

/-- The additive comparison retains the literal ambient representative
formula of the actual reduced ring stalk. -/
theorem reducedStalkEquiv_ambient (x : CentralSpace C ε) (hx : x.val ∈ (e).source)
    (V : Opens (QuotientSpace C ε)) (hxV : x.val ∈ V) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∀ g : HolomorphicFunctionSheaf.Section I₃ (QuotientSpace C ε) V,
    reducedStalkEquiv C ε hε hε1 hC hR a s x hx
      ((reducedSheaf C ε hε hε1 hC hR).presheaf.germ
        (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
        (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g)) =
      (Germs.toPlaneUnion (Germs.activeBranches ((e) x.val))).rangeRestrict
        (Germs.ofAnalytic (SheafManifoldStalk.centeredRepresentative e x.val V g)
          (SheafManifoldStalk.centeredRepresentative_analyticAt e
            (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
            x.val hx V g hxV)) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro g
  exact (congrArg (cuspStalkEquiv C ε hε hε1 hC hR a s x hx)
    (SheafForgetStalk.sheafStalkAddEquiv_germ
      (reducedRingSheaf C ε hε hε1 hC hR)
      (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
      (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g))).trans
        (cuspStalkEquiv_ambient C ε hε hε1 hC hR a s x hx V hxV g)

/-- On every actual ambient holomorphic representative, the actual
normalization sheaf pullback becomes the actual coordinate-plane pullback. -/
theorem normalizationStalkMap_ambient (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source) (V : Opens (QuotientSpace C ε)) (hxV : x.val ∈ V) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∀ g : HolomorphicFunctionSheaf.Section I₃ (QuotientSpace C ε) V,
    normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx
      (normalizationStalkMap C ε hε hε1 hC hR x
        ((reducedSheaf C ε hε hε1 hC hR).presheaf.germ
          (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
          (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g))) =
      Germs.toBranches (Germs.activeBranches ((e) x.val))
        (Germs.ofAnalytic (SheafManifoldStalk.centeredRepresentative e x.val V g)
          (SheafManifoldStalk.centeredRepresentative_analyticAt e
            (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s)
            x.val hx V g hxV)) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro g
  let b := (e) x.val
  let U := SheafReduced.ambientOpen (centralSet C ε) V
  let U' := (Opens.map (normalizationMap C ε hε)).obj U
  let r := SheafReduced.ambientRestriction I₃ (centralSet C ε) V g
  let f : HolomorphicFunctionSheaf.Section I₂ (rayDivisor 0) U' :=
    (normalizationPullback C ε hε hε1 hC hR).hom.app (op U) r
  let G := SheafManifoldStalk.centeredRepresentative e x.val V g
  have hG : AnalyticAt ℂ G (0 : E₃) :=
    SheafManifoldStalk.centeredRepresentative_analyticAt e
      (normalizationChart_mem_maximalAtlas C ε hε hε1 hC hR a s) x.val hx V g hxV
  funext j
  have hjU := branch_mem_preimage C ε hε hε1 hC hR a s b ((e).map_source hx)
    x ((e).left_inv hx).symm U hxV j
  have hf := branchSectionRepresentative_analyticAt C s j (removeCoordinate j b) U' f hjU
  have hfirst :
      normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx
          (normalizationStalkMap C ε hε hε1 hC hR x
            ((reducedSheaf C ε hε hε1 hC hR).presheaf.germ U x hxV r)) j =
        Germs.ofAnalytic (branchSectionRepresentative C s j (removeCoordinate j b) U' f) hf :=
    (congrArg (fun t => normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx t j)
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxV
        (normalizationPullback C ε hε hε1 hC hR).hom r)).trans
      (normalizationStalkEquiv_germ C ε hε hε1 hC hR a s b ((e).map_source hx)
        x ((e).left_inv hx).symm U hxV f j)
  refine hfirst.trans ?_
  change Germs.ofAnalytic (branchSectionRepresentative C s j (removeCoordinate j b) U' f) hf =
    Germs.toBranch j (Germs.ofAnalytic G hG)
  calc
    _ = Germs.normalizationBranchPullback C ε hε hε1 hC hR a s b
        ((e).map_source hx) j j.property (Germs.ofAnalytic G hG) := by
      rw [Germs.normalizationBranchPullback_ofAnalytic]
      apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
      have hext := normalizationPullback_ambient_extend C ε hε hε1 hC hR V g
      have he := centeredAmbient_comp_branch_eventuallyEq C ε hε hε1 hC hR a s b
        ((e).map_source hx) j j.property
        (HolomorphicFunctionSheaf.extendManifoldSection I₃ V g)
      filter_upwards [he] with y hy
      change HolomorphicFunctionSheaf.extendManifoldSection I₂ U' f
          (branchAffine C s j (removeCoordinate j b + y)) =
        HolomorphicFunctionSheaf.extendManifoldSection I₃ V g
          ((e).symm (b + Germs.centeredBranchMap C ε hε hε1 hC hR a s b j y))
      exact (congrFun hext (branchAffine C s j (removeCoordinate j b + y))).trans hy.symm
    _ = _ := congrArg (fun k => k (Germs.ofAnalytic G hG))
      (Germs.normalizationBranchPullback_eq_toBranch C ε hε hε1 hC hR a s b
        ((e).map_source hx) j j.property)

/-- The actual first normalization arrow is coordinate-plane restriction
under the independently proved genuine stalk equivalences. -/
theorem normalizationStalkMap_conjugacy (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source)
    (φ : (reducedSheaf C ε hε hε1 hC hR).presheaf.stalk x) :
    normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx
        (normalizationStalkMap C ε hε hε1 hC hR x φ) =
      Germs.restrictionToBranches (Germs.activeBranches ((e) x.val))
        (reducedStalkEquiv C ε hε hε1 hC hR a s x hx φ) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  obtain ⟨V, hxV, g, hg⟩ := SheafReduced.exists_ambient_germ_eq I₃ (centralSet C ε) x
    (reducedStalkAddEquiv C ε hε hε1 hC hR x φ)
  have hφ : (reducedSheaf C ε hε hε1 hC hR).presheaf.germ
      (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
      (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g) = φ := by
    apply (reducedStalkAddEquiv C ε hε hε1 hC hR x).injective
    exact (SheafForgetStalk.sheafStalkAddEquiv_germ
      (reducedRingSheaf C ε hε hε1 hC hR)
      (SheafReduced.ambientOpen (centralSet C ε) V) x hxV
      (SheafReduced.ambientRestriction I₃ (centralSet C ε) V g)).trans hg
  rw [← hφ, normalizationStalkMap_ambient, reducedStalkEquiv_ambient,
    Germs.restrictionToBranches_rangeRestrict]

/-- The same commutative diagram as equality of actual additive homomorphisms. -/
theorem normalizationStalkMap_conjugacy_hom (x : CentralSpace C ε)
    (hx : x.val ∈ (e).source) :
    (normalizationStalkEquivAt C ε hε hε1 hC hR a s x hx).toAddMonoidHom.comp
        (normalizationStalkMap C ε hε hε1 hC hR x) =
      (Germs.restrictionToBranches (Germs.activeBranches ((e) x.val))).toAddMonoidHom.comp
        (reducedStalkEquiv C ε hε hε1 hC hR a s x hx).toAddMonoidHom := by
  apply AddMonoidHom.ext
  exact normalizationStalkMap_conjugacy C ε hε hε1 hC hR a s x hx

end Wikipedia.HopfProblem.CuspNormalization.SheafNormalizationStalk
