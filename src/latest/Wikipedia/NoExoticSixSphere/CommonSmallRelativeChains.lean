import Wikipedia.NoExoticSixSphere.CommonSmallChains
import Wikipedia.NoExoticSixSphere.RelativeCoefficientCycleRepresentatives
import Wikipedia.NoExoticSixSphere.SmallCoefficientChainRange

/-!
# Relative classes represented by chains small for both covers

A subspace contained in a member of each cover maps into their common
small subcomplex. Quotienting by its original chains gives a genuine
relative comparison. The two short exact sequences and subdivision
prove this comparison is a quasi-isomorphism, with its original maps.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.CommonSmallRelative

open SingularSubcomplex SimplicialCoefficients

variable {X : Type} [TopologicalSpace X] (U A V B W : Set X)
  (hWA : W ⊆ A) (hWB : W ⊆ B)

/-- The original singular subspace maps into the simultaneous small subcomplex. -/
def subspaceMap : singular W ⟶ (commonSmall U A V B : SSet) :=
  (supportIso W).hom ≫ SSet.Subcomplex.homOfLE
    (le_inf ((support_mono hWA).trans le_sup_right) ((support_mono hWB).trans le_sup_right))

@[reassoc]
theorem subspaceMap_inclusion :
    subspaceMap U A V B W hWA hWB ≫ commonSmallInclusion U A V B =
      SingularSubcomplex.inclusion W := by
  dsimp [subspaceMap, commonSmallInclusion]
  rw [Category.assoc, SSet.Subcomplex.homOfLE_ι, supportIso_hom_inclusion]

variable (R : ModuleCat.{0} ℤ)

/-- The coefficient-chain map of the actual subspace inclusion into common small chains. -/
abbrev subspaceChainMap := (chains R).map (subspaceMap U A V B W hWA hWB)

@[reassoc]
theorem subspaceChainMap_inclusion :
    subspaceChainMap U A V B W hWA hWB R ≫ commonSmallChainInclusion U A V B R =
      RelativeCoefficients.inclusion R W := by
  rw [← Functor.map_comp, subspaceMap_inclusion]
  rfl

theorem subspaceChainMap_mono : Mono (subspaceChainMap U A V B W hWA hWB R) := by
  dsimp [subspaceChainMap, subspaceMap]
  infer_instance

/-- The actual common small chains modulo the original subspace chains. -/
abbrev complex : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (subspaceChainMap U A V B W hWA hWB R)

abbrev projection : (commonSmall U A V B : SSet).chainComplex R ⟶
    complex U A V B W hWA hWB R := cokernel.π _

abbrev sequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (subspaceChainMap U A V B W hWA hWB R)
    (projection U A V B W hWA hWB R) (cokernel.condition _)

theorem sequence_shortExact : (sequence U A V B W hWA hWB R).ShortExact where
  exact := ShortComplex.exact_cokernel (subspaceChainMap U A V B W hWA hWB R)
  mono_f := subspaceChainMap_mono U A V B W hWA hWB R
  epi_g := inferInstanceAs (Epi (cokernel.π (subspaceChainMap U A V B W hWA hWB R)))

/-- The map induced by the original common-small inclusion into ambient relative chains. -/
def comparison : complex U A V B W hWA hWB R ⟶ RelativeCoefficients.complex R W :=
  cokernel.map (subspaceChainMap U A V B W hWA hWB R) (RelativeCoefficients.inclusion R W)
    (𝟙 _) (commonSmallChainInclusion U A V B R)
    ((subspaceChainMap_inclusion U A V B W hWA hWB R).trans (Category.id_comp _).symm)

@[reassoc]
theorem projection_comparison :
    projection U A V B W hWA hWB R ≫ comparison U A V B W hWA hWB R =
      commonSmallChainInclusion U A V B R ≫ RelativeCoefficients.projection R W :=
  cokernel.π_desc _ _ _

/-- This map of actual pair sequences is the identity on the original subspace. -/
def sequenceMap : sequence U A V B W hWA hWB R ⟶ RelativeCoefficients.sequence R W where
  τ₁ := 𝟙 _
  τ₂ := commonSmallChainInclusion U A V B R
  τ₃ := comparison U A V B W hWA hWB R
  comm₁₂ := (Category.id_comp _).trans (subspaceChainMap_inclusion U A V B W hWA hWB R).symm
  comm₂₃ := (projection_comparison U A V B W hWA hWB R).symm

/-- The relative common-small comparison is a quasi-isomorphism with finite coefficients. -/
theorem comparison_mod_quasiIso (p : ℕ) (hp : p ≠ 0)
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ) :
    QuasiIso (comparison U A V B W hWA hWB (ModuleCat.of ℤ (ZMod p))) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (sequenceMap U A V B W hWA hWB (ModuleCat.of ℤ (ZMod p)))
    (sequence_shortExact U A V B W hWA hWB (ModuleCat.of ℤ (ZMod p)))
    (RelativeCoefficients.sequence_shortExact (ModuleCat.of ℤ (ZMod p)) W)
    (inferInstanceAs (QuasiIso (𝟙 ((singular W).chainComplex (ModuleCat.of ℤ (ZMod p))))))
    (commonSmallInclusion_mod_quasiIso U A V B p hp hU hA hUA hV hB hVB)

include hWA hWB

/-- Every original relative class has an actual simultaneous-small chain representative. -/
theorem exists_representative (p : ℕ) (hp : p ≠ 0)
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ)
    (n : ℕ) (a : (RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W).homology n) :
    ∃ c : ((commonSmall U A V B : SSet).chainComplex (ModuleCat.of ℤ (ZMod p))).X n,
      ∃ hc : ((RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W).d n (n - 1)).hom
        (RelativeCoefficients.quotientMap (ModuleCat.of ℤ (ZMod p)) W n
          (((commonSmallChainInclusion U A V B (ModuleCat.of ℤ (ZMod p))).f n).hom c)) = 0,
      ModuleHomology.cycleClass (RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W) n
        (ModuleHomology.mkCycle (RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W) n
          (RelativeCoefficients.quotientMap (ModuleCat.of ℤ (ZMod p)) W n
            (((commonSmallChainInclusion U A V B (ModuleCat.of ℤ (ZMod p))).f n).hom c)) hc) =
        a := by
  let R := ModuleCat.of ℤ (ZMod p)
  let Q := complex U A V B W hWA hWB R
  let f := comparison U A V B W hWA hWB R
  let π := projection U A V B W hWA hWB R
  let : QuasiIso f := comparison_mod_quasiIso U A V B W hWA hWB p hp hU hA hUA hV hB hVB
  obtain ⟨a', ha'⟩ := (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap f n)).mp
    inferInstance a
  obtain ⟨z, hz⟩ := ModuleHomology.cycleClass_surjective Q n a'
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (π.f n)).mp inferInstance z.1
  have he := congrArg (fun m => (m.f n).hom c) (projection_comparison U A V B W hWA hWB R)
  have hv : (ModuleHomology.mapCycles f n z).1 =
      RelativeCoefficients.quotientMap R W n
        (((commonSmallChainInclusion U A V B R).f n).hom c) :=
    (ModuleHomology.mapCycles_val f n z).trans ((congrArg (f.f n).hom hc).symm.trans he)
  have hcycle : ((RelativeCoefficients.complex R W).d n (n - 1)).hom
      (RelativeCoefficients.quotientMap R W n
        (((commonSmallChainInclusion U A V B R).f n).hom c)) = 0 := by
    rw [← hv]
    exact ModuleHomology.cycle_condition _ n (ModuleHomology.mapCycles f n z)
  refine ⟨c, hcycle, ?_⟩
  exact (congrArg (ModuleHomology.cycleClass (RelativeCoefficients.complex R W) n)
    (Subtype.ext hv.symm)).trans ((ModuleHomology.homologyMap_cycleClass f n z).symm.trans
      ((congrArg (HomologicalComplex.homologyMap f n).hom hz).trans ha'))

/-- Two native small representatives of one relative class have the same ambient chain. -/
theorem exists_two_small_representatives (p : ℕ) (hp : p ≠ 0)
    (hU : IsOpen U) (hA : IsOpen A) (hUA : U ∪ A = Set.univ)
    (hV : IsOpen V) (hB : IsOpen B) (hVB : V ∪ B = Set.univ)
    (n : ℕ) (a : (RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W).homology n) :
    ∃ c : CoefficientChains.Chains (ModuleCat.of ℤ (ZMod p)) X n,
      ∃ cU : SmallChains (ModuleCat.of ℤ (ZMod p)) U A n,
      ∃ cV : SmallChains (ModuleCat.of ℤ (ZMod p)) V B n,
      smallInclusionMap (ModuleCat.of ℤ (ZMod p)) U A n cU = c ∧
      smallInclusionMap (ModuleCat.of ℤ (ZMod p)) V B n cV = c ∧
      ((SphereHomologyCoefficients.coefficientComplex (ModuleCat.of ℤ (ZMod p)) X).d
        n (n - 1)).hom c ∈
        LinearMap.range ((RelativeCoefficients.inclusion (ModuleCat.of ℤ (ZMod p)) W).f
          (n - 1)).hom ∧
      ∃ hc : ((RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W).d n (n - 1)).hom
          (RelativeCoefficients.quotientMap (ModuleCat.of ℤ (ZMod p)) W n c) = 0,
        ModuleHomology.cycleClass (RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W) n
          (ModuleHomology.mkCycle (RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p)) W) n
            (RelativeCoefficients.quotientMap (ModuleCat.of ℤ (ZMod p)) W n c) hc) = a := by
  let R := ModuleCat.of ℤ (ZMod p)
  obtain ⟨z, hz, hclass⟩ :=
    exists_representative U A V B W hWA hWB p hp hU hA hUA hV hB hVB n a
  let c := ((commonSmallChainInclusion U A V B R).f n).hom z
  have hsmall :
      c ∈ LinearMap.range (smallInclusionMap R U A n) ⊓
        LinearMap.range (smallInclusionMap R V B n) := by
    exact (commonSmallInclusion_range U A V B R n).le ⟨z, rfl⟩
  obtain ⟨cU, hcU⟩ := hsmall.1
  obtain ⟨cV, hcV⟩ := hsmall.2
  refine ⟨c, cU, cV, hcU, hcV, ?_, hz, hclass⟩
  exact (RelativeCoefficients.quotientMap_eq_zero_iff R W (n - 1) _).mp
    ((RelativeCoefficients.boundary_quotientMap R W n (n - 1) c).symm.trans hz)

end NoExoticSixSphere.CommonSmallRelative
