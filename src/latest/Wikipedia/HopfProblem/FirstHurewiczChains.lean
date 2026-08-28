import Wikipedia.HopfProblem.FirstHurewiczSimplex
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Concrete generators in the actual integral singular chain complex

All chain groups and homology groups in this file are those of Mathlib's
`singularChainComplexFunctor` with coefficient object `ModuleCat.of ℤ ℤ`.
The simplex generator is the coproduct inclusion evaluated at `1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.FirstHurewicz

variable (X : Type) [TopologicalSpace X]

/-- Mathlib's integral singular chain complex, with its actual coproducts. -/
abbrev singularComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ)

theorem singularComplex_eq : singularComplex X =
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X) := rfl

abbrev Chains (n : ℕ) := (singularComplex X).X n

abbrev SingularH1 := (singularComplex X).homology 1

abbrev SingularSimplex (n : ℕ) := C(stdSimplex ℝ (Fin (n + 1)), X)

/-- A continuous singular simplex viewed as an actual simplex of `toSSet`. -/
def simplexIndex (n : ℕ) (σ : SingularSimplex X n) :
    (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ :=
  ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌)).symm σ

/-- The actual singular chain generator with coefficient one. -/
def simplexChain (n : ℕ) (σ : SingularSimplex X n) : Chains X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := ModuleCat.of ℤ ℤ) (simplexIndex X n σ)) 1

abbrev boundaryOne : Chains X 1 →ₗ[ℤ] Chains X 0 := (singularComplex X).d 1 0 |>.hom

abbrev boundaryTwo : Chains X 2 →ₗ[ℤ] Chains X 1 := (singularComplex X).d 2 1 |>.hom

theorem simplexIndex_face (n : ℕ) (σ : SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (simplexIndex X (n + 1) σ) =
      simplexIndex X n (σ.comp (simplexFace n i)) := by
  rfl

/-- The alternating face formula, evaluated on an actual coproduct generator. -/
theorem boundary_simplex (n : ℕ) (σ : SingularSimplex X (n + 1)) :
    (singularComplex X).d (n + 1) n (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        simplexChain X n (σ.comp (simplexFace n i)) := by
  have h := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
    (R := ModuleCat.of ℤ ℤ) (simplexIndex X (n + 1) σ)
  let ev : (ModuleCat.of ℤ ℤ ⟶ Chains X n) →+ Chains X n :=
    { toFun := fun f => f.hom 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev h
  rw [map_sum] at he
  simp only [map_zsmul, simplexIndex_face] at he
  exact he

/-- The boundary of a singular edge is its final vertex minus its initial vertex. -/
theorem boundaryOne_simplex (σ : SingularSimplex X 1) :
    boundaryOne X (simplexChain X 1 σ) =
      simplexChain X 0 (σ.comp (simplexFace 0 0)) -
        simplexChain X 0 (σ.comp (simplexFace 0 1)) := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg] using boundary_simplex X 0 σ

/-- The boundary of a singular triangle is the alternating sum of its three edges. -/
theorem boundaryTwo_simplex (σ : SingularSimplex X 2) :
    boundaryTwo X (simplexChain X 2 σ) =
      simplexChain X 1 (σ.comp (simplexFace 1 0)) -
        simplexChain X 1 (σ.comp (simplexFace 1 1)) +
        simplexChain X 1 (σ.comp (simplexFace 1 2)) := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using boundary_simplex X 1 σ

theorem boundaryOne_boundaryTwo (c : Chains X 2) : boundaryOne X (boundaryTwo X c) = 0 := by
  have h := congrArg (fun f : Chains X 2 ⟶ Chains X 0 => f.hom c)
    ((singularComplex X).d_comp_d 2 1 0)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- The coproduct universal map determined by the values on singular simplices. -/
def chainLift (n : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : SingularSimplex X n → M) : Chains X n →ₗ[ℤ] M :=
  (Sigma.desc (fun s : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M
      (f ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌) s)))) :
    Chains X n ⟶ ModuleCat.of ℤ M).hom

@[simp] theorem chainLift_simplex (n : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    (f : SingularSimplex X n → M) (σ : SingularSimplex X n) :
    chainLift X n f (simplexChain X n σ) = f σ := by
  have h := Sigma.ι_desc
    (fun s : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ =>
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M
        (f ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌) s))))
    (simplexIndex X n σ)
  have he := congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ M => g.hom 1) h
  change chainLift X n f (simplexChain X n σ) =
    (LinearMap.toSpanSingleton ℤ M
      (f ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌) (simplexIndex X n σ)))) 1 at he
  simpa only [LinearMap.toSpanSingleton_apply_one, simplexIndex, Equiv.apply_symm_apply] using he

/-- A linear map on actual chains is determined by its simplex generators. -/
theorem chainMap_ext (n : ℕ) {M : Type} [AddCommGroup M] [Module ℤ M]
    {f g : Chains X n →ₗ[ℤ] M}
    (h : ∀ σ : SingularSimplex X n, f (simplexChain X n σ) = g (simplexChain X n σ)) :
    f = g := by
  have hcat : (ModuleCat.ofHom f : Chains X n ⟶ ModuleCat.of ℤ M) = ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change f (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := ModuleCat.of ℤ ℤ) s).hom 1) =
      g (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) s).hom 1)
    have hs := h ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌) s)
    simpa only [simplexChain, simplexIndex, Equiv.symm_apply_apply] using hs
  exact congrArg ModuleCat.Hom.hom hcat

namespace ChainHomology

section ShortComplex

variable (S : ShortComplex (ModuleCat.{0} ℤ))

abbrev ShortCycle := LinearMap.ker S.g.hom

local instance shortCycleModule : Module ℤ (ShortCycle S) :=
  (LinearMap.ker S.g.hom).module

abbrev ShortBoundaries : Submodule ℤ (ShortCycle S) :=
  LinearMap.range S.moduleCatToCycles

/-- The canonical quotient projection transported to actual categorical homology. -/
def shortCycleClass : ShortCycle S →ₗ[ℤ] S.homology :=
  S.moduleCatHomologyIso.inv.hom.comp (ShortBoundaries S).mkQ

theorem shortCycleClass_surjective : Function.Surjective (shortCycleClass S) :=
  ((ModuleCat.epi_iff_surjective S.moduleCatHomologyIso.inv).mp inferInstance).comp
    (ShortBoundaries S).mkQ_surjective

theorem shortCycleClass_eq_zero_iff (c : ShortCycle S) :
    shortCycleClass S c = 0 ↔ ∃ b : S.X₁, S.f b = c.1 := by
  have hinj : Function.Injective S.moduleCatHomologyIso.inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  constructor
  · intro h
    have hq : (Submodule.Quotient.mk c : ShortCycle S ⧸ ShortBoundaries S) = 0 :=
      hinj (h.trans S.moduleCatHomologyIso.inv.hom.map_zero.symm)
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero (ShortBoundaries S)).mp hq
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have hc : c ∈ ShortBoundaries S := ⟨b, Subtype.ext hb⟩
    have hq := (Submodule.Quotient.mk_eq_zero (ShortBoundaries S)).mpr hc
    exact (congrArg S.moduleCatHomologyIso.inv.hom hq).trans
      S.moduleCatHomologyIso.inv.hom.map_zero

abbrev ShortOpchains := S.X₂ ⧸ LinearMap.range S.f.hom

local instance shortOpchainsModule : Module ℤ (ShortOpchains S) :=
  Submodule.Quotient.module (LinearMap.range S.f.hom)

/-- The canonical embedding of homology in chains modulo boundaries. -/
def shortHomologyToChainClass : S.homology →ₗ[ℤ] ShortOpchains S :=
  (S.homologyι ≫ S.moduleCatOpcyclesIso.hom).hom

theorem shortHomologyToChainClass_injective :
    Function.Injective (shortHomologyToChainClass S) :=
  (ModuleCat.mono_iff_injective (S.homologyι ≫ S.moduleCatOpcyclesIso.hom)).mp inferInstance

theorem shortHomologyToChainClass_cycleClass (c : ShortCycle S) :
    shortHomologyToChainClass S (shortCycleClass S c) =
      (Submodule.Quotient.mk c.1 : ShortOpchains S) := by
  have hcat : S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv ≫
      S.homologyι ≫ S.moduleCatOpcyclesIso.hom =
      S.moduleCatLeftHomologyData.i ≫ ModuleCat.ofHom (LinearMap.range S.f.hom).mkQ := by
    rw [← S.moduleCatCyclesIso_inv_π_assoc, S.homology_π_ι_assoc,
      S.moduleCatCyclesIso_inv_iCycles_assoc, S.pOpcycles_comp_moduleCatOpcyclesIso_hom]
  exact congrArg (fun f => f.hom c) hcat

end ShortComplex

attribute [local instance] shortCycleModule
attribute [local instance] shortOpchainsModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)

/-- The concrete kernel describing degree-one cycles of the actual complex. -/
abbrev Cycle1 := ShortCycle (K.sc 1)

abbrev Boundaries1 : Submodule ℤ (Cycle1 K) := ShortBoundaries (K.sc 1)

/-- The actual homology class of a degree-one cycle. -/
def cycleClass : Cycle1 K →ₗ[ℤ] K.homology 1 := shortCycleClass (K.sc 1)

theorem cycleClass_surjective : Function.Surjective (cycleClass K) :=
  shortCycleClass_surjective (K.sc 1)

def mkCycle1 (z : K.X 1) (hz : (K.d 1 0).hom z = 0) : Cycle1 K :=
  ⟨z, by
    change (K.d 1 ((ComplexShape.down ℕ).next 1)).hom z = 0
    have hn : (ComplexShape.down ℕ).next 1 = 0 :=
      (ComplexShape.down ℕ).next_eq' (by simp)
    rw [hn]
    exact hz⟩

@[simp] theorem mkCycle1_val (z : K.X 1) (hz : (K.d 1 0).hom z = 0) :
    (mkCycle1 K z hz).1 = z := rfl

theorem cycleClass_eq_zero_iff (c : Cycle1 K) :
    cycleClass K c = 0 ↔ ∃ b : K.X 2, (K.d 2 1).hom b = c.1 := by
  change shortCycleClass (K.sc 1) c = 0 ↔ _
  rw [shortCycleClass_eq_zero_iff]
  change (∃ b : K.X ((ComplexShape.down ℕ).prev 1),
    (K.d ((ComplexShape.down ℕ).prev 1) 1).hom b = c.1) ↔ _
  have hp : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (by simp)
  rw [hp]

def boundaryCycle1 (b : K.X 2) : Cycle1 K :=
  mkCycle1 K ((K.d 2 1).hom b)
    (congrArg (fun f : K.X 2 ⟶ K.X 0 => f.hom b) (K.d_comp_d 2 1 0))

@[simp] theorem cycleClass_boundary (b : K.X 2) : cycleClass K (boundaryCycle1 K b) = 0 :=
  (cycleClass_eq_zero_iff K _).mpr ⟨b, rfl⟩

theorem cycleClass_eq_iff (c d : Cycle1 K) :
    cycleClass K c = cycleClass K d ↔ ∃ b : K.X 2, (K.d 2 1).hom b = c.1 - d.1 := by
  simpa only [map_sub, sub_eq_zero, Submodule.coe_sub] using
    (cycleClass_eq_zero_iff K (c - d))

/-- Degree-one chains modulo the image of the actual differential from degree two. -/
abbrev Opchains := K.X 1 ⧸ LinearMap.range (K.d 2 1).hom

local instance opchainsModule : Module ℤ (Opchains K) :=
  Submodule.Quotient.module (LinearMap.range (K.d 2 1).hom)

def chainClass : K.X 1 →ₗ[ℤ] Opchains K := (LinearMap.range (K.d 2 1).hom).mkQ

theorem chainClass_surjective : Function.Surjective (chainClass K) :=
  (LinearMap.range (K.d 2 1).hom).mkQ_surjective

@[simp] theorem chainClass_boundary (b : K.X 2) : chainClass K ((K.d 2 1).hom b) = 0 :=
  (Submodule.Quotient.mk_eq_zero (LinearMap.range (K.d 2 1).hom)).mpr ⟨b, rfl⟩

theorem chainClass_eq_iff (x y : K.X 1) :
    chainClass K x = chainClass K y ↔ ∃ b : K.X 2, (K.d 2 1).hom b = x - y :=
  Submodule.Quotient.eq _

theorem range_sc_one_f :
    LinearMap.range (K.sc 1).f.hom = LinearMap.range (K.d 2 1).hom := by
  change LinearMap.range (K.d ((ComplexShape.down ℕ).prev 1) 1).hom = _
  have hp : (ComplexShape.down ℕ).prev 1 = 2 :=
    (ComplexShape.down ℕ).prev_eq' (by simp)
  rw [hp]

def opchainsEquiv : ShortOpchains (K.sc 1) ≃ₗ[ℤ] Opchains K :=
  Submodule.quotEquivOfEq _ _ (range_sc_one_f K)

def homologyToChainClass : K.homology 1 →ₗ[ℤ] Opchains K :=
  (opchainsEquiv K).toLinearMap.comp (shortHomologyToChainClass (K.sc 1))

theorem homologyToChainClass_injective : Function.Injective (homologyToChainClass K) :=
  (opchainsEquiv K).injective.comp (shortHomologyToChainClass_injective (K.sc 1))

@[simp] theorem homologyToChainClass_cycleClass (c : Cycle1 K) :
    homologyToChainClass K (cycleClass K c) = chainClass K c.1 := by
  change opchainsEquiv K (shortHomologyToChainClass (K.sc 1)
    (shortCycleClass (K.sc 1) c)) = _
  rw [shortHomologyToChainClass_cycleClass]
  rfl

section Descent

variable {M : Type*} [AddCommGroup M] [Module ℤ M]
  (f : Cycle1 K →ₗ[ℤ] M) (hf : ∀ b : K.X 2, f (boundaryCycle1 K b) = 0)

include hf in
theorem boundaries1_le_ker : Boundaries1 K ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : cycleClass K c = 0 :=
    (shortCycleClass_eq_zero_iff (K.sc 1) c).mpr ⟨b, congrArg Subtype.val hb⟩
  obtain ⟨b', hb'⟩ := (cycleClass_eq_zero_iff K c).mp hc
  have he : boundaryCycle1 K b' = c := Subtype.ext hb'
  exact (congrArg f he).symm.trans (hf b')

/-- A linear map on actual cycles annihilating boundaries descends canonically
to the actual categorical homology object. -/
def homologyDesc : K.homology 1 →ₗ[ℤ] M :=
  ((Boundaries1 K).liftQ f (boundaries1_le_ker K f hf)).comp
    (K.sc 1).moduleCatHomologyIso.hom.hom

@[simp] theorem homologyDesc_cycleClass (c : Cycle1 K) :
    homologyDesc K f hf (cycleClass K c) = f c := by
  have h := congrArg (fun q => q.hom (Submodule.Quotient.mk c))
    (K.sc 1).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((Boundaries1 K).liftQ f (boundaries1_le_ker K f hf)) h

theorem homologyDesc_unique (g : K.homology 1 →ₗ[ℤ] M)
    (hg : ∀ c : Cycle1 K, g (cycleClass K c) = f c) : g = homologyDesc K f hf := by
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := cycleClass_surjective K z
  rw [hg, homologyDesc_cycleClass]

end Descent

end ChainHomology

/-- Integral one-cycles in the actual singular chain complex. -/
abbrev Cycles1 := ChainHomology.Cycle1 (singularComplex X)

instance cycles1Module : Module ℤ (Cycles1 X) :=
  ChainHomology.shortCycleModule ((singularComplex X).sc 1)

abbrev Boundaries1 : Submodule ℤ (Cycles1 X) :=
  ChainHomology.Boundaries1 (singularComplex X)

def cycleVal : Cycles1 X →ₗ[ℤ] Chains X 1 :=
  (LinearMap.ker ((singularComplex X).sc 1).g.hom).subtype

@[simp] theorem cycleVal_apply (c : Cycles1 X) : cycleVal X c = c.1 := rfl

def mkCycle1 (c : Chains X 1) (hc : boundaryOne X c = 0) : Cycles1 X :=
  ChainHomology.mkCycle1 (singularComplex X) c hc

@[simp] theorem mkCycle1_val (c : Chains X 1) (hc : boundaryOne X c = 0) :
    (mkCycle1 X c hc).1 = c := rfl

theorem cycles1_boundary (c : Cycles1 X) : boundaryOne X c.1 = 0 := by
  have hc := c.2
  change ((singularComplex X).d 1 ((ComplexShape.down ℕ).next 1)).hom c.1 = 0 at hc
  have hn : (ComplexShape.down ℕ).next 1 = 0 :=
    (ComplexShape.down ℕ).next_eq' (by simp)
  rw [hn] at hc
  exact hc

/-- Cycle classes in Mathlib's actual first singular homology object. -/
abbrev cycleClass : Cycles1 X →ₗ[ℤ] SingularH1 X :=
  ChainHomology.cycleClass (singularComplex X)

theorem cycleClass_surjective : Function.Surjective (cycleClass X) :=
  ChainHomology.cycleClass_surjective (singularComplex X)

def boundaryCycle (b : Chains X 2) : Cycles1 X :=
  ChainHomology.boundaryCycle1 (singularComplex X) b

@[simp] theorem boundaryCycle_val (b : Chains X 2) :
    (boundaryCycle X b).1 = boundaryTwo X b := rfl

@[simp] theorem cycleClass_boundary (b : Chains X 2) : cycleClass X (boundaryCycle X b) = 0 :=
  ChainHomology.cycleClass_boundary (singularComplex X) b

theorem cycleClass_eq_zero_iff (c : Cycles1 X) :
    cycleClass X c = 0 ↔ ∃ b : Chains X 2, boundaryTwo X b = c.1 :=
  ChainHomology.cycleClass_eq_zero_iff (singularComplex X) c

theorem cycleClass_eq_iff (c d : Cycles1 X) :
    cycleClass X c = cycleClass X d ↔ ∃ b : Chains X 2, boundaryTwo X b = c.1 - d.1 :=
  ChainHomology.cycleClass_eq_iff (singularComplex X) c d

/-- Actual singular one-chains modulo boundaries, before imposing the cycle condition. -/
abbrev Opchains := ChainHomology.Opchains (singularComplex X)

instance opchainsModule : Module ℤ (Opchains X) :=
  ChainHomology.opchainsModule (singularComplex X)

abbrev chainClass : Chains X 1 →ₗ[ℤ] Opchains X :=
  ChainHomology.chainClass (singularComplex X)

theorem chainClass_surjective : Function.Surjective (chainClass X) :=
  ChainHomology.chainClass_surjective (singularComplex X)

@[simp] theorem chainClass_boundary (b : Chains X 2) : chainClass X (boundaryTwo X b) = 0 :=
  ChainHomology.chainClass_boundary (singularComplex X) b

theorem chainClass_eq_iff (x y : Chains X 1) :
    chainClass X x = chainClass X y ↔ ∃ b : Chains X 2, boundaryTwo X b = x - y :=
  ChainHomology.chainClass_eq_iff (singularComplex X) x y

abbrev homologyToChainClass : SingularH1 X →ₗ[ℤ] Opchains X :=
  ChainHomology.homologyToChainClass (singularComplex X)

theorem homologyToChainClass_injective : Function.Injective (homologyToChainClass X) :=
  ChainHomology.homologyToChainClass_injective (singularComplex X)

@[simp] theorem homologyToChainClass_cycleClass (c : Cycles1 X) :
    homologyToChainClass X (cycleClass X c) = chainClass X c.1 :=
  ChainHomology.homologyToChainClass_cycleClass (singularComplex X) c

/-- Descent from cycles killing boundaries to actual first singular homology. -/
def homologyDesc {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : Cycles1 X →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryCycle X b) = 0) :
    SingularH1 X →ₗ[ℤ] M :=
  ChainHomology.homologyDesc (singularComplex X) f hf

@[simp] theorem homologyDesc_cycleClass {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : Cycles1 X →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryCycle X b) = 0)
    (c : Cycles1 X) : homologyDesc X f hf (cycleClass X c) = f c :=
  ChainHomology.homologyDesc_cycleClass (singularComplex X) f hf c

/-- A chain map annihilating degree-two boundaries induces a map on actual homology. -/
def homologyDescOfChain {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : Chains X 1 →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryTwo X b) = 0) :
    SingularH1 X →ₗ[ℤ] M :=
  homologyDesc X (f.comp (cycleVal X)) hf

@[simp] theorem homologyDescOfChain_cycleClass {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : Chains X 1 →ₗ[ℤ] M) (hf : ∀ b : Chains X 2, f (boundaryTwo X b) = 0)
    (c : Cycles1 X) : homologyDescOfChain X f hf (cycleClass X c) = f c.1 :=
  homologyDesc_cycleClass X (f.comp (cycleVal X)) hf c

end Wikipedia.HopfProblem.FirstHurewicz
