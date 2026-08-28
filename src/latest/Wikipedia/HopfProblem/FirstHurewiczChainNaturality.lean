import Wikipedia.HopfProblem.FirstHurewiczChains

/-!
# Naturality in the actual integral singular chain complex

The induced maps below are Mathlib's singular chain and singular homology
functor maps. Their concrete simplex and cycle formulas are proved from
the categorical coproduct and homology APIs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The actual singular chain map induced by a continuous map. -/
abbrev singularChainMap (f : C(X, Y)) : singularComplex X ⟶ singularComplex Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)

theorem singularChainMap_eq (f : C(X, Y)) : singularChainMap f =
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f) := rfl

abbrev inducedChain (f : C(X, Y)) (n : ℕ) : Chains X n →ₗ[ℤ] Chains Y n :=
  ((singularChainMap f).f n).hom

/-- The actual first singular homology map, not a map on a replacement presentation. -/
abbrev inducedHomology (f : C(X, Y)) : SingularH1 X →ₗ[ℤ] SingularH1 Y :=
  (HomologicalComplex.homologyMap (singularChainMap f) 1).hom

theorem inducedHomology_eq (f : C(X, Y)) : inducedHomology f =
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f))).hom := rfl

theorem simplexIndex_map (f : C(X, Y)) (n : ℕ) (σ : SingularSimplex X n) :
    (TopCat.toSSet.map (TopCat.ofHom f)).app (.op ⦋n⦌) (simplexIndex X n σ) =
      simplexIndex Y n (f.comp σ) := rfl

@[simp] theorem inducedChain_simplex (f : C(X, Y)) (n : ℕ) (σ : SingularSimplex X n) :
    inducedChain f n (simplexChain X n σ) = simplexChain Y n (f.comp σ) := by
  have h := SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom f))
    (ModuleCat.of ℤ ℤ) (simplexIndex X n σ)
  have he := congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ Chains Y n => g.hom 1) h
  change inducedChain f n (simplexChain X n σ) = simplexChain Y n (f.comp σ) at he
  exact he

theorem inducedChain_boundary (f : C(X, Y)) (i j : ℕ) (c : Chains X i) :
    inducedChain f j (((singularComplex X).d i j).hom c) =
      ((singularComplex Y).d i j).hom (inducedChain f i c) :=
  congrArg (fun g : Chains X i ⟶ Chains Y j => g.hom c) ((singularChainMap f).comm i j).symm

@[simp] theorem inducedChain_boundaryOne (f : C(X, Y)) (c : Chains X 1) :
    inducedChain f 0 (boundaryOne X c) = boundaryOne Y (inducedChain f 1 c) :=
  inducedChain_boundary f 1 0 c

@[simp] theorem inducedChain_boundaryTwo (f : C(X, Y)) (c : Chains X 2) :
    inducedChain f 1 (boundaryTwo X c) = boundaryTwo Y (inducedChain f 2 c) :=
  inducedChain_boundary f 2 1 c

@[simp] theorem inducedChain_id (n : ℕ) :
    inducedChain (ContinuousMap.id X) n = LinearMap.id := by
  apply chainMap_ext X n
  intro σ
  simp only [inducedChain_simplex, LinearMap.id_apply]
  rfl

theorem inducedChain_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    inducedChain (g.comp f) n = (inducedChain g n).comp (inducedChain f n) := by
  apply chainMap_ext X n
  intro σ
  simp only [LinearMap.comp_apply, inducedChain_simplex]
  rfl

@[simp] theorem inducedHomology_id : inducedHomology (ContinuousMap.id X) = LinearMap.id := by
  have h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map_id (TopCat.of X)
  exact congrArg ModuleCat.Hom.hom h

theorem inducedHomology_comp (f : C(X, Y)) (g : C(Y, Z)) :
    inducedHomology (g.comp f) = (inducedHomology g).comp (inducedHomology f) := by
  have h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom f) (TopCat.ofHom g)
  exact congrArg ModuleCat.Hom.hom h

namespace ChainHomology

attribute [local instance] shortCycleModule shortOpchainsModule opchainsModule

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (F : K ⟶ L)

abbrev shortMap : K.sc 1 ⟶ L.sc 1 :=
  (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) 1).map F

/-- The concrete cycle map transported through the canonical cycle isomorphisms. -/
def mapCycles : Cycle1 K →ₗ[ℤ] Cycle1 L :=
  ((K.sc 1).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap F) ≫
    (L.sc 1).moduleCatCyclesIso.hom).hom

@[simp] theorem mapCycles_val (c : Cycle1 K) :
    (mapCycles F c).1 = (F.f 1).hom c.1 := by
  have hcat : (K.sc 1).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap F) ≫
      (L.sc 1).moduleCatCyclesIso.hom ≫ (L.sc 1).moduleCatLeftHomologyData.i =
      (K.sc 1).moduleCatLeftHomologyData.i ≫ (shortMap F).τ₂ := by
    rw [(L.sc 1).moduleCatCyclesIso_hom_i, ShortComplex.cyclesMap_i,
      (K.sc 1).moduleCatCyclesIso_inv_iCycles_assoc]
  exact congrArg (fun f => f.hom c) hcat

theorem homologyMap_cycleClass (c : Cycle1 K) :
    (HomologicalComplex.homologyMap F 1).hom (cycleClass K c) =
      cycleClass L (mapCycles F c) := by
  have hcat : (K.sc 1).moduleCatLeftHomologyData.π ≫
      (K.sc 1).moduleCatHomologyIso.inv ≫ ShortComplex.homologyMap (shortMap F) =
      ((K.sc 1).moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap (shortMap F) ≫
        (L.sc 1).moduleCatCyclesIso.hom) ≫ (L.sc 1).moduleCatLeftHomologyData.π ≫
          (L.sc 1).moduleCatHomologyIso.inv := by
    simp only [Category.assoc, ← (K.sc 1).moduleCatCyclesIso_inv_π_assoc,
      ← (L.sc 1).moduleCatCyclesIso_inv_π, Iso.hom_inv_id_assoc]
    rw [ShortComplex.homologyπ_naturality]
  exact congrArg (fun f => f.hom c) hcat

theorem map_boundaries : LinearMap.range (K.d 2 1).hom ≤
    (LinearMap.range (L.d 2 1).hom).comap (F.f 1).hom := by
  rintro x ⟨b, rfl⟩
  refine ⟨(F.f 2).hom b, ?_⟩
  exact congrArg (fun f => f.hom b) (F.comm 2 1)

def mapOpchains : Opchains K →ₗ[ℤ] Opchains L :=
  (LinearMap.range (K.d 2 1).hom).mapQ (LinearMap.range (L.d 2 1).hom)
    (F.f 1).hom (map_boundaries F)

@[simp] theorem mapOpchains_chainClass (z : K.X 1) :
    mapOpchains F (chainClass K z) = chainClass L ((F.f 1).hom z) := rfl

theorem homologyToChainClass_naturality (h : K.homology 1) :
    homologyToChainClass L ((HomologicalComplex.homologyMap F 1).hom h) =
      mapOpchains F (homologyToChainClass K h) := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective K h
  calc
    _ = homologyToChainClass L (cycleClass L (mapCycles F c)) :=
      congrArg (homologyToChainClass L) (homologyMap_cycleClass F c)
    _ = chainClass L (mapCycles F c).1 := homologyToChainClass_cycleClass L _
    _ = chainClass L ((F.f 1).hom c.1) := congrArg (chainClass L) (mapCycles_val F c)
    _ = mapOpchains F (chainClass K c.1) := (mapOpchains_chainClass F c.1).symm
    _ = _ := congrArg (mapOpchains F) (homologyToChainClass_cycleClass K c).symm

end ChainHomology

/-- The actual induced map on concrete singular cycles. -/
def inducedCycles (f : C(X, Y)) : Cycles1 X →ₗ[ℤ] Cycles1 Y :=
  ChainHomology.mapCycles (singularChainMap f)

@[simp] theorem inducedCycles_val (f : C(X, Y)) (c : Cycles1 X) :
    (inducedCycles f c).1 = inducedChain f 1 c.1 :=
  ChainHomology.mapCycles_val (singularChainMap f) c

@[simp] theorem inducedCycles_boundaryCycle (f : C(X, Y)) (b : Chains X 2) :
    inducedCycles f (boundaryCycle X b) = boundaryCycle Y (inducedChain f 2 b) := by
  apply Subtype.ext
  exact (inducedCycles_val f (boundaryCycle X b)).trans (inducedChain_boundaryTwo f b)

/-- The canonical singular cycle-class map commutes with the actual homology functor. -/
@[simp] theorem inducedHomology_cycleClass (f : C(X, Y)) (c : Cycles1 X) :
    inducedHomology f (cycleClass X c) = cycleClass Y (inducedCycles f c) :=
  ChainHomology.homologyMap_cycleClass (singularChainMap f) c

/-- The induced map on actual one-chains modulo boundaries. -/
abbrev inducedOpchains (f : C(X, Y)) : Opchains X →ₗ[ℤ] Opchains Y :=
  ChainHomology.mapOpchains (singularChainMap f)

@[simp] theorem inducedOpchains_chainClass (f : C(X, Y)) (c : Chains X 1) :
    inducedOpchains f (chainClass X c) = chainClass Y (inducedChain f 1 c) :=
  ChainHomology.mapOpchains_chainClass (singularChainMap f) c

theorem homologyToChainClass_naturality (f : C(X, Y)) (h : SingularH1 X) :
    homologyToChainClass Y (inducedHomology f h) =
      inducedOpchains f (homologyToChainClass X h) :=
  ChainHomology.homologyToChainClass_naturality (singularChainMap f) h

end Wikipedia.HopfProblem.FirstHurewicz
