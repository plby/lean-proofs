import Wikipedia.NoExoticSixSphere.CoefficientChainCarrierMap
import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria

/-!
# Actual singular homology representatives in directed open covers

Compact carriers put each original finite coefficient chain in a cover
member. Degreewise injectivity of the actual chain inclusion reflects
the cycle condition. A boundary in the ambient space is already a
boundary in a sufficiently large member, again by its compact carrier.
No injectivity of any homology inclusion is assumed.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.DirectedOpenCover

open RelativeCoefficients

variable {X : Type} [TopologicalSpace X] {ι : Type*} [Nonempty ι]
  (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
  (hdir : Directed (· ⊆ ·) U) (hcover : ⋃ i, U i = Set.univ)

include hU hdir hcover

/-- Each actual compact subset is contained in one member of the directed open cover. -/
theorem exists_compact_subset (K : Set X) (hK : IsCompact K) : ∃ i, K ⊆ U i :=
  hK.elim_directed_cover U hU (hcover ▸ Set.subset_univ K) hdir

variable (A : ModuleCat.{0} ℤ)

/-- Each original coefficient chain lifts to a chain on one actual cover member. -/
theorem exists_chain (k : ℕ) (c : CoefficientChains.Chains A X k) :
    ∃ (i : ι) (b : CoefficientChains.Chains A (U i) k),
      ((inclusion A (U i)).f k).hom b = c := by
  obtain ⟨K, hK, b, hb⟩ := CoefficientChains.exists_compactCarrier A X k c
  obtain ⟨i, hi⟩ := exists_compact_subset U hU hdir hcover K hK
  exact ⟨i, CoefficientChains.inclusion_range_mono A hi k ⟨b, hb⟩⟩

/-- The actual lifted chain is a cycle, reflected by the original degreewise injection. -/
theorem exists_cycle (k : ℕ) (c : ModuleHomology.Cycle (coefficientComplex A X) k) :
    ∃ (i : ι) (z : ModuleHomology.Cycle (coefficientComplex A (U i)) k),
      ModuleHomology.mapCycles (inclusion A (U i)) k z = c := by
  obtain ⟨i, b, hb⟩ := exists_chain U hU hdir hcover A k c.val
  let f := inclusion A (U i)
  have hz : ((coefficientComplex A (U i)).d k (k - 1)).hom b = 0 :=
    ModuleHomology.cycle_of_boundary_relation f k
      ((ModuleCat.mono_iff_injective (f.f (k - 1))).mp inferInstance)
      c.val (ModuleHomology.cycle_condition (coefficientComplex A X) k c) b 0
      (by rw [map_zero, hb, sub_self])
  let z := ModuleHomology.mkCycle (coefficientComplex A (U i)) k b hz
  exact ⟨i, z, Subtype.ext ((ModuleHomology.mapCycles_val f k z).trans hb)⟩

/-- Every original homology class comes from an actual member of the directed cover. -/
theorem exists_homology_class (k : ℕ) (a : (coefficientComplex A X).homology k) :
    ∃ (i : ι) (b : (coefficientComplex A (U i)).homology k),
      (HomologicalComplex.homologyMap (inclusion A (U i)) k).hom b = a := by
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (coefficientComplex A X) k a
  obtain ⟨i, z, hz⟩ := exists_cycle U hU hdir hcover A k c
  refine ⟨i, ModuleHomology.cycleClass (coefficientComplex A (U i)) k z, ?_⟩
  exact (ModuleHomology.homologyMap_cycleClass (inclusion A (U i)) k z).trans
    (congrArg (ModuleHomology.cycleClass (coefficientComplex A X) k) hz)

/-- An actual ambient boundary already bounds after passage to a larger cover member. -/
theorem exists_boundary_lift (i : ι) (k : ℕ)
    (c : CoefficientChains.Chains A (U i) k)
    (b : CoefficientChains.Chains A X (k + 1))
    (hb : ((coefficientComplex A X).d (k + 1) k).hom b =
      ((inclusion A (U i)).f k).hom c) :
    ∃ (j : ι) (hij : U i ⊆ U j) (v : CoefficientChains.Chains A (U j) (k + 1)),
      ((coefficientComplex A (U j)).d (k + 1) k).hom v =
        ((spaceMap A (ContinuousMap.inclusion hij)).f k).hom c := by
  obtain ⟨j₀, v₀, hv₀⟩ := exists_chain U hU hdir hcover A (k + 1) b
  obtain ⟨j, hij, hj₀⟩ := hdir i j₀
  obtain ⟨v, hv⟩ := CoefficientChains.inclusion_range_mono A hj₀ (k + 1) ⟨v₀, hv₀⟩
  let t := spaceMap A (ContinuousMap.inclusion hij)
  let f := inclusion A (U j)
  have ht : t ≫ f = inclusion A (U i) := by
    change spaceMap A (ContinuousMap.inclusion hij) ≫
      spaceMap A (subtypeInclusion (U j)) = spaceMap A (subtypeInclusion (U i))
    rw [← spaceMap_comp]
    rfl
  refine ⟨j, hij, v, ?_⟩
  apply (ModuleCat.mono_iff_injective (f.f k)).mp inferInstance
  exact (congrArg (fun m => m.hom v) (f.comm (k + 1) k)).symm.trans
    ((congrArg ((coefficientComplex A X).d (k + 1) k).hom hv).trans
      (hb.trans (congrArg (fun m => (m.f k).hom c) ht).symm))

/-- A class killed by the ambient map is killed in some actual larger cover member. -/
theorem homology_eventually_zero (i : ι) (k : ℕ)
    (a : (coefficientComplex A (U i)).homology k)
    (ha : (HomologicalComplex.homologyMap (inclusion A (U i)) k).hom a = 0) :
    ∃ (j : ι) (hij : U i ⊆ U j),
      (HomologicalComplex.homologyMap (spaceMap A (ContinuousMap.inclusion hij)) k).hom a = 0 := by
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (coefficientComplex A (U i)) k a
  have hc : ModuleHomology.cycleClass (coefficientComplex A X) k
      (ModuleHomology.mapCycles (inclusion A (U i)) k c) = 0 :=
    (ModuleHomology.homologyMap_cycleClass (inclusion A (U i)) k c).symm.trans ha
  obtain ⟨b, hb⟩ := (ModuleHomology.cycleClass_eq_zero_iff (coefficientComplex A X) k _).mp hc
  obtain ⟨j, hij, v, hv⟩ := exists_boundary_lift U hU hdir hcover A i k c.val b
    (hb.trans (ModuleHomology.mapCycles_val (inclusion A (U i)) k c))
  refine ⟨j, hij, ?_⟩
  apply (ModuleHomology.homologyMap_cycleClass
    (spaceMap A (ContinuousMap.inclusion hij)) k c).trans
  apply (ModuleHomology.cycleClass_eq_zero_iff (coefficientComplex A (U j)) k _).mpr
  exact ⟨v, hv.trans (ModuleHomology.mapCycles_val
    (spaceMap A (ContinuousMap.inclusion hij)) k c).symm⟩

end NoExoticSixSphere.DirectedOpenCover
