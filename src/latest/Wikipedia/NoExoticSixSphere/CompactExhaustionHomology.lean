import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsInclusions
import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual singular homology along a compactly exhaustive family of subspaces

Every singular chain has compact support: it is a finite combination of
continuous simplices with compact domains. If every compact subset lies
in one of a family of subspaces, chains, cycles, and homology classes lift
to a member of the family. For an increasing family, a class becoming
zero in the ambient space becomes zero at some later stage as well.
-/

noncomputable section

open CategoryTheory Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.CompactExhaustionHomology

variable {X : Type} [TopologicalSpace X]

theorem chain_compact_support (d : ℕ) (c : Chains X d) :
    ∃ K : Set X, IsCompact K ∧ c ∈ supportedChainSubmodule K d := by
  classical
  let S := (chainsEquivFinsupp X d c).support
  let K : Set X := ⋃ σ ∈ S, Set.range σ
  refine ⟨K, S.isCompact_biUnion (fun σ _ ↦ isCompact_range σ.continuous), ?_⟩
  apply (mem_simplex_span_iff X d _ c).mpr
  intro σ hσ x hx
  exact Set.mem_iUnion.mpr ⟨σ, Set.mem_iUnion.mpr ⟨hσ, hx⟩⟩

theorem supported_mono {U V : Set X} (h : U ⊆ V) (d : ℕ) :
    supportedChainSubmodule U d ≤ supportedChainSubmodule V d :=
  Submodule.span_mono (Set.image_mono (fun _ hσ ↦ hσ.trans h))

theorem inclusion_chain_comp {U V : Set X} (h : U ⊆ V) (d : ℕ) (c : Chains U d) :
    inducedChain (subtypeInclusion V) d (inducedChain (ContinuousMap.inclusion h) d c) =
      inducedChain (subtypeInclusion U) d c :=
  (LinearMap.congr_fun
    (inducedChain_comp (ContinuousMap.inclusion h) (subtypeInclusion V) d) c).symm

theorem inclusion_homology_comp {U V : Set X} (h : U ⊆ V) (d : ℕ)
    (a : SingularHomology U d) :
    singularHomologyMap (subtypeInclusion V) d
      (singularHomologyMap (ContinuousMap.inclusion h) d a) =
        singularHomologyMap (subtypeInclusion U) d a :=
  (LinearMap.congr_fun
    (singularHomologyMap_comp (ContinuousMap.inclusion h) (subtypeInclusion V) d) a).symm

variable (U : ℕ → Set X) (hcompact : ∀ K : Set X, IsCompact K → ∃ k, K ⊆ U k)

include hcompact in
theorem exists_chain_lift (d : ℕ) (c : Chains X d) :
    ∃ k, ∃ z : Chains (U k) d, inducedChain (subtypeInclusion (U k)) d z = c := by
  obtain ⟨K, hK, hc⟩ := chain_compact_support d c
  obtain ⟨k, hk⟩ := hcompact K hK
  refine ⟨k, ?_⟩
  change c ∈ LinearMap.range (inducedChain (subtypeInclusion (U k)) d)
  rw [subtypeInclusion_chain_range]
  exact supported_mono hk d hc

include hcompact in
theorem exists_cycle_lift (d : ℕ) (c : ModuleHomology.Cycle (singularComplex X) d) :
    ∃ k, ∃ z : ModuleHomology.Cycle (singularComplex (U k)) d,
      ModuleHomology.mapCycles (singularChainMap (subtypeInclusion (U k))) d z = c := by
  obtain ⟨k, z, hz⟩ := exists_chain_lift U hcompact d c.val
  have hcycle : ((singularComplex (U k)).d d (d - 1)).hom z = 0 := by
    apply subtypeInclusion_chain_injective (U k) (d - 1)
    rw [map_zero, inducedChain_boundary, hz]
    exact ModuleHomology.cycle_condition (singularComplex X) d c
  refine ⟨k, ModuleHomology.mkCycle (singularComplex (U k)) d z hcycle, ?_⟩
  apply Subtype.ext
  exact (ModuleHomology.mapCycles_val _ d _).trans hz

include hcompact in
theorem exists_homology_lift (d : ℕ) (a : SingularHomology X d) :
    ∃ k, ∃ b : SingularHomology (U k) d, singularHomologyMap (subtypeInclusion (U k)) d b = a := by
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) d a
  obtain ⟨k, z, hz⟩ := exists_cycle_lift U hcompact d c
  refine ⟨k, ModuleHomology.cycleClass (singularComplex (U k)) d z, ?_⟩
  change (HomologicalComplex.homologyMap (singularChainMap (subtypeInclusion (U k))) d).hom
    (ModuleHomology.cycleClass (singularComplex (U k)) d z) = _
  rw [ModuleHomology.homologyMap_cycleClass, hz]

variable (hmono : Monotone U)

include hcompact hmono in
theorem exists_later_zero (k d : ℕ) (a : SingularHomology (U k) d)
    (ha : singularHomologyMap (subtypeInclusion (U k)) d a = 0) :
    ∃ m, ∃ hkm : k ≤ m, singularHomologyMap (ContinuousMap.inclusion (hmono hkm)) d a = 0 := by
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex (U k)) d a
  change (HomologicalComplex.homologyMap (singularChainMap (subtypeInclusion (U k))) d).hom
    (ModuleHomology.cycleClass (singularComplex (U k)) d c) = 0 at ha
  rw [ModuleHomology.homologyMap_cycleClass] at ha
  obtain ⟨b, hb⟩ := (ModuleHomology.cycleClass_eq_zero_iff (singularComplex X) d _).mp ha
  rw [ModuleHomology.mapCycles_val] at hb
  obtain ⟨l, z, hz⟩ := exists_chain_lift U hcompact (d + 1) b
  let m := max k l
  have hkm : k ≤ m := le_max_left _ _
  have hlm : l ≤ m := le_max_right _ _
  refine ⟨m, hkm, ?_⟩
  change (HomologicalComplex.homologyMap
    (singularChainMap (ContinuousMap.inclusion (hmono hkm))) d).hom
      (ModuleHomology.cycleClass (singularComplex (U k)) d c) = 0
  rw [ModuleHomology.homologyMap_cycleClass]
  apply (ModuleHomology.cycleClass_eq_zero_iff (singularComplex (U m)) d _).mpr
  refine ⟨inducedChain (ContinuousMap.inclusion (hmono hlm)) (d + 1) z, ?_⟩
  rw [ModuleHomology.mapCycles_val]
  apply subtypeInclusion_chain_injective (U m) d
  rw [inducedChain_boundary, inclusion_chain_comp, inclusion_chain_comp, hz]
  exact hb

end NoExoticSixSphere.CompactExhaustionHomology
