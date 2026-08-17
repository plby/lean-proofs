import ErdosProblems.Erdos780.External.TargetChains
import ErdosProblems.Erdos780.External.TargetBridge

/-!
The positive-dimensional target complex.  The empty finset is deliberately
removed: it is fixed by every vertex permutation and therefore cannot occur
in the free-orbit argument.
-/

namespace PositiveTarget

open TargetChains TargetBridge

noncomputable section

universe u v

variable (R : Type*) [CommRing R]
variable (V : Type u) [Fintype V] [LinearOrder V]

abbrev Chain := PositiveChain R V

abbrev boundary : Chain R V →ₗ[R] Chain R V := reducedBoundary R V

theorem boundary_boundary (c : Chain R V) :
    boundary R V (boundary R V c) = 0 :=
  reducedBoundary_reducedBoundary R V c

/-! A vertex is a genuine positive chain, and the truncated boundary drops
its augmented empty-face boundary. -/
theorem iota_single_eq_exteriorBasis_singleton (v : V) :
    ExteriorAlgebra.ι R (Finsupp.single v 1) =
      exteriorBasis R V {v} := by
  change ExteriorAlgebra.ι R (Finsupp.single v 1) =
    (vertexBasis R V).ExteriorAlgebra {v}
  have hb := ExteriorAlgebra.basis_apply_ofCard (vertexBasis R V)
    (s := ({v} : Finset V)) (n := 1) (by simp)
  rw [hb]
  simp only [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp [vertexBasis, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_singleton]

theorem wedgePrepend_apply_empty (v : V) (c : FullChain ℤ V) :
    TargetBridge.wedgePrepend v c ∅ = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, Finsupp.add_apply, hc, hd, add_zero]
  | single s z =>
      rw [show Finsupp.single s z = z • Finsupp.single s (1 : ℤ) by
        simp]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      suffices TargetBridge.wedgePrepend v (Finsupp.single s (1 : ℤ)) ∅ = 0 by
        rw [this, mul_zero]
      by_cases hvs : v ∈ s
      · have hprod : exteriorBasis ℤ V {v} * exteriorBasis ℤ V s = 0 := by
          let sv : Set.powersetCard V 1 := ⟨{v}, by simp⟩
          let ss : Set.powersetCard V s.card := ⟨s, rfl⟩
          apply ExteriorAlgebra.basis_mul_of_not_disjoint (vertexBasis ℤ V) sv ss
          simpa [sv, ss, Finset.disjoint_singleton_left]
        have hw : TargetBridge.wedgePrepend v
            (Finsupp.single s (1 : ℤ)) = 0 := by
          apply (toExterior ℤ V).injective
          rw [map_zero, TargetBridge.toExterior_wedgePrepend,
            toExterior_single, one_smul,
            iota_single_eq_exteriorBasis_singleton, hprod]
        rw [hw]
        rfl
      · let sv : Set.powersetCard V 1 := ⟨{v}, by simp⟩
        let ss : Set.powersetCard V s.card := ⟨s, rfl⟩
        have hd : Disjoint sv.val ss.val := by
          simpa [sv, ss, Finset.disjoint_singleton_left]
        let u : Finset V := (Set.powersetCard.disjUnion hd).val
        have hu : u ≠ ∅ := by
          intro hu0
          have hvu : v ∈ u := by
            change v ∈ (Set.powersetCard.disjUnion hd).val
            simp [Set.powersetCard.disjUnion, sv, ss]
          simpa [hu0] using hvu
        have hw : TargetBridge.wedgePrepend v
            (Finsupp.single s (1 : ℤ)) =
            (Set.powersetCard.permOfDisjoint hd).sign •
              Finsupp.single u (1 : ℤ) := by
          apply (toExterior ℤ V).injective
          rw [TargetBridge.toExterior_wedgePrepend, toExterior_single, one_smul,
            iota_single_eq_exteriorBasis_singleton]
          change (vertexBasis ℤ V).ExteriorAlgebra sv.val *
              (vertexBasis ℤ V).ExteriorAlgebra ss.val = _
          rw [ExteriorAlgebra.basis_mul_of_disjoint (vertexBasis ℤ V) sv ss hd]
          simp [u, exteriorBasis]
        rw [hw]
        simp [hu]

theorem fullBoundary_singleton (v : V) :
    TargetChains.boundary R V (Finsupp.single {v} 1) =
      Finsupp.single ∅ 1 := by
  apply (toExterior R V).injective
  rw [toExterior_boundary, toExterior_single, toExterior_single]
  rw [← iota_single_eq_exteriorBasis_singleton]
  rw [one_smul]
  change CliffordAlgebra.contractLeft (augmentation R V)
      (ExteriorAlgebra.ι R (Finsupp.single v 1)) =
    (1 : R) • exteriorBasis R V ∅
  rw [show exteriorBasis R V ∅ = 1 by
    change (vertexBasis R V).ExteriorAlgebra ∅ = 1
    simp [ExteriorAlgebra.basis_apply]]
  simp [CliffordAlgebra.contractLeft_ι, augmentation_single]

noncomputable def vertex (v : V) : Chain R V :=
  projectPositive R V (Finsupp.single {v} 1)

@[simp]
theorem boundary_vertex (v : V) :
    boundary R V (vertex R V v) = 0 := by
  apply Subtype.ext
  change (projectPositive R V
    (TargetChains.boundary R V
      (positiveInclusion R V (projectPositive R V
        (Finsupp.single {v} 1)))) : FullChain R V) = 0
  rw [TargetChains.boundary_projectPositive, fullBoundary_singleton,
    projectPositive_single_empty]
  rfl

/-! This is the ordinary augmentation on 0-chains.  Algebraically it is
the empty-face coefficient of the augmented boundary before that coordinate
is discarded. -/
noncomputable def augmentation : Chain R V →ₗ[R] R :=
  Finsupp.lapply ∅ ∘ₗ TargetChains.boundary R V ∘ₗ positiveInclusion R V

theorem augmentation_boundary (c : Chain R V) :
    augmentation R V (boundary R V c) = 0 := by
  change TargetChains.boundary R V
      (positiveInclusion R V (projectPositive R V
        (TargetChains.boundary R V (positiveInclusion R V c)))) ∅ = 0
  rw [TargetChains.boundary_projectPositive, TargetChains.boundary_boundary]
  rfl

variable {R V}

noncomputable def map {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) : Chain R V →ₗ[R] Chain R W :=
  reducedMap f

theorem map_boundary {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : Chain R V) :
    map f (boundary R V c) = boundary R W (map f c) :=
  reducedMap_reducedBoundary f c

section Labels

variable {X : Type*}

noncomputable def labelLists (lab : X → V) :
    SourceFlags.Chain X →ₗ[ℤ] Chain ℤ V :=
  projectPositive ℤ V ∘ₗ TargetBridge.labelLists lab

theorem labelList_nil_eq_single_empty (lab : X → V) :
    TargetBridge.labelList lab [] = Finsupp.single ∅ 1 := by
  apply (toExterior ℤ V).injective
  rw [toExterior_labelList_nil, toExterior_single]
  rw [one_smul]
  change (1 : ExteriorAlgebra ℤ (V →₀ ℤ)) =
    (vertexBasis ℤ V).ExteriorAlgebra ∅
  simp [ExteriorAlgebra.basis_apply]

@[simp]
theorem labelLists_empty (lab : X → V) :
    labelLists lab (SourceFlags.basis []) = 0 := by
  simp only [labelLists, LinearMap.comp_apply, TargetBridge.labelLists_basis]
  rw [labelList_nil_eq_single_empty, projectPositive_single_empty]

theorem labelLists_basis (lab : X → V) (l : List X) :
    labelLists lab (SourceFlags.basis l) =
      projectPositive ℤ V (TargetBridge.labelList lab l) := by
  simp [labelLists]

theorem labelList_apply_empty_of_nonempty (lab : X → V)
    (l : List X) (hl : l ≠ []) :
    TargetBridge.labelList lab l ∅ = 0 := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hl
  exact wedgePrepend_apply_empty (V := V) (v := lab x)
    (TargetBridge.labelList lab xs)

/- On every actual (nonempty) source flag, projection does nothing: the
reduced label map is literally the pre-existing exterior-algebra label. -/
theorem positiveInclusion_labelLists_basis_of_nonempty (lab : X → V)
    (l : List X) (hl : l ≠ []) :
    positiveInclusion ℤ V (labelLists lab (SourceFlags.basis l)) =
      TargetBridge.labelList lab l := by
  rw [labelLists_basis, positiveInclusion_projectPositive]
  rw [labelList_apply_empty_of_nonempty lab l hl]
  simp

theorem labelLists_boundary (lab : X → V) (c : SourceFlags.Chain X) :
    boundary ℤ V (labelLists lab c) =
      labelLists lab (SourceFlags.boundary c) := by
  apply Subtype.ext
  change (projectPositive ℤ V
      (TargetChains.boundary ℤ V
        (positiveInclusion ℤ V (projectPositive ℤ V
          (TargetBridge.labelLists lab c)))) : FullChain ℤ V) =
    projectPositive ℤ V
      (TargetBridge.labelLists lab (SourceFlags.boundary c))
  rw [boundary_projectPositive, TargetBridge.labelLists_boundary]

end Labels

end

end PositiveTarget
