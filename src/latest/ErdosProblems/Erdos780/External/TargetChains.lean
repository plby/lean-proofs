import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
Finite oriented simplex chains, implemented as the exterior algebra of the
free module on the vertices.  The exterior-algebra basis is indexed by
`Finset V`; its coordinate module is literally `Finset V →₀ R`.
-/

namespace TargetChains

open scoped BigOperators

universe u v

section Contraction

variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

theorem contraction_natural (εM : M →ₗ[R] R) (εN : N →ₗ[R] R)
    (f : M →ₗ[R] N) (hε : εN.comp f = εM) (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft εN (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft εM x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp [hx, hy]
  | ι_mul x m hx =>
      rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, hx]
      have hm := LinearMap.congr_fun hε m
      simp only [LinearMap.comp_apply] at hm
      rw [hm]
      simp

end Contraction

section FiniteVertices

variable (R : Type*) [CommRing R]
variable (V : Type u) [Fintype V] [LinearOrder V]

abbrev OrientedSimplex (q : ℕ) := Set.powersetCard V (q + 1)
abbrev Chain (q : ℕ) := OrientedSimplex V q →₀ R
abbrev FullChain := Finset V →₀ R

noncomputable def vertexBasis : Module.Basis V R (V →₀ R) := Finsupp.basisSingleOne

noncomputable def exteriorBasis :
    Module.Basis (Finset V) R (ExteriorAlgebra R (V →₀ R)) :=
  (vertexBasis R V).ExteriorAlgebra

noncomputable def toExterior :
    FullChain R V ≃ₗ[R] ExteriorAlgebra R (V →₀ R) :=
  (exteriorBasis R V).repr.symm

@[simp]
theorem toExterior_single (s : Finset V) (r : R) :
    toExterior R V (Finsupp.single s r) = r • exteriorBasis R V s := by
  simp [toExterior]

noncomputable def augmentation : (V →₀ R) →ₗ[R] R :=
  Finsupp.lsum R (fun _ => LinearMap.id)

noncomputable def exteriorContraction :
    ExteriorAlgebra R (V →₀ R) →ₗ[R] ExteriorAlgebra R (V →₀ R) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (V →₀ R)))
    (augmentation R V)

@[simp]
theorem augmentation_single (v : V) (r : R) :
    augmentation R V (Finsupp.single v r) = r := by
  simp [augmentation]

noncomputable def boundary : FullChain R V →ₗ[R] FullChain R V :=
  (exteriorBasis R V).repr ∘ₗ
    exteriorContraction R V ∘ₗ
      (exteriorBasis R V).repr.symm

@[simp]
theorem toExterior_boundary (c : FullChain R V) :
    toExterior R V (boundary R V c) =
      exteriorContraction R V (toExterior R V c) := by
  simp [boundary, toExterior]

theorem boundary_boundary (c : FullChain R V) :
    boundary R V (boundary R V c) = 0 := by
  apply (toExterior R V).injective
  rw [map_zero, toExterior_boundary, toExterior_boundary]
  change CliffordAlgebra.contractLeft (augmentation R V)
      (CliffordAlgebra.contractLeft (augmentation R V) (toExterior R V c)) = 0
  exact CliffordAlgebra.contractLeft_contractLeft _ _

/-! Ordinary (non-augmented) chains exclude the empty face.  We realize
them as the kernel of the empty-face coordinate, and explicitly project
away that coordinate after applying the augmented boundary. -/

noncomputable def positiveSubmodule : Submodule R (FullChain R V) :=
  LinearMap.ker (Finsupp.lapply ∅)

noncomputable abbrev PositiveChain := positiveSubmodule R V

noncomputable def positiveInclusion : PositiveChain R V →ₗ[R] FullChain R V :=
  (positiveSubmodule R V).subtype

noncomputable def projectPositive : FullChain R V →ₗ[R] PositiveChain R V where
  toFun c := ⟨c - Finsupp.single ∅ (c ∅), by
    change c ∅ - (Finsupp.single ∅ (c ∅)) ∅ = 0
    simp⟩
  map_add' c d := by
    apply Subtype.ext
    ext s
    by_cases hs : s = ∅
    · subst s; simp
    · simp [hs, Ne.symm hs]
  map_smul' r c := by
    apply Subtype.ext
    ext s
    by_cases hs : s = ∅
    · subst s; simp
    · simp [hs, Ne.symm hs]

@[simp]
theorem projectPositive_coe (c : FullChain R V) :
    (projectPositive R V c : FullChain R V) =
      c - Finsupp.single ∅ (c ∅) := rfl

@[simp]
theorem positiveInclusion_projectPositive (c : FullChain R V) :
    positiveInclusion R V (projectPositive R V c) =
      c - Finsupp.single ∅ (c ∅) := rfl

@[simp]
theorem projectPositive_apply_empty (c : FullChain R V) :
    (projectPositive R V c : FullChain R V) ∅ = 0 := by simp

@[simp]
theorem projectPositive_inclusion (c : PositiveChain R V) :
    projectPositive R V (positiveInclusion R V c) = c := by
  apply Subtype.ext
  rw [projectPositive_coe]
  have hc : (c : FullChain R V) ∅ = 0 := by
    have hc' := c.property
    change Finsupp.lapply ∅ (c : FullChain R V) = 0 at hc'
    simpa using hc'
  change (c : FullChain R V) -
      Finsupp.single (∅ : Finset V) ((c : FullChain R V) ∅) = (c : FullChain R V)
  rw [hc]
  simp

@[simp]
theorem projectPositive_single_empty (r : R) :
    projectPositive R V (Finsupp.single ∅ r) = 0 := by
  apply Subtype.ext
  ext s
  by_cases hs : s = ∅ <;> simp [projectPositive_coe, hs]

theorem boundary_single_empty (r : R) :
    boundary R V (Finsupp.single ∅ r) = 0 := by
  apply (toExterior R V).injective
  rw [map_zero, toExterior_boundary, toExterior_single]
  change CliffordAlgebra.contractLeft (augmentation R V)
      (r • exteriorBasis R V ∅) = 0
  rw [map_smul]
  suffices exteriorBasis R V ∅ = 1 by
    rw [this, CliffordAlgebra.contractLeft_one, smul_zero]
  change (vertexBasis R V).ExteriorAlgebra ∅ = 1
  simp [ExteriorAlgebra.basis_apply]

theorem boundary_projectPositive (c : FullChain R V) :
    boundary R V (positiveInclusion R V (projectPositive R V c)) =
      boundary R V c := by
  rw [positiveInclusion_projectPositive]
  rw [map_sub, boundary_single_empty, sub_zero]

noncomputable def reducedBoundary : PositiveChain R V →ₗ[R] PositiveChain R V :=
  projectPositive R V ∘ₗ boundary R V ∘ₗ positiveInclusion R V

theorem reducedBoundary_reducedBoundary (c : PositiveChain R V) :
    reducedBoundary R V (reducedBoundary R V c) = 0 := by
  apply Subtype.ext
  change (projectPositive R V
    (boundary R V (positiveInclusion R V (projectPositive R V
      (boundary R V (positiveInclusion R V c))))) : FullChain R V) = 0
  rw [boundary_projectPositive, boundary_boundary]
  simp

variable {R V}

noncomputable def vertexMap {W : Type v} [Fintype W] [LinearOrder W] (f : V → W) :
    (V →₀ R) →ₗ[R] (W →₀ R) :=
  Finsupp.lmapDomain R R f

@[simp]
theorem vertexMap_single {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (v : V) (r : R) :
    vertexMap f (Finsupp.single v r) = Finsupp.single (f v) r := by
  simp [vertexMap]

theorem augmentation_vertexMap {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) :
    (augmentation R W).comp (vertexMap f) = augmentation R V := by
  ext v r
  simp

noncomputable def map {W : Type v} [Fintype W] [LinearOrder W] (f : V → W) :
    FullChain R V →ₗ[R] FullChain R W :=
  (exteriorBasis R W).repr ∘ₗ
    (ExteriorAlgebra.map (vertexMap f)).toLinearMap ∘ₗ
      (exteriorBasis R V).repr.symm

@[simp]
theorem toExterior_map {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : FullChain R V) :
    toExterior R W (map f c) =
      ExteriorAlgebra.map (vertexMap f) (toExterior R V c) := by
  simp [map, toExterior]

theorem map_boundary {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : FullChain R V) :
    map f (boundary R V c) = boundary R W (map f c) := by
  apply (toExterior R W).injective
  simp only [toExterior_map, toExterior_boundary]
  exact (contraction_natural (augmentation R V) (augmentation R W)
    (vertexMap f) (augmentation_vertexMap f) (toExterior R V c)).symm

theorem map_single_empty {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (r : R) :
    map f (Finsupp.single ∅ r) = Finsupp.single ∅ r := by
  apply (toExterior R W).injective
  rw [toExterior_map, toExterior_single, toExterior_single, map_smul]
  suffices exteriorBasis R V ∅ = 1 ∧ exteriorBasis R W ∅ = 1 by
    rw [this.1, this.2, map_one]
  constructor <;> change (vertexBasis R _).ExteriorAlgebra ∅ = 1 <;>
    simp [ExteriorAlgebra.basis_apply]

theorem projectPositive_map_projectPositive {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : FullChain R V) :
    projectPositive R W
        (map f (positiveInclusion R V (projectPositive R V c))) =
      projectPositive R W (map f c) := by
  rw [positiveInclusion_projectPositive]
  rw [map_sub, map_single_empty, map_sub, projectPositive_single_empty]
  exact sub_zero (projectPositive R W (map f c))

noncomputable def reducedMap {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) : PositiveChain R V →ₗ[R] PositiveChain R W :=
  projectPositive R W ∘ₗ map f ∘ₗ positiveInclusion R V

theorem reducedMap_reducedBoundary {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (c : PositiveChain R V) :
    reducedMap f (reducedBoundary R V c) =
      reducedBoundary R W (reducedMap f c) := by
  apply Subtype.ext
  change (projectPositive R W
      (map f (positiveInclusion R V (projectPositive R V
        (boundary R V (positiveInclusion R V c))))) : FullChain R W) =
    projectPositive R W
      (boundary R W (positiveInclusion R W (projectPositive R W
        (map f (positiveInclusion R V c)))))
  rw [projectPositive_map_projectPositive, boundary_projectPositive, map_boundary]

/-! On a basis simplex, `map` is the exterior product of the vertex images.
This is the normalized simplicial map: alternation supplies the sorting sign,
and a repeated image vertex makes the result zero. -/

theorem toExterior_map_single {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (s : Finset V) :
    toExterior R W (map f (Finsupp.single s 1)) =
      ExteriorAlgebra.map (vertexMap f) (exteriorBasis R V s) := by
  simp

theorem map_single_eq_zero_of_not_injective {W : Type v} [Fintype W] [LinearOrder W]
    (f : V → W) (s : Finset V)
    (h : ¬ Function.Injective
      ((vertexMap (R := R) f) ∘ (vertexBasis R V) ∘
        Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.prodEquiv.symm s).2)) :
    map (R := R) f (Finsupp.single s (1 : R)) = 0 := by
  apply (toExterior R W).injective
  rw [map_zero, toExterior_map_single]
  change ExteriorAlgebra.map (vertexMap f)
      ((vertexBasis R V).ExteriorAlgebra s) = 0
  rw [ExteriorAlgebra.basis_apply]
  dsimp only [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.map_apply_ιMulti]
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  exact h

end FiniteVertices

end TargetChains
