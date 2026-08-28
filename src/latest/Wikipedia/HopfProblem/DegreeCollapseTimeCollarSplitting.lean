import Wikipedia.HopfProblem.DegreeCollapseTimeCollarOverlap
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# The actual homology sum of the two collared halves

Mayer--Vietoris applies to the constructed open enlargements and their
actual boundary overlap. Transport through the collar homotopy inverses
retains the two original half inclusions and the native integer actions.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

open SingularMayerVietoris PeriodTorusHigherHomology

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem open_halves_right_injective (k : ℕ) [Subsingleton (SingularHomology B k)] :
    Injective (rightHomologyMap (C.positiveOpen : Set M) (C.reverse.positiveOpen : Set M) k) := by
  let : Subsingleton (SingularHomology C.overlap k) :=
    (homotopyEquivHomologyEquiv C.overlapHomotopyEquiv k).injective.subsingleton
  intro x y hxy
  have hker : x - y ∈ LinearMap.ker
      (rightHomologyMap (C.positiveOpen : Set M) (C.reverse.positiveOpen : Set M) k) := by
    change rightHomologyMap (C.positiveOpen : Set M) (C.reverse.positiveOpen : Set M) k (x - y) = 0
    rw [map_sub, hxy, sub_self]
  rw [← exact_at_pair (C.positiveOpen : Set M) (C.reverse.positiveOpen : Set M)
    C.positiveOpen.isOpen C.reverse.positiveOpen.isOpen C.open_halves_cover] at hker
  obtain ⟨z, hz⟩ := hker
  have hz0 : z = 0 := Subsingleton.elim _ _
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

theorem open_halves_right_surjective (k : ℕ) [Subsingleton (SingularHomology B k)] :
    Surjective (rightHomologyMap (C.positiveOpen : Set M)
      (C.reverse.positiveOpen : Set M) (k + 1)) := by
  let : Subsingleton (SingularHomology C.overlap k) :=
    (homotopyEquivHomologyEquiv C.overlapHomotopyEquiv k).injective.subsingleton
  intro a
  have ha : a ∈ LinearMap.ker (connectingHomomorphism
      (C.positiveOpen : Set M) (C.reverse.positiveOpen : Set M)
      C.positiveOpen.isOpen C.reverse.positiveOpen.isOpen C.open_halves_cover k) :=
    Subsingleton.elim _ _
  rw [← exact_at_ambient] at ha
  exact ha

def halvesHomologySum (_C : TimeCollar t B) (k : ℕ) :
    (SingularHomology (NonnegativeHalf t) k ×
      SingularHomology (NonnegativeHalf (fun p ↦ -t p)) k) →ₗ[ℤ] SingularHomology M k := by
  let f := (singularHomologyMap (halfInclusion t) k).toAddMonoidHom.coprod
    (singularHomologyMap (halfInclusion (fun p ↦ -t p)) k).toAddMonoidHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r x := by
        convert! f.map_zsmul r x using 1
        exact int_smul_eq_zsmul .. }

theorem halvesHomologySum_apply (k : ℕ)
    (x : SingularHomology (NonnegativeHalf t) k ×
      SingularHomology (NonnegativeHalf (fun p ↦ -t p)) k) :
    C.halvesHomologySum k x = singularHomologyMap (halfInclusion t) k x.1 +
      singularHomologyMap (halfInclusion (fun p ↦ -t p)) k x.2 := rfl

def halvesToOpenHomologyEquiv (k : ℕ) :
    (SingularHomology (NonnegativeHalf t) k ×
      SingularHomology (NonnegativeHalf (fun p ↦ -t p)) k) ≃ₗ[ℤ]
        (SingularHomology C.positiveOpen k × SingularHomology C.reverse.positiveOpen k) := by
  let e := (homotopyEquivHomologyEquiv C.positiveHalfHomotopyEquiv k).symm.toAddEquiv.prodCongr
    (homotopyEquivHomologyEquiv C.reverse.positiveHalfHomotopyEquiv k).symm.toAddEquiv
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' r x := by
        convert! e.toAddMonoidHom.map_zsmul r x using 1 }

theorem open_halves_right_original_sum (k : ℕ)
    (x : SingularHomology (NonnegativeHalf t) k ×
      SingularHomology (NonnegativeHalf (fun p ↦ -t p)) k) :
    rightHomologyMap (C.positiveOpen : Set M) (C.reverse.positiveOpen : Set M) k
      (C.halvesToOpenHomologyEquiv k x) = C.halvesHomologySum k x := by
  change singularHomologyMap (subtypeInclusion (C.positiveOpen : Set M)) k
      (singularHomologyMap C.positiveHalfHomotopyEquiv.invFun k x.1) +
    singularHomologyMap (subtypeInclusion (C.reverse.positiveOpen : Set M)) k
      (singularHomologyMap C.reverse.positiveHalfHomotopyEquiv.invFun k x.2) =
    singularHomologyMap (halfInclusion t) k x.1 +
      singularHomologyMap (halfInclusion (fun p ↦ -t p)) k x.2
  simp only [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    positiveHalf_inverse_inclusion]

theorem halvesHomologySum_injective (k : ℕ) [Subsingleton (SingularHomology B k)] :
    Injective (C.halvesHomologySum k) := by
  have hb := (C.open_halves_right_injective k).comp (C.halvesToOpenHomologyEquiv k).injective
  have he : (rightHomologyMap (C.positiveOpen : Set M) (C.reverse.positiveOpen : Set M) k) ∘
      C.halvesToOpenHomologyEquiv k = C.halvesHomologySum k :=
    funext (C.open_halves_right_original_sum k)
  rw [he] at hb
  exact hb

theorem halvesHomologySum_bijective (k : ℕ) [Subsingleton (SingularHomology B k)]
    [Subsingleton (SingularHomology B (k + 1))] : Bijective (C.halvesHomologySum (k + 1)) := by
  refine ⟨C.halvesHomologySum_injective (k + 1), ?_⟩
  have hb := (C.open_halves_right_surjective k).comp
    (C.halvesToOpenHomologyEquiv (k + 1)).surjective
  have he : (rightHomologyMap (C.positiveOpen : Set M)
      (C.reverse.positiveOpen : Set M) (k + 1)) ∘
      C.halvesToOpenHomologyEquiv (k + 1) = C.halvesHomologySum (k + 1) :=
    funext (C.open_halves_right_original_sum (k + 1))
  rw [he] at hb
  exact hb

include C in
theorem halfInclusion_homology_injective (k : ℕ) [Subsingleton (SingularHomology B k)] :
    Injective (singularHomologyMap (halfInclusion t) k) := by
  intro x y hxy
  have he : C.halvesHomologySum k (x, 0) = C.halvesHomologySum k (y, 0) := by
    simpa only [halvesHomologySum_apply, map_zero, add_zero] using hxy
  exact congrArg Prod.fst (C.halvesHomologySum_injective k he)

include C in
theorem negativeInclusion_homology_injective (k : ℕ) [Subsingleton (SingularHomology B k)] :
    Injective (singularHomologyMap (halfInclusion (fun p ↦ -t p)) k) := by
  intro x y hxy
  have he : C.halvesHomologySum k (0, x) = C.halvesHomologySum k (0, y) := by
    simpa only [halvesHomologySum_apply, map_zero, zero_add] using hxy
  exact congrArg Prod.snd (C.halvesHomologySum_injective k he)

include C in
theorem half_homology_finite (k : ℕ) [Subsingleton (SingularHomology B k)]
    [Finite (SingularHomology M k)] : Finite (SingularHomology (NonnegativeHalf t) k) :=
  Finite.of_injective _ (C.halfInclusion_homology_injective k)

include C in
theorem negative_homology_finite (k : ℕ) [Subsingleton (SingularHomology B k)]
    [Finite (SingularHomology M k)] :
    Finite (SingularHomology (NonnegativeHalf (fun p ↦ -t p)) k) :=
  Finite.of_injective _ (C.negativeInclusion_homology_injective k)

include C in
theorem half_homology_subsingleton (k : ℕ) [Subsingleton (SingularHomology B k)]
    [Subsingleton (SingularHomology M k)] : Subsingleton (SingularHomology (NonnegativeHalf t) k) :=
  (C.halfInclusion_homology_injective k).subsingleton

include C in
theorem negative_homology_subsingleton (k : ℕ) [Subsingleton (SingularHomology B k)]
    [Subsingleton (SingularHomology M k)] :
    Subsingleton (SingularHomology (NonnegativeHalf (fun p ↦ -t p)) k) :=
  (C.negativeInclusion_homology_injective k).subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
