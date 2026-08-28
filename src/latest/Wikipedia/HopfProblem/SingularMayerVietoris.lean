import Wikipedia.HopfProblem.SingularMayerVietorisSequence
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceRightTransport
import Wikipedia.HopfProblem.SingularMayerVietorisSmallEquivalence
import Wikipedia.HopfProblem.SingularMayerVietorisSubdivisionChainHomotopy

/-!
# The actual integral singular Mayer–Vietoris sequence

For an open cover by two subsets, barycentric subdivision proves that
the actual small-chain inclusion induces a homology isomorphism. We
transport the proved small-chain sequence through that isomorphism.
Every homology object below is Mathlib's actual integral singular homology.

The first map is the difference of the intersection inclusions, the
second is the sum of the two inclusions into the ambient space, and the
connecting map comes from the actual short exact sequence of small chains.
The only geometric hypotheses are openness and the covering equality.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

/-- The difference of the two actual intersection inclusions on homology. -/
abbrev leftHomologyMap (U V : Set X) (n : ℕ) :
    SingularHomology (U ∩ V : Set X) n →ₗ[ℤ]
      (SingularHomology U n × SingularHomology V n) :=
  smallLeftHomologyMap U V n

/-- The sum of the actual subtype-inclusion maps into ambient singular homology. -/
def rightHomologyMap (U V : Set X) (n : ℕ) :
    (SingularHomology U n × SingularHomology V n) →ₗ[ℤ] SingularHomology X n := by
  let f := (singularHomologyMap (subtypeInclusion U) n).toAddMonoidHom.coprod
    (singularHomologyMap (subtypeInclusion V) n).toAddMonoidHom
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' r a := by
        convert! f.map_zsmul r a using 1
        exact int_smul_eq_zsmul .. }

theorem leftHomologyMap_apply (U V : Set X) (n : ℕ)
    (a : SingularHomology (U ∩ V : Set X) n) :
    leftHomologyMap U V n a =
      (singularHomologyMap
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a,
        -singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n a) :=
  smallLeftHomologyMap_apply U V n a

@[simp] theorem rightHomologyMap_apply (U V : Set X) (n : ℕ)
    (a : SingularHomology U n × SingularHomology V n) :
    rightHomologyMap U V n a =
      singularHomologyMap (subtypeInclusion U) n a.1 +
        singularHomologyMap (subtypeInclusion V) n a.2 := rfl

/-- The concrete sum map factors through the actual small-chain homology map. -/
theorem rightHomologyMap_eq_comparison (U V : Set X) (n : ℕ) :
    rightHomologyMap U V n =
      (smallHomologyComparison U V n).comp (smallRightHomologyMap U V n) := by
  apply LinearMap.ext
  intro a
  exact (smallHomologyComparison_right U V n a).symm

/-- Consecutive inclusion maps compose to zero, for arbitrary subsets. -/
theorem leftHomologyMap_comp_right (U V : Set X) (n : ℕ) :
    (rightHomologyMap U V n).comp (leftHomologyMap U V n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha := LinearMap.congr_fun (smallLeftHomologyMap_comp_right U V n) a
  change smallRightHomologyMap U V n (smallLeftHomologyMap U V n a) = 0 at ha
  rw [rightHomologyMap_eq_comparison]
  change smallHomologyComparison U V n
    (smallRightHomologyMap U V n (smallLeftHomologyMap U V n a)) = 0
  rw [ha, map_zero]

variable (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
  (hcover : U ∪ V = Set.univ)

/-- The actual small-chain comparison is exactly the proved open-cover homology equivalence. -/
theorem smallHomologyEquiv_eq_comparison (n : ℕ) :
    (smallHomologyEquiv U V hU hV hcover n).toLinearMap =
      smallHomologyComparison U V n :=
  smallHomologyEquiv_toLinearMap U V hU hV hcover n

/-- The actual Mayer–Vietoris connecting homomorphism, in all degrees. -/
def connectingHomomorphism (n : ℕ) :
    SingularHomology X (n + 1) →ₗ[ℤ] SingularHomology (U ∩ V : Set X) n :=
  (smallConnectingMap U V n).comp
    (smallHomologyEquiv U V hU hV hcover (n + 1)).symm.toLinearMap

/-- On a genuine small-chain homology class, the connecting homomorphism
is the connecting map of the actual short exact sequence. -/
theorem connectingHomomorphism_comparison (n : ℕ) (a : SmallHomology U V (n + 1)) :
    connectingHomomorphism U V hU hV hcover n
        (smallHomologyComparison U V (n + 1) a) = smallConnectingMap U V n a := by
  rw [← smallHomologyEquiv_eq_comparison U V hU hV hcover]
  exact congrArg (smallConnectingMap U V n)
    ((smallHomologyEquiv U V hU hV hcover (n + 1)).symm_apply_apply a)

/-- The ordinary sum of inclusion maps is the transported actual small-chain map. -/
theorem rightHomologyMap_eq_transport (n : ℕ) :
    rightHomologyMap U V n =
      (smallHomologyEquiv U V hU hV hcover n).toLinearMap.comp
        (smallRightHomologyMap U V n) := by
  rw [smallHomologyEquiv_eq_comparison, rightHomologyMap_eq_comparison]

/-- Exactness at the actual singular homology of the intersection. -/
theorem exact_at_intersection (n : ℕ) :
    LinearMap.range (connectingHomomorphism U V hU hV hcover n) =
      LinearMap.ker (leftHomologyMap U V n) := by
  rw [connectingHomomorphism, rightTransport_connecting_range]
  exact small_exact_at_intersection U V n

include hU hV hcover in
/-- Exactness at the product of the actual homology groups of the two open subsets. -/
theorem exact_at_pair (n : ℕ) :
    LinearMap.range (leftHomologyMap U V n) =
      LinearMap.ker (rightHomologyMap U V n) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover,
    rightTransport_second_ker]
  exact small_exact_at_pair U V n

/-- Exactness at the actual positive-degree singular homology of the ambient space. -/
theorem exact_at_ambient (n : ℕ) :
    LinearMap.range (rightHomologyMap U V (n + 1)) =
      LinearMap.ker (connectingHomomorphism U V hU hV hcover n) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover]
  exact rightTransport_range_eq_ker
    (smallHomologyEquiv U V hU hV hcover (n + 1))
    (smallRightHomologyMap U V (n + 1)) (smallConnectingMap U V n)
    (small_exact_at_smallHomology U V n)

include hU hV hcover in
/-- The degree-zero endpoint of the actual singular Mayer–Vietoris sequence. -/
theorem rightHomologyMap_zero_surjective : Function.Surjective (rightHomologyMap U V 0) := by
  rw [rightHomologyMap_eq_transport U V hU hV hcover]
  exact rightTransport_second_surjective (smallHomologyEquiv U V hU hV hcover 0)
    (smallRightHomologyMap U V 0) (smallRightHomologyMap_zero_surjective U V)

theorem connectingHomomorphism_comp_left (n : ℕ) :
    (leftHomologyMap U V n).comp (connectingHomomorphism U V hU hV hcover n) = 0 := by
  apply LinearMap.ext
  intro a
  have ha : connectingHomomorphism U V hU hV hcover n a ∈
      LinearMap.range (connectingHomomorphism U V hU hV hcover n) := ⟨a, rfl⟩
  rw [exact_at_intersection] at ha
  exact ha

theorem rightHomologyMap_comp_connecting (n : ℕ) :
    (connectingHomomorphism U V hU hV hcover n).comp
      (rightHomologyMap U V (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  have ha : rightHomologyMap U V (n + 1) a ∈
      LinearMap.range (rightHomologyMap U V (n + 1)) := ⟨a, rfl⟩
  rw [exact_at_ambient U V hU hV hcover] at ha
  exact ha

/-- The all-degree exact integral singular Mayer–Vietoris sequence of an actual open cover. -/
theorem mayerVietoris_exact (n : ℕ) :
    LinearMap.range (connectingHomomorphism U V hU hV hcover n) =
        LinearMap.ker (leftHomologyMap U V n) ∧
      LinearMap.range (leftHomologyMap U V n) =
        LinearMap.ker (rightHomologyMap U V n) ∧
      LinearMap.range (rightHomologyMap U V (n + 1)) =
        LinearMap.ker (connectingHomomorphism U V hU hV hcover n) :=
  ⟨exact_at_intersection U V hU hV hcover n, exact_at_pair U V hU hV hcover n,
    exact_at_ambient U V hU hV hcover n⟩

end Wikipedia.HopfProblem.SingularMayerVietoris
