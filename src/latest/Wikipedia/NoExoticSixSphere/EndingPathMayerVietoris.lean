import Wikipedia.NoExoticSixSphere.EndingPathRestriction
import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# The homology splitting for a two-set cover of the path projection

The total path space is explicitly contracted, so exactness makes the
actual signed intersection-inclusion map an isomorphism in positive
degrees. Strong contractions of the two base sets identify the two target
groups with native loop-space homology. No James comparison equivalence
or homology computation is assumed.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.EndingPath

variable {Y : Type} [TopologicalSpace Y] (y₀ : Y)

theorem cover_left_bijective (P Q : Set (Space y₀)) (hP : IsOpen P) (hQ : IsOpen Q)
    (hc : P ∪ Q = Set.univ) (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective (leftHomologyMap P Q n) := by
  let := contractible_homology_subsingleton (Space y₀) n hn
  let := contractible_homology_subsingleton (Space y₀) (n + 1) (Nat.succ_ne_zero n)
  have hd : connectingHomomorphism P Q hP hQ hc n = 0 := by
    apply LinearMap.ext
    intro a
    have ha : a = 0 := Subsingleton.elim _ _
    rw [ha, map_zero]
    rfl
  have hr : rightHomologyMap P Q n = 0 := by
    apply LinearMap.ext
    intro a
    exact Subsingleton.elim _ _
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [← exact_at_intersection P Q hP hQ hc n, hd, LinearMap.range_zero]
  · apply LinearMap.range_eq_top.mp
    rw [exact_at_pair P Q hP hQ hc n, hr, LinearMap.ker_zero]

def coverHomologyEquiv (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hc : U ∪ V = Set.univ) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (restriction y₀ U ∩ restriction y₀ V : Set (Space y₀)) n ≃ₗ[ℤ]
      (SingularHomology (restriction y₀ U) n × SingularHomology (restriction y₀ V) n) :=
  LinearEquiv.ofBijective (leftHomologyMap (restriction y₀ U) (restriction y₀ V) n)
    (cover_left_bijective y₀ _ _ (restriction_isOpen y₀ hU) (restriction_isOpen y₀ hV)
      (restriction_cover y₀ hc) n hn)

theorem coverHomologyEquiv_apply (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hc : U ∪ V = Set.univ) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (restriction y₀ U ∩ restriction y₀ V : Set (Space y₀)) n) :
    coverHomologyEquiv y₀ U V hU hV hc n hn a =
      leftHomologyMap (restriction y₀ U) (restriction y₀ V) n a := rfl

def loopCoverHomologyEquiv (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hc : U ∪ V = Set.univ) (hyU : y₀ ∈ U) (hyV : y₀ ∈ V)
    (HU : (ContinuousMap.id U).HomotopyRel
      (ContinuousMap.const U ⟨y₀, hyU⟩) {⟨y₀, hyU⟩})
    (HV : (ContinuousMap.id V).HomotopyRel
      (ContinuousMap.const V ⟨y₀, hyV⟩) {⟨y₀, hyV⟩}) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (restriction y₀ U ∩ restriction y₀ V : Set (Space y₀)) n ≃ₗ[ℤ]
      (SingularHomology (Path y₀ y₀) n × SingularHomology (Path y₀ y₀) n) :=
  (coverHomologyEquiv y₀ U V hU hV hc n hn).trans
    (((homotopyEquivHomologyEquiv (restrictionEquiv y₀ U hyU HU) n).toAddEquiv.prodCongr
      (homotopyEquivHomologyEquiv (restrictionEquiv y₀ V hyV HV) n).toAddEquiv).toIntLinearEquiv)

end NoExoticSixSphere.EndingPath
