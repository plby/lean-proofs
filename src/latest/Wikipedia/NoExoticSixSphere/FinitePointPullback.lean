import Wikipedia.NoExoticSixSphere.FiniteSupportRestriction
import Wikipedia.NoExoticSixSphere.SupportedOpenEmbeddingPullback
import Wikipedia.NoExoticSixSphere.SpherePointEvaluation

/-!
# Finite point pullbacks with genuine local homeomorphism coordinates

When a continuous map is a local homeomorphism at every point in a
finite fiber, the original pullback of a nonzero point-supported class
has nonzero singleton components. On the original three-sphere its
evaluation is consequently the actual fiber cardinality modulo two.
The support maps below are original extensions between equal supports.
Transversality still has to provide the required normal-coordinate maps.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomology

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Extending between equal actual supports is injective, by the original composition law. -/
theorem extend_injective_of_reverse_subset {K L : Set X}
    (hKL : K ⊆ L) (hLK : L ⊆ K) (p : ℕ) : Function.Injective (extend hKL p) := by
  have hleft : Function.LeftInverse (extend hLK p) (extend hKL p) := by
    intro a
    exact (LinearMap.congr_fun (extend_trans hKL hLK p).symm a).trans
      (LinearMap.congr_fun (extend_refl K p) a)
  exact hleft.injective

variable [T1Space X] [T2Space Y]

/-- The original point pullback has a nonzero component wherever the map is locally invertible. -/
theorem pointPieces_pullback_ne_zero (f : C(X, Y)) (y : Y) (s : Finset X)
    (hs : f ⁻¹' ({y} : Set Y) = (s : Set X)) (p : ℕ)
    (a : Cohomology ({y} : Set Y) p) (ha : a ≠ 0) (x : X) (hx : x ∈ s)
    (hf : IsLocalHomeomorphOn f ({x} : Set X)) :
    pointPieces s p (extend hs.subset p (pullback f ({y} : Set Y) p a)) x ≠ 0 := by
  have hxy : f x = y := hs.symm.subset hx
  subst y
  obtain ⟨U, _hU, hxU, hi, hn⟩ := exists_point_pullback_ne_zero_neighborhood f x hf p a ha
  apply pointPieces_ne_zero_of_neighborhood s p x hx U
    (fun z hz hzU => hi hzU hxU (show f z = f x from hs.symm.subset hz))
  intro he
  apply hn
  apply extend_injective_of_reverse_subset (Set.preimage_mono hs.subset)
    (Set.preimage_mono hs.symm.subset) p
  rw [← pullback_extend]
  exact he.trans (map_zero _).symm

end NoExoticSixSphere.SupportedModTwoCohomology

namespace NoExoticSixSphere.SpherePointEvaluation

open SupportedModTwoCohomology

variable {Y : Type} [TopologicalSpace Y] [T2Space Y]

/-- Genuine local homeomorphisms make original point pullback evaluate to the finite fiber count. -/
theorem value_point_pullback_eq_card (f : C(Sphere 3, Y)) (y : Y) (s : Finset (Sphere 3))
    (hs : f ⁻¹' ({y} : Set Y) = (s : Set (Sphere 3)))
    (a : Cohomology ({y} : Set Y) 3) (ha : a ≠ 0)
    (hf : IsLocalHomeomorphOn f (f ⁻¹' ({y} : Set Y))) :
    value (f ⁻¹' ({y} : Set Y)) 3 (unitSphereTopClass 2) (pullback f ({y} : Set Y) 3 a) =
      (s.card : ZMod 2) := by
  rw [← value_extend hs.subset 3 (unitSphereTopClass 2) (pullback f ({y} : Set Y) 3 a)]
  apply finite_value_eq_card_of_nonzero
  intro x hx
  exact pointPieces_pullback_ne_zero f y s hs 3 a ha x hx
    (hf.mono (singleton_subset_iff.mpr (hs.symm.subset hx)))

/-- The count uses the literal inverse-image support, independent of its finite presentation. -/
theorem value_point_pullback_eq_ncard (f : C(Sphere 3, Y)) (y : Y)
    (hfinite : (f ⁻¹' ({y} : Set Y)).Finite)
    (a : Cohomology ({y} : Set Y) 3) (ha : a ≠ 0)
    (hf : IsLocalHomeomorphOn f (f ⁻¹' ({y} : Set Y))) :
    value (f ⁻¹' ({y} : Set Y)) 3 (unitSphereTopClass 2) (pullback f ({y} : Set Y) 3 a) =
      ((f ⁻¹' ({y} : Set Y)).ncard : ZMod 2) := by
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact value_point_pullback_eq_card f y hfinite.toFinset hfinite.coe_toFinset.symm a ha hf

end NoExoticSixSphere.SpherePointEvaluation
