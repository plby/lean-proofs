import Wikipedia.NoExoticSixSphere.FiniteSupportComponents
import Wikipedia.NoExoticSixSphere.SupportedModTwoPullback

/-!
# Isolating the actual singleton component by restriction

Pullback to a region avoiding all but one point kills the other original
singleton-supported summands. The remaining summand is the pullback of
the uniquely determined point component, followed by original extension
of support. Thus a nonzero local restriction detects a nonzero component.
Finite supports in T1 spaces admit such open isolating neighborhoods.
-/

noncomputable section

open scoped BigOperators

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- An actual cohomology class whose support is empty vanishes. -/
theorem eq_zero_of_support_eq_empty {K : Set X} (hK : K = ∅) (p : ℕ)
    (a : Cohomology K p) : a = 0 := by
  subst K
  exact cohomology_empty_eq_zero X p a

/-- Pullback vanishes if the actual inverse-image support is empty. -/
theorem pullback_eq_zero_of_preimage_empty (f : C(Y, X)) (K : Set X)
    (hK : f ⁻¹' K = ∅) (p : ℕ) (a : Cohomology K p) : pullback f K p a = 0 :=
  eq_zero_of_support_eq_empty hK p _

/-- A point summand vanishes on every region avoiding that point. -/
theorem pullback_pointTo_eq_zero (f : C(Y, X)) (K : Set X) (p : ℕ) (x : X)
    (hx : x ∈ K) (hpre : f ⁻¹' ({x} : Set X) = ∅)
    (a : Cohomology ({x} : Set X) p) : pullback f K p (pointTo K p x a) = 0 := by
  rw [pointTo_of_mem K p x hx, pullback_extend,
    pullback_eq_zero_of_preimage_empty f {x} hpre p a, map_zero]

/-- Restriction avoiding every other point retains exactly the original singleton summand. -/
theorem pullback_pointSum_of_isolated (f : C(Y, X)) (s : Finset X) (p : ℕ)
    (x : X) (hx : x ∈ s)
    (hisolate : ∀ y ∈ s, y ≠ x → f ⁻¹' ({y} : Set X) = ∅)
    (a : ∀ y : X, Cohomology ({y} : Set X) p) :
    pullback f (s : Set X) p (pointSum s p a) =
      extend (Set.preimage_mono (Set.singleton_subset_iff.mpr hx)) p
        (pullback f ({x} : Set X) p (a x)) := by
  classical
  rw [pointSum, map_sum]
  have hs : (∑ y ∈ s, pullback f (s : Set X) p (pointTo (s : Set X) p y (a y))) =
      pullback f (s : Set X) p (pointTo (s : Set X) p x (a x)) := by
    apply Finset.sum_eq_single x
    · intro y hy hne
      exact pullback_pointTo_eq_zero f (s : Set X) p y hy (hisolate y hy hne) (a y)
    · intro hnot
      exact (hnot hx).elim
  rw [hs, pointTo_of_mem (s : Set X) p x hx, pullback_extend]

variable [T1Space X]

/-- The restriction of a finite-supported class is its actual isolated point component. -/
theorem pullback_eq_extend_pointPieces (f : C(Y, X)) (s : Finset X) (p : ℕ)
    (x : X) (hx : x ∈ s)
    (hisolate : ∀ y ∈ s, y ≠ x → f ⁻¹' ({y} : Set X) = ∅)
    (a : Cohomology (s : Set X) p) :
    pullback f (s : Set X) p a =
      extend (Set.preimage_mono (Set.singleton_subset_iff.mpr hx)) p
        (pullback f ({x} : Set X) p (pointPieces s p a x)) :=
  (congrArg (pullback f (s : Set X) p) (pointSum_pointPieces s p a)).symm.trans
    (pullback_pointSum_of_isolated f s p x hx hisolate (pointPieces s p a))

/-- A nonzero original local restriction implies a nonzero actual point component. -/
theorem pointPieces_ne_zero_of_pullback_ne_zero (f : C(Y, X)) (s : Finset X) (p : ℕ)
    (x : X) (hx : x ∈ s)
    (hisolate : ∀ y ∈ s, y ≠ x → f ⁻¹' ({y} : Set X) = ∅)
    (a : Cohomology (s : Set X) p) (ha : pullback f (s : Set X) p a ≠ 0) :
    pointPieces s p a x ≠ 0 := by
  intro he
  apply ha
  rw [pullback_eq_extend_pointPieces f s p x hx hisolate a, he, map_zero, map_zero]

/-- Every point has an open neighborhood avoiding all other points of a finite support. -/
theorem exists_isolating_open (s : Finset X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ s, y ∈ U → y = x := by
  classical
  refine ⟨(↑(s.erase x) : Set X)ᶜ, (s.erase x).finite_toSet.isClosed.isOpen_compl, ?_, ?_⟩
  · exact Finset.notMem_erase x s
  · intro y hy hyU
    by_contra hne
    exact hyU (Finset.mem_erase.mpr ⟨hne, hy⟩)

/-- Neighborhood restriction detects the original singleton component, without changing it. -/
theorem pointPieces_ne_zero_of_neighborhood (s : Finset X) (p : ℕ)
    (x : X) (hx : x ∈ s) (U : Set X)
    (hisolate : ∀ y ∈ s, y ∈ U → y = x) (a : Cohomology (s : Set X) p)
    (ha : pullback (Wikipedia.HopfProblem.SingularMayerVietoris.subtypeInclusion U)
      (s : Set X) p a ≠ 0) : pointPieces s p a x ≠ 0 := by
  apply pointPieces_ne_zero_of_pullback_ne_zero
    (Wikipedia.HopfProblem.SingularMayerVietoris.subtypeInclusion U) s p x hx _ a ha
  intro y hy hne
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact hne (hisolate y hy ((Set.mem_singleton_iff.mp hz) ▸ z.property))

end NoExoticSixSphere.SupportedModTwoCohomology
