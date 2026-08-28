import Wikipedia.NoExoticSixSphere.CompactSupportCohomology
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedCohomology

/-!
# Compact-support cohomology of a compact space

The whole space is an actual final compact support. The directed-limit
equivalence with that component and the original empty-subspace cochain
isomorphism identify compact-support cohomology with absolute cohomology.
Both forward maps retain their original representative formulas.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactSupportCohomology

variable (X : Type) [TopologicalSpace X] [CompactSpace X] (p : ℕ)

/-- Extend each genuine representative to the actual whole-space support. -/
def toTop : Cohomology X p →ₗ[ℤ] Component X p ⊤ :=
  lift X p (fun K => transition X p K ⊤ le_top) (by
    intro K L h a
    exact (LinearMap.congr_fun
      (SupportedModTwoCohomology.extend_trans h (show (L : Set X) ⊆ Set.univ from le_top) p)
      a).symm)

theorem toTop_of (K : Compacts X) (a : Component X p K) :
    toTop X p (of X p K a) = transition X p K ⊤ le_top a := rfl

theorem toTop_of_top (a : Component X p ⊤) : toTop X p (of X p ⊤ a) = a := by
  rw [toTop_of]
  exact LinearMap.congr_fun
    (SupportedModTwoCohomology.extend_refl (Set.univ : Set X) p) a

theorem of_top_toTop (a : Cohomology X p) : of X p ⊤ (toTop X p a) = a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  rw [toTop_of]
  exact of_transition X p le_top b

/-- The final actual support computes this directed limit. -/
def topEquiv : Cohomology X p ≃ₗ[ℤ] Component X p ⊤ where
  toFun := toTop X p
  invFun := of X p ⊤
  left_inv := of_top_toTop X p
  right_inv := toTop_of_top X p
  map_add' := (toTop X p).map_add
  map_smul' := (toTop X p).map_smul

/-- Actual compact-support and absolute cohomology agree on a compact space. -/
def absoluteEquiv : Cohomology X p ≃ₗ[ℤ] ModTwoCapProduct.Cohomology X p :=
  (topEquiv X p).trans (SupportedModTwoCohomology.absoluteEquiv (X := X) p)

/-- Every relative representative goes to its original absolute cohomology class. -/
theorem absoluteEquiv_of (K : Compacts X) (a : Component X p K) :
    absoluteEquiv X p (of X p K a) =
      RelativeModTwoCochains.toAbsoluteCohomology ((K : Set X)ᶜ) p a :=
  SupportedModTwoCohomology.toAbsolute_extend (Set.subset_univ (K : Set X)) p a

end NoExoticSixSphere.CompactSupportCohomology
