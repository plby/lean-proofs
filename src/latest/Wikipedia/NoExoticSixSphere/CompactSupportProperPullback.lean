import Wikipedia.NoExoticSixSphere.SupportedModTwoPullback
import Wikipedia.NoExoticSixSphere.CompactSupportCohomologyCompact
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper pullback on the original compact-support cohomology

The inverse image of each actual compact support is compact for a
proper map. The original supported-cochain pullbacks commute with
support enlargement, so they induce a map of the genuine direct limits.
Identity, composition, and comparison with absolute pullback on compact
spaces all retain the original representative formulas.
-/

noncomputable section

open TopologicalSpace

namespace NoExoticSixSphere.CompactSupportCohomology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The actual inverse image of the compact support under a proper map. -/
def preimageCompact (f : C(X, Y)) (hf : IsProperMap f) (K : Compacts Y) : Compacts X :=
  ⟨f ⁻¹' (K : Set Y), hf.isCompact_preimage K.isCompact⟩

/-- Original relative pullback followed by insertion at the actual inverse-image support. -/
def properPullbackComponent (f : C(X, Y)) (hf : IsProperMap f) (p : ℕ) (K : Compacts Y) :
    Component Y p K →ₗ[ℤ] Cohomology X p :=
  (of X p (preimageCompact f hf K)).comp (SupportedModTwoCohomology.pullback f (K : Set Y) p)

theorem properPullbackComponent_transition (f : C(X, Y)) (hf : IsProperMap f) (p : ℕ)
    (K L : Compacts Y) (h : K ≤ L) (a : Component Y p K) :
    properPullbackComponent f hf p L (transition Y p K L h a) =
      properPullbackComponent f hf p K a := by
  apply (congrArg (of X p (preimageCompact f hf L))
    (SupportedModTwoCohomology.pullback_extend f
      (show (K : Set Y) ⊆ (L : Set Y) from h) p a)).trans
  exact of_transition X p (K := preimageCompact f hf K) (L := preimageCompact f hf L)
    (show preimageCompact f hf K ≤ preimageCompact f hf L from fun _ hx => h hx)
    (SupportedModTwoCohomology.pullback f (K : Set Y) p a)

/-- Proper pullback is induced by the actual maps of the compact-support diagram. -/
def properPullback (f : C(X, Y)) (hf : IsProperMap f) (p : ℕ) :
    Cohomology Y p →ₗ[ℤ] Cohomology X p :=
  lift Y p (properPullbackComponent f hf p) (properPullbackComponent_transition f hf p)

theorem properPullback_of (f : C(X, Y)) (hf : IsProperMap f) (p : ℕ)
    (K : Compacts Y) (a : Component Y p K) :
    properPullback f hf p (of Y p K a) = of X p (preimageCompact f hf K)
      (SupportedModTwoCohomology.pullback f (K : Set Y) p a) := rfl

/-- Pullback by the actual identity does not change a compact-supported class. -/
theorem properPullback_id (p : ℕ) (a : Cohomology X p) :
    properPullback (ContinuousMap.id X) isProperMap_id p a = a := by
  obtain ⟨K, b, rfl⟩ := exists_representative X p a
  exact congrArg (of X p K) (SupportedModTwoCohomology.pullback_id (K : Set X) p b)

/-- Composite proper pullback is successive original pullback in reverse order. -/
theorem properPullback_comp (f : C(X, Y)) (hf : IsProperMap f)
    (g : C(Y, Z)) (hg : IsProperMap g) (p : ℕ) (a : Cohomology Z p) :
    properPullback (g.comp f) (hg.comp hf) p a =
      properPullback f hf p (properPullback g hg p a) := by
  obtain ⟨K, b, rfl⟩ := exists_representative Z p a
  exact congrArg (of X p (preimageCompact f hf (preimageCompact g hg K)))
    (SupportedModTwoCohomology.pullback_comp f g (K : Set Z) p b)

/-- On compact spaces, this is precisely original absolute cohomology pullback. -/
theorem absoluteEquiv_properPullback [CompactSpace X] [CompactSpace Y]
    (f : C(X, Y)) (hf : IsProperMap f) (p : ℕ) (a : Cohomology Y p) :
    absoluteEquiv X p (properPullback f hf p a) =
      ModTwoCapProduct.cohomologyPullback f p (absoluteEquiv Y p a) := by
  obtain ⟨K, b, rfl⟩ := exists_representative Y p a
  exact (absoluteEquiv_of X p (preimageCompact f hf K)
    (SupportedModTwoCohomology.pullback f (K : Set Y) p b)).trans
      ((SupportedModTwoCohomology.toAbsolute_pullback f (K : Set Y) p b).trans
        (congrArg (ModTwoCapProduct.cohomologyPullback f p) (absoluteEquiv_of Y p K b).symm))

end NoExoticSixSphere.CompactSupportCohomology
