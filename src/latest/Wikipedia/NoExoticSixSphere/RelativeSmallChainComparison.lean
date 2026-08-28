import Wikipedia.NoExoticSixSphere.RelativeSingularHomologyMaps
import Wikipedia.HopfProblem.SingularMayerVietorisSmallEquivalence
import Mathlib.Algebra.Homology.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Relative small chains and excision comparisons

For two actual subsets, the square of their singular-chain inclusions into
small chains is a pushout. Consequently, quotienting the small chains by
chains in the second subset gives the same complex as quotienting chains
in the first subset by chains in their intersection. For an open cover,
the map to ambient relative chains is a quasi-isomorphism, proved using
barycentric subdivision and the actual short exact chain sequences.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The actual small-chain square is a pushout, even without openness. -/
theorem smallChainSquare_isPushout :
    IsPushout (intersectionToLeft U V) (intersectionToRight U V)
      (toSmallLeft U V) (toSmallRight U V) := by
  let sq : CommSq (intersectionToLeft U V) (intersectionToRight U V)
      (toSmallLeft U V) (toSmallRight U V) := ⟨intersection_toSmall_comm U V⟩
  have := (chainSequence_shortExact U V).epi_g
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ sq.w)
  exact sq.isColimitEquivIsColimitCokernelCofork.symm
    (chainSequence_shortExact U V).exact.gIsCokernel

/-- Chains in the first subset modulo chains in the actual intersection. -/
abbrev intersectionQuotient : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (intersectionToLeft U V)

/-- Actual small chains modulo chains in the second subset. -/
abbrev smallRelativeComplex : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (toSmallRight U V)

/-- The map from the first-subset quotient into the small-chain quotient. -/
def intersectionToSmall : intersectionQuotient U V ⟶ smallRelativeComplex U V :=
  cokernel.map (intersectionToLeft U V) (toSmallRight U V)
    (intersectionToRight U V) (toSmallLeft U V) (intersection_toSmall_comm U V)

@[reassoc]
theorem intersectionProjection_toSmall :
    cokernel.π (intersectionToLeft U V) ≫ intersectionToSmall U V =
      toSmallLeft U V ≫ cokernel.π (toSmallRight U V) :=
  cokernel.π_desc _ _ _

instance intersectionToSmall_isIso : IsIso (intersectionToSmall U V) :=
  isIso_cokernel_map_of_isPushout (smallChainSquare_isPushout U V)

/-- Its forward map is the map induced by the actual inclusion into small chains. -/
def intersectionToSmallIso : intersectionQuotient U V ≅ smallRelativeComplex U V :=
  asIso (intersectionToSmall U V)

theorem toSmallRight_mono : Mono (toSmallRight U V) := by
  apply mono_of_mono_fac (toSmallRight_inclusion U V)

/-- The short chain sequence for the actual small-chain quotient. -/
def smallRelativeSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (toSmallRight U V) (cokernel.π (toSmallRight U V))
    (cokernel.condition _)

theorem smallRelativeSequence_shortExact : (smallRelativeSequence U V).ShortExact where
  exact := ShortComplex.exact_cokernel (toSmallRight U V)
  mono_f := toSmallRight_mono U V
  epi_g := inferInstanceAs (Epi (cokernel.π (toSmallRight U V)))

/-- Inclusion of small chains induces a map to the ambient relative complex. -/
def smallRelativeComparison : smallRelativeComplex U V ⟶ complex V :=
  cokernel.map (toSmallRight U V) (inclusion V) (𝟙 _) (smallInclusion U V)
    (by rw [Category.id_comp]; exact toSmallRight_inclusion U V)

@[reassoc]
theorem smallProjection_comparison :
    cokernel.π (toSmallRight U V) ≫ smallRelativeComparison U V =
      smallInclusion U V ≫ projection V :=
  cokernel.π_desc _ _ _

/-- The first map is the identity on the original subspace's singular complex. -/
def smallRelativeSequenceMap : smallRelativeSequence U V ⟶ sequence V where
  τ₁ := 𝟙 _
  τ₂ := smallInclusion U V
  τ₃ := smallRelativeComparison U V
  comm₁₂ := by
    change 𝟙 _ ≫ inclusion V = toSmallRight U V ≫ smallInclusion U V
    rw [Category.id_comp]
    exact (toSmallRight_inclusion U V).symm
  comm₂₃ := (smallProjection_comparison U V).symm

/-- Subdivision on the actual open cover proves the relative comparison in every degree. -/
theorem smallRelativeComparison_quasiIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : QuasiIso (smallRelativeComparison U V) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (smallRelativeSequenceMap U V)
    (smallRelativeSequence_shortExact U V) (sequence_shortExact V)
    (inferInstanceAs (QuasiIso (𝟙 (singularComplex V))))
    (smallInclusion_quasiIso U V hU hV hcover)

/-- The concrete inclusion map from the intersection quotient to the ambient relative complex. -/
def intersectionComparison : intersectionQuotient U V ⟶ complex V :=
  intersectionToSmall U V ≫ smallRelativeComparison U V

theorem intersectionComparison_quasiIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : QuasiIso (intersectionComparison U V) := by
  let := smallRelativeComparison_quasiIso U V hU hV hcover
  exact inferInstanceAs (QuasiIso (intersectionToSmall U V ≫ smallRelativeComparison U V))

@[reassoc]
theorem intersectionProjection_comparison :
    cokernel.π (intersectionToLeft U V) ≫ intersectionComparison U V =
      inclusion U ≫ projection V := by
  change cokernel.π _ ≫ (intersectionToSmall U V ≫ smallRelativeComparison U V) = _
  rw [← Category.assoc, intersectionProjection_toSmall, Category.assoc,
    smallProjection_comparison,
    ← Category.assoc, toSmallLeft_inclusion]

end NoExoticSixSphere.RelativeSingularHomology
