import Wikipedia.HopfProblem.HolomorphicMeromorphicLocalDiffeomorph
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackRegular
import Wikipedia.HopfProblem.HolomorphicMeromorphicScalarBasic

/-!
# Regularity and canonical values under native local biholomorphisms

Surjectivity of the actual holomorphic stalk pullback lifts an upstairs
holomorphic representative to the target. Injectivity of the genuine
fraction-field pullback then proves reflection of regularity. At poles,
both canonical ordinary representatives are zero, so their value equality
requires no regularity hypothesis.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

section Manifolds

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℂ E' H') [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [IsManifold I ω M] [J.Boundaryless] [IsManifold J ω N]

/-- An upstairs regular germ under a native local biholomorphism comes
from a holomorphic germ in the original target local ring. -/
theorem regularAt_of_pullbackSection_of_isLocalDiffeomorphAt
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U : Opens N} (s : Section J N U) (x : pullbackOpen I J f U)
    (hlocal : IsLocalDiffeomorphAt I J ω f x.val)
    (hx : RegularAt I M (pullbackSection I J f hf U s) x) :
    RegularAt J N s (pullbackPoint I J f U x) := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ :=
    holomorphicPullbackStalk_surjective_of_isLocalDiffeomorphAt I J f x.val hlocal p
  refine ⟨q, ?_⟩
  apply germPullback_injective I J f hf x.val
  exact (germPullback_ofHolomorphicGerm I J f hf x.val q).trans
    ((congrArg (ofHolomorphicGerm I M x.val) hq).trans hp)

/-- Native local biholomorphisms preserve and reflect regularity of the
full meromorphic germs. -/
theorem regularAt_pullbackSection_iff_of_isLocalDiffeomorphAt
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U : Opens N} (s : Section J N U) (x : pullbackOpen I J f U)
    (hlocal : IsLocalDiffeomorphAt I J ω f x.val) :
    RegularAt I M (pullbackSection I J f hf U s) x ↔
      RegularAt J N s (pullbackPoint I J f U x) :=
  ⟨regularAt_of_pullbackSection_of_isLocalDiffeomorphAt I J f hf s x hlocal,
    regularAt_pullbackSection I J f hf s x⟩

/-- Canonical ordinary values commute with native local biholomorphic
pullback, including at nonregular germs. -/
theorem value_pullbackSection_of_isLocalDiffeomorphAt
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    {U : Opens N} (s : Section J N U) (x : pullbackOpen I J f U)
    (hlocal : IsLocalDiffeomorphAt I J ω f x.val) :
    value I M (pullbackSection I J f hf U s) x =
      value J N s (pullbackPoint I J f U x) := by
  classical
  by_cases ht : RegularAt J N s (pullbackPoint I J f U x)
  · exact value_pullbackSection_of_regularAt I J f hf s x ht
  · have hs : ¬ RegularAt I M (pullbackSection I J f hf U s) x := fun h =>
      ht (regularAt_of_pullbackSection_of_isLocalDiffeomorphAt I J f hf s x hlocal h)
    simp only [value, dif_neg hs, dif_neg ht]

end Manifolds

/-- Scalar representatives on the plane commute with native locally
biholomorphic pullback. Outside the inverse-image domain both sides are zero. -/
theorem scalarValue_pullbackSection_of_isLocalDiffeomorphAt
    (f : ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) ℂ ℂ ω) (hf : IsOpenMap f)
    {U : Opens ℂ} (s : Section 𝓘(ℂ) ℂ U) (x : ℂ)
    (hlocal : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    scalarValue (pullbackSection 𝓘(ℂ) 𝓘(ℂ) f hf U s) x = scalarValue s (f x) := by
  by_cases hx : f x ∈ U
  · rw [scalarValue_apply _ x hx, scalarValue_apply s (f x) hx]
    exact value_pullbackSection_of_isLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) f hf s ⟨x, hx⟩ hlocal
  · rw [scalarValue_of_not_mem _ x hx, scalarValue_of_not_mem s (f x) hx]

end Wikipedia.HopfProblem.HolomorphicMeromorphic
