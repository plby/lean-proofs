import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartier
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundlePullback

/-!
# Holomorphic pullback of a Cartier presentation

The local fractions and actual unit transition functions are composed
with the given holomorphic map.  Density of the inverse image of the
generic open is an explicit hypothesis: it does not follow for arbitrary
maps from density in the target.  In the application to the constructed
threefold this hypothesis is proved by the genuine cusp charts.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobal.CartierData

variable {E H E' H' M N ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M] [ChartedSpace H' N]
  {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
  (D : CartierData J N ι) (f : M → N) (hf : ContMDiff I J ω f)
  (hd : Dense (f ⁻¹' (D.genericSet : Set N)))

/-- The genuine pullback presentation on the inverse-image cover. -/
def pullback : CartierData I M ι where
  transitions := CanonicalGlobalLineBundle.pullback D.transitions f hf.continuous
  isHolomorphic := CanonicalGlobalLineBundle.pullback_isHolomorphic
    D.transitions f hf.continuous I J hf
  numerator i := D.numerator i ∘ f
  denominator i := D.denominator i ∘ f
  numerator_holomorphic i :=
    (D.numerator_holomorphic i).comp hf.contMDiffOn (fun _ hx => hx)
  denominator_holomorphic i :=
    (D.denominator_holomorphic i).comp hf.contMDiffOn (fun _ hx => hx)
  genericSet := ⟨f ⁻¹' (D.genericSet : Set N), D.genericSet.isOpen.preimage hf.continuous⟩
  genericSet_dense := hd
  numerator_ne_zero i x hi hx := D.numerator_ne_zero i (f x) hi hx
  denominator_ne_zero i x hi hx := D.denominator_ne_zero i (f x) hi hx
  ratio i j x hx := D.ratio i j (f x) hx

@[simp] theorem pullback_numerator (i : ι) (x : M) :
    (D.pullback f hf hd).numerator i x = D.numerator i (f x) := rfl

@[simp] theorem pullback_denominator (i : ι) (x : M) :
    (D.pullback f hf hd).denominator i x = D.denominator i (f x) := rfl

@[simp] theorem pullback_genericSet :
    ((D.pullback f hf hd).genericSet : Set M) = f ⁻¹' (D.genericSet : Set N) := rfl

@[simp] theorem pullback_transition (i j : ι) (x : M) :
    (D.pullback f hf hd).transitions.transition i j x = D.transitions.transition i j (f x) := rfl

@[simp] theorem pullback_localFraction (i : ι) (x : M) :
    (D.pullback f hf hd).localFraction i x = D.localFraction i (f x) := rfl

/-- In the actual native bundle atlases the pulled-back meromorphic
section maps to the original one, including its literal chosen coefficient. -/
theorem pullback_rawSectionMap (x : M) :
    CanonicalGlobalLineBundle.pullbackTotalMap D.transitions f hf.continuous
      ((D.pullback f hf hd).rawSectionMap x) = D.rawSectionMap (f x) := rfl

theorem pullbackTotalMap_holomorphic :
    ContMDiff (I.prod (modelWithCornersSelf ℂ ℂ))
      (J.prod (modelWithCornersSelf ℂ ℂ)) ω
      (CanonicalGlobalLineBundle.pullbackTotalMap D.transitions f hf.continuous) :=
  CanonicalGlobalLineBundle.pullbackTotalMap_holomorphic D.transitions f hf.continuous I J hf

end Wikipedia.HopfProblem.CanonicalGlobal.CartierData
