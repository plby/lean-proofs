import Wikipedia.HopfProblem.HolomorphicMeromorphicPartialDiffeomorphSections
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackPointwise

/-!
# Naturality of native meromorphic germs in partial charts

An actual commuting square of holomorphic maps induces a commuting square
of the original fraction-stalk pullbacks. Restriction to the genuine chart
sources makes all maps globally holomorphic and open; no chart is extended
outside its domain and no manifold structure is replaced.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PartialBiholomorph

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H'] (J : ModelWithCorners ℂ E' H')
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Restriction of an actual holomorphic map between original open subsets. -/
def restrictedMap (f : ContMDiffMap I J M N ω) (U : Opens M) (V : Opens N)
    (hUV : ∀ x ∈ U, f x ∈ V) : ContMDiffMap I J U V ω :=
  ⟨fun x => ⟨f x.val, hUV x.val x.property⟩, by
    intro x
    exact (analyticWithinAt_subtypeVal_comp_iff I J V
      (fun z : U => ⟨f z.val, hUV z.val z.property⟩) univ x).mp
        ((f.contMDiff x.val).comp x (contMDiff_subtype_val x))⟩

@[simp] theorem restrictedMap_apply (f : ContMDiffMap I J M N ω)
    (U : Opens M) (V : Opens N) (hUV : ∀ x ∈ U, f x ∈ V) (x : U) :
    (restrictedMap I J f U V hUV x).val = f x.val := rfl

/-- Restriction to open source and target subsets preserves openness. -/
theorem restrictedMap_isOpenMap (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens M) (V : Opens N) (hUV : ∀ x ∈ U, f x ∈ V) :
    IsOpenMap (restrictedMap I J f U V hUV) :=
  (hf.comp (openInclusionMap_isOpenMap I U)).codRestrict
    (fun x : U => hUV x.val x.property)

variable [I.Boundaryless] [IsManifold I ω M]
  [J.Boundaryless] [IsManifold J ω N]

/-- The native restriction square commutes on full meromorphic germs. -/
theorem restrictedMap_pullback_comm (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens M) (V : Opens N) (hUV : ∀ x ∈ U, f x ∈ V)
    (x : U) (a : Germ J N (f x.val)) :
    germPullback I J (restrictedMap I J f U V hUV)
      (restrictedMap_isOpenMap I J f hf U V hUV) x
      (germPullback J J (openInclusionMap J V) (openInclusionMap_isOpenMap J V)
        (restrictedMap I J f U V hUV x) a) =
    germPullback I I (openInclusionMap I U) (openInclusionMap_isOpenMap I U) x
      (germPullback I J f hf x.val a) := by
  have hmap :
      germPullback I J ((openInclusionMap J V).comp (restrictedMap I J f U V hUV))
        ((openInclusionMap_isOpenMap J V).comp (restrictedMap_isOpenMap I J f hf U V hUV)) x a =
      germPullback I J (f.comp (openInclusionMap I U))
        (hf.comp (openInclusionMap_isOpenMap I U)) x a := rfl
  exact (germPullback_comp_apply I J J (restrictedMap I J f U V hUV)
    (restrictedMap_isOpenMap I J f hf U V hUV) (openInclusionMap J V)
    (openInclusionMap_isOpenMap J V) x a).trans
      (hmap.trans (germPullback_comp_apply I I J (openInclusionMap I U)
        (openInclusionMap_isOpenMap I U) f hf x a).symm)

variable {EA HA A : Type} [NormedAddCommGroup EA] [NormedSpace ℂ EA]
  [TopologicalSpace HA] (K : ModelWithCorners ℂ EA HA)
  [TopologicalSpace A] [ChartedSpace HA A] [K.Boundaryless] [IsManifold K ω A]
  {EB HB B : Type} [NormedAddCommGroup EB] [NormedSpace ℂ EB]
  [TopologicalSpace HB] (L : ModelWithCorners ℂ EB HB)
  [TopologicalSpace B] [ChartedSpace HB B] [L.Boundaryless] [IsManifold L ω B]

/-- Exact naturality of genuine meromorphic germs in original partial charts.
The two section evaluations are kept at their actual points, so the statement
requires no casts between unrelated stalks. -/
theorem germEquiv_pullback_naturality
    (e : PartialDiffeomorph I K M A ω) (d : PartialDiffeomorph J L N B ω)
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (ψ : ContMDiffMap K L A B ω) (hψ : IsOpenMap ψ)
    (hfd : ∀ x ∈ e.source, f x ∈ d.source)
    (hcomm : ∀ x ∈ e.source, d (f x) = ψ (e x))
    (U : Opens B) (s : Section L B U) (x : M) (hx : x ∈ e.source)
    (hψx : ψ (e x) ∈ U) (hdfx : d (f x) ∈ U) :
    germEquiv I K e x hx
      (germPullback K L ψ hψ (e x) (s ⟨ψ (e x), hψx⟩)) =
    germPullback I J f hf x
      (germEquiv J L d (f x) (hfd x hx) (s ⟨d (f x), hdfx⟩)) := by
  let r := restrictedMap I J f (sourceOpen I K e) (sourceOpen J L d) hfd
  have hr : IsOpenMap r :=
    restrictedMap_isOpenMap I J f hf (sourceOpen I K e) (sourceOpen J L d) hfd
  let xs : sourceOpen I K e := ⟨x, hx⟩
  have hsquare :
      germPullback I K (sourceMap I K e) (sourceMap_isOpenMap I K e) xs
        (germPullback K L ψ hψ (e x) (s ⟨ψ (e x), hψx⟩)) =
      germPullback I J r hr xs
        (germPullback J L (sourceMap J L d) (sourceMap_isOpenMap J L d)
          (r xs) (s ⟨d (f x), hdfx⟩)) := by
    exact (germPullback_comp_apply I K L (sourceMap I K e) (sourceMap_isOpenMap I K e)
      ψ hψ xs (s ⟨ψ (e x), hψx⟩)).trans
        ((germPullback_section_congr I L (ψ.comp (sourceMap I K e))
          ((sourceMap J L d).comp r) (hψ.comp (sourceMap_isOpenMap I K e))
          ((sourceMap_isOpenMap J L d).comp hr)
          (fun z => (hcomm z.val z.property).symm) U s xs hψx hdfx).trans
            (germPullback_comp_apply I J L r hr (sourceMap J L d)
              (sourceMap_isOpenMap J L d) xs (s ⟨d (f x), hdfx⟩)).symm)
  apply (germPullback I I (openInclusionMap I (sourceOpen I K e))
    (openInclusionMap_isOpenMap I (sourceOpen I K e)) xs).injective
  exact (inclusion_pullback_germEquiv I K e x hx _).trans
    (hsquare.trans
      ((congrArg (germPullback I J r hr xs)
        (inclusion_pullback_germEquiv J L d (f x) (hfd x hx)
          (s ⟨d (f x), hdfx⟩)).symm).trans
            (restrictedMap_pullback_comm I J f hf (sourceOpen I K e) (sourceOpen J L d)
              hfd xs (germEquiv J L d (f x) (hfd x hx) (s ⟨d (f x), hdfx⟩)))))

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PartialBiholomorph
