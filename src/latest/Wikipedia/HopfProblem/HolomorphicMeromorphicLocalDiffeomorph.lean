import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackFunctor
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Genuine meromorphic stalks under local biholomorphisms

A native local biholomorphic inverse transfers any local holomorphic
representative to the target.  The actual holomorphic stalk pullback is
therefore surjective, and its fraction-field extension is surjective
as well.  No identification of stalks or meromorphic coordinate-change
law is assumed.
-/

noncomputable section

open Set Filter Topology TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]

/-- Equality of actual local holomorphic function germs follows from
equality on an original neighborhood, even for different section domains. -/
theorem holomorphicGerm_eq_of_eventuallyEq
    {U V : Opens M} (x : M) (hxU : x ∈ U) (hxV : x ∈ V)
    (p : HolomorphicFunctionSheaf.Section I M U)
    (q : HolomorphicFunctionSheaf.Section I M V)
    (h : HolomorphicFunctionSheaf.extendManifoldSection I U p =ᶠ[𝓝 x]
      HolomorphicFunctionSheaf.extendManifoldSection I V q) :
    holomorphicGerm I M U ⟨x, hxU⟩ p = holomorphicGerm I M V ⟨x, hxV⟩ q := by
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ y ∈ V ∧
      HolomorphicFunctionSheaf.extendManifoldSection I U p y =
        HolomorphicFunctionSheaf.extendManifoldSection I V q y := by
    filter_upwards [U.isOpen.mem_nhds hxU, V.isOpen.mem_nhds hxV, h] with y hyU hyV hy
    exact ⟨hyU, hyV, hy⟩
  obtain ⟨W, hW, hWopen, hxW⟩ := mem_nhds_iff.mp hnear
  let W' : Opens M := ⟨W, hWopen⟩
  have hWU : W' ≤ U := fun _ hy => (hW hy).1
  have hWV : W' ≤ V := fun _ hy => (hW hy).2.1
  apply (HolomorphicFunctionSheaf.presheaf I M).germ_ext W' hxW
    (homOfLE hWU) (homOfLE hWV)
  apply ContMDiffMap.ext
  intro y
  exact (HolomorphicFunctionSheaf.extendManifoldSection_apply I U p y.val
    (hWU y.property)).symm.trans ((hW y.property).2.2.trans
      (HolomorphicFunctionSheaf.extendManifoldSection_apply I V q y.val (hWV y.property)))

variable {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℂ E' H') [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ω N]

/-- The true local inverse supplies preimages of every original
holomorphic germ under a native local biholomorphism. -/
theorem holomorphicPullbackStalk_surjective_of_isLocalDiffeomorphAt
    (f : ContMDiffMap I J M N ω) (x : M) (hx : IsLocalDiffeomorphAt I J ω f x) :
    Function.Surjective (holomorphicPullbackStalk I J f x) := by
  intro a
  obtain ⟨U, hxU, p, rfl⟩ := (HolomorphicFunctionSheaf.presheaf I M).exists_germ_eq a
  change HolomorphicFunctionSheaf.Section I M U at p
  let P := HolomorphicFunctionSheaf.extendManifoldSection I U p
  have hleft : hx.localInverse (f x) = x := hx.localInverse_left_inv hx.localInverse_mem_target
  have hP : ContMDiffAt I 𝓘(ℂ) ω P (hx.localInverse (f x)) := by
    rw [hleft]
    exact HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt I U p x hxU
  obtain ⟨V, hxV, q, hq⟩ := HolomorphicFunctionSheaf.exists_manifold_section_of_contMDiffAt J
    (hP.comp (f x) hx.localInverse_contMDiffAt)
  refine ⟨holomorphicGerm J N V ⟨f x, hxV⟩ q, ?_⟩
  rw [holomorphicPullbackStalk_germ I J f V x hxV q]
  apply holomorphicGerm_eq_of_eventuallyEq I x hxV hxU
  have hVnear : ∀ᶠ y in 𝓝 x, f y ∈ V := f.contMDiff.continuous.continuousAt.eventually
    (V.isOpen.mem_nhds hxV)
  filter_upwards [hVnear, U.isOpen.mem_nhds hxU, hx.localInverse_eventuallyEq_left]
    with y hyV hyU hyinv
  rw [HolomorphicFunctionSheaf.extendManifoldSection_apply I
    (pullbackOpen I J f V) (holomorphicPullback I J f V q) y hyV,
    HolomorphicFunctionSheaf.extendManifoldSection_apply I U p y hyU]
  change q ⟨f y, hyV⟩ = p ⟨y, hyU⟩
  rw [hq (f y) hyV]
  change P (hx.localInverse (f y)) = p ⟨y, hyU⟩
  change hx.localInverse (f y) = y at hyinv
  rw [hyinv]
  exact HolomorphicFunctionSheaf.extendManifoldSection_apply I U p y hyU

variable [I.Boundaryless] [IsManifold I ω M] [J.Boundaryless]

/-- The genuine fraction-field pullback of a local biholomorphism is
surjective, because both numerator and denominator germs lift. -/
theorem germPullback_surjective_of_isLocalDiffeomorphAt
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f) (x : M)
    (hx : IsLocalDiffeomorphAt I J ω f x) :
    Function.Surjective (germPullback I J f hf x) := by
  intro a
  obtain ⟨p, q, _hq, rfl⟩ := IsFractionRing.div_surjective (HolomorphicStalk I M x) a
  obtain ⟨p', hp⟩ := holomorphicPullbackStalk_surjective_of_isLocalDiffeomorphAt I J f x hx p
  obtain ⟨q', hq⟩ := holomorphicPullbackStalk_surjective_of_isLocalDiffeomorphAt I J f x hx q
  refine ⟨ofHolomorphicGerm J N (f x) p' / ofHolomorphicGerm J N (f x) q', ?_⟩
  rw [map_div₀, germPullback_ofHolomorphicGerm, germPullback_ofHolomorphicGerm, hp, hq]
  rfl

/-- The induced equivalence is the actual native fraction-field germ map. -/
def germPullbackEquivOfIsLocalDiffeomorphAt
    (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f) (x : M)
    (hx : IsLocalDiffeomorphAt I J ω f x) : Germ J N (f x) ≃+* Germ I M x :=
  RingEquiv.ofBijective (germPullback I J f hf x)
    ⟨(germPullback I J f hf x).injective,
      germPullback_surjective_of_isLocalDiffeomorphAt I J f hf x hx⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic
