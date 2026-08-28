import Wikipedia.NoExoticSixSphere.SmoothSphereTubeLocalContribution
import Wikipedia.NoExoticSixSphere.EmbeddedIntersectionSupport

/-!
# Original supported tube evaluation is the transverse intersection count

Each point in the actual finite inverse-image core support has an
isolating open neighborhood inside the tube. Native transversality
proves nonvanishing of the original local restriction and therefore of
its actual singleton component. The proved sphere point evaluation and
finite-support sum then give the original intersection-pair parity.
The first sphere is the embedded tube core; the second may be immersed.
-/

noncomputable section

open Set Function
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothSphereTube

open SphereNormalCapNormalization SupportedModTwoCohomology OpenSphereTubeCap

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace AmbientVector M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 3)) (𝓡 6) (Sphere 3 × NormalVector) M ∞)
  (hsource : Φ.source = univ) (f : Sphere 3 → M)
  (hcore : ∀ s, Φ (s, 0) = f s)

include hsource hcore in
omit [T2Space M] in
/-- The original whole-source tube proves that its core sphere is embedded. -/
theorem injective_core : Injective f := by
  intro x y hxy
  have he : tube Φ hsource (x, 0) = tube Φ hsource (y, 0) :=
    (hcore x).trans (hxy.trans (hcore y).symm)
  exact congrArg Prod.fst ((isOpenEmbedding_tube Φ hsource).injective he)

include hcore in
omit [T2Space M] in
/-- The constructed core support is exactly the range of the original sphere map. -/
theorem coreSupport_eq_range : (coreSupport (tube Φ hsource) : Set M) = range f := by
  change range (core (tube Φ hsource)) = range f
  exact congrArg (fun k : Sphere 3 → M => range k) (funext hcore)

variable (g : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
  (ht : ∀ x y, f x = g y → Surjective ((mfderiv (𝓡 3) (𝓡 6) f x).coprod
    (mfderiv (𝓡 3) (𝓡 6) g y)))

include hcore hf hg ht in
/-- Every actual singleton component of the transverse supported tube pullback is nonzero. -/
theorem pointPieces_supportedPullback_ne_zero (s : Finset (Sphere 3))
    (hs : g ⁻¹' (coreSupport (tube Φ hsource) : Set M) = (s : Set (Sphere 3)))
    (y : Sphere 3) (hy : y ∈ s) :
    pointPieces s 3 (pullbackTo g (coreSupport (tube Φ hsource) : Set M) s hs.subset 3
      (supportedClass (tube Φ hsource) (isOpenEmbedding_tube Φ hsource))) y ≠ 0 := by
  have hmem : g y ∈ (coreSupport (tube Φ hsource) : Set M) := hs.symm.subset hy
  change ∃ x, Φ (x, 0) = g y at hmem
  obtain ⟨x, hx⟩ := hmem
  have hxy : f x = g y := (hcore x).symm.trans hx
  have hxsource : (x, (0 : NormalVector)) ∈ Φ.source := hsource.symm ▸ Set.mem_univ _
  have hytarget : g y ∈ Φ.target := hx ▸ Φ.map_source hxsource
  obtain ⟨V, hV, hyV, hisolate⟩ := exists_isolating_open s y
  let U : Set (Sphere 3) := V ∩ g ⁻¹' Φ.target
  have hU : IsOpen U := hV.inter (Φ.open_target.preimage g.continuous)
  have hyU : y ∈ U := ⟨hyV, hytarget⟩
  have htarget : ∀ z ∈ U, g z ∈ Φ.target := fun _ hz => hz.2
  let L : Set U := (Subtype.val : U → Sphere 3) ⁻¹' (s : Set (Sphere 3))
  have hL : (g.comp (subtypeInclusion U)) ⁻¹'
      (coreSupport (tube Φ hsource) : Set M) = L :=
    congrArg (fun K : Set (Sphere 3) => (Subtype.val : U → Sphere 3) ⁻¹' K) hs
  have hn := local_pullback_ne_zero Φ hsource g U hU htarget f hf hg hcore x ⟨y, hyU⟩
    hxy (ht x y hxy) L hL
  apply pointPieces_ne_zero_of_neighborhood s 3 y hy U
    (fun z hz hzU => hisolate z hz hzU.1)
  intro he
  have hc := pullbackTo_comp (subtypeInclusion U) g
    (coreSupport (tube Φ hsource) : Set M) (s : Set (Sphere 3)) L hs.subset (Subset.refl L) 3
    (supportedClass (tube Φ hsource) (isOpenEmbedding_tube Φ hsource))
  exact hn (hc.trans he)

include hcore hf hg ht in
/-- The original transverse supported pullback evaluates to its finite support cardinality. -/
theorem value_supportedPullback_eq_card (s : Finset (Sphere 3))
    (hs : g ⁻¹' (coreSupport (tube Φ hsource) : Set M) = (s : Set (Sphere 3))) :
    value (g ⁻¹' (coreSupport (tube Φ hsource) : Set M)) 3 (unitSphereTopClass 2)
      (pullback g (coreSupport (tube Φ hsource) : Set M) 3
        (supportedClass (tube Φ hsource) (isOpenEmbedding_tube Φ hsource))) =
      (s.card : ZMod 2) := by
  let a := supportedClass (tube Φ hsource) (isOpenEmbedding_tube Φ hsource)
  have hc := SpherePointEvaluation.finite_value_eq_card_of_nonzero s
    (pullbackTo g (coreSupport (tube Φ hsource) : Set M) s hs.subset 3 a)
    (fun y hy => pointPieces_supportedPullback_ne_zero Φ hsource f hcore g hf hg ht s hs y hy)
  have hv := congrArg (value (s : Set (Sphere 3)) 3 (unitSphereTopClass 2))
    (pullbackTo_eq_extend g (coreSupport (tube Φ hsource) : Set M) s hs.subset 3 a).symm
  exact (value_extend hs.subset 3 (unitSphereTopClass 2)
    (pullback g (coreSupport (tube Φ hsource) : Set M) 3 a)).symm.trans (hv.trans hc)

variable [IsManifold (𝓡 6) ∞ M]

include hcore hf hg ht in
/-- Native transversality supplies finiteness of the literal inverse-image core support. -/
theorem finite_core_preimage : (g ⁻¹' (coreSupport (tube Φ hsource) : Set M)).Finite := by
  rw [coreSupport_eq_range Φ hsource f hcore]
  exact MapIntersections.finite_preimage_range_of_nativeTransverse hf hg
    (injective_core Φ hsource f hcore) ht

include hcore hf hg ht in
/-- The original tube pullback evaluates to the actual geometric source-pair parity. -/
theorem value_supportedPullback_eq_parity :
    value (g ⁻¹' (coreSupport (tube Φ hsource) : Set M)) 3 (unitSphereTopClass 2)
      (pullback g (coreSupport (tube Φ hsource) : Set M) 3
        (supportedClass (tube Φ hsource) (isOpenEmbedding_tube Φ hsource))) =
      MapIntersections.parity f g := by
  have hfin := finite_core_preimage Φ hsource f hcore g hf hg ht
  have he := value_supportedPullback_eq_card Φ hsource f hcore g hf hg ht
    hfin.toFinset hfin.coe_toFinset.symm
  have hc : hfin.toFinset.card = (g ⁻¹' range f).ncard := by
    rw [← Set.ncard_eq_toFinset_card _ hfin, coreSupport_eq_range Φ hsource f hcore]
  exact he.trans ((congrArg (fun k : ℕ => (k : ZMod 2)) hc).trans
    (MapIntersections.parity_eq_preimage_count f g (injective_core Φ hsource f hcore)).symm)

end NoExoticSixSphere.SmoothSphereTube
