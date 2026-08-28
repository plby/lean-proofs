import Wikipedia.HopfProblem.HolomorphicMeromorphicSheaf

/-!
# Actual holomorphic pullback and its map on categorical stalks

Composition with a holomorphic map pulls local holomorphic sections back
to the actual inverse-image open set. The compatible maps into a source
stalk induce a ring homomorphism from the target stalk by its categorical
colimit. If the map is open, equality of pulled-back germs descends to
the open image of a genuine source neighborhood, proving injectivity.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H E' H' M N : Type}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

/-- The actual inverse image of an open set under the given holomorphic map. -/
def pullbackOpen (f : ContMDiffMap I J M N ω) (U : Opens N) : Opens M :=
  ⟨f ⁻¹' U, U.isOpen.preimage f.contMDiff.continuous⟩

/-- The original map, restricted to an actual inverse-image open set. -/
def pullbackPoint (f : ContMDiffMap I J M N ω) (U : Opens N)
    (x : pullbackOpen I J f U) : U := ⟨f x.val, x.property⟩

theorem pullbackOpen_mono (f : ContMDiffMap I J M N ω) {U V : Opens N} (h : U ≤ V) :
    pullbackOpen I J f U ≤ pullbackOpen I J f V := fun _ hx => h hx

/-- Composition pulls genuine holomorphic functions back on their actual domains. -/
def holomorphicPullback (f : ContMDiffMap I J M N ω) (U : Opens N) :
    HolomorphicFunctionSheaf.Section J N U →+*
      HolomorphicFunctionSheaf.Section I M (pullbackOpen I J f U) where
  toFun s := ⟨fun x => s (pullbackPoint I J f U x), by
    have hc : ContMDiff I 𝓘(ℂ) ω
        (fun x : pullbackOpen I J f U =>
          HolomorphicFunctionSheaf.extendManifoldSection J U s (f x.val)) := by
      intro x
      exact (contMDiffAt_subtype_iff
        (f := fun z : M => HolomorphicFunctionSheaf.extendManifoldSection J U s (f z))
        (x := x)).mpr
          ((HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt J U s
            (f x.val) x.property).comp x.val (f.contMDiff x.val))
    exact hc.congr fun x =>
      (HolomorphicFunctionSheaf.extendManifoldSection_apply J U s
        (f x.val) x.property).symm⟩
  map_zero' := ContMDiffMap.ext fun _ => rfl
  map_one' := ContMDiffMap.ext fun _ => rfl
  map_add' _ _ := ContMDiffMap.ext fun _ => rfl
  map_mul' _ _ := ContMDiffMap.ext fun _ => rfl

@[simp] theorem holomorphicPullback_apply (f : ContMDiffMap I J M N ω) (U : Opens N)
    (s : HolomorphicFunctionSheaf.Section J N U) (x : pullbackOpen I J f U) :
    holomorphicPullback I J f U s x = s (pullbackPoint I J f U x) := rfl

@[simp] theorem holomorphicPullback_restrict (f : ContMDiffMap I J M N ω)
    {U V : Opens N} (h : U ≤ V) (s : HolomorphicFunctionSheaf.Section J N V) :
    holomorphicPullback I J f U (HolomorphicFunctionSheaf.restrictionAlgHom J N h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M (pullbackOpen_mono I J f h)
        (holomorphicPullback I J f V s) :=
  ContMDiffMap.ext fun _ => rfl

/-- A target holomorphic section gives its actual pulled-back source germ. -/
def holomorphicPullbackOnGerm (f : ContMDiffMap I J M N ω) (x : M)
    (U : Opens N) (hx : f x ∈ U) :
    HolomorphicFunctionSheaf.Section J N U →+* HolomorphicStalk I M x :=
  (holomorphicGerm I M (pullbackOpen I J f U) ⟨x, hx⟩).comp
    (holomorphicPullback I J f U)

theorem holomorphicPullbackOnGerm_restrict (f : ContMDiffMap I J M N ω)
    (x : M) {U V : Opens N} (h : U ≤ V) (hx : f x ∈ U)
    (s : HolomorphicFunctionSheaf.Section J N V) :
    holomorphicPullbackOnGerm I J f x U hx
        (HolomorphicFunctionSheaf.restrictionAlgHom J N h s) =
      holomorphicPullbackOnGerm I J f x V (h hx) s := by
  change holomorphicGerm I M (pullbackOpen I J f U) ⟨x, hx⟩
      (holomorphicPullback I J f U
        (HolomorphicFunctionSheaf.restrictionAlgHom J N h s)) = _
  rw [holomorphicPullback_restrict, holomorphicGerm_restrict]
  rfl

/-- The genuine compatible family on the target open-neighborhood diagram. -/
def holomorphicPullbackStalkCocone (f : ContMDiffMap I J M N ω) (x : M) :
    Cocone ((OpenNhds.inclusion (X := TopCat.of N) (f x)).op ⋙
      HolomorphicFunctionSheaf.presheaf J N) where
  pt := CommRingCat.of (HolomorphicStalk I M x)
  ι :=
    { app := fun U => CommRingCat.ofHom
        (holomorphicPullbackOnGerm I J f x U.unop.1 U.unop.2)
      naturality := by
        intro U V h
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro s
        exact holomorphicPullbackOnGerm_restrict I J f x
          (CategoryTheory.leOfHom h.unop) V.unop.2 s }

/-- Pullback on the actual categorical holomorphic stalks, defined by the colimit. -/
def holomorphicPullbackStalk (f : ContMDiffMap I J M N ω) (x : M) :
    HolomorphicStalk J N (f x) →+* HolomorphicStalk I M x :=
  (colimit.desc _ (holomorphicPullbackStalkCocone I J f x)).hom

@[simp] theorem holomorphicPullbackStalk_germ (f : ContMDiffMap I J M N ω)
    (U : Opens N) (x : M) (hx : f x ∈ U)
    (s : HolomorphicFunctionSheaf.Section J N U) :
    holomorphicPullbackStalk I J f x (holomorphicGerm J N U ⟨f x, hx⟩ s) =
      holomorphicGerm I M (pullbackOpen I J f U) ⟨x, hx⟩
        (holomorphicPullback I J f U s) := by
  exact congrArg (fun h => h s)
    (colimit.ι_desc (holomorphicPullbackStalkCocone I J f x) (op ⟨U, hx⟩))

/-- Openness proves injectivity: equality near the source point gives equality
on the actual open image of that neighborhood near the target point. -/
theorem holomorphicPullbackStalk_injective (f : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (x : M) : Function.Injective (holomorphicPullbackStalk I J f x) := by
  intro a b hab
  obtain ⟨U, hxU, p, rfl⟩ := (HolomorphicFunctionSheaf.presheaf J N).exists_germ_eq a
  obtain ⟨V, hxV, q, rfl⟩ := (HolomorphicFunctionSheaf.presheaf J N).exists_germ_eq b
  have he : holomorphicGerm I M (pullbackOpen I J f U) ⟨x, hxU⟩
      (holomorphicPullback I J f U p) =
      holomorphicGerm I M (pullbackOpen I J f V) ⟨x, hxV⟩
        (holomorphicPullback I J f V q) :=
    (holomorphicPullbackStalk_germ I J f U x hxU p).symm.trans
      (hab.trans (holomorphicPullbackStalk_germ I J f V x hxV q))
  obtain ⟨W, hxW, iU, iV, hW⟩ :=
    (HolomorphicFunctionSheaf.presheaf I M).germ_eq x hxU hxV
      (holomorphicPullback I J f U p) (holomorphicPullback I J f V q) he
  let W' : Opens N := ⟨f '' (W : Set M), hf W W.isOpen⟩
  have hxW' : f x ∈ W' := ⟨x, hxW, rfl⟩
  have hWU : W' ≤ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact iU.le hz
  have hWV : W' ≤ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact iV.le hz
  apply (HolomorphicFunctionSheaf.presheaf J N).germ_ext W' hxW'
    (homOfLE hWU) (homOfLE hWV)
  apply ContMDiffMap.ext
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, rfl⟩ := hy
  exact congrArg (fun s : HolomorphicFunctionSheaf.Section I M W => s ⟨z, hz⟩) hW

end Wikipedia.HopfProblem.HolomorphicMeromorphic
