import Wikipedia.HopfProblem.HolomorphicMeromorphicPullback
import Wikipedia.HopfProblem.HolomorphicMeromorphicField

/-!
# Functoriality of genuine meromorphic pullback

Identity and composition are first checked on actual local holomorphic
functions, then on their categorical stalks. The fraction-field
universal property gives the corresponding identities for meromorphic
germ maps, and pointwise evaluation gives them for actual meromorphic
sections. Pullback also preserves the native complex constants, making
it a homomorphism of complex algebras.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  (I : ModelWithCorners ℂ E H) [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
  (J : ModelWithCorners ℂ E' H') [TopologicalSpace N] [ChartedSpace H' N]
  {E'' H'' P : Type} [NormedAddCommGroup E''] [NormedSpace ℂ E''] [TopologicalSpace H'']
  (K : ModelWithCorners ℂ E'' H'') [TopologicalSpace P] [ChartedSpace H'' P]

@[simp] theorem pullbackOpen_id (U : Opens M) :
    pullbackOpen I I (ContMDiffMap.id : ContMDiffMap I I M M ω) U = U := rfl

@[simp] theorem pullbackOpen_top (f : ContMDiffMap I J M N ω) :
    pullbackOpen I J f ⊤ = ⊤ := rfl

@[simp] theorem pullbackOpen_comp (f : ContMDiffMap I J M N ω)
    (g : ContMDiffMap J K N P ω) (U : Opens P) :
    pullbackOpen I J f (pullbackOpen J K g U) = pullbackOpen I K (g.comp f) U := rfl

/-- Identity pullback is the identity on the original holomorphic sections. -/
@[simp] theorem holomorphicPullback_id (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M U) :
    holomorphicPullback I I (ContMDiffMap.id : ContMDiffMap I I M M ω) U s = s :=
  ContMDiffMap.ext fun _ => rfl

/-- Composition is literal composition of the original local holomorphic functions. -/
theorem holomorphicPullback_comp (f : ContMDiffMap I J M N ω)
    (g : ContMDiffMap J K N P ω) (U : Opens P)
    (s : HolomorphicFunctionSheaf.Section K P U) :
    holomorphicPullback I J f (pullbackOpen J K g U) (holomorphicPullback J K g U s) =
      holomorphicPullback I K (g.comp f) U s :=
  ContMDiffMap.ext fun _ => rfl

@[simp] theorem holomorphicPullback_algebraMap (f : ContMDiffMap I J M N ω)
    (U : Opens N) (c : ℂ) :
    holomorphicPullback I J f U (algebraMap ℂ (HolomorphicFunctionSheaf.Section J N U) c) =
      algebraMap ℂ (HolomorphicFunctionSheaf.Section I M (pullbackOpen I J f U)) c :=
  ContMDiffMap.ext fun _ => rfl

/-- The identity law on genuine categorical holomorphic stalks follows from
the identity law on every actual neighborhood representative. -/
@[simp] theorem holomorphicPullbackStalk_id (x : M) :
    holomorphicPullbackStalk I I (ContMDiffMap.id : ContMDiffMap I I M M ω) x =
      RingHom.id (HolomorphicStalk I M x) := by
  apply RingHom.ext
  intro a
  obtain ⟨U, hxU, s, rfl⟩ := (HolomorphicFunctionSheaf.presheaf I M).exists_germ_eq a
  exact (holomorphicPullbackStalk_germ I I ContMDiffMap.id U x hxU s).trans
    (congrArg (holomorphicGerm I M U ⟨x, hxU⟩) (holomorphicPullback_id I U s))

/-- Categorical holomorphic stalk pullbacks compose because each germ has
an actual local section representative and local composition is literal. -/
theorem holomorphicPullbackStalk_comp (f : ContMDiffMap I J M N ω)
    (g : ContMDiffMap J K N P ω) (x : M) :
    (holomorphicPullbackStalk I J f x).comp (holomorphicPullbackStalk J K g (f x)) =
      holomorphicPullbackStalk I K (g.comp f) x := by
  apply RingHom.ext
  intro a
  obtain ⟨U, hxU, s, rfl⟩ :=
    (HolomorphicFunctionSheaf.presheaf K P).exists_germ_eq a
  have hfirst := congrArg (holomorphicPullbackStalk I J f x)
    (holomorphicPullbackStalk_germ J K g U (f x) hxU s)
  have hsecond := holomorphicPullbackStalk_germ I J f (pullbackOpen J K g U)
    x hxU (holomorphicPullback J K g U s)
  have hlocal := congrArg
    (holomorphicGerm I M (pullbackOpen I J f (pullbackOpen J K g U)) ⟨x, hxU⟩)
    (holomorphicPullback_comp I J K f g U s)
  exact hfirst.trans (hsecond.trans
    (hlocal.trans (holomorphicPullbackStalk_germ I K (g.comp f) U x hxU s).symm))

variable [I.Boundaryless] [IsManifold I ω M]
  [J.Boundaryless] [IsManifold J ω N] [K.Boundaryless] [IsManifold K ω P]

/-- Extending the actual identity stalk map to fractions gives the identity. -/
@[simp] theorem germPullback_id (x : M) :
    germPullback I I (ContMDiffMap.id : ContMDiffMap I I M M ω) IsOpenMap.id x =
      RingHom.id (Germ I M x) := by
  apply IsFractionRing.ringHom_ext (A := HolomorphicStalk I M x)
    (K := Germ I M x) (L := Germ I M x)
  intro a
  exact (germPullback_ofHolomorphicGerm I I ContMDiffMap.id IsOpenMap.id x a).trans
    (congrArg (ofHolomorphicGerm I M x)
      (RingHom.congr_fun (holomorphicPullbackStalk_id I x) a))

@[simp] theorem germPullback_id_apply (x : M) (a : Germ I M x) :
    germPullback I I (ContMDiffMap.id : ContMDiffMap I I M M ω) IsOpenMap.id x a = a :=
  RingHom.congr_fun (germPullback_id I x) a

/-- Composition in the genuine fraction fields is forced by the proved
composition identity on their actual holomorphic local rings. -/
theorem germPullback_comp (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (g : ContMDiffMap J K N P ω) (hg : IsOpenMap g) (x : M) :
    (germPullback I J f hf x).comp (germPullback J K g hg (f x)) =
      germPullback I K (g.comp f) (hg.comp hf) x := by
  apply IsFractionRing.ringHom_ext (A := HolomorphicStalk K P (g (f x)))
  intro a
  have hfirst := congrArg (germPullback I J f hf x)
    (germPullback_ofHolomorphicGerm J K g hg (f x) a)
  have hsecond := germPullback_ofHolomorphicGerm I J f hf x
    (holomorphicPullbackStalk J K g (f x) a)
  have hlocal := congrArg (ofHolomorphicGerm I M x)
    (RingHom.congr_fun (holomorphicPullbackStalk_comp I J K f g x) a)
  exact hfirst.trans (hsecond.trans
    (hlocal.trans (germPullback_ofHolomorphicGerm I K (g.comp f) (hg.comp hf) x a).symm))

theorem germPullback_comp_apply (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (g : ContMDiffMap J K N P ω) (hg : IsOpenMap g) (x : M) (a : Germ K P (g (f x))) :
    germPullback I J f hf x (germPullback J K g hg (f x) a) =
      germPullback I K (g.comp f) (hg.comp hf) x a :=
  RingHom.congr_fun (germPullback_comp I J K f hf g hg x) a

/-- The genuine section pullback obeys the identity law on every original open set. -/
@[simp] theorem pullbackRingHom_id (U : Opens M) :
    pullbackRingHom I I (ContMDiffMap.id : ContMDiffMap I I M M ω) IsOpenMap.id U =
      RingHom.id (Section I M U) := by
  apply RingHom.ext
  intro s
  apply section_ext
  intro x
  exact germPullback_id_apply I x.val (s x)

/-- Genuine section pullbacks compose on their actual inverse-image domains. -/
theorem pullbackRingHom_comp (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (g : ContMDiffMap J K N P ω) (hg : IsOpenMap g) (U : Opens P) :
    (pullbackRingHom I J f hf (pullbackOpen J K g U)).comp (pullbackRingHom J K g hg U) =
      pullbackRingHom I K (g.comp f) (hg.comp hf) U := by
  apply RingHom.ext
  intro s
  apply section_ext
  intro x
  exact germPullback_comp_apply I J K f hf g hg x.val
    (s (pullbackPoint I K (g.comp f) U x))

/-- The composition identity on the actual global section rings. -/
theorem pullbackRingHom_comp_top (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (g : ContMDiffMap J K N P ω) (hg : IsOpenMap g) :
    (pullbackRingHom I J f hf ⊤).comp (pullbackRingHom J K g hg ⊤) =
      pullbackRingHom I K (g.comp f) (hg.comp hf) ⊤ :=
  pullbackRingHom_comp I J K f hf g hg ⊤

theorem pullbackSection_comp (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (g : ContMDiffMap J K N P ω) (hg : IsOpenMap g) (U : Opens P) (s : Section K P U) :
    pullbackSection I J f hf (pullbackOpen J K g U) (pullbackSection J K g hg U s) =
      pullbackSection I K (g.comp f) (hg.comp hf) U s :=
  RingHom.congr_fun (pullbackRingHom_comp I J K f hf g hg U) s

/-- Equal actual maps induce the same pullback on the original global section rings. -/
theorem pullbackRingHom_congr_top (f g : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (hg : IsOpenMap g) (hfg : ∀ x, f x = g x) :
    pullbackRingHom I J f hf ⊤ = pullbackRingHom I J g hg ⊤ := by
  have heq : f = g := ContMDiffMap.ext hfg
  cases heq
  rfl

/-- Genuine meromorphic pullback preserves the complex constants from the
original holomorphic function sheaves. -/
@[simp] theorem pullbackRingHom_algebraMap (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens N) (c : ℂ) :
    pullbackRingHom I J f hf U (algebraMap ℂ (Section J N U) c) =
      algebraMap ℂ (Section I M (pullbackOpen I J f U)) c := by
  exact (pullbackSection_ofHolomorphic I J f hf U
    (algebraMap ℂ (HolomorphicFunctionSheaf.Section J N U) c)).trans
      (congrArg (ofHolomorphic I M (pullbackOpen I J f U))
        (holomorphicPullback_algebraMap I J f U c))

/-- The actual pullback is a homomorphism of the native complex algebras. -/
def pullbackAlgHom (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f) (U : Opens N) :
    Section J N U →ₐ[ℂ] Section I M (pullbackOpen I J f U) where
  __ := pullbackRingHom I J f hf U
  commutes' c := pullbackRingHom_algebraMap I J f hf U c

@[simp] theorem pullbackAlgHom_toRingHom (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens N) : (pullbackAlgHom I J f hf U).toRingHom = pullbackRingHom I J f hf U := rfl

@[simp] theorem pullbackAlgHom_apply (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (U : Opens N) (s : Section J N U) :
    pullbackAlgHom I J f hf U s = pullbackSection I J f hf U s := rfl

@[simp] theorem pullbackAlgHom_id (U : Opens M) :
    pullbackAlgHom I I (ContMDiffMap.id : ContMDiffMap I I M M ω) IsOpenMap.id U =
      AlgHom.id ℂ (Section I M U) := by
  apply AlgHom.ext
  intro s
  exact RingHom.congr_fun (pullbackRingHom_id I U) s

theorem pullbackAlgHom_comp_top (f : ContMDiffMap I J M N ω) (hf : IsOpenMap f)
    (g : ContMDiffMap J K N P ω) (hg : IsOpenMap g) :
    (pullbackAlgHom I J f hf ⊤).comp (pullbackAlgHom J K g hg ⊤) =
      pullbackAlgHom I K (g.comp f) (hg.comp hf) ⊤ := by
  apply AlgHom.ext
  intro s
  exact RingHom.congr_fun (pullbackRingHom_comp_top I J K f hf g hg) s

theorem pullbackAlgHom_congr_top (f g : ContMDiffMap I J M N ω)
    (hf : IsOpenMap f) (hg : IsOpenMap g) (hfg : ∀ x, f x = g x) :
    pullbackAlgHom I J f hf ⊤ = pullbackAlgHom I J g hg ⊤ := by
  apply AlgHom.ext
  intro s
  exact RingHom.congr_fun (pullbackRingHom_congr_top I J f g hf hg hfg) s

end Wikipedia.HopfProblem.HolomorphicMeromorphic
