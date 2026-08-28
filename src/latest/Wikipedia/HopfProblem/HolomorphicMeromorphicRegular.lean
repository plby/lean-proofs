import Wikipedia.HopfProblem.HolomorphicMeromorphicValue

/-!
# The dense native holomorphic locus of an arbitrary meromorphic function

Regularity is membership in the original holomorphic local ring. It is
an open condition, and every local fraction supplies a dense set of
regular points through the cozero locus of its actual denominator. On
this open locus the canonical ordinary values form a genuine native
holomorphic function, whose meromorphic germs are the original section.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- A regular germ has an actual holomorphic representative on an
original neighborhood, agreeing there with all meromorphic germs. -/
theorem local_holomorphic_representation {U : Opens M} (a : Section I M U) (x : U)
    (hx : RegularAt I M a x) :
    ∃ (V : Opens M) (hVU : V ≤ U) (_hxV : x.val ∈ V)
      (f : HolomorphicFunctionSheaf.Section I M V),
      ∀ y : V, a (Set.inclusion hVU y) = sectionGerm I M V y f := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨V, hxV, f, hf⟩ := (HolomorphicFunctionSheaf.presheaf I M).exists_germ_eq p
  have hf' : holomorphicGerm I M V ⟨x.val, hxV⟩ f = p := hf
  let b := ofHolomorphic I M V f
  have hb : a x = b ⟨x.val, hxV⟩ :=
    hp.symm.trans ((congrArg (ofHolomorphicGerm I M x.val) hf').symm.trans
      (ofHolomorphic_apply I M V f ⟨x.val, hxV⟩).symm)
  obtain ⟨W, hWU, hWV, hxW, hW⟩ :=
    exists_neighborhood_eq_of_germ_eq I M a b x.val x.property hxV hb
  refine ⟨W, hWU, hxW, HolomorphicFunctionSheaf.restrictionAlgHom I M hWV f, ?_⟩
  intro y
  exact (hW y).trans ((ofHolomorphic_apply I M V f (Set.inclusion hWV y)).trans
    (sectionGerm_restrict I M hWV y f).symm)

/-- Regularity is open in the original section domain. -/
theorem isOpen_regularAt {U : Opens M} (a : Section I M U) :
    IsOpen {x : U | RegularAt I M a x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨V, hVU, hxV, f, hf⟩ := local_holomorphic_representation I M a x hx
  have hr : IsOpen (range (Set.inclusion hVU)) :=
    (Opens.isOpenEmbedding_of_le hVU).isOpen_range
  apply mem_of_superset (hr.mem_nhds ⟨⟨x.val, hxV⟩, rfl⟩)
  rintro y ⟨z, rfl⟩
  exact ⟨holomorphicGerm I M V z f, (hf z).symm⟩

/-- The canonical ordinary representative is genuinely holomorphic
at every regular point, in the original induced atlas. -/
theorem value_contMDiffAt_of_regularAt {U : Opens M} (a : Section I M U) (x : U)
    (hx : RegularAt I M a x) : ContMDiffAt I 𝓘(ℂ) ω (value I M a) x := by
  obtain ⟨V, hVU, hxV, f, hf⟩ := local_holomorphic_representation I M a x hx
  have hF : ContMDiffAt I 𝓘(ℂ) ω
      (fun y : U => HolomorphicFunctionSheaf.extendManifoldSection I V f y.val) x :=
    (HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt I V f x.val hxV).comp x
      (contMDiff_subtype_val x)
  apply hF.congr_of_eventuallyEq
  filter_upwards [continuous_subtype_val.continuousAt.eventually (V.isOpen.mem_nhds hxV)]
    with y hy
  have hfy : a y = sectionGerm I M V ⟨y.val, hy⟩ f := hf ⟨y.val, hy⟩
  exact (value_eq_of_holomorphicGerm I M a y _ hfy.symm).trans
    ((HolomorphicFunctionSheaf.stalkEval_germ I M V y.val hy f).trans
      (HolomorphicFunctionSheaf.extendManifoldSection_apply I V f y.val hy).symm)

/-- A point where an actual denominator is nonzero is regular. -/
theorem regularAt_of_local_fraction {U V : Opens M} (a : Section I M U)
    (p q : HolomorphicFunctionSheaf.Section I M V) (x : M) (hxU : x ∈ U) (hxV : x ∈ V)
    (ha : a ⟨x, hxU⟩ = fraction I M V p q ⟨x, hxV⟩) (hq : q ⟨x, hxV⟩ ≠ 0) :
    RegularAt I M a ⟨x, hxU⟩ := by
  have hqv : HolomorphicFunctionSheaf.stalkEval I M x
      (holomorphicGerm I M V ⟨x, hxV⟩ q) = q ⟨x, hxV⟩ :=
    HolomorphicFunctionSheaf.stalkEval_germ I M V x hxV q
  obtain ⟨r, hr, _⟩ := exists_holomorphic_fraction_of_denominator_value_ne_zero I M x
    (holomorphicGerm I M V ⟨x, hxV⟩ p) (holomorphicGerm I M V ⟨x, hxV⟩ q)
    (fun h => hq (hqv.symm.trans h))
  exact ⟨r, hr.trans ha.symm⟩

/-- Regular points are dense for every genuine meromorphic section. -/
theorem dense_regularAt {U : Opens M} (a : Section I M U) :
    Dense {x : U | RegularAt I M a x} := by
  apply dense_iff_inter_open.mpr
  intro S hSo hSne
  obtain ⟨x, hxS⟩ := hSne
  obtain ⟨V, hVU, hxV, p, q, hq, ha⟩ := local_representation I M a x
  have hqd : Dense {y : V | q y ≠ 0} :=
    HolomorphicFunctionSheaf.dense_cozero_of_germs_ne_zero I V q hq
  have hTo : IsOpen ((Set.inclusion hVU) ⁻¹' S) :=
    hSo.preimage (Opens.isOpenEmbedding_of_le hVU).continuous
  obtain ⟨y, hyS, hyq⟩ := dense_iff_inter_open.mp hqd _ hTo ⟨⟨x.val, hxV⟩, hxS⟩
  exact ⟨Set.inclusion hVU y, hyS,
    regularAt_of_local_fraction I M a p q y.val (hVU y.property) y.property (ha y) hyq⟩

/-- The genuine regular locus as an actual open subset of the original manifold. -/
def regularDomain {U : Opens M} (a : Section I M U) : Opens M :=
  ⟨Subtype.val '' {x : U | RegularAt I M a x},
    U.isOpen.isOpenMap_subtype_val _ (isOpen_regularAt I M a)⟩

theorem regularDomain_le {U : Opens M} (a : Section I M U) : regularDomain I M a ≤ U :=
  Subtype.coe_image_subset _ _

theorem regularAt_of_mem_regularDomain {U : Opens M} (a : Section I M U)
    (x : regularDomain I M a) :
    RegularAt I M a (Set.inclusion (regularDomain_le I M a) x) := by
  obtain ⟨u, hu, he⟩ := x.property
  have hx : Set.inclusion (regularDomain_le I M a) x = u := Subtype.ext he.symm
  rw [hx]
  exact hu

/-- The actual ordinary holomorphic function on the dense regular locus. -/
def regularRepresentative {U : Opens M} (a : Section I M U) :
    HolomorphicFunctionSheaf.Section I M (regularDomain I M a) :=
  ⟨fun x => value I M a (Set.inclusion (regularDomain_le I M a) x), fun x =>
    (value_contMDiffAt_of_regularAt I M a _ (regularAt_of_mem_regularDomain I M a x)).comp x
      (contMDiff_inclusion (regularDomain_le I M a) x)⟩

@[simp] theorem regularRepresentative_apply {U : Opens M} (a : Section I M U)
    (x : regularDomain I M a) :
    regularRepresentative I M a x =
      value I M a (Set.inclusion (regularDomain_le I M a) x) := rfl

/-- The regular holomorphic representative has exactly the original
meromorphic germs, not merely the same point values. -/
theorem regularRepresentative_germ {U : Opens M} (a : Section I M U)
    (x : regularDomain I M a) :
    sectionGerm I M (regularDomain I M a) x (regularRepresentative I M a) =
      a (Set.inclusion (regularDomain_le I M a) x) := by
  let u : U := Set.inclusion (regularDomain_le I M a) x
  obtain ⟨V, hVU, hxV, f, hf⟩ := local_holomorphic_representation I M a u
    (regularAt_of_mem_regularDomain I M a x)
  let W : Opens M := regularDomain I M a ⊓ V
  have hWD : W ≤ regularDomain I M a := inf_le_left
  have hWV : W ≤ V := inf_le_right
  let w : W := ⟨x.val, ⟨x.property, hxV⟩⟩
  have he : HolomorphicFunctionSheaf.restrictionAlgHom I M hWD (regularRepresentative I M a) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M hWV f := by
    apply ContMDiffMap.ext
    intro y
    have hfy := hf (Set.inclusion hWV y)
    change value I M a ⟨y.val, _⟩ = f (Set.inclusion hWV y)
    exact (value_eq_of_holomorphicGerm I M a _ _ hfy.symm).trans
      (HolomorphicFunctionSheaf.stalkEval_germ I M V y.val (hWV y.property) f)
  calc
    sectionGerm I M (regularDomain I M a) x (regularRepresentative I M a) =
        sectionGerm I M W w (HolomorphicFunctionSheaf.restrictionAlgHom I M hWD
          (regularRepresentative I M a)) :=
      (sectionGerm_restrict I M hWD w (regularRepresentative I M a)).symm
    _ = sectionGerm I M W w (HolomorphicFunctionSheaf.restrictionAlgHom I M hWV f) :=
      congrArg (sectionGerm I M W w) he
    _ = sectionGerm I M V (Set.inclusion hWV w) f := sectionGerm_restrict I M hWV w f
    _ = a (Set.inclusion (regularDomain_le I M a) x) := (hf (Set.inclusion hWV w)).symm

theorem ofHolomorphic_regularRepresentative {U : Opens M} (a : Section I M U) :
    ofHolomorphic I M (regularDomain I M a) (regularRepresentative I M a) =
      restrict I M (regularDomain_le I M a) a := by
  apply section_ext
  intro x
  exact (ofHolomorphic_apply I M _ _ x).trans (regularRepresentative_germ I M a x)

end Wikipedia.HopfProblem.HolomorphicMeromorphic
