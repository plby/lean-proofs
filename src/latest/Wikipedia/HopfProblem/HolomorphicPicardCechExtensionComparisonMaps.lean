import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionComparisonBasic

/-!
# The actual comparison map and its endpoint squares

The additive local gluing construction induces a presheaf map into the
given sheaf, hence a genuine map from the sheafified Čech extension.
When the chosen local sections lift the native constant integer one,
both endpoint maps of this comparison are literal identities.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
  (ιF : F ⟶ G) (πG : G ⟶ degreeSheaf X) (hzero : ιF ≫ πG = 0)
  (t : ∀ i : ι, Section G (U i))
  (hp : ∀ i : ι, πG.hom.app (op (U i)) (t i) =
    (degreeUnit X).app (op (U i)) (ULift.up (1 : ℤ)))
  (hdiff : ∀ i j : ι, res G inf_le_right (t j) - res G inf_le_left (t i) =
    ιF.hom.app (op (U i ⊓ U j)) (c.value i j))

include hU in
private theorem comparisonMapsCover_covers (V : Opens X) :
    V ≤ ⨆ i : ι, V ⊓ U i := by
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- The glued section agrees with the given sheaf map on degree-zero
data that come from an actual section of the original sheaf. -/
theorem comparisonSectionHom_includeHom (V : Opens X) (a : Section F V) :
    comparisonSectionHom c hU ιF t hdiff V (includeHom c V a) =
      ιF.hom.app (op V) a := by
  apply G.eq_of_locally_eq' (fun i : ι => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (comparisonMapsCover_covers hU V)
  intro i
  change res G inf_le_left
      (comparisonSection c hU ιF t hdiff V (includeHom c V a)) =
    res G inf_le_left (ιF.hom.app (op V) a)
  rw [comparisonSection_spec, res_map]
  change ιF.hom.app (op (V ⊓ U i)) (res F inf_le_left a) +
      (0 : ℤ) • res G inf_le_right (t i) =
    ιF.hom.app (op (V ⊓ U i)) (res F inf_le_left a)
  simp only [zero_zsmul, add_zero]

private theorem comparison_degreeUnit_restrict {V W : Opens X} (hWV : W ≤ V)
    (n : ULift.{0} ℤ) :
    res (degreeSheaf X) hWV ((degreeUnit X).app (op V) n) =
      (degreeUnit X).app (op W) n :=
  (ConcreteCategory.congr_hom ((degreeUnit X).naturality (homOfLE hWV).op) n).symm

private theorem comparison_degreeUnit_zsmul_one (V : Opens X) (n : ULift.{0} ℤ) :
    n.down • (degreeUnit X).app (op V) (ULift.up (1 : ℤ)) =
      (degreeUnit X).app (op V) n := by
  have hn : n.down • (ULift.up (1 : ℤ)) = n := by
    apply ULift.ext
    simp
  have hm := map_zsmul ((degreeUnit X).app (op V)).hom n.down (ULift.up (1 : ℤ))
  exact hm.symm.trans (congrArg (fun z => (degreeUnit X).app (op V) z) hn)

include hzero in
private theorem comparison_zero_app (V : Opens X) (a : Section F V) :
    πG.hom.app (op V) (ιF.hom.app (op V) a) = 0 :=
  congrArg (fun e : F ⟶ degreeSheaf X => e.hom.app (op V) a) hzero

include hzero hp in
/-- The image of a genuinely glued section has its prescribed actual
constant-sheaf degree. -/
theorem comparisonSectionHom_projection (V : Opens X) (s : ExtensionSection c V) :
    πG.hom.app (op V) (comparisonSectionHom c hU ιF t hdiff V s) =
      (degreeUnit X).app (op V) (degreeHom c V s) := by
  apply (degreeSheaf X).eq_of_locally_eq' (fun i : ι => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (comparisonMapsCover_covers hU V)
  intro i
  change res (degreeSheaf X) inf_le_left
      (πG.hom.app (op V) (comparisonSection c hU ιF t hdiff V s)) =
    res (degreeSheaf X) inf_le_left ((degreeUnit X).app (op V) (degreeHom c V s))
  rw [res_map, comparisonSection_spec, comparison_degreeUnit_restrict]
  change πG.hom.app (op (V ⊓ U i))
      (ιF.hom.app (op (V ⊓ U i)) (s.1.2 i) + s.1.1.down • res G inf_le_right (t i)) =
    (degreeUnit X).app (op (V ⊓ U i)) s.1.1
  rw [map_add, map_zsmul, comparison_zero_app ιF πG hzero, zero_add,
    ← res_map, hp, comparison_degreeUnit_restrict, comparison_degreeUnit_zsmul_one]

/-- Actual gluing provides a genuine presheaf morphism. -/
def comparisonPre : presheaf c ⟶ G.obj where
  app V := AddCommGrpCat.ofHom (comparisonSectionHom c hU ιF t hdiff V.unop)
  naturality V W h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (comparisonSection_restrict c hU ιF t hdiff (leOfHom h.unop) s).symm

@[simp] theorem comparisonPre_app (V : Opens X) (s : ExtensionSection c V) :
    (comparisonPre c hU ιF t hdiff).app (op V) s =
      comparisonSectionHom c hU ιF t hdiff V s := rfl

theorem inclusionPre_comparisonPre : inclusionPre c ≫ comparisonPre c hU ιF t hdiff = ιF.hom := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro a
  exact comparisonSectionHom_includeHom c hU ιF t hdiff V.unop a

include hzero hp in
theorem comparisonPre_projection :
    comparisonPre c hU ιF t hdiff ≫ πG.hom = projectionPre c ≫ degreeUnit X := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  exact comparisonSectionHom_projection c hU ιF πG hzero t hp hdiff V.unop s

/-- The genuine sheaf comparison induced from the actual presheaf
gluing map by the universal property of sheafification. -/
def comparison : extensionSheaf c ⟶ G where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (comparisonPre c hU ιF t hdiff) G.property

theorem unit_comparison : unit c ≫ (comparison c hU ιF t hdiff).hom =
    comparisonPre c hU ιF t hdiff :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X)
    (comparisonPre c hU ιF t hdiff) G.property

@[simp] theorem comparison_app_unit (V : Opens X) (s : ExtensionSection c V) :
    (comparison c hU ιF t hdiff).hom.app (op V) ((unit c).app (op V) s) =
      comparisonSectionHom c hU ιF t hdiff V s :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (unit_comparison c hU ιF t hdiff) (op V)) s

/-- The left endpoint of the actual comparison is the identity. -/
theorem inclusion_comparison : inclusion c ≫ comparison c hU ιF t hdiff = ιF := by
  apply CategoryTheory.Sheaf.hom_ext
  change (inclusionPre c ≫ unit c) ≫ (comparison c hU ιF t hdiff).hom = ιF.hom
  rw [Category.assoc, unit_comparison, inclusionPre_comparisonPre]

include hzero hp in
/-- The right endpoint of the actual comparison is the identity. -/
theorem comparison_projection :
    comparison c hU ιF t hdiff ≫ πG = projection c := by
  apply extensionHom_ext c
  change unit c ≫ ((comparison c hU ιF t hdiff).hom ≫ πG.hom) =
    unit c ≫ (projection c).hom
  rw [← Category.assoc, unit_comparison,
    comparisonPre_projection c hU ιF πG hzero t hp hdiff, unit_projection]

/-- The genuine map to the supplied extension complex has literal
identity endpoint maps, not just equivalent endpoint objects. -/
def comparisonComplexMap : complex c ⟶ ShortComplex.mk ιF πG hzero where
  τ₁ := 𝟙 F
  τ₂ := comparison c hU ιF t hdiff
  τ₃ := 𝟙 (degreeSheaf X)
  comm₁₂ := by
    change (𝟙 F) ≫ ιF = inclusion c ≫ comparison c hU ιF t hdiff
    rw [Category.id_comp, inclusion_comparison]
  comm₂₃ := by
    change comparison c hU ιF t hdiff ≫ πG = projection c ≫ 𝟙 (degreeSheaf X)
    rw [Category.comp_id]
    exact comparison_projection c hU ιF πG hzero t hp hdiff

@[simp] theorem comparisonComplexMap_τ₁ :
    (comparisonComplexMap c hU ιF πG hzero t hp hdiff).τ₁ = 𝟙 F := rfl

@[simp] theorem comparisonComplexMap_τ₂ :
    (comparisonComplexMap c hU ιF πG hzero t hp hdiff).τ₂ =
      comparison c hU ιF t hdiff := rfl

@[simp] theorem comparisonComplexMap_τ₃ :
    (comparisonComplexMap c hU ιF πG hzero t hp hdiff).τ₃ = 𝟙 (degreeSheaf X) := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
