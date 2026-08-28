import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionComparisonMaps

/-!
# The actual Čech comparison with a prescribed degree map

The local comparison sections may lift the image of the native integer
degree in any target sheaf. The resulting genuine sheaf comparison has
that prescribed map as its right endpoint.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension

variable {X : TopCat.{0}} {F G H : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
  (ιF : F ⟶ G) (p : G ⟶ H) (a : degreeSheaf X ⟶ H)
  (hzero : ιF ≫ p = 0) (t : ∀ i : ι, Section G (U i))
  (hp : ∀ i : ι, p.hom.app (op (U i)) (t i) =
    a.hom.app (op (U i)) ((degreeUnit X).app (op (U i)) (ULift.up (1 : ℤ))))
  (hdiff : ∀ i j : ι, res G inf_le_right (t j) - res G inf_le_left (t i) =
    ιF.hom.app (op (U i ⊓ U j)) (c.value i j))

include hU in
private theorem cover_covers (V : Opens X) : V ≤ ⨆ i : ι, V ⊓ U i := by
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

private theorem degreeUnit_restrict {V W : Opens X} (hWV : W ≤ V)
    (n : ULift.{0} ℤ) :
    res (degreeSheaf X) hWV ((degreeUnit X).app (op V) n) =
      (degreeUnit X).app (op W) n :=
  (ConcreteCategory.congr_hom ((degreeUnit X).naturality (homOfLE hWV).op) n).symm

private theorem degreeUnit_zsmul_one (V : Opens X) (n : ULift.{0} ℤ) :
    n.down • (degreeUnit X).app (op V) (ULift.up (1 : ℤ)) =
      (degreeUnit X).app (op V) n := by
  have hn : n.down • (ULift.up (1 : ℤ)) = n := by
    apply ULift.ext
    simp
  have hm := map_zsmul ((degreeUnit X).app (op V)).hom n.down (ULift.up (1 : ℤ))
  exact hm.symm.trans (congrArg (fun z => (degreeUnit X).app (op V) z) hn)

include hzero in
private theorem zero_app (V : Opens X) (s : Section F V) :
    p.hom.app (op V) (ιF.hom.app (op V) s) = 0 :=
  congrArg (fun e : F ⟶ H => e.hom.app (op V) s) hzero

include hzero hp in
/-- The image of the genuinely glued comparison section is the
prescribed image of its actual constant-sheaf degree. -/
theorem comparisonSectionHom_projection_map (V : Opens X) (s : ExtensionSection c V) :
    p.hom.app (op V) (comparisonSectionHom c hU ιF t hdiff V s) =
      a.hom.app (op V) ((degreeUnit X).app (op V) (degreeHom c V s)) := by
  apply H.eq_of_locally_eq' (fun i : ι => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (cover_covers hU V)
  intro i
  change res H inf_le_left
      (p.hom.app (op V) (comparisonSection c hU ιF t hdiff V s)) =
    res H inf_le_left
      (a.hom.app (op V) ((degreeUnit X).app (op V) (degreeHom c V s)))
  rw [res_map, comparisonSection_spec, res_map, degreeUnit_restrict]
  change p.hom.app (op (V ⊓ U i))
      (ιF.hom.app (op (V ⊓ U i)) (s.1.2 i) + s.1.1.down • res G inf_le_right (t i)) =
    a.hom.app (op (V ⊓ U i)) ((degreeUnit X).app (op (V ⊓ U i)) s.1.1)
  rw [map_add, map_zsmul, zero_app ιF p hzero, zero_add, ← res_map, hp,
    res_map, degreeUnit_restrict, ← map_zsmul, degreeUnit_zsmul_one]

include hzero hp in
/-- The actual presheaf comparison commutes with the supplied degree map. -/
theorem comparisonPre_projection_map :
    comparisonPre c hU ιF t hdiff ≫ p.hom =
      projectionPre c ≫ degreeUnit X ≫ a.hom := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  exact comparisonSectionHom_projection_map c hU ιF p a hzero t hp hdiff V.unop s

include hzero hp in
/-- The genuine sheaf comparison has the prescribed right endpoint
map, for an arbitrary target sheaf. -/
theorem comparison_projection_map :
    comparison c hU ιF t hdiff ≫ p = projection c ≫ a := by
  apply extensionHom_ext c
  change unit c ≫ ((comparison c hU ιF t hdiff).hom ≫ p.hom) =
    unit c ≫ ((projection c).hom ≫ a.hom)
  rw [← Category.assoc, unit_comparison,
    comparisonPre_projection_map c hU ιF p a hzero t hp hdiff]
  simpa only [Category.assoc] using
    congrArg (fun u : presheaf c ⟶ (degreeSheaf X).obj => u ≫ a.hom)
      (unit_projection c).symm

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
