import Wikipedia.HopfProblem.CuspNormalizationSheafFiniteStalkBasic

/-!
# Injectivity of the closed-map pushforward stalk comparison

If two sections have the same germs at all points of a fibre, their
restrictions agree on a neighbourhood of that fibre. Closedness then
shrinks this neighbourhood to the inverse image of a base neighbourhood.
The sheaf locality axiom proves the required equality of restrictions.
Neither finiteness nor separation of the fibre is needed for this part.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk

variable {X Y : TopCat.{0}}

/-- Actual pushforward germs are equal whenever the corresponding
section germs coincide at every point of the fibre of a closed map. -/
theorem pushforward_germ_eq_of_fiber_germ_eq (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y)
    (U V : Opens Y) (hyU : y ∈ U) (hyV : y ∈ V)
    (s : F.presheaf.obj (op ((Opens.map f).obj U)))
    (t : F.presheaf.obj (op ((Opens.map f).obj V)))
    (h : ∀ x : f ⁻¹' {y},
      F.presheaf.germ ((Opens.map f).obj U) x.val
          (fiber_mem_preimage f y x U hyU) s =
        F.presheaf.germ ((Opens.map f).obj V) x.val
          (fiber_mem_preimage f y x V hyV) t) :
    (f _* F.presheaf).germ U y hyU s = (f _* F.presheaf).germ V y hyV t := by
  classical
  choose W hW iWU iWV heq using fun x : f ⁻¹' {y} =>
    F.presheaf.germ_eq x.val (fiber_mem_preimage f y x U hyU)
      (fiber_mem_preimage f y x V hyV) s t (h x)
  have hcover : f ⁻¹' {y} ⊆ (iSup W : Opens X) := by
    intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hW ⟨x, hx⟩⟩
  obtain ⟨T, hyT, hT⟩ := exists_open_preimage_subset f hf y (iSup W) hcover
  let Z : Opens Y := (T ⊓ U) ⊓ V
  have hyZ : y ∈ Z := ⟨⟨hyT, hyU⟩, hyV⟩
  let iZU : Z ⟶ U := homOfLE (inf_le_left.trans inf_le_right)
  let iZV : Z ⟶ V := homOfLE inf_le_right
  apply (f _* F.presheaf).germ_ext Z hyZ iZU iZV
  change F.presheaf.map ((Opens.map f).map iZU).op s =
    F.presheaf.map ((Opens.map f).map iZV).op t
  apply TopCat.Presheaf.section_ext F ((Opens.map f).obj Z) _ _
  intro z hz
  have hzT : z ∈ (Opens.map f).obj T := hz.1.1
  obtain ⟨x, hx⟩ := Opens.mem_iSup.mp (hT hzT)
  rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
  have hlocal := congrArg (F.presheaf.germ (W x) z hx) (heq x)
  simpa only [F.presheaf.germ_res_apply] using hlocal

/-- For a closed map, the canonical map into all stalks of the fibre is
injective. This uses actual representatives and sheaf locality, and holds
even when the fibre is infinite or the source is not Hausdorff. -/
theorem pushforwardStalkHom_injective (f : X ⟶ Y) (hf : IsClosedMap f)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (y : Y) :
    Function.Injective (pushforwardStalkHom f F.presheaf y) := by
  intro s t hst
  obtain ⟨U, hyU, u, rfl⟩ := (f _* F.presheaf).exists_germ_eq s
  obtain ⟨V, hyV, v, rfl⟩ := (f _* F.presheaf).exists_germ_eq t
  apply pushforward_germ_eq_of_fiber_germ_eq f hf F y U V hyU hyV u v
  intro x
  simpa only [pushforwardStalkHom_germ] using congrFun hst x

end Wikipedia.HopfProblem.CuspNormalization.SheafFiniteStalk
