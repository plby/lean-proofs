import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSheafBasic

/-!
# Genuine gluing for comparison with an extension admitting local lifts

Suppose local sections `t i` of a sheaf `G` have overlap differences
equal to the image of the cocycle. For compatible extension data
`(n, b)`, the actual local sections `i(b i) + n • t i` agree on
intersections and glue in `G`. This gluing is additive and respects
literal restrictions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U) (hU : ∀ x : X, ∃ i : ι, x ∈ U i)
  (ιF : F ⟶ G) (t : ∀ i : ι, Section G (U i))
  (hdiff : ∀ i j : ι, res G inf_le_right (t j) - res G inf_le_left (t i) =
    ιF.hom.app (op (U i ⊓ U j)) (c.value i j))

include hU in
private theorem comparisonCover_covers (V : Opens X) : V ≤ ⨆ i : ι, V ⊓ U i := by
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩

/-- The literal local section to be glued in the target sheaf. -/
def comparisonLocalSection (V : Opens X) (s : ExtensionSection c V) (i : ι) :
    Section G (V ⊓ U i) :=
  ιF.hom.app (op (V ⊓ U i)) (s.1.2 i) + s.1.1.down • res G inf_le_right (t i)

private theorem extension_coordinate_difference_restrict
    {V W : Opens X} (s : ExtensionSection c V) (i j : ι)
    (hWV : W ≤ V) (hi : W ≤ U i) (hj : W ≤ U j) :
    res F (le_inf hWV hi) (s.1.2 i) - res F (le_inf hWV hj) (s.1.2 j) =
      s.1.1.down • res F (le_inf hi hj) (c.value i j) := by
  have h := congrArg (res F (le_inf hWV (le_inf hi hj))) (s.2 i j)
  simpa only [map_sub, map_zsmul, res_trans] using h

include hdiff in
private theorem localLift_difference_restrict (i j : ι) {W : Opens X}
    (hi : W ≤ U i) (hj : W ≤ U j) :
    res G hj (t j) - res G hi (t i) =
      ιF.hom.app (op W) (res F (le_inf hi hj) (c.value i j)) := by
  have h := congrArg (res G (le_inf hi hj)) (hdiff i j)
  simpa only [map_sub, res_trans, res_map] using h

include hdiff in
/-- The local comparison sections satisfy the actual sheaf
compatibility relation on pairwise intersections. -/
theorem comparisonLocalSection_compatible (V : Opens X) (s : ExtensionSection c V) :
    TopCat.Presheaf.IsCompatible G.obj (fun i : ι => V ⊓ U i)
      (comparisonLocalSection c ιF t V s) := by
  intro i j
  let W := (V ⊓ U i) ⊓ (V ⊓ U j)
  have hWV : W ≤ V := inf_le_left.trans inf_le_left
  have hi : W ≤ U i := inf_le_left.trans inf_le_right
  have hj : W ≤ U j := inf_le_right.trans inf_le_right
  have hcoordinates := congrArg (fun a => ιF.hom.app (op W) a)
    (extension_coordinate_difference_restrict c s i j hWV hi hj)
  rw [map_sub, map_zsmul, ← localLift_difference_restrict c ιF t hdiff i j hi hj]
    at hcoordinates
  change res G inf_le_left (comparisonLocalSection c ιF t V s i) =
    res G inf_le_right (comparisonLocalSection c ιF t V s j)
  simp only [comparisonLocalSection, map_add, map_zsmul, res_map, res_trans]
  apply sub_eq_zero.mp
  calc
    _ = (ιF.hom.app (op W) (res F (le_inf hWV hi) (s.1.2 i)) -
          ιF.hom.app (op W) (res F (le_inf hWV hj) (s.1.2 j))) -
        s.1.1.down • (res G hj (t j) - res G hi (t i)) := by
      rw [smul_sub]
      abel
    _ = 0 := by rw [hcoordinates, sub_self]

include hU hdiff in
/-- Actual sheaf gluing supplies the unique comparison section. -/
theorem existsUnique_comparisonSection (V : Opens X) (s : ExtensionSection c V) :
    ∃! a : Section G V, ∀ i : ι,
      res G inf_le_left a = comparisonLocalSection c ιF t V s i :=
  G.existsUnique_gluing' (fun i : ι => V ⊓ U i) V
    (fun _ => homOfLE inf_le_left) (comparisonCover_covers hU V)
    (comparisonLocalSection c ιF t V s)
    (comparisonLocalSection_compatible c ιF t hdiff V s)

/-- The section constructed by genuine gluing, not an assumed
comparison or cocycle solution. -/
def comparisonSection (V : Opens X) (s : ExtensionSection c V) : Section G V :=
  Classical.choose (existsUnique_comparisonSection c hU ιF t hdiff V s)

theorem comparisonSection_spec (V : Opens X) (s : ExtensionSection c V) (i : ι) :
    res G inf_le_left (comparisonSection c hU ιF t hdiff V s) =
      comparisonLocalSection c ιF t V s i :=
  (Classical.choose_spec (existsUnique_comparisonSection c hU ιF t hdiff V s)).1 i

/-- The genuinely glued section is additive in the extension data. -/
def comparisonSectionHom (V : Opens X) : ExtensionSection c V →+ Section G V where
  toFun := comparisonSection c hU ιF t hdiff V
  map_zero' := by
    apply G.eq_of_locally_eq' (fun i : ι => V ⊓ U i) V
      (fun _ => homOfLE inf_le_left) (comparisonCover_covers hU V)
    intro i
    change res G inf_le_left (comparisonSection c hU ιF t hdiff V 0) =
      res G inf_le_left (0 : Section G V)
    rw [comparisonSection_spec]
    change ιF.hom.app (op (V ⊓ U i)) 0 + (0 : ℤ) • res G inf_le_right (t i) =
      res G inf_le_left 0
    simp only [map_zero, zero_zsmul, add_zero]
  map_add' r s := by
    apply G.eq_of_locally_eq' (fun i : ι => V ⊓ U i) V
      (fun _ => homOfLE inf_le_left) (comparisonCover_covers hU V)
    intro i
    change res G inf_le_left (comparisonSection c hU ιF t hdiff V (r + s)) =
      res G inf_le_left
        (comparisonSection c hU ιF t hdiff V r + comparisonSection c hU ιF t hdiff V s)
    rw [map_add, comparisonSection_spec, comparisonSection_spec, comparisonSection_spec]
    change ιF.hom.app (op (V ⊓ U i)) (r.1.2 i + s.1.2 i) +
      (r.1.1.down + s.1.1.down) • res G inf_le_right (t i) =
        (ιF.hom.app (op (V ⊓ U i)) (r.1.2 i) + r.1.1.down • res G inf_le_right (t i)) +
        (ιF.hom.app (op (V ⊓ U i)) (s.1.2 i) + s.1.1.down • res G inf_le_right (t i))
    rw [map_add, add_zsmul]
    abel

@[simp] theorem comparisonSectionHom_apply (V : Opens X) (s : ExtensionSection c V) :
    comparisonSectionHom c hU ιF t hdiff V s =
      comparisonSection c hU ιF t hdiff V s := rfl

/-- The local formulas commute with the literal restriction maps. -/
theorem comparisonLocalSection_restrict {V W : Opens X} (hWV : W ≤ V)
    (s : ExtensionSection c V) (i : ι) :
    res G (inf_le_inf_right (U i) hWV) (comparisonLocalSection c ιF t V s i) =
      comparisonLocalSection c ιF t W (restrict c hWV s) i := by
  change res G (inf_le_inf_right (U i) hWV)
      (ιF.hom.app (op (V ⊓ U i)) (s.1.2 i) + s.1.1.down • res G inf_le_right (t i)) =
    ιF.hom.app (op (W ⊓ U i)) (res F (inf_le_inf_right (U i) hWV) (s.1.2 i)) +
      s.1.1.down • res G inf_le_right (t i)
  rw [map_add, map_zsmul, res_map, res_trans]

/-- The glued comparison respects actual restrictions. -/
theorem comparisonSection_restrict {V W : Opens X} (hWV : W ≤ V)
    (s : ExtensionSection c V) :
    res G hWV (comparisonSection c hU ιF t hdiff V s) =
      comparisonSection c hU ιF t hdiff W (restrict c hWV s) := by
  apply G.eq_of_locally_eq' (fun i : ι => W ⊓ U i) W
    (fun _ => homOfLE inf_le_left) (comparisonCover_covers hU W)
  intro i
  change res G inf_le_left (res G hWV (comparisonSection c hU ιF t hdiff V s)) =
    res G inf_le_left (comparisonSection c hU ιF t hdiff W (restrict c hWV s))
  have hrestrict :
      res G inf_le_left (res G hWV (comparisonSection c hU ιF t hdiff V s)) =
        res G (inf_le_inf_right (U i) hWV)
          (res G inf_le_left (comparisonSection c hU ιF t hdiff V s)) := by
    rw [res_trans, res_trans]
  rw [hrestrict, comparisonSection_spec, comparisonSection_spec]
  exact comparisonLocalSection_restrict c ιF t hWV s i

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
