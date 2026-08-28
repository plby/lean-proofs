import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticAction
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusQuotient
import Mathlib.Topology.LocalAtTarget

/-!
# The genuine punctured elliptic filling as radius times a mapping torus

Both quotient maps used below are the original continuous open quotient
maps.  Their fibres are compared using the actual affine cyclic action.
The resulting mapping-torus monodromy is the positive affine generator.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods Wikipedia.HopfProblem.Elliptic
open Wikipedia.HopfProblem.Elliptic.HigherHomology.MappingTorusQuotient

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (r : ℝ)

/-- The literal punctured part of the radius-restricted original filling. -/
def puncturedSet : Set (Filling j v hv) :=
  {y | (fillingProjection j v hv y : ℂ) ≠ 0 ∧ ‖(fillingProjection j v hv y : ℂ)‖ < r}

abbrev PuncturedFilling := puncturedSet j v hv r

/-- Its full preimage under the genuine finite covering. -/
abbrev PuncturedUpstairs := fillingQuotient j v hv ⁻¹' puncturedSet j v hv r

theorem puncturedUpstairs_mem (x : Family j) :
    x ∈ PuncturedUpstairs j v hv r ↔
      (x.1 : ℂ) ≠ 0 ∧ ‖(x.1 : ℂ)‖ ^ j.order < r := by
  change ((x.1 : ℂ) ^ j.order ≠ 0 ∧ ‖(x.1 : ℂ) ^ j.order‖ < r) ↔ _
  rw [norm_pow]
  constructor
  · rintro ⟨hne, hnorm⟩
    exact ⟨fun hz => hne (by rw [hz, zero_pow j.order_pos.ne']), hnorm⟩
  · rintro ⟨hne, hnorm⟩
    exact ⟨pow_ne_zero _ hne, hnorm⟩

/-- The preimage is exactly the punctured root disc times the real period torus. -/
def upstairsRootHomeomorph :
    PuncturedUpstairs j v hv r ≃ₜ RootDisc j.order r × RealTorus₄ where
  toFun y := (⟨y.val.1, (puncturedUpstairs_mem j v hv r y.val).mp y.property⟩, y.val.2)
  invFun p := ⟨(p.1.val, p.2),
    (puncturedUpstairs_mem j v hv r (p.1.val, p.2)).mpr p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp continuous_subtype_val)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk
    continuous_snd).subtype_mk _

/-- Genuine polar coordinates on the full preimage of the punctured filling. -/
def upstairsPolarHomeomorph :
    PuncturedUpstairs j v hv r ≃ₜ Radius j.order r × (Circle × RealTorus₄) :=
  (upstairsRootHomeomorph j v hv r).trans
    (((polarHomeomorph j.order r).prodCongr (Homeomorph.refl RealTorus₄)).trans
      (Homeomorph.prodAssoc _ _ _))

@[simp] theorem upstairsPolarHomeomorph_symm_val
    (p : Radius j.order r × (Circle × RealTorus₄)) :
    ((upstairsPolarHomeomorph j v hv r).symm p : Family j) =
      polarFamilyAt j r p.1 p.2 := rfl

/-- The original quotient map, expressed in polar coordinates. -/
def polarQuotient (p : Radius j.order r × (Circle × RealTorus₄)) :
    PuncturedFilling j v hv r :=
  (puncturedSet j v hv r).restrictPreimage (fillingQuotient j v hv)
    ((upstairsPolarHomeomorph j v hv r).symm p)

@[simp] theorem polarQuotient_val (p : Radius j.order r × (Circle × RealTorus₄)) :
    (polarQuotient j v hv r p : Filling j v hv) =
      fillingQuotient j v hv (polarFamilyAt j r p.1 p.2) := rfl

theorem polarQuotient_isOpenQuotientMap : IsOpenQuotientMap (polarQuotient j v hv r) := by
  have hq : IsOpenQuotientMap (fillingQuotient j v hv) :=
    ⟨fillingQuotient_surjective j v hv, fillingQuotient_continuous j v hv,
      (fillingQuotient_isCoveringMap j v hv).isOpenMap⟩
  have hr := hq.restrictPreimage (puncturedSet j v hv r)
  let e := (upstairsPolarHomeomorph j v hv r).symm
  exact ⟨hr.surjective.comp e.surjective, hr.continuous.comp e.continuous,
    hr.isOpenMap.comp e.isOpenMap⟩

@[simp] theorem polarQuotient_projection_norm
    (p : Radius j.order r × (Circle × RealTorus₄)) :
    ‖(fillingProjection j v hv (polarQuotient j v hv r p) : ℂ)‖ =
      (p.1 : ℝ) ^ j.order := by
  change ‖(root j.order r p.1 p.2.1 : ℂ) ^ j.order‖ = _
  rw [norm_pow, root_norm]

/-- The finite circle quotient using the inverse affine map. -/
abbrev BoundaryQuotient := ProductQuotient j.order (flatTorusAffine j v).symm
  (affine_symm_pow_order j v hv.1)

/-- The product quotient has the same radius coordinate. -/
def radialQuotient (p : Radius j.order r × (Circle × RealTorus₄)) :
    Radius j.order r × BoundaryQuotient j v hv :=
  (p.1, project j.order (flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1) p.2)

theorem radialQuotient_isOpenQuotientMap : IsOpenQuotientMap (radialQuotient j v hv r) := by
  let := productAction j.order (flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  let := productAction_continuousConstSMul j.order (flatTorusAffine j v).symm
    (affine_symm_pow_order j v hv.1)
  exact IsOpenQuotientMap.id.prodMap
    (FiniteQuotient.project_isOpenQuotientMap (CyclicGroup j) (Circle × RealTorus₄))

/-- Orbit equality is the same for the two actual quotient maps. -/
theorem polarQuotient_eq_iff (p q : Radius j.order r × (Circle × RealTorus₄)) :
    polarQuotient j v hv r p = polarQuotient j v hv r q ↔
      radialQuotient j v hv r p = radialQuotient j v hv r q := by
  let := productAction j.order (flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  let := familyAction j v hv.1
  rcases p with ⟨a, p⟩
  rcases q with ⟨b, q⟩
  constructor
  · intro h
    have hpow := congrArg (fun y : PuncturedFilling j v hv r =>
      ‖(fillingProjection j v hv y : ℂ)‖) h
    simp only [polarQuotient_projection_norm] at hpow
    have hab : a = b := Subtype.ext
      ((pow_left_inj₀ a.property.1.le b.property.1.le j.order_pos.ne').mp hpow)
    subst b
    apply Prod.ext
    · rfl
    have hq : fillingQuotient j v hv (polarFamilyAt j r a p) =
        fillingQuotient j v hv (polarFamilyAt j r a q) := congrArg Subtype.val h
    obtain ⟨g, hg⟩ := (FiniteQuotient.project_eq_iff_mem_orbit
      (CyclicGroup j) (Family j) _ _).mp hq
    apply (FiniteQuotient.project_eq_iff_mem_orbit (CyclicGroup j)
      (Circle × RealTorus₄) _ _).mpr
    refine ⟨g⁻¹, (polarFamilyAt_injective j r a) ?_⟩
    have he := polarFamilyAt_smul j v hv.1 r a g⁻¹ q
    have he' : polarFamilyAt j r a (g⁻¹ • q) = g • polarFamilyAt j r a q := by
      simpa only [inv_inv] using he
    exact he'.trans hg
  · intro h
    have hab : a = b := congrArg Prod.fst h
    subst b
    have hp : project j.order (flatTorusAffine j v).symm
        (affine_symm_pow_order j v hv.1) p =
      project j.order (flatTorusAffine j v).symm
        (affine_symm_pow_order j v hv.1) q := congrArg Prod.snd h
    obtain ⟨g, hg⟩ := (FiniteQuotient.project_eq_iff_mem_orbit
      (CyclicGroup j) (Circle × RealTorus₄) _ _).mp hp
    apply Subtype.ext
    change fillingQuotient j v hv (polarFamilyAt j r a p) =
      fillingQuotient j v hv (polarFamilyAt j r a q)
    rw [← hg, polarFamilyAt_smul j v hv.1]
    exact FiniteQuotient.project_smul (CyclicGroup j) (Family j) g⁻¹ _

/-- Comparison of the genuine punctured quotient with its finite circle quotient. -/
def puncturedPolarHomeomorph :
    PuncturedFilling j v hv r ≃ₜ Radius j.order r × BoundaryQuotient j v hv :=
  quotientHomeomorph (polarQuotient j v hv r) (radialQuotient j v hv r)
    (polarQuotient_isOpenQuotientMap j v hv r).isQuotientMap
    (radialQuotient_isOpenQuotientMap j v hv r).isQuotientMap
    (polarQuotient_eq_iff j v hv r)

@[simp] theorem puncturedPolarHomeomorph_polarQuotient
    (p : Radius j.order r × (Circle × RealTorus₄)) :
    puncturedPolarHomeomorph j v hv r (polarQuotient j v hv r p) =
      radialQuotient j v hv r p :=
  quotientHomeomorph_apply _ _ _ _ _ p

@[simp] theorem puncturedPolarHomeomorph_symm_radialQuotient
    (p : Radius j.order r × (Circle × RealTorus₄)) :
    (puncturedPolarHomeomorph j v hv r).symm (radialQuotient j v hv r p) =
      polarQuotient j v hv r p :=
  quotientHomeomorph_symm_apply _ _ _ _ _ p

/-- The boundary monodromy is the genuine affine map, in positive orientation. -/
abbrev Boundary := MappingTorus.Torus (flatTorusAffine j v)

/-- The actual whole punctured filling is a radius times its boundary mapping torus. -/
def puncturedProductHomeomorph :
    PuncturedFilling j v hv r ≃ₜ Radius j.order r × Boundary j v :=
  (puncturedPolarHomeomorph j v hv r).trans
    ((Homeomorph.refl _).prodCongr
      (mappingTorusHomeomorph j.order (flatTorusAffine j v).symm
        (affine_symm_pow_order j v hv.1)))

/-- The inverse has the literal family-quotient formula for every cylinder point. -/
theorem puncturedProductHomeomorph_symm_mk
    (a : Radius j.order r) (t : ℝ) (x : RealTorus₄) :
    (puncturedProductHomeomorph j v hv r).symm
        (a, MappingTorus.mk (flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r (a, (((t / j.order : ℝ) : Circle), x)) := by
  change (puncturedPolarHomeomorph j v hv r).symm
    (a, (mappingTorusHomeomorph j.order (flatTorusAffine j v).symm
      (affine_symm_pow_order j v hv.1)).symm (MappingTorus.mk _ (t, x))) = _
  rw [mappingTorusHomeomorph_symm_mk]
  exact puncturedPolarHomeomorph_symm_radialQuotient j v hv r
    (a, (((t / j.order : ℝ) : Circle), x))

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
