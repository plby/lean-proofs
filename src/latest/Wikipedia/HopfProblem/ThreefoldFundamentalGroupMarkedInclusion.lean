import Wikipedia.HopfProblem.ThreefoldFundamentalGroupRegularSurjectivity
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupSpecialMarked
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupGeneration

/-!
# Actual marked generators in the threefold fundamental group

The regular-family marking is transported by its literal inclusion into
the constructed threefold.  Surjectivity comes from the actual van Kampen
attachments, so these genuine lattice and joint meridian classes generate
the fundamental group of the threefold.  Their two matrix-conjugation
laws are inherited from the proved covering transport in the regular
family.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne

open TrianglePeriodFamily Meridians

/-- The actual point of the threefold above normalized base coordinate one half. -/
def basepoint : Space := regularFamilyInclusionMap specialRegularFamilyMarkedPoint

/-- The native fundamental group of the constructed space at its marked point. -/
abbrev GlobalGroup := FundamentalGroup Space basepoint

/-- The actual regular-family inclusion on pointed fundamental groups. -/
def regularHom :
    FundamentalGroup SpecialRegularFamily specialRegularFamilyMarkedPoint →* GlobalGroup :=
  FundamentalGroup.map regularFamilyInclusionMap specialRegularFamilyMarkedPoint

theorem regularHom_surjective : Function.Surjective regularHom :=
  regularFamilyInclusionMap_fundamentalGroup_surjective specialRegularFamilyMarkedPoint

/-- The original source-column lattice, followed by the actual inclusion. -/
def latticeHom : Multiplicative Lattice →* GlobalGroup :=
  regularHom.comp specialRegularFamilyMarkedLatticeHom

/-- The two jointly based, geometrically specified meridians in the actual space. -/
def meridian (b : Bool) : GlobalGroup :=
  regularHom (specialRegularFamilyMarkedMeridianClass b)

/-- The whole zero-section free factor, in the same proved joint marking. -/
def freeSectionHom : FreeGroup Bool →* GlobalGroup :=
  regularHom.comp specialRegularFamilyMarkedFreeSectionHom

@[simp] theorem freeSectionHom_of (b : Bool) :
    freeSectionHom (FreeGroup.of b) = meridian b := by
  change regularHom (specialRegularFamilyMarkedFreeSectionHom (FreeGroup.of b)) = _
  rw [specialRegularFamilyMarkedFreeSectionHom_of]
  rfl

/-- A genuine surjective map from the marked semidirect product to the
native fundamental group, with its geometric origin retained. -/
def semidirectHom :
    (Multiplicative Lattice) ⋊[sourceFreeLatticeAction] FreeGroup Bool →* GlobalGroup :=
  regularHom.comp specialRegularFamilyMarkedFundamentalGroupEquiv.symm.toMonoidHom

theorem semidirectHom_surjective : Function.Surjective semidirectHom :=
  regularHom_surjective.comp specialRegularFamilyMarkedFundamentalGroupEquiv.symm.surjective

@[simp] theorem semidirectHom_inl (v : Multiplicative Lattice) :
    semidirectHom (SemidirectProduct.inl v) = latticeHom v := by
  change regularHom (specialRegularFamilyMarkedFundamentalGroupEquiv.symm
    (SemidirectProduct.inl v)) = _
  rw [← specialRegularFamilyMarkedFundamentalGroupEquiv_lattice,
    MulEquiv.symm_apply_apply]
  rfl

@[simp] theorem semidirectHom_inr_of (b : Bool) :
    semidirectHom (SemidirectProduct.inr (FreeGroup.of b)) = meridian b := by
  change regularHom (specialRegularFamilyMarkedFundamentalGroupEquiv.symm
    (SemidirectProduct.inr (FreeGroup.of b))) = _
  rw [← specialRegularFamilyMarkedFundamentalGroupEquiv_meridian,
    MulEquiv.symm_apply_apply]
  rfl

/-- The first actual meridian acts on the original lattice by exactly `A₁`. -/
theorem meridian_first_conjugation (v : Lattice) :
    meridian false * latticeHom (Multiplicative.ofAdd v) * (meridian false)⁻¹ =
      latticeHom (Multiplicative.ofAdd (A₁ *ᵥ v)) := by
  simpa only [map_mul, map_inv, meridian, latticeHom, MonoidHom.comp_apply] using
    congrArg regularHom (specialRegularFamilyMarkedMeridian_first_conjugation v)

/-- The second actual meridian acts on the same lattice by exactly `A₂`. -/
theorem meridian_second_conjugation (v : Lattice) :
    meridian true * latticeHom (Multiplicative.ofAdd v) * (meridian true)⁻¹ =
      latticeHom (Multiplicative.ofAdd (A₂ *ᵥ v)) := by
  simpa only [map_mul, map_inv, meridian, latticeHom, MonoidHom.comp_apply] using
    congrArg regularHom (specialRegularFamilyMarkedMeridian_second_conjugation v)

/-- A homomorphism out of the actual threefold group is determined by
the source lattice and the two jointly based meridians. -/
theorem hom_ext {H : Type*} [Monoid H] (f g : GlobalGroup →* H)
    (hL : ∀ v : Multiplicative Lattice, f (latticeHom v) = g (latticeHom v))
    (hM : ∀ b : Bool, f (meridian b) = g (meridian b)) : f = g := by
  have h := TrianglePeriodFamily.markedRegularFundamentalGroupHom_ext
    specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    (f.comp regularHom) (g.comp regularHom) hL hM
  ext γ
  obtain ⟨δ, rfl⟩ := regularHom_surjective γ
  exact DFunLike.congr_fun h δ

/-- In particular, killing these actual marked classes kills the whole group. -/
theorem hom_eq_one {H : Type*} [Monoid H] (f : GlobalGroup →* H)
    (hL : ∀ v : Multiplicative Lattice, f (latticeHom v) = 1)
    (hM : ∀ b : Bool, f (meridian b) = 1) : f = 1 :=
  hom_ext f 1 hL hM

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.PiOne
