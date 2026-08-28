import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupGenerators
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupFreeCoverMonodromy

/-!
# The actual regular base has free fundamental group on two positive meridians

Path subdivision through the two slit domains proves generation. A
constructed discrete free-group covering reads the two positive circles
as the two free letters, proving independence. The resulting equivalence
and universal property concern Mathlib's actual fundamental group.

The already constructed normalized uniformization transfers this result
to the original regular triangle quotient. No presentation, meridian
identification, or uniformizing coordinate remains an assumption.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

@[simp] theorem meridianFreeWordHom_meridianClass (b : Bool) :
    meridianFreeWordHom (meridianClass b) = FreeGroup.of b := by
  cases b
  · exact meridianFreeWordHom_positiveMeridianZero
  · exact meridianFreeWordHom_positiveMeridianOne

/-- Reading a word of actual meridians returns the same free word. -/
theorem meridianFreeWordHom_comp_wordMap :
    meridianFreeWordHom.comp meridianWordMap = MonoidHom.id (FreeGroup Bool) := by
  apply FreeGroup.ext_hom
  intro b
  simp only [MonoidHom.comp_apply, meridianWordMap_of,
    meridianFreeWordHom_meridianClass, MonoidHom.id_apply]

@[simp] theorem meridianFreeWordHom_wordMap (w : FreeGroup Bool) :
    meridianFreeWordHom (meridianWordMap w) = w :=
  DFunLike.congr_fun meridianFreeWordHom_comp_wordMap w

/-- There are no relations between the two positive meridians. -/
theorem meridianWordMap_injective : Function.Injective meridianWordMap := by
  intro v w h
  have h' := congrArg meridianFreeWordHom h
  simpa only [meridianFreeWordHom_wordMap] using h'

theorem meridianWordMap_bijective : Function.Bijective meridianWordMap :=
  ⟨meridianWordMap_injective, meridianWordMap_surjective⟩

@[simp] theorem meridianWordMap_freeWordHom
    (γ : FundamentalGroup TwicePuncturedPlane meridianBasepoint) :
    meridianWordMap (meridianFreeWordHom γ) = γ := by
  obtain ⟨w, rfl⟩ := meridianWordMap_surjective γ
  rw [meridianFreeWordHom_wordMap]

/-- The genuine free-group marking of the twice-punctured plane. -/
def twicePuncturedFundamentalGroupFreeEquiv :
    FundamentalGroup TwicePuncturedPlane meridianBasepoint ≃* FreeGroup Bool where
  __ := meridianFreeWordHom
  invFun := meridianWordMap
  left_inv := meridianWordMap_freeWordHom
  right_inv := meridianFreeWordHom_wordMap

@[simp] theorem twicePuncturedFundamentalGroupFreeEquiv_apply
    (γ : FundamentalGroup TwicePuncturedPlane meridianBasepoint) :
    twicePuncturedFundamentalGroupFreeEquiv γ = meridianFreeWordHom γ := rfl

@[simp] theorem twicePuncturedFundamentalGroupFreeEquiv_symm_apply (w : FreeGroup Bool) :
    twicePuncturedFundamentalGroupFreeEquiv.symm w = meridianWordMap w := rfl

@[simp] theorem twicePuncturedFundamentalGroupFreeEquiv_meridianClass (b : Bool) :
    twicePuncturedFundamentalGroupFreeEquiv (meridianClass b) = FreeGroup.of b :=
  meridianFreeWordHom_meridianClass b

@[simp] theorem twicePuncturedFundamentalGroupFreeEquiv_symm_of (b : Bool) :
    twicePuncturedFundamentalGroupFreeEquiv.symm (FreeGroup.of b) = meridianClass b :=
  meridianWordMap_of b

instance twicePuncturedPlane_pathConnectedSpace : PathConnectedSpace TwicePuncturedPlane := by
  apply pathConnectedSpace_iff_univ.mpr
  rw [← upperSlit_union_lowerSlit]
  exact meridianSlitCover.simplyU.isPathConnected.union
    meridianSlitCover.simplyV.isPathConnected
    ⟨meridianBasepoint, meridianSlitCover.baseU, meridianSlitCover.baseV⟩

/-- The same free abstract fundamental group at any actual plane basepoint. -/
def twicePuncturedFundamentalGroupFreeEquivAt (x : TwicePuncturedPlane) :
    FundamentalGroup TwicePuncturedPlane x ≃* FreeGroup Bool :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x meridianBasepoint).trans
    twicePuncturedFundamentalGroupFreeEquiv

/-- The point of the original regular quotient with normalized coordinate `1/2`. -/
def triangleRegularMeridianBasepoint : TriangleRegularQuotient :=
  triangleRegularPlaneHomeomorph.symm meridianBasepoint

@[simp] theorem triangleRegularMeridianBasepoint_coordinate :
    triangleRegularPlaneHomeomorph triangleRegularMeridianBasepoint = meridianBasepoint :=
  triangleRegularPlaneHomeomorph.apply_symm_apply meridianBasepoint

/-- Pull back the two actual positive circles through the proved homeomorphism. -/
def triangleRegularMeridian (b : Bool) :
    Path triangleRegularMeridianBasepoint triangleRegularMeridianBasepoint :=
  (if b then positiveMeridianOne else positiveMeridianZero).map
    triangleRegularPlaneHomeomorph.symm.continuous

def triangleRegularMeridianClass (b : Bool) :
    FundamentalGroup TriangleRegularQuotient triangleRegularMeridianBasepoint :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (triangleRegularMeridian b))

/-- The classes are induced by the actual inverse uniformization, not assigned
abstract free generators. -/
theorem triangleRegularMeridianClass_eq_induced (b : Bool) :
    triangleRegularMeridianClass b =
      twicePuncturedPlaneFundamentalGroupEquiv meridianBasepoint (meridianClass b) := rfl

/-- A proved free-group presentation for the original regular triangle base. -/
def triangleRegularFundamentalGroupFreeEquiv :
    FundamentalGroup TriangleRegularQuotient triangleRegularMeridianBasepoint ≃*
      FreeGroup Bool :=
  (twicePuncturedPlaneFundamentalGroupEquiv meridianBasepoint).symm.trans
    twicePuncturedFundamentalGroupFreeEquiv

@[simp] theorem triangleRegularFundamentalGroupFreeEquiv_meridianClass (b : Bool) :
    triangleRegularFundamentalGroupFreeEquiv (triangleRegularMeridianClass b) =
      FreeGroup.of b := by
  rw [triangleRegularMeridianClass_eq_induced]
  change twicePuncturedFundamentalGroupFreeEquiv
    ((twicePuncturedPlaneFundamentalGroupEquiv meridianBasepoint).symm
      (twicePuncturedPlaneFundamentalGroupEquiv meridianBasepoint (meridianClass b))) = _
  rw [MulEquiv.symm_apply_apply, twicePuncturedFundamentalGroupFreeEquiv_meridianClass]

@[simp] theorem triangleRegularFundamentalGroupFreeEquiv_symm_of (b : Bool) :
    triangleRegularFundamentalGroupFreeEquiv.symm (FreeGroup.of b) =
      triangleRegularMeridianClass b := by
  apply triangleRegularFundamentalGroupFreeEquiv.injective
  rw [MulEquiv.apply_symm_apply, triangleRegularFundamentalGroupFreeEquiv_meridianClass]

/-- The free fundamental group at an arbitrary point of the actual regular quotient. -/
def triangleRegularFundamentalGroupFreeEquivAt (x : TriangleRegularQuotient) :
    FundamentalGroup TriangleRegularQuotient x ≃* FreeGroup Bool :=
  (triangleRegularFundamentalGroupEquiv x).trans
    (twicePuncturedFundamentalGroupFreeEquivAt (triangleRegularPlaneHomeomorph x))

private theorem freeGroup_marking_presentation {K G : Type*} [Group K] [Group G]
    (e : K ≃* FreeGroup Bool) (g : Bool → G) :
    ∃! F : K →* G, ∀ b, F (e.symm (FreeGroup.of b)) = g b := by
  refine ⟨(FreeGroup.lift g).comp e.toMonoidHom, ?_, ?_⟩
  · intro b
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, FreeGroup.lift_apply_of]
  · intro F hF
    have he : F.comp e.symm.toMonoidHom = FreeGroup.lift g := by
      apply FreeGroup.ext_hom
      intro b
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        FreeGroup.lift_apply_of] using hF b
    apply DFunLike.ext
    intro x
    have hx := DFunLike.congr_fun he (e x)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hx

/-- Arbitrary images of the two positive plane meridians extend uniquely
to a homomorphism from the actual fundamental group. -/
theorem twicePuncturedFundamentalGroup_presentation {G : Type*} [Group G] (g : Bool → G) :
    ∃! F : FundamentalGroup TwicePuncturedPlane meridianBasepoint →* G,
      ∀ b, F (meridianClass b) = g b := by
  simpa only [twicePuncturedFundamentalGroupFreeEquiv_symm_of] using
    freeGroup_marking_presentation twicePuncturedFundamentalGroupFreeEquiv g

/-- The corresponding genuine presentation for the normalized positive
meridians of the original regular quotient. -/
theorem triangleRegularFundamentalGroup_presentation {G : Type*} [Group G] (g : Bool → G) :
    ∃! F : FundamentalGroup TriangleRegularQuotient triangleRegularMeridianBasepoint →* G,
      ∀ b, F (triangleRegularMeridianClass b) = g b := by
  simpa only [triangleRegularFundamentalGroupFreeEquiv_symm_of] using
    freeGroup_marking_presentation triangleRegularFundamentalGroupFreeEquiv g

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
