import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopologyBasic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The middle band of the suspension

The quotient map is injective away from its two end slices.  Restriction to
the actual open middle band therefore gives a homeomorphism, not merely a
homotopy model.  Removing its contractible interval factor identifies the
band up to homotopy with the original space.
-/

noncomputable section

open Set Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspCentralHomology.Suspension

variable {X : Type*} [TopologicalSpace X]

/-- The actual overlap of the two suspension cones. -/
abbrev middleBand (X : Type*) :=
  (northOpen ∩ southOpen : Set (Suspension X))

/-- The cylinder over the open middle interval. -/
abbrev middleCylinder (X : Type*) :=
  (fun p : unitInterval × X => mk p.1 p.2) ⁻¹' middleBand X

theorem middleBand_isOpen : IsOpen (middleBand X) :=
  northOpen_isOpen.inter southOpen_isOpen

omit [TopologicalSpace X] in
private theorem middleCylinder_height (p : middleCylinder X) :
    (1 / 4 : ℝ) < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) < 3 / 4 :=
  ⟨p.2.2, p.2.1⟩

omit [TopologicalSpace X] in
/-- The restricted quotient is injective, because the band contains neither pole. -/
theorem middleBand_restrict_injective : Function.Injective
    ((middleBand X).restrictPreimage (fun p : unitInterval × X => mk p.1 p.2)) := by
  intro p q h
  have hmk : mk p.1.1 p.1.2 = mk q.1.1 q.1.2 := congrArg Subtype.val h
  obtain ⟨ht, hx⟩ := (mk_eq_mk_iff _ _ _ _).mp hmk
  have hp := middleCylinder_height p
  have hx' : p.1.2 = q.1.2 := by
    rcases hx with h0 | h1 | hx
    · have hz : (p.1.1 : ℝ) = 0 := congrArg Subtype.val h0
      linarith [hp.1]
    · have hz : (p.1.1 : ℝ) = 1 := congrArg Subtype.val h1
      linarith [hp.2]
    · exact hx
  exact Subtype.ext (Prod.ext ht hx')

/-- The actual cylinder band maps homeomorphically to the suspension overlap. -/
def middleBandQuotientHomeomorph : middleCylinder X ≃ₜ middleBand X :=
  ((isHomeomorph_iff_isQuotientMap_injective).mpr
    ⟨isQuotientMap_mk.restrictPreimage_isOpen middleBand_isOpen,
      middleBand_restrict_injective⟩).homeomorph _

@[simp] theorem middleBandQuotientHomeomorph_coe (p : middleCylinder X) :
    (middleBandQuotientHomeomorph p : Suspension X) = mk p.1.1 p.1.2 := rfl

/-- The cylinder band has the ordinary product coordinates given by real height and label. -/
def middleCylinderHomeomorph :
    middleCylinder X ≃ₜ (Ioo (1 / 4 : ℝ) (3 / 4) × X) where
  toFun p := (⟨p.1.1, middleCylinder_height p⟩, p.1.2)
  invFun p := ⟨(⟨p.1, by constructor <;> linarith [p.1.2.1, p.1.2.2]⟩, p.2),
    p.1.2.2, p.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    · exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_fst
    · exact continuous_snd

/-- The overlap of the two open cones is exactly an open interval times the suspended space. -/
def middleBandHomeomorph :
    middleBand X ≃ₜ (Ioo (1 / 4 : ℝ) (3 / 4) × X) :=
  middleBandQuotientHomeomorph.symm.trans middleCylinderHomeomorph

@[simp] theorem middleBandHomeomorph_symm_coe
    (p : Ioo (1 / 4 : ℝ) (3 / 4) × X) :
    (middleBandHomeomorph.symm p : Suspension X) =
      mk ⟨p.1, by constructor <;> linarith [p.1.2.1, p.1.2.2]⟩ p.2 := rfl

@[simp] theorem middleBandHomeomorph_height (p : middleBand X) :
    ((middleBandHomeomorph p).1 : ℝ) = (height p.1 : ℝ) := by
  obtain ⟨q, rfl⟩ := middleBandQuotientHomeomorph.surjective p
  change ((middleCylinderHomeomorph
    (middleBandQuotientHomeomorph.symm (middleBandQuotientHomeomorph q))).1 : ℝ) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

instance middleInterval_contractibleSpace :
    ContractibleSpace (Ioo (1 / 4 : ℝ) (3 / 4)) :=
  (convex_Ioo (1 / 4 : ℝ) (3 / 4)).contractibleSpace ⟨1 / 2, by norm_num⟩

/-- Dropping the contractible height interval is a genuine homotopy equivalence. -/
def middleBandHomotopyEquiv : middleBand X ≃ₕ X :=
  middleBandHomeomorph.toHomotopyEquiv.trans
    (((Classical.choice (ContractibleSpace.hequiv_unit
      (Ioo (1 / 4 : ℝ) (3 / 4)))).prodCongr (HomotopyEquiv.refl X)).trans
      (Homeomorph.uniqueProd Unit X).toHomotopyEquiv)

variable [Nonempty X]

omit [TopologicalSpace X] in
theorem middleBand_nonempty : (middleBand X).Nonempty := by
  refine ⟨mk ⟨1 / 2, by norm_num⟩ (Classical.choice ‹Nonempty X›), ?_⟩
  constructor <;> norm_num [northOpen, southOpen]

/-- Every suspension point can be joined to the height-zero pole by its vertical segment. -/
theorem joined_north (p : Suspension X) : Joined (north : Suspension X) p := by
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective p
  refine ⟨{
    toFun := fun s : unitInterval => mk (s * t) x
    continuous_toFun := by
      apply continuous_mk.comp (f := fun s : unitInterval => (s * t, x))
      apply Continuous.prodMk
      · apply Continuous.subtype_mk
        exact continuous_subtype_val.mul continuous_const
      · exact continuous_const
    source' := by simp
    target' := by simp }⟩

/-- Suspending any nonempty space makes it path-connected, even if the original space is not. -/
instance suspension_pathConnectedSpace : PathConnectedSpace (Suspension X) where
  nonempty := inferInstance
  joined p q := (joined_north p).symm.trans (joined_north q)

end Wikipedia.HopfProblem.CuspCentralHomology.Suspension
