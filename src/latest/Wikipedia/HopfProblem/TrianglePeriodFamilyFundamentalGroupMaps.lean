import Wikipedia.HopfProblem.TrianglePeriodFamilyTopology
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Actual fundamental-group maps of a diagonal quotient family

The fibre inclusion, projection, and fixed-point section are literal
continuous maps between the previously constructed spaces. Their
fundamental-group maps preserve the specified basepoints. The section
splits the projection, and every fibre loop projects to the constant
loop. Covering monodromy supplies the inverse-deck transport convention.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F]

/-- A fixed point of the fibre action defines an actual quotient section. -/
def zeroSection (c : F) (hc : ∀ g : G, g • c = c) : BaseSpace G B → Space G B F :=
  Quotient.lift (fun b : B => quotient G B F (b, c)) (by
    rintro b b' ⟨g, hg⟩
    exact (quotient_eq_iff G B F _ _).mpr ⟨g, Prod.ext hg (hc g)⟩)

omit [TopologicalSpace B] [TopologicalSpace F] in
@[simp] theorem zeroSection_baseQuotient (c : F) (hc : ∀ g : G, g • c = c) (b : B) :
    zeroSection c hc (baseQuotient G B b) = fibreInclusion G B F b c := rfl

theorem zeroSection_continuous (c : F) (hc : ∀ g : G, g • c = c) :
    Continuous (zeroSection (B := B) c hc) :=
  isQuotientMap_quotient_mk'.continuous_iff.mpr
    ((quotient_continuous G B F).comp (continuous_id.prodMk continuous_const))

omit [TopologicalSpace B] [TopologicalSpace F] in
@[simp] theorem projection_zeroSection (c : F) (hc : ∀ g : G, g • c = c)
    (x : BaseSpace G B) : projection G B F (zeroSection c hc x) = x := by
  induction x using Quotient.inductionOn with
  | h b => rfl

/-- The actual homomorphism induced by inclusion of the fibre over `b`. -/
def fibreFundamentalGroupHom (b : B) (c : F) :
    FundamentalGroup F c →*
      FundamentalGroup (Space G B F) (fibreInclusion G B F b c) :=
  FundamentalGroup.map ⟨fibreInclusion G B F b, fibreInclusion_continuous G B F b⟩ c

/-- The actual homomorphism induced by the descended projection. -/
def projectionFundamentalGroupHom (b : B) (c : F) :
    FundamentalGroup (Space G B F) (fibreInclusion G B F b c) →*
      FundamentalGroup (BaseSpace G B) (baseQuotient G B b) :=
  FundamentalGroup.map ⟨projection G B F, projection_continuous G B F⟩
    (fibreInclusion G B F b c)

/-- The actual homomorphism induced by the fixed-point section. -/
def sectionFundamentalGroupHom (c : F) (hc : ∀ g : G, g • c = c) (b : B) :
    FundamentalGroup (BaseSpace G B) (baseQuotient G B b) →*
      FundamentalGroup (Space G B F) (fibreInclusion G B F b c) :=
  FundamentalGroup.map ⟨zeroSection c hc, zeroSection_continuous c hc⟩
    (baseQuotient G B b)

/-- The section splits the actual projection on fundamental groups. -/
theorem projectionFundamentalGroupHom_comp_section
    (c : F) (hc : ∀ g : G, g • c = c) (b : B) :
    (projectionFundamentalGroupHom (G := G) b c).comp (sectionFundamentalGroupHom c hc b) =
      MonoidHom.id (FundamentalGroup (BaseSpace G B) (baseQuotient G B b)) := by
  apply DFunLike.ext
  intro γ
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
      change Path.Homotopic.Quotient.mk
        ((γ.map (zeroSection_continuous c hc)).map (projection_continuous G B F)) =
          Path.Homotopic.Quotient.mk γ
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      exact projection_zeroSection c hc (γ t)

theorem sectionFundamentalGroupHom_injective
    (c : F) (hc : ∀ g : G, g • c = c) (b : B) :
    Function.Injective (sectionFundamentalGroupHom c hc b) := by
  apply Function.LeftInverse.injective (g := projectionFundamentalGroupHom (G := G) b c)
  intro γ
  exact DFunLike.congr_fun (projectionFundamentalGroupHom_comp_section c hc b) γ

theorem projectionFundamentalGroupHom_surjective
    (c : F) (hc : ∀ g : G, g • c = c) (b : B) :
    Function.Surjective (projectionFundamentalGroupHom (G := G) b c) := by
  intro γ
  exact ⟨sectionFundamentalGroupHom c hc b γ,
    DFunLike.congr_fun (projectionFundamentalGroupHom_comp_section c hc b) γ⟩

/-- A loop in a fixed fibre has constant projected loop. -/
@[simp] theorem projectionFundamentalGroupHom_fibre (b : B) (c : F)
    (γ : FundamentalGroup F c) :
    projectionFundamentalGroupHom (G := G) b c (fibreFundamentalGroupHom b c γ) = 1 := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
      change Path.Homotopic.Quotient.mk
        ((γ.map (fibreInclusion_continuous G B F b)).map
          (projection_continuous G B F)) =
        Path.Homotopic.Quotient.mk (Path.refl (baseQuotient G B b))
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      rfl

theorem fibreFundamentalGroupHom_range_le_ker (b : B) (c : F) :
    (fibreFundamentalGroupHom (G := G) b c).range ≤
      (projectionFundamentalGroupHom (G := G) b c).ker := by
  rintro γ ⟨δ, rfl⟩
  exact projectionFundamentalGroupHom_fibre b c δ

variable (hq : IsQuotientCoveringMap (baseQuotient G B) G)

/-- Inverse deck monodromy, with the same convention as actual flat transport. -/
def deckTransportHom (b : B) :
    FundamentalGroup (BaseSpace G B) (baseQuotient G B b) →* G :=
  (MulEquiv.inv' G).symm.toMonoidHom.comp (hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩)

theorem deckTransportHom_monodromy (b : B)
    (γ : FundamentalGroup (BaseSpace G B) (baseQuotient G B b)) :
    (deckTransportHom hq b γ)⁻¹ • b =
      (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) := by
  change ((hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩ γ).unop⁻¹)⁻¹ • b = _
  rw [inv_inv]
  exact hq.unop_fundamentalGroupToMulOpposite_smul

variable [ContinuousConstSMul G F]

/-- The actual fibre map induced by one group element, preserving the fixed point. -/
def fibreActionFundamentalGroupHom (c : F) (hc : ∀ g : G, g • c = c) (g : G) :
    FundamentalGroup F c →* FundamentalGroup F c :=
  FundamentalGroup.mapOfEq ⟨fun x : F => g • x, continuous_const_smul g⟩ (hc g)

end Wikipedia.HopfProblem.DiagonalQuotient
