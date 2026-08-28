import Wikipedia.HopfProblem.TrianglePeriodFamilyGeometry
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularElliptic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# The integral representation determined by actual lifted base loops

The monodromy of a left quotient covering naturally takes values in the
opposite deck group. Inversion gives a genuine homomorphism to the deck
group, and the proved dual lattice representation gives the actual
integral representation relevant to flat fibre transport.

The convention is explicit: a loop ending at `g • b` upstairs acts on the
fixed fibre marking by the dual representation of `g⁻¹`. The matrices
`A₁`, `A₂`, and `M₀` therefore correspond to loops whose specified lifts
end at the inverse generators. Projecting any such actual upstairs path
constructs a loop with precisely this lifted endpoint.
-/

noncomputable section

open Set Topology
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- Inverting the actual opposite-valued covering monodromy gives the
deck element acting on the original fibre marking. -/
def deckTransportHom (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →* TriangleGroup :=
  (MulEquiv.inv' TriangleGroup).symm.toMonoidHom.comp
    (hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩)

/-- The actual integral special-linear representation obtained from
lifted base loops and the constructed dual lattice representation. -/
def latticeTransportHom (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →* SL(4, ℤ) :=
  triangleDualRepresentation.comp (D.deckTransportHom hq b)

@[simp] theorem latticeTransportHom_apply (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.latticeTransportHom hq b γ = triangleDualRepresentation (D.deckTransportHom hq b γ) :=
  rfl

/-- The inverse of the assigned deck element is the actual endpoint
translation of the unique lifted loop. -/
theorem deckTransportHom_monodromy (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    (D.deckTransportHom hq b γ)⁻¹ • b =
      (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) := by
  change ((hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩ γ).unop⁻¹)⁻¹ • b = _
  rw [inv_inv]
  exact hq.unop_fundamentalGroupToMulOpposite_smul

theorem deckTransportHom_eq_of_inverse_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g⁻¹ • b) :
    D.deckTransportHom hq b γ = g := by
  let := hq.isCancelSMul
  apply inv_injective
  exact IsCancelSMul.right_cancel _ _ b ((D.deckTransportHom_monodromy hq b γ).trans hγ)

/-- Specifying the lifted endpoint determines the actual integral
monodromy, with its inverse convention exposed. -/
theorem latticeTransportHom_eq_of_inverse_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g⁻¹ • b) :
    D.latticeTransportHom hq b γ = triangleDualRepresentation g := by
  rw [latticeTransportHom_apply, D.deckTransportHom_eq_of_inverse_endpoint hq b γ g hγ]

theorem latticeTransportHom_eq_of_endpoint (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g • b) :
    D.latticeTransportHom hq b γ = triangleDualRepresentation g⁻¹ :=
  D.latticeTransportHom_eq_of_inverse_endpoint hq b γ g⁻¹ (by simpa only [inv_inv] using hγ)

/-- The first specified inverse-generator lift yields the source matrix. -/
theorem latticeTransportHom_generator₁ (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = triangleGenerator₁⁻¹ • b) :
    (D.latticeTransportHom hq b γ : LatticeMatrix) = A₁ := by
  rw [D.latticeTransportHom_eq_of_inverse_endpoint hq b γ triangleGenerator₁ hγ,
    triangleDualRepresentation_generator₁_matrix]

theorem latticeTransportHom_generator₂ (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = triangleGenerator₂⁻¹ • b) :
    (D.latticeTransportHom hq b γ : LatticeMatrix) = A₂ := by
  rw [D.latticeTransportHom_eq_of_inverse_endpoint hq b γ triangleGenerator₂ hγ,
    triangleDualRepresentation_generator₂_matrix]

theorem latticeTransportHom_cusp (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b))
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = triangleCuspGenerator⁻¹ • b) :
    (D.latticeTransportHom hq b γ : LatticeMatrix) = M₀ := by
  rw [D.latticeTransportHom_eq_of_inverse_endpoint hq b γ triangleCuspGenerator hγ,
    triangleDualRepresentation_cusp_matrix]

/-- Project an actual path to the inverse deck translate to an actual
based loop of the regular quotient. -/
def projectedLoop (b : B) (g : TriangleGroup) (δ : Path b (g⁻¹ • b)) :
    Path (D.baseQuotient b) (D.baseQuotient b) :=
  (δ.map hq.continuous).cast rfl (hq.map_smul g⁻¹).symm

@[simp] theorem projectedLoop_apply (b : B) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) (t : unitInterval) :
    D.projectedLoop hq b g δ t = D.baseQuotient (δ t) := rfl

/-- Unique path lifting verifies the endpoint of the projected actual
loop; it is not included as extra monodromy data. -/
theorem projectedLoop_monodromy (b : B) (g : TriangleGroup) (δ : Path b (g⁻¹ • b)) :
    hq.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (D.projectedLoop hq b g δ))
      ⟨b, rfl⟩ = ⟨g⁻¹ • b, hq.map_smul g⁻¹⟩ := by
  apply hq.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk δ)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

theorem latticeTransportHom_projectedLoop (b : B) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    D.latticeTransportHom hq b (Path.Homotopic.Quotient.mk (D.projectedLoop hq b g δ)) =
      triangleDualRepresentation g := by
  apply D.latticeTransportHom_eq_of_inverse_endpoint hq b _ g
  exact congrArg Subtype.val (D.projectedLoop_monodromy hq b g δ)

/-- When the actual covering domain is path connected, every deck
element is realized by an actual lifted loop. -/
theorem deckTransportHom_surjective [PathConnectedSpace B] (b : B) :
    Function.Surjective (D.deckTransportHom hq b) :=
  (MulEquiv.inv' TriangleGroup).symm.surjective.comp
    (hq.fundamentalGroupToMulOpposite_surjective ⟨b, rfl⟩)

/-- The image is exactly the prescribed dual-representation image, not
merely contained in it. The actual regular triangle domain is path connected. -/
theorem latticeTransportHom_range [PathConnectedSpace B] (b : B) :
    (D.latticeTransportHom hq b).range = triangleDualRepresentation.range := by
  ext A
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨D.deckTransportHom hq b γ, rfl⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨γ, hγ⟩ := D.deckTransportHom_surjective hq b g
    exact ⟨γ, congrArg triangleDualRepresentation hγ⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
