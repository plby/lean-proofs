import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportTopology
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportRepresentation

/-!
# Actual flat transport in the descended triangle period family

The existing varying-period family is topologically the real coordinate
torus over the actual covering base. The intrinsic diagonal-quotient
transport therefore gives homeomorphisms between the literal fibres of
its actual descended projection. Its horizontal paths are obtained by
unique covering lifts and constant real torus coordinates.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)
    {x y z : D.BaseSpace}

/-- Transport along a homotopy class of actual base paths, between the
literal fibres of the constructed family projection. -/
def transport (γ : Path.Homotopic.Quotient x y) :
    (D.projection ⁻¹' {x}) ≃ₜ (D.projection ⁻¹' {y}) := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.transport (F := RealTorus₄) hq γ

@[simp] theorem transport_refl (x : D.BaseSpace) :
    D.transport hq (Path.Homotopic.Quotient.refl x) = Homeomorph.refl _ := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.transport_refl hq x

theorem transport_trans (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) :
    D.transport hq (γ.trans δ) = (D.transport hq γ).trans (D.transport hq δ) := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.transport_trans hq γ δ

@[simp] theorem transport_symm (γ : Path.Homotopic.Quotient x y) :
    D.transport hq γ.symm = (D.transport hq γ).symm := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.transport_symm hq γ

/-- Equal actual lifted endpoints give the same fibre homeomorphism,
even if the corresponding homotopy classes differ in the covering kernel. -/
theorem transport_eq_of_lift_endpoint_eq {γ δ : Path.Homotopic.Quotient x y}
    (b : D.baseQuotient ⁻¹' {x})
    (he : hq.isCoveringMap.monodromy γ b = hq.isCoveringMap.monodromy δ b) :
    D.transport hq γ = D.transport hq δ := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  change DiagonalQuotient.transport hq γ = DiagonalQuotient.transport (F := RealTorus₄) hq δ
  rw [DiagonalQuotient.transport_eq_transportFromLift hq γ b,
    DiagonalQuotient.transport_eq_transportFromLift hq δ b]
  exact congrArg (fun e : D.baseQuotient ⁻¹' {y} =>
    (DiagonalQuotient.fibreMarking (F := RealTorus₄) hq b).symm.trans
      (DiagonalQuotient.fibreMarking hq e)) he

/-- The actual endpoint uses the unique lifted base path and the original
unchanged real-torus coordinate. -/
theorem transport_apply_quotient (γ : Path.Homotopic.Quotient x y)
    (b : B) (hb : D.baseQuotient b = x) (f : RealTorus₄) :
    (D.transport hq γ ⟨D.quotient (b, f), hb⟩ : D.Space) =
      D.quotient ((hq.isCoveringMap.monodromy γ ⟨b, hb⟩ : B), f) := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact DiagonalQuotient.transport_apply_quotient hq γ b hb f

/-- Transport of actual paths factors through their relative homotopy
classes, rather than through a supplied local-system action. -/
def pathTransport (γ : Path x y) :
    (D.projection ⁻¹' {x}) ≃ₜ (D.projection ⁻¹' {y}) :=
  D.transport hq (Path.Homotopic.Quotient.mk γ)

theorem pathTransport_eq_of_homotopic {γ δ : Path x y} (h : γ.Homotopic δ) :
    D.pathTransport hq γ = D.pathTransport hq δ :=
  congrArg (D.transport hq) (Path.Homotopic.Quotient.eq.mpr h)

@[simp] theorem pathTransport_refl (x : D.BaseSpace) :
    D.pathTransport hq (Path.refl x) = Homeomorph.refl _ :=
  D.transport_refl hq x

theorem pathTransport_trans (γ : Path x y) (δ : Path y z) :
    D.pathTransport hq (γ.trans δ) =
      (D.pathTransport hq γ).trans (D.pathTransport hq δ) :=
  D.transport_trans hq (Path.Homotopic.Quotient.mk γ) (Path.Homotopic.Quotient.mk δ)

@[simp] theorem pathTransport_symm (γ : Path x y) :
    D.pathTransport hq γ.symm = (D.pathTransport hq γ).symm :=
  D.transport_symm hq (Path.Homotopic.Quotient.mk γ)

/-- The genuine path in the total family associated to a base path and
constant real-torus coordinate in its unique covering lift. -/
def horizontalPath (γ : Path x y) (b : B) (hb : D.baseQuotient b = x) (f : RealTorus₄) :
    Path (D.quotient (b, f))
      (D.quotient
        ((hq.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk γ) ⟨b, hb⟩ : B), f)) := by
  let := triangleTorusAction
  exact DiagonalQuotient.horizontalPath hq γ b hb f

@[simp] theorem horizontalPath_apply (γ : Path x y) (b : B)
    (hb : D.baseQuotient b = x) (f : RealTorus₄) (t : unitInterval) :
    D.horizontalPath hq γ b hb f t =
      D.quotient (hq.isCoveringMap.liftPath γ b (γ.source.trans hb.symm) t, f) := rfl

@[simp] theorem projection_horizontalPath (γ : Path x y) (b : B)
    (hb : D.baseQuotient b = x) (f : RealTorus₄) (t : unitInterval) :
    D.projection (D.horizontalPath hq γ b hb f t) = γ t := by
  let := triangleTorusAction
  exact DiagonalQuotient.projection_horizontalPath hq γ b hb f t

@[simp] theorem horizontalPath_source (γ : Path x y) (b : B)
    (hb : D.baseQuotient b = x) (f : RealTorus₄) :
    D.horizontalPath hq γ b hb f 0 = D.quotient (b, f) :=
  (D.horizontalPath hq γ b hb f).source

/-- The constructed fibre transport is literally the endpoint of the
actual horizontal path, not merely an isomorphic auxiliary map. -/
theorem horizontalPath_target_transport (γ : Path x y) (b : B)
    (hb : D.baseQuotient b = x) (f : RealTorus₄) :
    D.horizontalPath hq γ b hb f 1 =
      (D.pathTransport hq γ ⟨D.quotient (b, f), hb⟩ : D.Space) := by
  rw [(D.horizontalPath hq γ b hb f).target]
  exact (D.transport_apply_quotient hq (Path.Homotopic.Quotient.mk γ) b hb f).symm

/-- In a fixed initial marking, the inverse endpoint deck element acts
on the coordinate torus. -/
theorem transport_loop_apply_quotient (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (f : RealTorus₄) :
    (D.transport hq γ ⟨D.quotient (b, f), rfl⟩ : D.Space) =
      D.quotient (b, triangleTorusHomeomorph (D.deckTransportHom hq b γ) f) := by
  rw [D.transport_apply_quotient hq γ b rfl f,
    ← D.deckTransportHom_monodromy hq b γ]
  let := triangleTorusAction
  exact (DiagonalQuotient.quotient_smul_fst
    ((D.deckTransportHom hq b γ)⁻¹) b f).trans (by simp only [inv_inv]; rfl)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
