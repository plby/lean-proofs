import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfPairedFiniteOperators

/-!
# Contracting both exact finite Hopf factor operators

Place the balanced quaternionic contraction in either retained ambient
block, with the outer radial coordinate and other block fixed. It carries
the actual reference operator to the computed factor operator. Every
intermediate operator remains injective. The paired chart homotopy then
reflects these contractions back to the original finite operators.
-/

noncomputable section

open Function unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFactorContraction

open NoExoticSixSphere QuaternionicHopf Stiefel
open QuaternionicHopfFiniteBalancedFrame QuaternionicHopfPairedFrameCoordinates
open QuaternionicHopfPairedFiniteOperators

def blockOperator (B C : V 8 →L[ℝ] V 8) : V 17 →L[ℝ] V 17 :=
  axes.symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℝ ℝ).prodMap (B.prodMap C)).comp axes.toContinuousLinearMap)

theorem blockOperator_apply (B C : V 8 →L[ℝ] V 8) (v : V 17) :
    blockOperator B C v = axes.symm ((axes v).1, (B (axes v).2.1, C (axes v).2.2)) := by
  simp only [blockOperator, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply]

theorem axes_blockOperator (B C : V 8 →L[ℝ] V 8) (v : V 17) :
    axes (blockOperator B C v) = ((axes v).1, (B (axes v).2.1, C (axes v).2.2)) := by
  rw [blockOperator_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem blockOperator_injective (B C : V 8 →L[ℝ] V 8)
    (hB : Injective B) (hC : Injective C) : Injective (blockOperator B C) := by
  intro v w h
  have he := congrArg axes h
  rw [axes_blockOperator, axes_blockOperator] at he
  have hfirst := congrArg Prod.fst he
  apply axes.injective
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact hfirst
  · exact hB (congrArg (fun p : ℝ × (V 8 × V 8) ↦ p.2.1) he)
  · exact hC (congrArg (fun p : ℝ × (V 8 × V 8) ↦ p.2.2) he)

theorem continuous_blockOperator {X : Type*} [TopologicalSpace X]
    (B C : X → V 8 →L[ℝ] V 8) (hB : Continuous B) (hC : Continuous C) :
    Continuous (fun x ↦ blockOperator (B x) (C x)) := by
  apply continuous_clm_apply.mpr
  intro v
  simp_rw [blockOperator_apply]
  exact axes.symm.continuous.comp (continuous_const.prodMk
    ((hB.clm_apply continuous_const).prodMk (hC.clm_apply continuous_const)))

theorem blockOperator_id (v : V 17) :
    blockOperator (ContinuousLinearMap.id ℝ (V 8)) (ContinuousLinearMap.id ℝ (V 8)) v = v := by
  apply axes.injective
  rw [axes_blockOperator]
  rfl

theorem balanced_left_zero (a : Sphere 16) (r q : Sphere 3) (v : V 14) :
    blockOperator (balancedFrameContraction (0, q)) (ContinuousLinearMap.id ℝ (V 8))
      ((leftTransport a r reference).val v) = (leftTransport a r q).val v := by
  apply axes.injective
  rw [axes_blockOperator, leftTransport_axes, leftTransport_axes]
  dsimp only [Prod.fst, Prod.snd, ContinuousLinearMap.id_apply]
  rw [map_add, balanced_normal, balanced_tangent]

theorem balanced_right_zero (a : Sphere 16) (q r : Sphere 3) (v : V 14) :
    blockOperator (ContinuousLinearMap.id ℝ (V 8)) (balancedFrameContraction (0, r))
      ((rightTransport a q reference).val v) = (rightTransport a q r).val v := by
  apply axes.injective
  rw [axes_blockOperator, rightTransport_axes, rightTransport_axes]
  dsimp only [Prod.fst, Prod.snd, ContinuousLinearMap.id_apply]
  rw [map_add, balanced_normal, balanced_tangent]

theorem balanced_left_one (q : Sphere 3) (v : V 17) :
    blockOperator (balancedFrameContraction (1, q)) (ContinuousLinearMap.id ℝ (V 8)) v = v := by
  have h : balancedFrameContraction (1, q) = ContinuousLinearMap.id ℝ (V 8) :=
    ContinuousLinearMap.ext (balancedFrameContraction_one q)
  rw [h]
  exact blockOperator_id v

theorem balanced_right_one (q : Sphere 3) (v : V 17) :
    blockOperator (ContinuousLinearMap.id ℝ (V 8)) (balancedFrameContraction (1, q)) v = v := by
  have h : balancedFrameContraction (1, q) = ContinuousLinearMap.id ℝ (V 8) :=
    ContinuousLinearMap.ext (balancedFrameContraction_one q)
  rw [h]
  exact blockOperator_id v

def leftContraction (a : Sphere 16) (r : Sphere 3) : (leftTransport a r).Homotopy
    (ContinuousMap.const _ (leftTransport a r reference)) where
  toFun p := ⟨(blockOperator (balancedFrameContraction p) (ContinuousLinearMap.id ℝ (V 8))).comp
    (leftTransport a r reference).val,
      (blockOperator_injective _ _ (balancedFrameContraction_injective p) injective_id).comp
        (leftTransport a r reference).property⟩
  continuous_toFun := by
    have h := continuous_blockOperator balancedFrameContraction
      (fun _ ↦ ContinuousLinearMap.id ℝ (V 8)) continuous_balancedFrameContraction continuous_const
    exact (h.clm_comp continuous_const).subtype_mk _
  map_zero_left q := Subtype.ext (ContinuousLinearMap.ext (balanced_left_zero a r q))
  map_one_left q := Subtype.ext (ContinuousLinearMap.ext (fun v ↦
    balanced_left_one q ((leftTransport a r reference).val v)))

def rightContraction (a : Sphere 16) (q : Sphere 3) : (rightTransport a q).Homotopy
    (ContinuousMap.const _ (rightTransport a q reference)) where
  toFun p := ⟨(blockOperator (ContinuousLinearMap.id ℝ (V 8)) (balancedFrameContraction p)).comp
    (rightTransport a q reference).val,
      (blockOperator_injective _ _ injective_id (balancedFrameContraction_injective p)).comp
        (rightTransport a q reference).property⟩
  continuous_toFun := by
    have h := continuous_blockOperator (fun _ ↦ ContinuousLinearMap.id ℝ (V 8))
      balancedFrameContraction continuous_const continuous_balancedFrameContraction
    exact (h.clm_comp continuous_const).subtype_mk _
  map_zero_left r := Subtype.ext (ContinuousLinearMap.ext (balanced_right_zero a q r))
  map_one_left r := Subtype.ext (ContinuousLinearMap.ext (fun v ↦
    balanced_right_one r ((rightTransport a q reference).val v)))

theorem leftMap_contracts (a : Sphere 16) (r : Sphere 3) :
    ∃ b, (leftMap a r).Homotopic (ContinuousMap.const _ b) :=
  exists_contraction_of_transport finiteChartMap (ContinuousMap.const _ (finiteChartMap r))
    (leftMap a r) (leftTransport a r reference) ⟨leftContraction a r⟩

theorem rightMap_contracts (a : Sphere 16) (q : Sphere 3) :
    ∃ b, (rightMap a q).Homotopic (ContinuousMap.const _ b) :=
  exists_contraction_of_transport (ContinuousMap.const _ (finiteChartMap q)) finiteChartMap
    (rightMap a q) (rightTransport a q reference) ⟨rightContraction a q⟩

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFactorContraction
