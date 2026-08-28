import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSuspendedFrameCoordinates
import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist

/-!
# Removing both actual suspended Hopf coordinate changes together

Keep the outer radial coordinate and split the original sixteen finite
coordinates into the two original suspension blocks. Apply the proved
radial/chart equivalence in each block. Scaling both finite chart parameters
to zero gives an injective homotopy to a fixed ambient coordinate change.
Consequently contraction of the transported frame implies contraction of
the original finite frame, without assuming that an arbitrary varying
coordinate field extends over the disk.
-/

noncomputable section

open unitInterval
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfPairedFrameCoordinates

open NoExoticSixSphere QuaternionicHopf Stiefel
open QuaternionicHopfSuspendedFrameCoordinates
open FiniteSphereProductCharts hiding V

def axes : V 17 ≃L[ℝ] ℝ × (V 8 × V 8) :=
  (EuclideanTailCoordinates.split 16).toContinuousLinearEquiv.trans
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V 16)).trans
      ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (sumCoordinates 8).symm))

theorem axes_apply (w : V 17) : axes w =
    ((EuclideanTailCoordinates.split 16 w).fst,
      (sumCoordinates 8).symm (EuclideanTailCoordinates.split 16 w).snd) := rfl

attribute [local irreducible] axes ambientCoordinates ambientOperator

def coordinates (u v : V 7) : V 17 ≃L[ℝ] V 17 :=
  axes.trans (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
    ((ambientCoordinates u).prodCongr (ambientCoordinates v))).trans axes.symm)

def operator (u v : V 7) : V 17 →L[ℝ] V 17 :=
  axes.symm.toContinuousLinearMap.comp
    (((ContinuousLinearMap.id ℝ ℝ).prodMap
      ((ambientOperator u).prodMap (ambientOperator v))).comp axes.toContinuousLinearMap)

theorem operator_apply (u v : V 7) (w : V 17) : operator u v w =
    axes.symm ((axes w).1,
      (ambientOperator u (axes w).2.1, ambientOperator v (axes w).2.2)) := by
  simp only [operator, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply]

theorem coordinates_apply (u v : V 7) (w : V 17) : coordinates u v w =
    axes.symm ((axes w).1,
      (ambientCoordinates u (axes w).2.1, ambientCoordinates v (axes w).2.2)) := by
  simp only [coordinates, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, ContinuousLinearEquiv.refl_apply]

theorem coordinates_eq_operator (u v : V 7) :
    (coordinates u v : V 17 → V 17) = operator u v := by
  funext w
  rw [coordinates_apply, operator_apply, ambientOperator_apply, ambientOperator_apply]

theorem operator_injective (u v : V 7) : Function.Injective (operator u v) := by
  rw [← coordinates_eq_operator]
  exact (coordinates u v).injective

theorem axes_operator (u v : V 7) (w : V 17) : axes (operator u v w) =
    ((axes w).1, (ambientCoordinates u (axes w).2.1, ambientCoordinates v (axes w).2.2)) := by
  rw [operator_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [ambientOperator_apply, ambientOperator_apply]

theorem continuous_operator {X : Type*} [TopologicalSpace X]
    (u v : X → V 7) (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x ↦ operator (u x) (v x)) := by
  apply continuous_clm_apply.mpr
  intro w
  simp_rw [operator_apply]
  have hU := contDiff_ambientOperator.continuous.comp hu
  have hV := contDiff_ambientOperator.continuous.comp hv
  exact axes.symm.continuous.comp (continuous_const.prodMk
    ((hU.clm_apply continuous_const).prodMk (hV.clm_apply continuous_const)))

attribute [local irreducible] coordinates operator

variable {X : Type*} [TopologicalSpace X] {k : ℕ}

def transport (u v : C(X, V 7)) (A : C(X, Monomorphism.Space 17 k)) :
    C(X, Monomorphism.Space 17 k) where
  toFun x := ⟨(operator (u x) (v x)).comp (A x).val,
    (operator_injective (u x) (v x)).comp (A x).property⟩
  continuous_toFun := ((continuous_operator u v u.continuous v.continuous).clm_comp
    (continuous_subtype_val.comp A.continuous)).subtype_mk _

def contraction (u v : C(X, V 7)) (A : C(X, Monomorphism.Space 17 k)) :
    (transport u v A).Homotopy
      (transport (ContinuousMap.const X 0) (ContinuousMap.const X 0) A) where
  toFun p := ⟨(operator ((1 - (p.1 : ℝ)) • u p.2) ((1 - (p.1 : ℝ)) • v p.2)).comp
    (A p.2).val, (operator_injective _ _).comp (A p.2).property⟩
  continuous_toFun := by
    have ht : Continuous (fun p : I × X ↦ 1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    exact ((continuous_operator _ _ (ht.smul (u.continuous.comp continuous_snd))
      (ht.smul (v.continuous.comp continuous_snd))).clm_comp
        (continuous_subtype_val.comp (A.continuous.comp continuous_snd))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change (operator ((1 - (0 : ℝ)) • u x) ((1 - (0 : ℝ)) • v x)).comp (A x).val = _
    rw [sub_zero, one_smul, one_smul]
    rfl
  map_one_left x := by
    apply Subtype.ext
    change (operator ((1 - (1 : ℝ)) • u x) ((1 - (1 : ℝ)) • v x)).comp (A x).val = _
    rw [sub_self, zero_smul, zero_smul]
    rfl

def fixedChange : C(Monomorphism.Space 17 k, Monomorphism.Space 17 k) :=
  ⟨Monomorphism.recoordinate (coordinates 0 0) (ContinuousLinearEquiv.refl ℝ (V k)),
    Monomorphism.continuous_recoordinate _ _⟩

theorem transport_zero_eq (A : C(X, Monomorphism.Space 17 k)) :
    transport (ContinuousMap.const X 0) (ContinuousMap.const X 0) A = fixedChange.comp A := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  exact congrFun (coordinates_eq_operator 0 0) ((A x).val w) |>.symm

theorem homotopic_fixed (u v : C(X, V 7)) (A : C(X, Monomorphism.Space 17 k)) :
    (transport u v A).Homotopic (fixedChange.comp A) := by
  rw [← transport_zero_eq]
  exact ⟨contraction u v A⟩

theorem exists_contraction_of_transport (u v : C(X, V 7))
    (A : C(X, Monomorphism.Space 17 k)) (c : Monomorphism.Space 17 k)
    (h : (transport u v A).Homotopic (ContinuousMap.const X c)) :
    ∃ a, A.Homotopic (ContinuousMap.const X a) := by
  let K : C(Monomorphism.Space 17 k, Monomorphism.Space 17 k) :=
    (Monomorphism.recoordinateHomeomorph (coordinates 0 0).symm
      (ContinuousLinearEquiv.refl ℝ (V k)) : C(_, _))
  have hi : K.comp (fixedChange.comp A) = A := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    change (coordinates 0 0).symm (coordinates 0 0 ((A x).val w)) = (A x).val w
    exact (coordinates 0 0).symm_apply_apply _
  have hh : (fixedChange.comp A).Homotopic (ContinuousMap.const X c) :=
    (homotopic_fixed u v A).symm.trans h
  have hk := (ContinuousMap.Homotopic.refl K).comp hh
  rw [hi, ContinuousMap.comp_const] at hk
  exact ⟨K c, hk⟩

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfPairedFrameCoordinates
