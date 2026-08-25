import StackExchange.Puzzling139335.CentralRotation.CrosscutPaths.Data
import StackExchange.Puzzling139335.CentralRotation.CrosscutPaths.CircleEmbedding
import StackExchange.Puzzling139335.CentralRotation.CrosscutPaths.HalfImages
import StackExchange.Puzzling139335.CentralRotation.BoundaryCoordinates

/-!
# Circle parametrizations of the boundaries of a Jordan crosscut

The three circle embeddings have exactly the traces of the three compatible
half-speed path loops.  Their parametrizations are not chosen independently:
the crosscut is traversed by the same path in opposite directions.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335.CentralRotation.CrosscutPaths.Data

variable {C Γ M N : Set Plane} {p q : Plane} (d : Data C Γ M N p q)

/-- Circle parametrization of the first side, using the first outer arc and
then the crosscut. -/
noncomputable def fA : AddCircle (1 : ℝ) → Plane := loopCircle d.loopA.extend

/-- Circle parametrization of the second side, using the reversed crosscut
and then the second outer arc. -/
noncomputable def fB : AddCircle (1 : ℝ) → Plane := loopCircle d.loopB.extend

/-- Circle parametrization of the whole boundary from its two outer arcs. -/
noncomputable def fU : AddCircle (1 : ℝ) → Plane := loopCircle d.loopU.extend

theorem fA_continuous : Continuous d.fA := loopCircle_continuous d.loopA_extends_isLoop

theorem fB_continuous : Continuous d.fB := loopCircle_continuous d.loopB_extends_isLoop

theorem fU_continuous : Continuous d.fU := loopCircle_continuous d.loopU_extends_isLoop

theorem fA_injective : Function.Injective d.fA := loopCircle_injective d.loopA_extends_isLoop

theorem fB_injective : Function.Injective d.fB := loopCircle_injective d.loopB_extends_isLoop

theorem fU_injective : Function.Injective d.fU := loopCircle_injective d.loopU_extends_isLoop

@[simp] theorem fA_coe (t : I) : d.fA (t : ℝ) = (d.m.trans d.gamma) t := by
  exact (loopCircle_coe d.loopA_extends_isLoop t.property).trans
    (Path.extend_extends' d.loopA t)

@[simp] theorem fB_coe (t : I) : d.fB (t : ℝ) = (d.gamma.symm.trans d.n) t := by
  exact (loopCircle_coe d.loopB_extends_isLoop t.property).trans
    (Path.extend_extends' d.loopB t)

@[simp] theorem fU_coe (t : I) : d.fU (t : ℝ) = (d.m.trans d.n) t := by
  exact (loopCircle_coe d.loopU_extends_isLoop t.property).trans
    (Path.extend_extends' d.loopU t)

theorem range_fA : range d.fA = M ∪ Γ := by
  change range (loopCircle d.loopA.extend) = M ∪ Γ
  rw [range_loopCircle d.loopA_extends_isLoop]
  exact (d.loopA.image_extend_of_subset subset_rfl).trans d.range_loopA

theorem range_fB : range d.fB = Γ ∪ N := by
  change range (loopCircle d.loopB.extend) = Γ ∪ N
  rw [range_loopCircle d.loopB_extends_isLoop]
  exact (d.loopB.image_extend_of_subset subset_rfl).trans d.range_loopB

theorem range_fU : range d.fU = C := by
  change range (loopCircle d.loopU.extend) = C
  rw [range_loopCircle d.loopU_extends_isLoop]
  exact (d.loopU.image_extend_of_subset subset_rfl).trans d.range_loopU

/-- The common crosscut is traversed in opposite directions in the two side
circle parametrizations, with the exact real parameter change `t ↦ 1 - t`. -/
theorem fA_eq_fB_on_crosscut {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    d.fA (t : AddCircle (1 : ℝ)) = d.fB ((1 - t : ℝ) : AddCircle (1 : ℝ)) := by
  have htI : t ∈ I := ⟨by linarith [ht.1], ht.2⟩
  have ht'I : 1 - t ∈ I := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  change loopCircle d.loopA.extend (t : AddCircle (1 : ℝ)) =
    loopCircle d.loopB.extend ((1 - t : ℝ) : AddCircle (1 : ℝ))
  rw [loopCircle_coe d.loopA_extends_isLoop htI,
    loopCircle_coe d.loopB_extends_isLoop ht'I]
  change (d.m.trans d.gamma).extend t = (d.gamma.symm.trans d.n).extend (1 - t)
  rw [Path.extend_trans_of_half_le d.m d.gamma ht.1,
    Path.extend_trans_of_le_half d.gamma.symm d.n (by linarith [ht.1]),
    Path.extend_symm_apply]
  congr 1
  ring

theorem fA_eq_fU_on_outer {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 2)) :
    d.fA (t : AddCircle (1 : ℝ)) = d.fU (t : AddCircle (1 : ℝ)) := by
  have htI : t ∈ I := ⟨ht.1, by linarith [ht.2]⟩
  change loopCircle d.loopA.extend (t : AddCircle (1 : ℝ)) =
    loopCircle d.loopU.extend (t : AddCircle (1 : ℝ))
  rw [loopCircle_coe d.loopA_extends_isLoop htI,
    loopCircle_coe d.loopU_extends_isLoop htI]
  change (d.m.trans d.gamma).extend t = (d.m.trans d.n).extend t
  rw [Path.extend_trans_of_le_half d.m d.gamma ht.2,
    Path.extend_trans_of_le_half d.m d.n ht.2]

theorem fB_eq_fU_on_outer {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    d.fB (t : AddCircle (1 : ℝ)) = d.fU (t : AddCircle (1 : ℝ)) := by
  have htI : t ∈ I := ⟨by linarith [ht.1], ht.2⟩
  change loopCircle d.loopB.extend (t : AddCircle (1 : ℝ)) =
    loopCircle d.loopU.extend (t : AddCircle (1 : ℝ))
  rw [loopCircle_coe d.loopB_extends_isLoop htI,
    loopCircle_coe d.loopU_extends_isLoop htI]
  change (d.gamma.symm.trans d.n).extend t = (d.m.trans d.n).extend t
  rw [Path.extend_trans_of_half_le d.gamma.symm d.n ht.1,
    Path.extend_trans_of_half_le d.m d.n ht.1]

theorem fA_lowerHalf_image : circleParam d.fA '' Icc (0 : ℝ) (1 / 2) = M := by
  have htrace : EqOn (circleParam d.fA) (⇑d.loopA.extend) (Icc (0 : ℝ) (1 / 2)) := by
    intro t ht
    exact loopCircle_coe d.loopA_extends_isLoop ⟨ht.1, by linarith [ht.2]⟩
  rw [htrace.image_eq]
  exact (path_trans_extend_image_lowerHalf d.m d.gamma).trans d.range_m

theorem fA_upperHalf_image : circleParam d.fA '' Icc (1 / 2 : ℝ) 1 = Γ := by
  have htrace : EqOn (circleParam d.fA) (⇑d.loopA.extend) (Icc (1 / 2 : ℝ) 1) := by
    intro t ht
    exact loopCircle_coe d.loopA_extends_isLoop ⟨by linarith [ht.1], ht.2⟩
  rw [htrace.image_eq]
  exact (path_trans_extend_image_upperHalf d.m d.gamma).trans d.range_gamma

theorem fB_upperHalf_image : circleParam d.fB '' Icc (1 / 2 : ℝ) 1 = N := by
  have htrace : EqOn (circleParam d.fB) (⇑d.loopB.extend) (Icc (1 / 2 : ℝ) 1) := by
    intro t ht
    exact loopCircle_coe d.loopB_extends_isLoop ⟨by linarith [ht.1], ht.2⟩
  rw [htrace.image_eq]
  exact (path_trans_extend_image_upperHalf d.gamma.symm d.n).trans d.range_n

/-- The constructed path data supplies all compatible boundary coordinates;
no orientation assumption is introduced by this conversion. -/
noncomputable def boundaryCoordinates : BoundaryCoordinates M Γ N where
  leftParam := d.fA
  rightParam := d.fB
  outerParam := d.fU
  leftContinuous := d.fA_continuous
  rightContinuous := d.fB_continuous
  outerContinuous := d.fU_continuous
  leftInjective := d.fA_injective
  rightInjective := d.fB_injective
  outerInjective := d.fU_injective
  leftOuterImage := d.fA_lowerHalf_image
  leftCutImage := d.fA_upperHalf_image
  rightOuterImage := d.fB_upperHalf_image
  outerLeftAgree := fun _ ht => d.fA_eq_fU_on_outer ht
  outerRightAgree := fun _ ht => d.fB_eq_fU_on_outer ht
  cutAgree := fun _ ht => d.fA_eq_fB_on_crosscut ht

end Puzzling139335.CentralRotation.CrosscutPaths.Data

namespace Puzzling139335.JordanCrosscut

/-- Compatible boundary coordinates exist for every actual Jordan crosscut. -/
theorem exists_boundaryCoordinates {C Γ M N : Set Plane} {p q : Plane}
    (h : JordanCrosscut C Γ p q) (hc : IsCutPair C p q M N) :
    Nonempty (CentralRotation.BoundaryCoordinates M Γ N) := by
  obtain ⟨d⟩ := h.exists_crosscutPaths hc
  exact ⟨d.boundaryCoordinates⟩

end Puzzling139335.JordanCrosscut
