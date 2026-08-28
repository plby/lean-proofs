import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order

/-!
# The determinant-sign cover of a real vector bundle

The two local orientation choices are glued by the signs of the actual
linear transition maps. The total space has the topology supplied by
`FiberBundleCore`, not the product topology on its underlying dependent
pair type. On a simply connected, locally path connected base, covering
space lifting supplies a continuous orientation section.
-/

noncomputable section

open Set Function Topology Filter

namespace Wikipedia.HopfProblem.OrbitPair.DeterminantSignCover

/-- A positive determinant preserves a local orientation bit; a negative
determinant reverses it. Only nonzero determinants occur on overlaps. -/
def action (d : ℝ) (b : Bool) : Bool := if 0 < d then b else !b

@[simp] theorem action_one (b : Bool) : action 1 b = b := by
  simp [action]

@[simp] theorem action_twice (d : ℝ) (b : Bool) : action d (action d b) = b := by
  by_cases hd : 0 < d <;> simp [action, hd]

theorem action_neg (d : ℝ) (hd : d ≠ 0) (b : Bool) :
    action (-d) b = !(action d b) := by
  rcases lt_or_gt_of_ne hd with hd | hd
  · simp [action, not_lt_of_ge hd.le, neg_pos.mpr hd]
  · simp [action, hd, not_lt_of_ge (neg_nonpos.mpr hd.le)]

theorem action_mul (d e : ℝ) (hd : d ≠ 0) (he : e ≠ 0) (b : Bool) :
    action (d * e) b = action d (action e b) := by
  rcases lt_or_gt_of_ne hd with hd | hd <;> rcases lt_or_gt_of_ne he with he | he
  · simp [action, not_lt_of_ge hd.le, not_lt_of_ge he.le,
      mul_pos_of_neg_of_neg hd he]
  · simp [action, not_lt_of_ge hd.le, he,
      not_lt_of_ge (mul_neg_of_neg_of_pos hd he).le]
  · simp [action, hd, not_lt_of_ge he.le,
      not_lt_of_ge (mul_neg_of_pos_of_neg hd he).le]
  · simp [action, hd, he, mul_pos hd he]

theorem action_mul_cancel (d e : ℝ) (hd : d ≠ 0) (he : e ≠ 0) (b : Bool) :
    action (d * e) (action d b) = action e b := by
  rw [mul_comm, action_mul e d he hd, action_twice]

theorem continuousOn_action {B : Type*} [TopologicalSpace B]
    {f : B → ℝ} {s : Set B} (hf : ContinuousOn f s)
    (hne : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun p : B × Bool => action (f p.1) p.2) (s ×ˢ univ) := by
  have hg : ContinuousOn (fun p : B × Bool => f p.1) (s ×ˢ univ) :=
    hf.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  intro p hp
  rcases lt_or_gt_of_ne (hne p.1 hp.1) with hneg | hpos
  · have hevent : ∀ᶠ q in 𝓝[s ×ˢ univ] p, f q.1 < 0 :=
      (hg p hp).eventually_lt tendsto_const_nhds hneg
    have heq : (fun q : B × Bool => action (f q.1) q.2) =ᶠ[𝓝[s ×ˢ univ] p]
        (fun q => !q.2) := by
      filter_upwards [hevent] with q hq
      simp [action, not_lt_of_ge hq.le]
    have hc : Continuous (fun q : B × Bool => !q.2) :=
      (continuous_of_discreteTopology : Continuous (fun b : Bool => !b)).comp continuous_snd
    exact hc.continuousWithinAt.congr_of_eventuallyEq heq (by
      simp [action, not_lt_of_ge hneg.le])
  · have hevent : ∀ᶠ q in 𝓝[s ×ˢ univ] p, 0 < f q.1 :=
      tendsto_const_nhds.eventually_lt (hg p hp) hpos
    have heq : (fun q : B × Bool => action (f q.1) q.2) =ᶠ[𝓝[s ×ˢ univ] p]
        Prod.snd := by
      filter_upwards [hevent] with q hq
      simp [action, hq]
    exact continuous_snd.continuousWithinAt.congr_of_eventuallyEq heq (by simp [action, hpos])

theorem continuousAt_action {d : ℝ} (hd : d ≠ 0) (b : Bool) :
    ContinuousAt (fun p : ℝ × Bool => action p.1 p.2) (d, b) := by
  have hc : ContinuousOn (fun p : ℝ × Bool => action p.1 p.2)
      ({r : ℝ | r ≠ 0} ×ˢ univ) :=
    continuousOn_action continuousOn_id (fun _ hr => hr)
  exact hc.continuousAt
    (((isOpen_ne : IsOpen {r : ℝ | r ≠ 0}).prod isOpen_univ).mem_nhds ⟨hd, mem_univ b⟩)

variable {B E ι : Type*} [TopologicalSpace B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Z : VectorBundleCore ℝ B E ι)

theorem coordChange_self_eq (i : ι) {x : B} (hx : x ∈ Z.baseSet i) :
    Z.coordChange i i x = ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  exact Z.coordChange_self i x hx v

theorem coordChange_det_self (i : ι) {x : B} (hx : x ∈ Z.baseSet i) :
    (Z.coordChange i i x).det = 1 := by
  rw [coordChange_self_eq Z i hx]
  exact LinearMap.det_id

theorem coordChange_det_comp (i j k : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) :
    (Z.coordChange j k x).det * (Z.coordChange i j x).det =
      (Z.coordChange i k x).det := by
  rw [← LinearMap.det_comp]
  exact congrArg (fun L : E →L[ℝ] E => L.det) (Z.coordChange_linear_comp i j k x hx)

theorem coordChange_det_ne_zero (i j : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) : (Z.coordChange i j x).det ≠ 0 := by
  have h := coordChange_det_comp Z i j i ⟨hx, hx.1⟩
  rw [coordChange_det_self Z i hx.1] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

variable [FiniteDimensional ℝ E]

/-- The orientation cover obtained from the given vector bundle's own
transition maps and cover. -/
def core : FiberBundleCore ι B Bool where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := action (Z.coordChange i j x).det
  coordChange_self i x hx b := by
    rw [coordChange_det_self Z i hx]
    exact action_one b
  continuousOn_coordChange i j :=
    continuousOn_action
      (ContinuousLinearMap.continuous_det.comp_continuousOn (Z.continuousOn_coordChange i j))
      (fun _ hx => coordChange_det_ne_zero Z i j hx)
  coordChange_comp i j k x hx b := by
    rw [← action_mul _ _ (coordChange_det_ne_zero Z j k ⟨hx.1.2, hx.2⟩)
      (coordChange_det_ne_zero Z i j hx.1), coordChange_det_comp Z i j k hx]

theorem isEvenlyCovered (x : B) : IsEvenlyCovered (core Z).proj x Bool :=
  IsEvenlyCovered.of_trivialization ((core Z).mem_localTrivAt_baseSet x)

theorem isCoveringMap : IsCoveringMap (core Z).proj :=
  fun x => (isEvenlyCovered Z x).to_isEvenlyCovered_preimage

/-- A coherent orientation, fixed at one basepoint, exists on a simply
connected base. This is a section of the actual determinant-sign cover. -/
theorem existsUnique_section [SimplyConnectedSpace B] [LocallyPathConnectedSpace B]
    (x₀ : B) (b₀ : Bool) :
    ∃! s : C(B, (core Z).TotalSpace),
      s x₀ = ⟨x₀, b₀⟩ ∧ (core Z).proj ∘ s = id := by
  exact (isCoveringMap Z).existsUnique_continuousMap_lifts
    (ContinuousMap.id B) x₀ ⟨x₀, b₀⟩ rfl

end Wikipedia.HopfProblem.OrbitPair.DeterminantSignCover
