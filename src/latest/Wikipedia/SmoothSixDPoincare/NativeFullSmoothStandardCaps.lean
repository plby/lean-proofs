import Wikipedia.SmoothSixDPoincare.FullSmoothMorseDecomposition
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainStandardCaps
import Wikipedia.SmoothSixDPoincare.NativeTopIndexSphereDiffeomorph

/-!
# Native full Morse decompositions retain standard smooth cap spheres

The additional cap data is constructed from the original negative Morse
coordinates. It is retained through all original regular bands and through
the exact identifications of the first and last sublevels with the empty
body and the original closed manifold. No cap or handle is cancelled here.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

namespace MorseSurgeryData

variable {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem topIndex_hasStandardCapSphere
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E) :
    (d.lowerSmoothBody hf).HasStandardCapSphere d.surgery.attachingSphere
      (d.topIndex_attaching_isOpen hindex) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro n hn
  let _ : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = n + 1) := ⟨hn⟩
  exact ⟨(d.topIndexCapDiffeomorph hindex hf n).symm.trans
    (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates n).symm⟩

open Classical in
theorem exists_fullSmoothStep_standardCaps (hd : d.HasSmoothExterior hf) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1,
      c.HasStandardCaps ∧ c.indices = [Module.finrank ℝ d.chart.NegativeCoordinates] ∧
      ∀ x : (d.lowerSmoothBody hf).body,
        c.sourceMap x = d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  have hsplit := d.chart.finrank_negative_add_positive
  by_cases hzero : Module.finrank ℝ d.chart.NegativeCoordinates = 0
  · have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = Module.finrank ℝ E := by omega
    let c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1 :=
      .birth (d.zeroIndexSmoothDisk hf hzero) hpos (d.zeroIndexSmoothBodyEquiv hzero hf hd)
        (.nil (SmoothBoundaryBodyEquiv.refl (d.upperSmoothBody hf).inclusion))
    refine ⟨c, True.intro, ?_, ?_⟩
    · change [0] = [Module.finrank ℝ d.chart.NegativeCoordinates]
      rw [hzero]
    · intro x
      exact d.zeroIndexSublevelHomeomorph_old hf.continuous hzero x
  by_cases htop : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E
  · let c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1 :=
      .cap d.surgery.attachingSphere d.attaching_isClosedEmbedding
        (d.topIndex_attaching_isOpen htop) htop (d.topIndexSmoothBodyEquiv htop hf hd)
        (.nil (SmoothBoundaryBodyEquiv.refl (d.upperSmoothBody hf).inclusion))
    refine ⟨c, ⟨d.topIndex_hasStandardCapSphere hf htop, True.intro⟩, rfl, ?_⟩
    intro x
    exact d.topIndexCapBodyRealization_old htop hf x
  let m := Module.finrank ℝ d.chart.NegativeCoordinates - 1
  let n := Module.finrank ℝ d.chart.PositiveCoordinates - 1
  let _ : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1) :=
    ⟨by dsimp [m]; omega⟩
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1) :=
    ⟨by dsimp [n]; omega⟩
  obtain ⟨P⟩ := d.nonempty_framedSmoothBoundaryData hf m n
  let c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
      (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1 :=
    .interior (d.attachingSmoothFace hf m) P hsplit (d.beltSmoothBodyEquiv hf m n P hd)
      (.nil (SmoothBoundaryBodyEquiv.refl (d.upperSmoothBody hf).inclusion))
  refine ⟨c, True.intro, rfl, ?_⟩
  intro x
  exact d.beltFramedBodyRealization_old hf m x

end MorseSurgeryData

namespace SurgeryWindows

variable (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem exists_fullSmoothInterval_standardCaps (hs : S.HasSmoothExteriors hf) (i : Fin S.count)
    (n : ℕ) (h : i.val + n < S.count) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        ((S.data (S.point i)).lowerSmoothBody hf)
        ((S.data (S.point (S.intervalEnd i n h))).upperSmoothBody hf) (n + 1),
      c.HasStandardCaps ∧ c.indices = S.intervalIndices i n h ∧
      ∀ x, c.sourceMap x = S.intervalSource hf i n h x := by
  induction n with
  | zero => exact (S.data (S.point i)).exists_fullSmoothStep_standardCaps hf (hs (S.point i))
  | succ n ih =>
      have hp : i.val + n < S.count := by omega
      let prev := S.intervalEnd i n hp
      let last := S.intervalEnd i (n + 1) h
      let B := S.consecutiveBandData hf prev last (by dsimp [prev, last, intervalEnd]; omega)
      obtain ⟨c, hcs, hc, hcx⟩ := ih hp
      obtain ⟨d, hds, hd, hdx⟩ :=
        (S.data (S.point last)).exists_fullSmoothStep_standardCaps hf (hs (S.point last))
      let e := B.smoothBodyEquiv hf
      let a := (c.retarget e).append d
      let b := a.castLength (show 1 + (n + 1) = (n + 1) + 1 by omega)
      refine ⟨b, a.hasStandardCaps_castLength _
        ((c.retarget e).hasStandardCaps_append d (c.hasStandardCaps_retarget e hcs) hds), ?_, ?_⟩
      · change (a.castLength _).indices = _
        rw [FullSmoothHandleChain.castLength_indices]
        exact ((c.retarget e).append_indices d).trans
          (congrArg₂ List.append ((c.retarget_indices e).trans hc) hd)
      · intro x
        change (a.castLength _).sourceMap x = _
        rw [FullSmoothHandleChain.castLength_sourceMap]
        have he := (c.retarget_sourceMap e x).trans (congrArg e.body (hcx x))
        exact ((c.retarget e).append_sourceMap d x).trans
          ((congrArg d.sourceMap he).trans (hdx _))

open Classical in
theorem exists_fullSmoothSequence_standardCaps (hs : S.HasSmoothExteriors hf)
    (hcount : 0 < S.count) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        ((S.data (S.first hcount)).lowerSmoothBody hf)
        ((S.data (S.last hcount)).upperSmoothBody hf) S.count,
      c.HasStandardCaps ∧ c.indices = List.ofFn (fun i : Fin S.count =>
        Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) := by
  let i : Fin S.count := ⟨0, hcount⟩
  have hn : S.count - 1 + 1 = S.count := by omega
  have h : i.val + (S.count - 1) < S.count := by dsimp [i]; omega
  obtain ⟨c, hcs, hc, -⟩ := S.exists_fullSmoothInterval_standardCaps hf hs i (S.count - 1) h
  let d := c.castLength hn
  have hend : S.intervalEnd i (S.count - 1) h =
      (⟨S.count - 1, Nat.sub_lt hcount zero_lt_one⟩ : Fin S.count) := by
    apply Fin.ext
    exact Nat.zero_add _
  have hd : d.indices = List.ofFn (fun j : Fin S.count =>
      Module.finrank ℝ (S.data (S.point j)).chart.NegativeCoordinates) := by
    rw [FullSmoothHandleChain.castLength_indices, hc, S.intervalIndices_eq_ofFn]
    rw [List.ofFn_congr hn]
    apply congrArg List.ofFn
    funext j
    apply congrArg (fun t : Fin S.count =>
      Module.finrank ℝ (S.data (S.point t)).chart.NegativeCoordinates)
    apply Fin.ext
    exact Nat.zero_add _
  change ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
      ((S.data (S.point i)).lowerSmoothBody hf)
      ((S.data (S.point ⟨S.count - 1, Nat.sub_lt hcount zero_lt_one⟩)).upperSmoothBody hf) S.count,
    c.HasStandardCaps ∧ c.indices = _
  rw [← hend]
  exact ⟨d, c.hasStandardCaps_castLength hn hcs, hd⟩

open Classical in
theorem exists_fullSmoothDecomposition_standardCaps (hs : S.HasSmoothExteriors hf)
    (hcount : 0 < S.count) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model E))
        (SmoothBoundaryBody.closed 𝓘(ℝ, RegularLevel.Model E) M) S.count,
      c.HasStandardCaps ∧ c.indices = List.ofFn (fun i : Fin S.count =>
        Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) := by
  let _ := S.first_lowerSmoothBody_isEmpty hf hcount
  let _ := S.last_upperSmoothBoundary_isEmpty hf hcount
  obtain ⟨c, hcs, hc⟩ := S.exists_fullSmoothSequence_standardCaps hf hs hcount
  let e := SmoothBoundaryBody.toEmptyEquiv ((S.data (S.first hcount)).lowerSmoothBody hf)
  let e' := SmoothBoundaryBody.toClosedEquiv ((S.data (S.last hcount)).upperSmoothBody hf)
    (S.last_upperSmoothBodyHomeomorph hf hcount)
  exact ⟨(c.rebase e).retarget e',
    (c.rebase e).hasStandardCaps_retarget e' (c.hasStandardCaps_rebase e hcs),
    ((c.rebase e).retarget_indices e').trans ((c.rebase_indices e).trans hc)⟩

end SurgeryWindows

variable (E M) [Nonempty M]

theorem exists_fullSmoothHandleDecomposition_standardCaps (hdim : 0 < Module.finrank ℝ E) :
    ∃ (k : ℕ) (c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model E))
        (SmoothBoundaryBody.closed 𝓘(ℝ, RegularLevel.Model E) M) k),
      2 ≤ k ∧ c.HasStandardCaps := by
  obtain ⟨f, hf, _, S, hs⟩ := exists_morse_function_with_smoothSurgeryWindows E M
  obtain ⟨c, hcs, -⟩ := S.exists_fullSmoothDecomposition_standardCaps hf hs (S.count_pos hf)
  exact ⟨S.count, c, S.two_le_count hf hdim, hcs⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
