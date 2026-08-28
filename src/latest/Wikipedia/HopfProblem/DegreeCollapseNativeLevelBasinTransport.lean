import Wikipedia.HopfProblem.DegreeCollapseBeltCircleReachingLevel

/-!
# Native partial diffeomorphisms between two regular levels along actual orbits

No critical-point-free band is assumed. The source consists exactly of the
first level's points whose orbits reach the second level, and conversely
for the target. The previously constructed whole flow cylinders provide
both smooth maps and exact inverse identities on these open subsets.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_native_level_basin_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (za : {x : M // f x = a}) (zb : {x : M // f x = b}) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    ∃ D : PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {x : M // f x = a} {x : M // f x = b} ∞,
      D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f b} ∧
      D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
      ∀ x ∈ D.source, ∃ t : ℝ, S.flow t x.val = (D x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  let A := {x : M // f x = a}
  let B := {x : M // f x = b}
  obtain ⟨Φa, hsa, hta, hfa, -⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf ha S.smooth S.flow S.integral (fun x hx => S.descent x (ha x hx)) za
  obtain ⟨Φb, hsb, htb, hfb, -⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hb S.smooth S.flow S.integral (fun x hx => S.descent x (hb x hx)) zb
  let U : Set A := {x | x.val ∈ FlowCancellation.levelBasin S.flow f b}
  let V : Set B := {x | x.val ∈ FlowCancellation.levelBasin S.flow f a}
  let P : A → B := fun x => (Φb.symm x.val).1
  let Q : B → A := fun y => (Φa.symm y.val).1
  have hU : IsOpen U := by
    have hh : IsOpen (FlowCancellation.levelBasin S.flow f b) := htb ▸ Φb.open_target
    exact hh.preimage continuous_subtype_val
  have hV : IsOpen V := by
    have hh : IsOpen (FlowCancellation.levelBasin S.flow f a) := hta ▸ Φa.open_target
    exact hh.preimage continuous_subtype_val
  have hPa (x : A) (t : ℝ) : Φa.symm (S.flow t x.val) = (x, t) := by
    have hs : (x, t) ∈ Φa.source := by rw [hsa]; trivial
    have hh : Φa.symm (Φa (x, t)) = (x, t) := Φa.left_inv' hs
    rwa [hfa] at hh
  have hPb (y : B) (t : ℝ) : Φb.symm (S.flow t y.val) = (y, t) := by
    have hs : (y, t) ∈ Φb.source := by rw [hsb]; trivial
    have hh : Φb.symm (Φb (y, t)) = (y, t) := Φb.left_inv' hs
    rwa [hfb] at hh
  have horbP (x : A) (hx : x ∈ U) :
      S.flow (-(Φb.symm x.val).2) x.val = (P x).val := by
    have hh : S.flow (Φb.symm x.val).2 (P x).val = x.val :=
      (hfb (Φb.symm x.val)).symm.trans (Φb.right_inv' (htb.symm ▸ hx))
    have hi := congrArg (S.flow (-(Φb.symm x.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have horbQ (y : B) (hy : y ∈ V) :
      S.flow (-(Φa.symm y.val).2) y.val = (Q y).val := by
    have hh : S.flow (Φa.symm y.val).2 (Q y).val = y.val :=
      (hfa (Φa.symm y.val)).symm.trans (Φa.right_inv' (hta.symm ▸ hy))
    have hi := congrArg (S.flow (-(Φa.symm y.val).2)) hh
    rw [← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply] at hi
    exact hi.symm
  have hPU : MapsTo P U V := by
    intro x hx
    have hxa : x.val ∈ FlowCancellation.levelBasin S.flow f a :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using x.property⟩
    change (P x).val ∈ FlowCancellation.levelBasin S.flow f a
    exact horbP x hx ▸ (FlowCancellation.levelBasin_flow_iff S.flow f a
      (-(Φb.symm x.val).2) x.val).mpr hxa
  have hQV : MapsTo Q V U := by
    intro y hy
    have hyb : y.val ∈ FlowCancellation.levelBasin S.flow f b :=
      ⟨0, by simpa only [S.flow.map_zero_apply] using y.property⟩
    change (Q y).val ∈ FlowCancellation.levelBasin S.flow f b
    exact horbQ y hy ▸ (FlowCancellation.levelBasin_flow_iff S.flow f b
      (-(Φa.symm y.val).2) y.val).mpr hyb
  have hQP (x : A) (hx : x ∈ U) : Q (P x) = x := by
    have hh := hPa x (-(Φb.symm x.val).2)
    rw [horbP x hx] at hh
    exact congrArg Prod.fst hh
  have hPQ (y : B) (hy : y ∈ V) : P (Q y) = y := by
    have hh := hPb y (-(Φa.symm y.val).2)
    rw [horbQ y hy] at hh
    exact congrArg Prod.fst hh
  have hPs : ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞ P U := by
    have hh := Φb.contMDiffOn_invFun.comp (RegularLevel.contMDiff_inclusion hf ha).contMDiffOn
      (show MapsTo (Subtype.val : A → M) U Φb.target from fun _ hx => htb.symm ▸ hx)
    exact contMDiff_fst.comp_contMDiffOn hh
  have hQs : ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞ Q V := by
    have hh := Φa.contMDiffOn_invFun.comp (RegularLevel.contMDiff_inclusion hf hb).contMDiffOn
      (show MapsTo (Subtype.val : B → M) V Φa.target from fun _ hy => hta.symm ▸ hy)
    exact contMDiff_fst.comp_contMDiffOn hh
  let D : PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) A B ∞ := {
    toFun := P
    invFun := Q
    source := U
    target := V
    map_source' := hPU
    map_target' := hQV
    left_inv' := hQP
    right_inv' := hPQ
    open_source := hU
    open_target := hV
    contMDiffOn_toFun := hPs
    contMDiffOn_invFun := hQs }
  exact ⟨D, rfl, rfl, fun x hx => ⟨-(Φb.symm x.val).2, horbP x hx⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
