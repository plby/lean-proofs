import Wikipedia.HopfProblem.DegreeCollapseIndexFourBasinFamily

/-!
# Construct the full original index-four block at one native lower cut

Induct down the actual finite block. Shrink windows, transport the whole
higher family through a regular band, and add the original next attaching
three-sphere by the constructed four-handle step. The final regular band
reaches the prescribed cut with exact complete backward-basin labels.
The function, critical points, signed charts, and critical germs are retained.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_index_four_block_realization
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (n : ℕ) {c : ℝ} (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    (p : Fin n → criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (horder : StrictMono (fun j => f (p j))) (habove : ∀ j, c < f (p j))
    (hblock : ∀ j (q : criticalPoints E f), c < f q → f q ≤ f (p j) → q ∈ range p)
    (ε : criticalPoints E f → ℝ) (hε : ∀ q, 0 < ε q) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ q, (T.data q).chart = (S.data q).chart) ∧
      (∀ q, (T.data q).radius < ε q) ∧
      (∀ q ∈ criticalPoints E f, ∀ᶠ y in 𝓝 q, T.field y = S.field y) ∧
      ∃ α : Fin n → S₃ → {y : M // f y = c}, IsNativeFourBasinFamily T hf hc p α := by
  induction n generalizing S c ε with
  | zero =>
    obtain ⟨T, hfield, -, hcharts, hradii⟩ := exists_adapted_windows_with_prescribed_flow_lt
      hf hm S.distinct S.smooth S.flow S.integral S.zero S.descent
        (fun q => (S.data q).chart) S.critical_model_germ ε hε
    refine ⟨T, hcharts, hradii, ?_, (fun j => Fin.elim0 j), ?_⟩
    · intro q hq
      exact Filter.Eventually.of_forall (fun y => congrFun hfield y)
    · exact ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j,
        fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  | succ n ih =>
    let a := S.toSurgeryWindows.upper (p 0)
    have hpa : f (p 0) < a := S.toSurgeryWindows.value_lt_upper (p 0)
    have htail (j : Fin n) : a < f (p j.succ) :=
      (S.separated (p 0) (p j.succ) (horder (Fin.succ_pos j))).trans
        (S.toSurgeryWindows.lower_lt_value (p j.succ))
    have htailblock (j : Fin n) (q : criticalPoints E f)
        (haq : a < f q) (hqj : f q ≤ f (p j.succ)) :
        q ∈ range (fun i : Fin n => p i.succ) := by
      obtain ⟨i, hi⟩ := hblock j.succ q ((habove 0).trans (hpa.trans haq)) hqj
      cases i using Fin.cases with
      | zero => exact (not_lt_of_ge haq.le (hi ▸ hpa)).elim
      | succ i => exact ⟨i, hi⟩
    let δ := Real.sqrt (f (p 0) - c)
    have hδ : 0 < δ := Real.sqrt_pos.mpr (sub_pos.mpr (habove 0))
    let η : criticalPoints E f → ℝ := fun q => min (ε q) (min (S.data q).radius δ)
    have hη (q : criticalPoints E f) : 0 < η q :=
      lt_min (hε q) (lt_min (S.data q).radius_pos hδ)
    obtain ⟨T, hchartsT, hradiiT, hgermsT, α, hα⟩ :=
      ih S (S.data (p 0)).upper_regular (fun j => p j.succ) (fun j => hp j.succ)
        (fun i j hij => horder (Fin.succ_lt_succ_iff.mpr hij)) htail htailblock η hη
    have hradius : (T.data (p 0)).radius < (S.data (p 0)).radius :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hradδ : (T.data (p 0)).radius < δ :=
      (hradiiT (p 0)).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hupper : T.toSurgeryWindows.upper (p 0) < a := by
      have hh := mul_pos (sub_pos.mpr hradius)
        (add_pos (S.data (p 0)).radius_pos (T.data (p 0)).radius_pos)
      change f (p 0) + (T.data (p 0)).radius ^ 2 < f (p 0) + (S.data (p 0)).radius ^ 2
      nlinarith
    have hlower : c < T.toSurgeryWindows.lower (p 0) := by
      have hh := mul_pos (sub_pos.mpr hradδ) (add_pos hδ (T.data (p 0)).radius_pos)
      have hs : δ ^ 2 = f (p 0) - c := Real.sq_sqrt (sub_pos.mpr (habove 0)).le
      change c < f (p 0) - (T.data (p 0)).radius ^ 2
      nlinarith
    have hgapUpper : ∀ q ∈ criticalPoints E f,
        f q ∉ Icc (T.toSurgeryWindows.upper (p 0)) a := by
      intro q hq hh
      have heq := S.isolated (p 0) q hq
        ⟨((S.toSurgeryWindows.lower_lt_value (p 0)).trans
          (T.toSurgeryWindows.value_lt_upper (p 0))).le.trans hh.1, hh.2⟩
      rw [heq] at hh
      exact not_le_of_gt (T.toSurgeryWindows.value_lt_upper (p 0)) hh.1
    let _ : Fact (Module.finrank ℝ (S.data (p 0)).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have hs := (S.data (p 0)).chart.finrank_negative_add_positive
          have hn := (nativeMorseIndex_eq_chart (S.data (p 0)).chart).symm.trans (hp 0)
          omega⟩
    let x₀ : S₃ := Hemisphere.point true ⟨0, by simp⟩
    let x₂ : Hemisphere.Sphere 2 := Hemisphere.point true ⟨0, by simp⟩
    let v := SphereCoordinates.standardParametrization (S.data (p 0)).chart.PositiveCoordinates 2 x₂
    obtain ⟨β, hβ, -⟩ := T.exists_regular_band_four_basin_family hf hupper
      (S.data (p 0)).upper_regular (T.data (p 0)).upper_regular hgapUpper
        ((S.data (p 0)).surgery.beltSphere v) (fun j => p j.succ) htail α hα
    obtain ⟨U, hchartsU, hradiiU, hgermsU, Γ, hΓ⟩ := T.exists_four_basin_family_step
      hf hm hdim (p 0) (hp 0) (fun j => p j.succ)
        (fun j => hupper.trans (htail j)) β hβ ε hε
    have hp_cases : Fin.cases (p 0) (fun j => p j.succ) = p := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hp_cases] at hΓ
    have hbelow (q : criticalPoints E f) (hqp : f q < f (p 0)) : f q < c := by
      by_contra h
      have hcq : c < f q := lt_of_le_of_ne (le_of_not_gt h)
        (Ne.symm (fun heq => hc q.val heq q.property))
      obtain ⟨j, hj⟩ := hblock 0 q hcq hqp.le
      have hh := horder.monotone (Fin.zero_le j)
      rw [hj] at hh
      exact not_lt_of_ge hh hqp
    have hgapLower : ∀ q ∈ criticalPoints E f,
        f q ∉ Icc c (T.toSurgeryWindows.lower (p 0)) := by
      intro q hq hh
      exact not_le_of_gt (hbelow ⟨q, hq⟩
        (hh.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p 0)))) hh.1
    obtain ⟨Ω, hΩ, -⟩ := U.exists_regular_band_four_basin_family hf hlower
      (T.data (p 0)).lower_regular hc hgapLower
        (nativeIndexFourAttachingSphere T (p 0) (hp 0) x₀) p
        (fun j => (T.toSurgeryWindows.lower_lt_value (p 0)).trans_le
          (horder.monotone (Fin.zero_le j))) Γ hΓ
    refine ⟨U, fun q => (hchartsU q).trans (hchartsT q), hradiiU, ?_, Ω, hΩ⟩
    intro q hq
    filter_upwards [hgermsU q hq, hgermsT q hq] with y hyU hyT
    exact hyU.trans hyT

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
