import Wikipedia.HopfProblem.DegreeCollapseSublevelThreeFourMatrix

/-!
# A pure four-handle block cannot remain when the final H4 vanishes

The original presentation with zero three-handles proves zero H3 before
the final four-handle. Its actual Morse exact sequence would then make the
nonzero attaching-sphere H3 a quotient of the upper H4. The genuine final
regular band transports the assumed H4 vanishing, giving a contradiction.
This closes the zero-row case without inferring injectivity from a
surjective matrix or assuming a balanced number of handles.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] in
theorem four_handle_impossible_of_adjacent_vanishing {p : M}
    (D : MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 4)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - D.radius ^ 2} 3)]
    [Subsingleton (SingularHomology {y : M // f y ≤ f p + D.radius ^ 2} 4)] : False := by
  let e := IndexFour.indexFourBoundaryEquiv D hindex
  have hker : e.symm 1 ∈ LinearMap.ker (D.coreBoundaryHomologyMap 3) :=
    Subsingleton.elim _ _
  rw [← D.morse_exact_at_attachingSphere hf 3 (by decide)] at hker
  obtain ⟨x, hx⟩ := hker
  have hx0 : x = 0 := Subsingleton.elim _ _
  rw [hx0, map_zero] at hx
  have he := congrArg e hx
  simp only [map_zero, LinearEquiv.apply_symm_apply] at he
  norm_num at he

theorem SurgeryWindows.four_block_empty_of_upper_fourth_zero
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    [Subsingleton (SingularHomology {y : M // f y ≤ b} 4)]
    (n : ℕ) (hn : n < S.count)
    (hfour : ThreeFourPresentation.HasIndexFourBlock S 0 n)
    (hcut : S.upper (S.point ⟨n, hn⟩) < b)
    (hwhich : ∀ i : Fin S.count, f (S.point i) < b ↔ i.val ≤ n) : n = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    exfalso
    let q := S.point ⟨n + 1, hn⟩
    have hband : ∀ y, f y ∈ Icc (S.upper q) b → y ∉ criticalPoints E f := by
      intro y hy hcrit
      have hyb : f y < b := lt_of_le_of_ne hy.2 (fun he => hb y he hcrit)
      obtain ⟨i, hi⟩ := S.point.surjective ⟨y, hcrit⟩
      have hib : f (S.point i) < b := by rw [hi]; exact hyb
      have hiq : i ≤ (⟨n + 1, hn⟩ : Fin S.count) := (hwhich i).mp hib
      have hle : f y ≤ f q := by simpa only [hi] using S.point_strictMono.monotone hiq
      exact ((S.value_lt_upper q).trans_le hy.1).not_ge hle
    let _ : Subsingleton
        (SingularHomology {y : M // f y ≤ f q + (S.data q).radius ^ 2} 4) :=
      (regular_sublevel_inclusion_bijective hf hcut.le hband 4).injective.subsingleton
    have hthree : S.HasIndexThreeBlock 0 0 := by
      intro i hi hil
      omega
    have hprev : 0 + n < S.count := by omega
    let P := ThreeFourPresentation.presentation S hf 0 hthree n hprev
      (ThreeFourPresentation.indexFourBlock_mono S (Nat.le_succ n) hfour)
    let _ : Subsingleton
        (SingularHomology {y : M // f y ≤ S.upper (S.point ⟨0 + n, hprev⟩)} 3) :=
      P.surjective.subsingleton
    let H := S.consecutiveBandData hf ⟨0 + n, hprev⟩ ⟨n + 1, hn⟩ (by simp)
    let _ : Subsingleton
        (SingularHomology {y : M // f y ≤ f q - (S.data q).radius ^ 2} 3) :=
      (H.homologyEquiv 3).surjective.subsingleton
    have hq : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 4 :=
      hfour ⟨n + 1, hn⟩ (by dsimp; omega) (by dsimp; omega)
    exact four_handle_impossible_of_adjacent_vanishing (S.data q) hf.continuous hq

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
