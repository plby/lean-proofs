import Wikipedia.HopfProblem.DegreeCollapseThreeFourLevelContractions
import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryJoined

/-!
# Actual paths in the original three/four-prefix levels

Start at the genuine minimum-disk boundary. Transfer joinedness through the
original regular bands and native surgery complements. No connectedness of
the intermediate levels or index bounds on the untouched half are assumed.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}

theorem native_upper_joined_of_lower (D : MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    [Fact (Module.finrank ℝ D.chart.NegativeCoordinates = n + 1)]
    (hn : 0 < n) (hdim : n + 2 < Module.finrank ℝ E)
    (hjoin : ∀ x y : D.LowerLevel, Joined x y) : ∀ x y : D.UpperLevel, Joined x y := by
  let _ := RegularLevel.chartedSpace hf D.lower_regular
  let _ := RegularLevel.isManifold hf D.lower_regular
  apply D.surgery.newBoundary_joined n hn (D.attaching_smooth hf n) ?_ hjoin
  simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
  omega

variable [CompactSpace M]

theorem joined_of_regular_level_band (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ criticalPoints E f)
    (hjoin : ∀ x y : {z : M // f z = a}, Joined x y) :
    ∀ x y : {z : M // f z = b}, Joined x y := by
  obtain ⟨e⟩ := FlowConstruction.nonempty_regularLevelHomeomorph hf hab hband
  intro x y
  simpa only [e.apply_symm_apply] using (hjoin (e.symm x) (e.symm y)).map e.continuous

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem upper_joined_of_three_four_prefix
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (j : Fin S.count)
    (hindex : ∀ i : Fin S.count, 0 < i.val → i.val ≤ j.val →
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 4) :
    ∀ x y : (S.data (S.point j)).UpperLevel, Joined x y := by
  have hupper : ∀ n : ℕ, ∀ hn : n < S.count, n ≤ j.val →
      ∀ x y : (S.data (S.point ⟨n, hn⟩)).UpperLevel, Joined x y := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨d⟩ := S.nonempty_firstSublevelDisk hf hn
      have d' : SublevelDisk 7 f (S.upper (S.first hn)) := hdim ▸ d
      let e : Hemisphere.Sphere 6 ≃ₜ (S.data (S.point ⟨0, hn⟩)).UpperLevel :=
        d'.boundaryHomeomorph
      intro x y
      have h : Joined (e.symm x) (e.symm y) := PathConnectedSpace.joined _ _
      simpa only [e.apply_symm_apply] using h.map e.continuous
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      have hprev := ih hn' (by omega)
      have hlt : (⟨n, hn'⟩ : Fin S.count) < ⟨n + 1, hn⟩ := Nat.lt_succ_self n
      have hlow : ∀ x y : (S.data (S.point ⟨n + 1, hn⟩)).LowerLevel, Joined x y :=
        joined_of_regular_level_band hf (S.ordered_windows _ _ hlt).le
          (S.consecutive_regular _ _ rfl) hprev
      rcases hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj with hthree | hfour
      · let _ : Fact (Module.finrank ℝ
            (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 2 + 1) := ⟨hthree⟩
        exact native_upper_joined_of_lower _ hf 2 (by norm_num) (by omega) hlow
      · let _ : Fact (Module.finrank ℝ
            (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 3 + 1) := ⟨hfour⟩
        exact native_upper_joined_of_lower _ hf 3 (by norm_num) (by omega) hlow
  exact hupper j.val j.isLt le_rfl

theorem upper_joined_of_three_four_before
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (q : criticalPoints E f)
    (hindex : ∀ i : Fin S.count, 0 < i.val → f (S.point i) ≤ f q →
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 4) :
    ∀ x y : (S.data q).UpperLevel, Joined x y := by
  obtain ⟨j, rfl⟩ := S.point.surjective q
  apply S.upper_joined_of_three_four_prefix hf hdim j
  intro i hi hij
  exact hindex i hi (S.point_strictMono.monotone hij)

theorem pathConnectedSpace_upper_of_three_four_prefix
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (j : Fin S.count)
    (hindex : ∀ i : Fin S.count, 0 < i.val → i.val ≤ j.val →
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 4)
    (z₀ : (S.data (S.point j)).UpperLevel) :
    PathConnectedSpace (S.data (S.point j)).UpperLevel where
  nonempty := ⟨z₀⟩
  joined := S.upper_joined_of_three_four_prefix hf hdim j hindex

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
