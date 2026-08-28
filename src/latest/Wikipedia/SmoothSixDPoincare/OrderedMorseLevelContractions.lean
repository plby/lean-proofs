import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints
import Wikipedia.SmoothSixDPoincare.InitialMorseLevelContractions
import Wikipedia.SmoothSixDPoincare.RegularLevelContractions

/-!
# Circle contractions along the actual finite middle-index surgery sequence

The first upper level bounds the constructed minimum disk. Induction through
the actual regular bands and surgeries then supplies circle contractions
below any later handle, provided all intervening handles have index two or
three. The index condition remains explicit; its global construction is a
separate handle-elimination obligation.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

variable (S : SurgeryWindows E f)

open Classical in
/-- Circle contractions below a chosen handle are constructed from the first disk and
the original preceding surgeries, with no assumed contractions at intermediate levels. -/
theorem lower_circle_nullhomotopies_of_middle_indices
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (j : Fin S.count) (hj : 0 < j.val)
    (hindex : ∀ i : Fin S.count, 0 < i.val → i.val < j.val →
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3) :
    ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point j)).LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  have hupper : ∀ n : ℕ, ∀ hn : n < S.count, n < j.val →
      ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point ⟨n, hn⟩)).UpperLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨d⟩ := S.nonempty_firstSublevelDisk hf hn
      have d' : SublevelDisk 6 f (S.upper (S.first hn)) := hdim ▸ d
      exact d'.circle_nullhomotopies (n := 5) (by norm_num)
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      have hprev := ih hn' (by omega)
      have hlt : (⟨n, hn'⟩ : Fin S.count) < ⟨n + 1, hn⟩ := Nat.lt_succ_self n
      have hlow : ∀ g : C(Hemisphere.Sphere 1,
          (S.data (S.point ⟨n + 1, hn⟩)).LowerLevel),
          ∃ q, g.Homotopic (ContinuousMap.const _ q) :=
        FlowConstruction.circle_nullhomotopies_regular_level hf
          (S.ordered_windows _ _ hlt).le (S.consecutive_regular _ _ rfl) hprev
      rcases hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj with htwo | hthree
      · let : Fact (Module.finrank ℝ
            (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 1 + 1) := ⟨htwo⟩
        exact (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 1
          (by norm_num) (by omega) hlow
      · let : Fact (Module.finrank ℝ
            (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 2 + 1) := ⟨hthree⟩
        exact (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 2
          (by norm_num) (by omega) hlow
  have hprev : j.val - 1 < S.count := by omega
  have hprevj : (⟨j.val - 1, hprev⟩ : Fin S.count) < j := by
    change j.val - 1 < j.val
    omega
  exact FlowConstruction.circle_nullhomotopies_regular_level hf
    (S.ordered_windows _ _ hprevj).le
    (S.consecutive_regular _ _ (by change j.val - 1 + 1 = j.val; omega))
    (hupper (j.val - 1) hprev hprevj)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
