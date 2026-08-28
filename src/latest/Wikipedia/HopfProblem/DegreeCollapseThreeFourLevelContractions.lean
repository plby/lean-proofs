import Wikipedia.HopfProblem.DegreeCollapseThreeFourPresentation
import Wikipedia.SmoothSixDPoincare.OrderedMorseLevelContractions

/-!
# Circle contractions along the actual seven-dimensional three/four prefix

Start with the constructed minimum disk, and transport contractions through
the original regular bands and the actual three- and four-handle boundaries.
No global index ordering beyond the prefix or assumed level contractions are
needed. These are the original regular levels with their unchanged topology.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem upper_circle_nullhomotopies_of_three_four_prefix
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (j : Fin S.count)
    (hindex : ∀ i : Fin S.count, 0 < i.val → i.val ≤ j.val →
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 4) :
    ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point j)).UpperLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  have hupper : ∀ n : ℕ, ∀ hn : n < S.count, n ≤ j.val →
      ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point ⟨n, hn⟩)).UpperLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨d⟩ := S.nonempty_firstSublevelDisk hf hn
      have d' : SublevelDisk 7 f (S.upper (S.first hn)) := hdim ▸ d
      exact d'.circle_nullhomotopies (n := 6) (by norm_num)
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
      rcases hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj with hthree | hfour
      · let : Fact (Module.finrank ℝ
            (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 2 + 1) := ⟨hthree⟩
        exact (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 2
          (by norm_num) (by omega) hlow
      · let : Fact (Module.finrank ℝ
            (S.data (S.point ⟨n + 1, hn⟩)).chart.NegativeCoordinates = 3 + 1) := ⟨hfour⟩
        exact (S.data (S.point ⟨n + 1, hn⟩)).upper_circle_nullhomotopies hf 3
          (by norm_num) (by omega) hlow
  exact hupper j.val j.isLt le_rfl

theorem lower_circle_nullhomotopies_of_three_four_prefix
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (j : Fin S.count) (hj : 0 < j.val)
    (hindex : ∀ i : Fin S.count, 0 < i.val → i.val < j.val →
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 4) :
    ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point j)).LowerLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  have hprev : j.val - 1 < S.count := by omega
  have hprevj : (⟨j.val - 1, hprev⟩ : Fin S.count) < j := by
    change j.val - 1 < j.val
    omega
  exact FlowConstruction.circle_nullhomotopies_regular_level hf
    (S.ordered_windows _ _ hprevj).le
    (S.consecutive_regular _ _ (by change j.val - 1 + 1 = j.val; omega))
    (S.upper_circle_nullhomotopies_of_three_four_prefix hf hdim ⟨j.val - 1, hprev⟩
      (fun i hi hij => hindex i hi (by dsimp at hij; omega)))

theorem three_four_block_upper_circle_nullhomotopies
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7) (r n : ℕ)
    (hthree : S.HasIndexThreeBlock 0 r)
    (hfour : ThreeFourPresentation.HasIndexFourBlock S r n)
    (j : Fin S.count) (hj : j.val ≤ r + n) :
    ∀ g : C(Hemisphere.Sphere 1, (S.data (S.point j)).UpperLevel),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  apply S.upper_circle_nullhomotopies_of_three_four_prefix hf hdim j
  intro i hi hij
  by_cases hir : i.val ≤ r
  · exact Or.inl (hthree i hi (by simpa only [zero_add] using hir))
  · exact Or.inr (hfour i (by omega) (by omega))

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
