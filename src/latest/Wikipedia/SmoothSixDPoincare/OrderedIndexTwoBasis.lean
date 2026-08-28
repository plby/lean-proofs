import Wikipedia.SmoothSixDPoincare.OrderedMorseBandData
import Wikipedia.SmoothSixDPoincare.OrderedMorseHomologyOne
import Wikipedia.SmoothSixDPoincare.MorseIndexTwoBasisExtension

/-!
# Coherent integer bases along the actual initial index-two sequence

Start with the constructed minimum disk. At every consecutive index-two
handle, use the retained actual band map and the native basis extension.
The resulting recursively chosen bases preserve the old coordinates and
identify each newly adjoined coordinate with its actual collapse map.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f)

def HasIndexTwoPrefix (n : ℕ) : Prop :=
  ∀ i : Fin S.count, 0 < i.val → i.val ≤ n →
    Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 2

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem indexTwoPrefix_mono {n m : ℕ} (hnm : n ≤ m) (h : S.HasIndexTwoPrefix m) :
    S.HasIndexTwoPrefix n := fun i hi hin => h i hi (hin.trans hnm)

theorem indexTwoBasis_step
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n + 1 < S.count)
    (hpre : S.HasIndexTwoPrefix (n + 1))
    (e : (Fin n → ℤ) ≃ₗ[ℤ]
      SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩)} 2) :
    let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
    ∃ H : (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n + 1, hn⟩)} 2,
      (∀ v, H (Fin.cons 0 v) =
        (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 2
          (B.homologyEquiv 2 (e v))) ∧
      ∀ v, (S.data (S.point ⟨n + 1, hn⟩)).indexTwoCollapseCoordinate hf.continuous
        (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) (H v) = v 0 := by
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) -
        (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2} 1) :=
    S.lower_homologyOne_subsingleton_of_indices hf ⟨n + 1, hn⟩ (Nat.succ_pos n)
      (fun i hi hin => by
        have h := hpre i hi (Nat.le_of_lt hin)
        omega)
  let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
  exact (S.data (S.point ⟨n + 1, hn⟩)).exists_indexTwoBasis_extension hf.continuous
    (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) n (e.trans (B.homologyEquiv 2))

def indexTwoBasis (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (n : ℕ) → (hn : n < S.count) → S.HasIndexTwoPrefix n →
      (Fin n → ℤ) ≃ₗ[ℤ] SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n, hn⟩)} 2
  | 0, hn, _ => by
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ S.upper (S.point ⟨0, hn⟩)} 2) := by
        obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
        exact D.homology_subsingleton 2 (by norm_num)
      exact LinearEquiv.ofSubsingleton _ _
  | n + 1, hn, hpre =>
      Classical.choose (S.indexTwoBasis_step hf n hn hpre
        (indexTwoBasis hf n (Nat.lt_of_succ_lt hn)
          (S.indexTwoPrefix_mono (Nat.le_succ n) hpre)))

theorem indexTwoBasis_succ_old
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n + 1 < S.count)
    (hpre : S.HasIndexTwoPrefix (n + 1)) (v : Fin n → ℤ) :
    S.indexTwoBasis hf (n + 1) hn hpre (Fin.cons 0 v) =
      (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 2
        ((S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl).homologyEquiv 2
          (S.indexTwoBasis hf n (Nat.lt_of_succ_lt hn)
            (S.indexTwoPrefix_mono (Nat.le_succ n) hpre) v)) :=
  (Classical.choose_spec (S.indexTwoBasis_step hf n hn hpre
    (S.indexTwoBasis hf n (Nat.lt_of_succ_lt hn)
      (S.indexTwoPrefix_mono (Nat.le_succ n) hpre)))).1 v

theorem indexTwoBasis_succ_coordinate
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n + 1 < S.count)
    (hpre : S.HasIndexTwoPrefix (n + 1)) (v : Fin (n + 1) → ℤ) :
    (S.data (S.point ⟨n + 1, hn⟩)).indexTwoCollapseCoordinate hf.continuous
      (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl)
        (S.indexTwoBasis hf (n + 1) hn hpre v) = v 0 :=
  (Classical.choose_spec (S.indexTwoBasis_step hf n hn hpre
    (S.indexTwoBasis hf n (Nat.lt_of_succ_lt hn)
      (S.indexTwoPrefix_mono (Nat.le_succ n) hpre)))).2 v

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
