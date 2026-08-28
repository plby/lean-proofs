import Wikipedia.SmoothSixDPoincare.OrderedIndexTwoBasis
import Wikipedia.SmoothSixDPoincare.MorseIndexThreePresentation

/-!
# The actual finite middle-homology presentation after the two/three handle blocks

The initial index-two block supplies its coherent free basis. Each subsequent
index-three handle uses the retained original band bridge, the original
realized lower map, and a lift of its actual attaching class. The presentation
records the exact kernel and all columns; newest columns are inserted first.
The required index arrangement is an explicit hypothesis, not constructed here.
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

def HasIndexThreeBlock (r c : ℕ) : Prop :=
  ∀ i : Fin S.count, r < i.val → i.val ≤ r + c →
    Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 3

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem indexThreeBlock_mono {r c b : ℕ} (hcb : c ≤ b) (h : S.HasIndexThreeBlock r b) :
    S.HasIndexThreeBlock r c :=
  fun i hri hic => h i hri (hic.trans (Nat.add_le_add_left hcb r))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem indexThreeBlock_last (r c : ℕ) (hc : r + (c + 1) < S.count)
    (h : S.HasIndexThreeBlock r (c + 1)) :
    Module.finrank ℝ (S.data (S.point ⟨r + (c + 1), hc⟩)).chart.NegativeCoordinates = 3 :=
  h ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl

def middlePresentation (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (r : ℕ) (htwo : S.HasIndexTwoPrefix r) :
    (c : ℕ) → (hc : r + c < S.count) → S.HasIndexThreeBlock r c →
      IntegerPresentation
        (SingularHomology {x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩)} 2) r c
  | 0, hc, _ => IntegerPresentation.ofEquiv (S.indexTwoBasis hf r hc htwo)
  | c + 1, hc, hthree =>
      let P := middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
      let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
      (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation hf.continuous
        (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2))

theorem middlePresentation_succ_map
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + (c + 1) < S.count)
    (hthree : S.HasIndexThreeBlock r (c + 1)) (v : Fin r → ℤ) :
    (S.middlePresentation hf r htwo (c + 1) hc hthree).map v =
      (S.data (S.point ⟨r + (c + 1), hc⟩)).lowerRealizationHomologyMap 2
        ((S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩
          ⟨r + (c + 1), hc⟩ rfl).homologyEquiv 2
            ((S.middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
              (S.indexThreeBlock_mono (Nat.le_succ c) hthree)).map v)) := rfl

theorem middlePresentation_succ_column_zero
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + (c + 1) < S.count)
    (hthree : S.HasIndexThreeBlock r (c + 1)) :
    (S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩
      ⟨r + (c + 1), hc⟩ rfl).homologyEquiv 2
        ((S.middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
          (S.indexThreeBlock_mono (Nat.le_succ c) hthree)).map
            ((S.middlePresentation hf r htwo (c + 1) hc hthree).columns 0)) =
      (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreeAttachingClass
        (S.indexThreeBlock_last r c hc hthree) := by
  let P := S.middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
    (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
  let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
  exact (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation_column_zero
    hf.continuous (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2))

theorem middlePresentation_succ_column_succ
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + (c + 1) < S.count)
    (hthree : S.HasIndexThreeBlock r (c + 1)) (i : Fin c) :
    (S.middlePresentation hf r htwo (c + 1) hc hthree).columns i.succ =
      (S.middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)).columns i := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
