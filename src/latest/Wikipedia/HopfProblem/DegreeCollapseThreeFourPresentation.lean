import Wikipedia.HopfProblem.DegreeCollapseOrderedMiddleBasis
import Wikipedia.HopfProblem.DegreeCollapseIndexFourRelation
import Wikipedia.SmoothSixDPoincare.IntegerPresentationMatrix

/-!
# The retained integral presentation for a native three/four handle prefix

The actual first minimum and index-three prefix supply a coherent H3
basis. Each index-four handle adjoins its original attaching class through
the genuine intervening band map. All preceding columns and maps remain.
The resulting matrix has image exactly the kernel of this native map.
The block arrangement and terminal H3 vanishing are explicit hypotheses;
no geometric cancellation or realization of matrix operations is inferred.
-/

noncomputable section

open Set Function Topology ContinuousMap
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.ThreeFourPresentation

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f)

def HasIndexFourBlock (r c : ℕ) : Prop :=
  ∀ i : Fin S.count, r < i.val → i.val ≤ r + c →
    Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates = 4

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem indexFourBlock_mono {r c b : ℕ} (hcb : c ≤ b) (h : HasIndexFourBlock S r b) :
    HasIndexFourBlock S r c :=
  fun i hri hic => h i hri (hic.trans (Nat.add_le_add_left hcb r))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem indexFourBlock_last (r c : ℕ) (hc : r + (c + 1) < S.count)
    (h : HasIndexFourBlock S r (c + 1)) :
    Module.finrank ℝ (S.data (S.point ⟨r + (c + 1), hc⟩)).chart.NegativeCoordinates = 4 :=
  h ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl

def presentation (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (r : ℕ) (hthree : S.HasIndexThreeBlock 0 r) :
    (c : ℕ) → (hc : r + c < S.count) → HasIndexFourBlock S r c →
      IntegerPresentation
        (SingularHomology {x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩)} 3) r c
  | 0, hc, _ => IntegerPresentation.ofEquiv (MiddleBasis.middleBasis S hf r hc hthree)
  | c + 1, hc, hfour =>
      let P := presentation hf r hthree c (Nat.lt_of_succ_lt hc)
        (indexFourBlock_mono S (Nat.le_succ c) hfour)
      let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
      IndexFour.indexFourPresentation (S.data (S.point ⟨r + (c + 1), hc⟩)) hf.continuous
        (indexFourBlock_last S r c hc hfour) (P.transport (B.homologyEquiv 3))

theorem presentation_succ_map
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (hthree : S.HasIndexThreeBlock 0 r) (hc : r + (c + 1) < S.count)
    (hfour : HasIndexFourBlock S r (c + 1)) (v : Fin r → ℤ) :
    (presentation S hf r hthree (c + 1) hc hfour).map v =
      (S.data (S.point ⟨r + (c + 1), hc⟩)).lowerRealizationHomologyMap 3
        ((S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩
          ⟨r + (c + 1), hc⟩ rfl).homologyEquiv 3
            ((presentation S hf r hthree c (Nat.lt_of_succ_lt hc)
              (indexFourBlock_mono S (Nat.le_succ c) hfour)).map v)) := rfl

theorem presentation_succ_column_zero
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (hthree : S.HasIndexThreeBlock 0 r) (hc : r + (c + 1) < S.count)
    (hfour : HasIndexFourBlock S r (c + 1)) :
    (S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩
      ⟨r + (c + 1), hc⟩ rfl).homologyEquiv 3
        ((presentation S hf r hthree c (Nat.lt_of_succ_lt hc)
          (indexFourBlock_mono S (Nat.le_succ c) hfour)).map
            ((presentation S hf r hthree (c + 1) hc hfour).columns 0)) =
      IndexFour.indexFourAttachingClass (S.data (S.point ⟨r + (c + 1), hc⟩))
        (indexFourBlock_last S r c hc hfour) := by
  let P := presentation S hf r hthree c (Nat.lt_of_succ_lt hc)
    (indexFourBlock_mono S (Nat.le_succ c) hfour)
  let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
  exact IndexFour.indexFourPresentation_column_zero (S.data (S.point ⟨r + (c + 1), hc⟩))
    hf.continuous (indexFourBlock_last S r c hc hfour) (P.transport (B.homologyEquiv 3))

theorem presentation_succ_column_succ
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (hthree : S.HasIndexThreeBlock 0 r) (hc : r + (c + 1) < S.count)
    (hfour : HasIndexFourBlock S r (c + 1)) (i : Fin c) :
    (presentation S hf r hthree (c + 1) hc hfour).columns i.succ =
      (presentation S hf r hthree c (Nat.lt_of_succ_lt hc)
        (indexFourBlock_mono S (Nat.le_succ c) hfour)).columns i := rfl

def matrix (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (hthree : S.HasIndexThreeBlock 0 r) (hc : r + c < S.count)
    (hfour : HasIndexFourBlock S r c) : Matrix (Fin r) (Fin c) ℤ :=
  (presentation S hf r hthree c hc hfour).matrix

theorem matrix_image_eq_kernel
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (hthree : S.HasIndexThreeBlock 0 r) (hc : r + c < S.count)
    (hfour : HasIndexFourBlock S r c) :
    range (matrix S hf r c hthree hc hfour).mulVec =
      (LinearMap.ker (presentation S hf r hthree c hc hfour).map : Set (Fin r → ℤ)) :=
  (presentation S hf r hthree c hc hfour).matrix_image_eq_kernel

theorem matrix_surjective_of_upper_third_zero
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (hthree : S.HasIndexThreeBlock 0 r) (hc : r + c < S.count)
    (hfour : HasIndexFourBlock S r c)
    [Subsingleton (SingularHomology {x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩)} 3)] :
    Surjective (matrix S hf r c hthree hc hfour).mulVec :=
  (presentation S hf r hthree c hc hfour).matrix_surjective_of_subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.ThreeFourPresentation
