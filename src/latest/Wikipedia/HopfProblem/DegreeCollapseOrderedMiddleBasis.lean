import Wikipedia.HopfProblem.DegreeCollapseIndexHomologyBasis
import Wikipedia.SmoothSixDPoincare.OrderedMiddlePresentation

/-!
# Coherent actual H3 bases along a native index-three prefix

The initial minimum disk has zero H3. The actual index-three maps preserve
vanishing of H2 along the entire prefix. Each
index-three handle therefore adds its actual integral collapse coordinate.
The recursive basis retains the original band and lower-realization maps.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f)

theorem upper_second_zero
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n < S.count)
    (hpre : S.HasIndexThreeBlock 0 n) :
    Subsingleton (SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n, hn⟩)} 2) := by
  induction n with
  | zero =>
    obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
    exact D.homology_subsingleton 2 (by norm_num)
  | succ n ih =>
    let : Subsingleton (SingularHomology
        {x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩)} 2) :=
      ih (Nat.lt_of_succ_lt hn) (S.indexThreeBlock_mono (Nat.le_succ n) hpre)
    let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
    let : Subsingleton (SingularHomology
        {x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) -
          (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2} 2) :=
      (B.homologyEquiv 2).surjective.subsingleton
    exact ((S.data (S.point ⟨n + 1, hn⟩)).indexThree_lowerRealization_surjective hf.continuous
      (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) (by change n + 1 ≤ 0 + (n + 1); omega))).subsingleton

def middleCollapseCoordinate
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n + 1 < S.count)
    (hpre : S.HasIndexThreeBlock 0 (n + 1)) :
    SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n + 1, hn⟩)} 3 →ₗ[ℤ] ℤ :=
  collapseCoordinate (S.data (S.point ⟨n + 1, hn⟩)) 1 hf.continuous
    (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) (by change n + 1 ≤ 0 + (n + 1); omega))

theorem middleBasis_step
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n + 1 < S.count)
    (hpre : S.HasIndexThreeBlock 0 (n + 1))
    (e : (Fin n → ℤ) ≃ₗ[ℤ]
      SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩)} 3) :
    let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
    ∃ H : (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n + 1, hn⟩)} 3,
      (∀ v, H (Fin.cons 0 v) =
        (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 3
          (B.homologyEquiv 3 (e v))) ∧
      ∀ v, middleCollapseCoordinate S hf n hn hpre (H v) = v 0 := by
  let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩)} 2) :=
    upper_second_zero S hf n (Nat.lt_of_succ_lt hn)
      (S.indexThreeBlock_mono (Nat.le_succ n) hpre)
  let : Subsingleton (SingularHomology
      {x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) -
        (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2} 2) :=
    (B.homologyEquiv 2).surjective.subsingleton
  exact exists_basis_extension (S.data (S.point ⟨n + 1, hn⟩)) 1 hf.continuous
    (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) (by change n + 1 ≤ 0 + (n + 1); omega))
    n (e.trans (B.homologyEquiv 3))

def middleBasis (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (n : ℕ) → (hn : n < S.count) → S.HasIndexThreeBlock 0 n →
      (Fin n → ℤ) ≃ₗ[ℤ] SingularHomology {x : M // f x ≤ S.upper (S.point ⟨n, hn⟩)} 3
  | 0, hn, _ => by
      let : Subsingleton (SingularHomology
          {x : M // f x ≤ S.upper (S.point ⟨0, hn⟩)} 3) := by
        obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
        exact D.homology_subsingleton 3 (by norm_num)
      exact LinearEquiv.ofSubsingleton _ _
  | n + 1, hn, hpre =>
      Classical.choose (middleBasis_step S hf n hn hpre
        (middleBasis hf n (Nat.lt_of_succ_lt hn)
          (S.indexThreeBlock_mono (Nat.le_succ n) hpre)))

theorem middleBasis_succ_old
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n + 1 < S.count)
    (hpre : S.HasIndexThreeBlock 0 (n + 1)) (v : Fin n → ℤ) :
    middleBasis S hf (n + 1) hn hpre (Fin.cons 0 v) =
      (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 3
        ((S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl).homologyEquiv 3
          (middleBasis S hf n (Nat.lt_of_succ_lt hn)
            (S.indexThreeBlock_mono (Nat.le_succ n) hpre) v)) :=
  (Classical.choose_spec (middleBasis_step S hf n hn hpre
    (middleBasis S hf n (Nat.lt_of_succ_lt hn)
      (S.indexThreeBlock_mono (Nat.le_succ n) hpre)))).1 v

theorem middleBasis_succ_coordinate
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ) (hn : n + 1 < S.count)
    (hpre : S.HasIndexThreeBlock 0 (n + 1)) (v : Fin (n + 1) → ℤ) :
    middleCollapseCoordinate S hf n hn hpre (middleBasis S hf (n + 1) hn hpre v) = v 0 := by
  rw [middleBasis]
  exact (Classical.choose_spec (middleBasis_step S hf n hn hpre
    (middleBasis S hf n (Nat.lt_of_succ_lt hn)
      (S.indexThreeBlock_mono (Nat.le_succ n) hpre)))).2 v

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleBasis
