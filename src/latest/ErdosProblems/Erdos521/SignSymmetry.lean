/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Sign symmetry and the negative-endpoint version of the proved endpoint bound.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointLimit
import ErdosProblems.Erdos521.CoefficientProbability

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem signLaw_map_neg : signLaw.map (fun x : ℝ ↦ -x) = signLaw := by
  rw [signLaw_eq_diracs, Measure.map_add _ _ measurable_neg,
    Measure.map_smul, Measure.map_smul]
  rw [Measure.map_dirac' measurable_neg, Measure.map_dirac' measurable_neg, neg_neg]
  exact add_comm _ _

theorem signLaw_map_mul {u : ℝ} (hu : u = 1 ∨ u = -1) :
    signLaw.map (fun x ↦ u * x) = signLaw := by
  rcases hu with rfl | rfl
  · simp
  · simpa only [neg_one_mul] using signLaw_map_neg

def alternateSigns (ε : ℕ → ℝ) (k : ℕ) : ℝ := (-1) ^ k * ε k

theorem measurable_alternateSigns : Measurable alternateSigns := by
  fun_prop [alternateSigns]

theorem measurePreserving_alternateSigns : MeasurePreserving alternateSigns sequenceLaw sequenceLaw := by
  refine ⟨measurable_alternateSigns, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ ↦ signLaw)).map (fun ε i ↦ (-1 : ℝ) ^ i * ε i) =
    Measure.infinitePi (fun _ : ℕ ↦ signLaw)
  rw [Measure.infinitePi_map_pi (fun _ : ℕ ↦ signLaw) (f := fun i x ↦ (-1 : ℝ) ^ i * x)
    (fun _ ↦ measurable_const.mul measurable_id)]
  congr 1
  funext i
  exact signLaw_map_mul (neg_one_pow_eq_or ℝ i)

theorem powerSum_alternateSigns (ε : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    powerSum (alternateSigns ε) n x = powerSum ε n (-x) := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp [alternateSigns]
  rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
  ring

theorem mem_realRoots_alternateSigns (ε : ℕ → ℝ) (n : ℕ) (hε : ε 0 ≠ 0) (x : ℝ) :
    x ∈ realRoots (alternateSigns ε) n ↔ -x ∈ realRoots ε n := by
  have hε' : alternateSigns ε 0 ≠ 0 := by simpa only [alternateSigns, pow_zero, one_mul] using hε
  rw [mem_realRoots _ _ hε', mem_realRoots _ _ hε, powerSum_alternateSigns]

theorem intervalRootCount_alternateSigns (ε : ℕ → ℝ) (n : ℕ) (hε : ε 0 ≠ 0) (l u : ℝ) :
    intervalRootCount (alternateSigns ε) n l u = intervalRootCount ε n (-u) (-l) := by
  classical
  have hset : ((realRoots (alternateSigns ε) n).filter fun x ↦ x ∈ Set.Icc l u) =
      ((realRoots ε n).filter fun x ↦ x ∈ Set.Icc (-u) (-l)).image (fun x ↦ -x) := by
    ext x
    simp only [Finset.mem_filter, mem_realRoots_alternateSigns ε n hε, Finset.mem_image]
    constructor
    · rintro ⟨hroot, hlo, hhi⟩
      exact ⟨-x, ⟨hroot, by constructor <;> linarith⟩, neg_neg x⟩
    · rintro ⟨y, ⟨hroot, hlo, hhi⟩, rfl⟩
      exact ⟨by simpa only [neg_neg] using hroot, by constructor <;> linarith⟩
  unfold intervalRootCount
  rw [hset, Finset.card_image_of_injective _ neg_injective]

theorem ae_negativeEndpointRootCount_div_log_tendsto_zero {C : ℝ} (hC : 0 ≤ C) :
    ∀ᵐ ε ∂sequenceLaw,
      Tendsto (fun n : ℕ ↦ (intervalRootCount ε n (-1) (-endpointCenter C n) : ℝ) / Real.log n)
        atTop (𝓝 0) := by
  have h := measurePreserving_alternateSigns.quasiMeasurePreserving.ae
    (ae_endpointRootCount_div_log_tendsto_zero hC)
  filter_upwards [h, ae_sequence_signs] with ε hε hsign
  have hε₀ : ε 0 ≠ 0 := by rcases hsign 0 with h | h <;> simp [h]
  simpa only [intervalRootCount_alternateSigns ε _ hε₀] using hε

end Erdos521
