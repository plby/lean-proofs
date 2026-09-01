/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterRank

/-!
# Resonant kernel frequencies of a typical rotation
-/

open Set Function MeasureTheory Metric
open scoped BigOperators

namespace Erdos984

noncomputable section

/-- Embed a kernel digit into the larger alphabet used in the exceptional
rotation union bound. -/
def kernelDigitToHunterFrequency (D : ℕ) (hD : 0 < D)
    (q : HunterKernelDigit (hunterKernelPower D)) :
    HunterFrequencyAlphabet D :=
  ⟨q.val + (hunterFrequencyBound D - hunterKernelPower D), by
    have hk := hunterKernelPower_le_frequencyBound D hD
    have hq := q.isLt
    omega⟩

lemma decode_kernelDigitToHunterFrequency (D : ℕ) (hD : 0 < D)
    (q : HunterKernelDigit (hunterKernelPower D)) :
    decodeHunterFrequency D (kernelDigitToHunterFrequency D hD q) =
      decodeKernelDigit (hunterKernelPower D) q := by
  have hk := hunterKernelPower_le_frequencyBound D hD
  change ((q.val + (hunterFrequencyBound D - hunterKernelPower D) : ℕ) : ℤ) -
      hunterFrequencyBound D = (q.val : ℤ) - hunterKernelPower D
  rw [Nat.cast_add, Nat.cast_sub hk]
  ring

def kernelTupleToHunterFrequency (D : ℕ) (hD : 0 < D)
    (q : Fin (hunterRankWitness D) →
      Fin D → HunterKernelDigit (hunterKernelPower D)) :
    Fin (hunterRankWitness D) → Fin D → HunterFrequencyAlphabet D :=
  fun r j ↦ kernelDigitToHunterFrequency D hD (q r j)

lemma decoded_kernelTupleToHunterFrequency (D : ℕ) (hD : 0 < D)
    (q : Fin (hunterRankWitness D) →
      Fin D → HunterKernelDigit (hunterKernelPower D)) :
    decodedFrequency (decodeHunterFrequency D)
        (kernelTupleToHunterFrequency D hD q) =
      fun r ↦ kernelFrequency (hunterKernelPower D) (q r) := by
  funext r j
  exact decode_kernelDigitToHunterFrequency D hD (q r j)

/-- Kernel digits whose character has small phase at the given step. -/
def hunterResonantDigits (D : ℕ) (theta : UnitAddTorus (Fin D)) (d : ℕ) :
    Finset (Fin D → HunterKernelDigit (hunterKernelPower D)) :=
  Finset.univ.filter fun q ↦
    ‖integerCharacter (kernelFrequency (hunterKernelPower D) q) (d • theta)‖ ≤
      hunterPhaseTolerance D

lemma mem_hunterResonantDigits_iff (D : ℕ)
    (theta : UnitAddTorus (Fin D)) (d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    q ∈ hunterResonantDigits D theta d ↔
      ‖integerCharacter (kernelFrequency (hunterKernelPower D) q) (d • theta)‖ ≤
        hunterPhaseTolerance D := by
  simp [hunterResonantDigits]

lemma finrank_resonant_lt_rankWitness
    (D : ℕ) (hD : 4 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta)
    {d : ℕ} (hd : 0 < d) (hdN : d < hunterN D) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun q : ↑(hunterResonantDigits D theta d) ↦
        fun j ↦ (decodeKernelDigit (hunterKernelPower D) (q.1 j) : ℝ))) <
      hunterRankWitness D := by
  classical
  let S := hunterResonantDigits D theta d
  let v : ↑S → Fin D → ℝ := fun q j ↦
    (decodeKernelDigit (hunterKernelPower D) (q.1 j) : ℝ)
  let m := Module.finrank ℝ (Submodule.span ℝ (Set.range v))
  by_contra hnot
  have hrm : hunterRankWitness D ≤ m := by
    simpa [m, v, S] using Nat.le_of_not_gt hnot
  obtain ⟨f, hfmem, _hfspan, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range v)
  let emb : Fin (hunterRankWitness D) → Fin m := fun i ↦
    ⟨i, lt_of_lt_of_le i.isLt hrm⟩
  have hemb : Function.Injective emb := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin m ↦ z.val) hij
  have hex : ∀ r : Fin (hunterRankWitness D),
      ∃ q : ↑S, v q = f (emb r) := by
    intro r
    simpa only [Set.mem_range] using hfmem (emb r)
  choose q hq using hex
  have hqli : LinearIndependent ℝ (fun r ↦ v (q r)) := by
    have hcomp := hfind.comp emb hemb
    have heq : (fun r ↦ v (q r)) = f ∘ emb := by
      funext r
      exact hq r
    rw [heq]
    exact hcomp
  obtain ⟨sigma, hsigma⟩ :=
    exists_ne_zero_coordinate_minor (fun r ↦ v (q r)) hqli
  let qdigits : Fin (hunterRankWitness D) →
      Fin D → HunterKernelDigit (hunterKernelPower D) := fun r ↦ (q r).1
  have hdet : (integerCharacterMinorRealMatrix
      (fun r ↦ kernelFrequency (hunterKernelPower D) (qdigits r)) sigma).det ≠ 0 := by
    change (Matrix.of fun r c ↦
      ((decodeKernelDigit (hunterKernelPower D) ((q r).1 (sigma c)) : ℤ) : ℝ)).det ≠ 0
    simpa [v] using hsigma
  let n : Fin (hunterN D) := ⟨d - 1, by omega⟩
  have hbad := htheta n (kernelTupleToHunterFrequency D (by omega) qdigits)
    sigma
  rw [decoded_kernelTupleToHunterFrequency D (by omega) qdigits] at hbad
  apply hbad hdet
  rw [Metric.mem_closedBall, dist_zero_right]
  let _ : Nonempty (Fin (hunterRankWitness D)) :=
    ⟨⟨0, by simp [hunterRankWitness]⟩⟩
  rw [pi_norm_le_iff_of_nonempty]
  intro r
  rw [nsmulIntegerCharacterTuple_apply]
  have hn : (n : ℕ) + 1 = d := by
    dsimp [n]
    omega
  rw [hn]
  change ‖d • integerCharacter
    (kernelFrequency (hunterKernelPower D) (qdigits r)) theta‖ ≤ _
  rw [← map_nsmul]
  exact (mem_hunterResonantDigits_iff D theta d (qdigits r)).mp (q r).2

/-- The resonant digit set has the cardinality of a box in fewer than
`hunterRankWitness D` coordinates. -/
lemma card_hunterResonantDigits_le
    (D : ℕ) (hD : 4 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta)
    {d : ℕ} (hd : 0 < d) (hdN : d < hunterN D) :
    (hunterResonantDigits D theta d).card ≤
      (2 * hunterKernelPower D + 1) ^ hunterRankWitness D := by
  let S := hunterResonantDigits D theta d
  have hcard := finite_box_card_le_pow_finrank
    (D := Fin D) (Q := HunterKernelDigit (hunterKernelPower D))
    (decodeKernelDigit (hunterKernelPower D))
    (decodeKernelDigit_injective (hunterKernelPower D)) S
  have hrank := finrank_resonant_lt_rankWitness D hD htheta hd hdN
  calc
    S.card ≤ (2 * hunterKernelPower D + 1) ^
        Module.finrank ℝ (Submodule.span ℝ
          (Set.range fun q : ↑S ↦
            fun j ↦ (decodeKernelDigit (hunterKernelPower D) (q.1 j) : ℝ))) := by
      simpa only [Fintype.card_fin] using hcard
    _ ≤ (2 * hunterKernelPower D + 1) ^ hunterRankWitness D := by
      exact Nat.pow_le_pow_right (by positivity) hrank.le

end

end Erdos984
