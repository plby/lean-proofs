import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenMorseCancellation
import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseBirth

/-!
# A supported indexed birth in the original positive half

The actual native birth is performed in an original regular positive band.
Its two new critical values stay inside that same band, and every old
critical germ is retained. The proved positive-band replacement therefore
gives an excellent presentation of the SAME state, with its original
nonpositive germ, literal halves, zero fiber, and native boundary unchanged.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_positive_indexed_birth {l u : ℝ} (hl : 0 ≤ l)
    (hband : ∀ y, P.function y ∈ Icc l u → y ∉ criticalPoints (Vector 7) P.function)
    {x : S.Space} (hx : P.function x ∈ Ioo l u) {k : ℕ} (hk : k < 7) :
    ∃ (Q : S.ExcellentMorsePresentation) (p q : S.Space),
      P.function p ∈ Ioo l u ∧ P.function q ∈ Ioo l u ∧
      nativeMorseIndex (Vector 7) Q.function p = k ∧
      nativeMorseIndex (Vector 7) Q.function q = k + 1 ∧
      Q.function p < Q.function q ∧ Q.function p ∈ Ioo l u ∧ Q.function q ∈ Ioo l u ∧
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard + 2 ∧
      (∀ y, y ∈ criticalPoints (Vector 7) Q.function ↔
        y ∈ criticalPoints (Vector 7) P.function ∨ y = p ∨ y = q) ∧
      (∀ y, P.function y ∉ Ioo l u → Q.function =ᶠ[𝓝 y] P.function) ∧
      (∀ y ∈ criticalPoints (Vector 7) P.function, Q.function =ᶠ[𝓝 y] P.function) ∧
      (∀ y, S.time y ≤ 0 → Q.function =ᶠ[𝓝 y] P.function) ∧
      nativeMorseCount (Vector 7) Q.function k = nativeMorseCount (Vector 7) P.function k + 1 ∧
      nativeMorseCount (Vector 7) Q.function (k + 1) =
        nativeMorseCount (Vector 7) P.function (k + 1) + 1 ∧
      ∀ j, j ≠ k → j ≠ k + 1 →
        nativeMorseCount (Vector 7) Q.function j = nativeMorseCount (Vector 7) P.function j := by
  let U : Set S.Space := P.function ⁻¹' Ioo l u
  have hU : IsOpen U := isOpen_Ioo.preimage P.function.continuous
  obtain ⟨g, p, q, hg, hmg, hinjg, hpU, hqU, hip, hiq, hpq, hpval, hqval,
      hcount, hcrit, hexterior, hkeep, hcountk, hcountk', hother⟩ :=
    exists_excellent_indexed_morse_birth P.smooth P.morse P.distinct
      (fun y hy => hband y ⟨hy.1.le, hy.2.le⟩) hx
      (by simpa only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] using hk) hU hx
  have hvalues (y : S.Space) (hy : P.function y ∈ Icc l u)
      (hcy : y ∈ criticalPoints (Vector 7) g) : g y ∈ Ioo l u := by
    rcases (hcrit y).mp hcy with hold | rfl | rfl
    · exact (hband y hy hold).elim
    · exact hpval
    · exact hqval
  let Q := P.replacePositiveBandWithCriticalValues ⟨g, hg.continuous⟩ hg hmg hinjg hl
    hexterior hvalues
  refine ⟨Q, p, q, hpU, hqU, hip, hiq, hpq, hpval, hqval, hcount, hcrit,
    hexterior, hkeep, ?_, hcountk, hcountk', hother⟩
  intro y hy
  apply hexterior y
  intro h
  have hp : 0 < P.function y := hl.trans_lt h.1
  exact (not_lt_of_ge hy) ((P.positive_iff y).mp hp)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
