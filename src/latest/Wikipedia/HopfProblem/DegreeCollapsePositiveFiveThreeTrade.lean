import Wikipedia.HopfProblem.DegreeCollapseNegatedTwoFourTrade

/-!
# The supported five-to-three trade on the same original positive half

Negate the actual two-to-four trade back to the original presentation.
The intrinsic native indices reflect in dimension seven. The total count
is unchanged, index-five count drops by one, index-three count rises by
one, and all other indexed counts remain unchanged. The entire original
nonpositive germ and both original atlases are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] [Subsingleton (SingularHomology B 2)]
  {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_positive_five_to_three_handle_trade
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hmaximum : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → 0 < P.function q →
      nativeMorseIndex (Vector 7) P.function p = 7 →
      nativeMorseIndex (Vector 7) P.function q = 7 → p = q)
    (hnosix : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      nativeMorseIndex (Vector 7) P.function p ≠ 6)
    (p₀ : criticalPoints (Vector 7) P.function) (hp₀ : 0 < P.function p₀)
    (hindex₀ : nativeMorseIndex (Vector 7) P.function p₀ = 5) :
    ∃ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard ∧
      nativeMorseCount (Vector 7) Q.function 5 + 1 =
        nativeMorseCount (Vector 7) P.function 5 ∧
      nativeMorseCount (Vector 7) Q.function 3 =
        nativeMorseCount (Vector 7) P.function 3 + 1 ∧
      (∀ j, j ≠ 5 → j ≠ 3 → nativeMorseCount (Vector 7) Q.function j =
        nativeMorseCount (Vector 7) P.function j) ∧
      ∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function := by
  classical
  obtain ⟨h, hh, hmh, hinjh, hcard, htwo, hfour, hother, hkeep, hcut⟩ :=
    P.exists_negated_two_to_four_handle_trade horder hmaximum hnosix p₀ hp₀ hindex₀
  let Q := P.replaceByNegatedSublevel h hh hmh hinjh hkeep hcut
  have hQcount (j : ℕ) (hj : j ≤ 7) :
      nativeMorseCount (Vector 7) Q.function j = nativeMorseCount (Vector 7) h (7 - j) := by
    change nativeMorseCount (Vector 7) (fun x => -h x) j = _
    have hid : 7 - (7 - j) = j := by omega
    have he := nativeMorseCount_neg hh hmh (k := 7 - j)
      (by simpa only [finrank_euclideanSpace_fin] using Nat.sub_le 7 j)
    simpa only [finrank_euclideanSpace_fin, hid] using he
  have hPcount (j : ℕ) (hj : j ≤ 7) :
      nativeMorseCount (Vector 7) (fun x => -P.function x) (7 - j) =
        nativeMorseCount (Vector 7) P.function j := by
    simpa only [finrank_euclideanSpace_fin] using
      nativeMorseCount_neg P.smooth P.morse (k := j) (by simpa using hj)
  have hlarge (u : S.Space → ℝ) (j : ℕ) (hj : 7 < j) :
      nativeMorseCount (Vector 7) u j = 0 := by
    unfold nativeMorseCount
    have hempty : {z | z ∈ criticalPoints (Vector 7) u ∧
        nativeMorseIndex (Vector 7) u z = j} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨_, hz⟩
      have hb := nativeMorseIndex_le (E := Vector 7) (f := u) (p := z)
      simp only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] at hb hz
      omega
    rw [hempty, Set.ncard_empty]
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · change (criticalPoints (Vector 7) (fun x => -h x)).ncard = _
    rw [criticalPoints_neg]
    exact hcard.trans (congrArg Set.ncard (criticalPoints_neg (E := Vector 7) P.function))
  · rw [hQcount 5 (by decide), ← hPcount 5 (by decide)]
    exact htwo
  · rw [hQcount 3 (by decide), ← hPcount 3 (by decide)]
    exact hfour
  · intro j hj5 hj3
    by_cases hj : j ≤ 7
    · rw [hQcount j hj, ← hPcount j hj]
      exact hother (7 - j) (by omega) (by omega)
    · rw [hlarge Q.function j (lt_of_not_ge hj), hlarge P.function j (lt_of_not_ge hj)]
  · intro x hx
    have hpx : P.function x ≤ 0 :=
      le_of_not_gt (fun h => (not_lt_of_ge hx) ((P.positive_iff x).mp h))
    change (fun y => -h y) =ᶠ[𝓝 x] P.function
    filter_upwards [hkeep x (neg_nonneg.mpr hpx)] with y hy
    simp only [hy, neg_neg]

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
