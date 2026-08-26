import ErdosProblems.Erdos327.Defs

namespace Erdos327

/-- The even-endpoint construction implies the all-endpoint density statement.

The loss from replacing `X` by `2 * (X / 2)` is absorbed by halving the
positive density gain.
-/
theorem erdos327Conclusion_of_evenEndpoint
    (h : EvenEndpointConclusion) : Erdos327Conclusion := by
  rcases h with ⟨η, hη, N₀, hN₀⟩
  obtain ⟨K, hK⟩ := exists_nat_ge (4 * (1 + η) / η)
  refine ⟨η / 4, by positivity, max (2 * N₀) K, ?_⟩
  intro X hX
  have htwoN₀ : 2 * N₀ ≤ X :=
    le_trans (le_max_left (2 * N₀) K) hX
  have hhalfN₀ : N₀ ≤ X / 2 := by omega
  rcases hN₀ (X / 2) hhalfN₀ with ⟨A, hA, hAdm, hcard⟩
  refine ⟨A, ?_, hAdm, ?_⟩
  · intro a ha
    have ha' := (mem_upto.mp (hA ha))
    apply mem_upto.mpr
    constructor
    · exact ha'.1
    · have hdouble : 2 * (X / 2) ≤ X := by omega
      exact le_trans ha'.2 hdouble
  · have hKX_nat : K ≤ X :=
      le_trans (le_max_right (2 * N₀) K) hX
    have hKX : (K : ℝ) ≤ (X : ℝ) := by exact_mod_cast hKX_nat
    have hscale : 4 * (1 + η) ≤ η * (X : ℝ) := by
      have hdiv : 4 * (1 + η) / η ≤ (X : ℝ) :=
        le_trans hK hKX
      simpa [mul_comm] using (div_le_iff₀ hη).mp hdiv
    have hfloorNat : X ≤ 2 * (X / 2) + 1 := by omega
    have hfloorCast :
        (X : ℝ) / 2 - 1 ≤ ((X / 2 : ℕ) : ℝ) := by
      have hfloorCast' :
          (X : ℝ) ≤ 2 * ((X / 2 : ℕ) : ℝ) + 1 := by
        exact_mod_cast hfloorNat
      linarith
    calc
      (1 / 2 + η / 4) * (X : ℝ)
          ≤ (1 + η) * ((X : ℝ) / 2 - 1) := by
              nlinarith
      _ ≤ (1 + η) * ((X / 2 : ℕ) : ℝ) := by
              gcongr
      _ ≤ (A.card : ℝ) := hcard

end Erdos327
