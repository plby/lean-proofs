import ErdosProblems.Erdos1148.ZetaCharacterHyperbolaEstimate
import Mathlib.Topology.Order.IntermediateValue

/-! # Small real Dirichlet values force a zero below one -/

namespace Erdos1148.DukeArithmetic

open Set

theorem exists_realDirichlet_zero_of_nonpos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hnonpos : realDirichletValue χ s ≤ 0) :
    ∃ β : ℝ, s ≤ β ∧ β < 1 ∧ realDirichletValue χ β = 0 := by
  have hcont : ContinuousOn (realDirichletValue χ) (Icc s 1) :=
    continuousOn_of_forall_continuousAt (fun x hx =>
      realDirichletValue_continuousAt χ hχ (hs.trans_le hx.1))
  obtain ⟨β, hβ, hzero⟩ := intermediate_value_Icc hs1.le hcont
    (show (0 : ℝ) ∈ Icc (realDirichletValue χ s) (realDirichletValue χ 1) from
      ⟨hnonpos, (realDirichletValue_one_pos χ hχ).le⟩)
  refine ⟨β, hβ.1, lt_of_le_of_ne hβ.2 ?_, hzero⟩
  intro heq
  subst β
  exact (realDirichletValue_one_ne_zero χ hχ) hzero

theorem realDirichlet_lower_bound_or_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) (hs1 : s < 1)
    {N : ℕ} (hN : 0 < N)
    (herror : 12 * ((q : ℝ) / (1 - s)) * (N : ℝ) ^ (1 - 2 * s) ≤ 1 / 2) :
    (1 - s) / (2 * ((N * N : ℕ) : ℝ) ^ (1 - s)) ≤ realDirichletValue χ 1 ∨
      ∃ β : ℝ, s ≤ β ∧ β < 1 ∧ realDirichletValue χ β = 0 := by
  by_cases hLs : 0 ≤ realDirichletValue χ s
  · left
    have hd : 0 < 1 - s := by linarith
    have hNX : 1 ≤ N * N := Nat.mul_pos hN hN
    have hsum := one_le_weighted_realZetaConvolution χ s hNX
    have h := (realZetaConvolution_hyperbola_error_le χ hχ hs hs1 hN).trans herror
    rw [Real.norm_eq_abs] at h
    have herr := (le_abs_self _).trans h
    have hsign : realZetaRegularized s * realDirichletValue χ s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (realZetaRegularized_neg hs hs1).le hLs
    have hmain : (1 : ℝ) / 2 ≤
        (((N * N : ℕ) : ℝ) ^ (1 - s) * realDirichletValue χ 1) / (1 - s) := by
      rw [← div_mul_eq_mul_div]
      linarith
    have hm := (le_div_iff₀ hd).mp hmain
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((N * N : ℕ) : ℝ) ^ (1 - s))).mpr
    nlinarith
  · exact Or.inr (exists_realDirichlet_zero_of_nonpos χ hχ hs hs1 (le_of_not_ge hLs))

end Erdos1148.DukeArithmetic
