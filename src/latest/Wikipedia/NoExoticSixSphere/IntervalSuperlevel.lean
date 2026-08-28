import Wikipedia.NoExoticSixSphere.SuperlevelNormalForm
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A common half-space atlas for a cylinder with two endpoints

For positive height `h`, the superlevel of `t * (h - t)` is exactly the
closed interval cylinder. Its differential is nonzero at both endpoints,
so the regular-superlevel construction applies in the original product atlas.
-/

noncomputable section

open Function Set Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntervalSuperlevel

variable {M : Type*}

def level (h : ℝ) (p : M × ℝ) : ℝ := p.2 * (h - p.2)

theorem nonneg_iff {h : ℝ} (hh : 0 < h) (p : M × ℝ) :
    0 ≤ level h p ↔ p.2 ∈ Icc 0 h := by
  change 0 ≤ p.2 * (h - p.2) ↔ 0 ≤ p.2 ∧ p.2 ≤ h
  constructor
  · intro hp
    constructor
    · by_contra ht
      have ht' : p.2 < 0 := lt_of_not_ge ht
      have hn := mul_neg_of_neg_of_pos ht' (sub_pos.mpr (ht'.trans hh))
      exact (not_lt_of_ge hp) hn
    · by_contra ht
      have ht' : h < p.2 := lt_of_not_ge ht
      have hn := mul_neg_of_pos_of_neg (hh.trans ht') (sub_neg.mpr ht')
      exact (not_lt_of_ge hp) hn
  · rintro ⟨ht, ht'⟩
    exact mul_nonneg ht (sub_nonneg.mpr ht')

theorem zero_iff (h : ℝ) (p : M × ℝ) : level h p = 0 ↔ p.2 = 0 ∨ p.2 = h := by
  simp only [level, mul_eq_zero, sub_eq_zero, eq_comm (a := h)]

variable {B H : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_level (h : ℝ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (level (M := M) h) :=
  ((contDiff_id.mul (contDiff_const.sub contDiff_id) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ t * (h - t))).contMDiff).comp contMDiff_snd

theorem mfderiv_level_apply (h : ℝ) (p : M × ℝ) (v : B × ℝ) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (level h) p v = (h - 2 * p.2) * v.2 := by
  have hd : HasDerivAt (fun t : ℝ ↦ t * (h - t)) (h - 2 * p.2) p.2 := by
    convert (hasDerivAt_id p.2).mul ((hasDerivAt_const p.2 h).sub (hasDerivAt_id p.2))
      using 1
    · rfl
    · rfl
    · rfl
    · change h - 2 * p.2 = 1 * (h - p.2) + p.2 * (0 - 1)
      ring
  have ht : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : M × ℝ → ℝ) p
      (ContinuousLinearMap.snd ℝ B ℝ) := hasMFDerivAt_snd p
  have he := (hd.hasFDerivAt.hasMFDerivAt.comp p ht).mfderiv
  change mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (level h) p = _ at he
  rw [he]
  change v.2 * (h - 2 * p.2) = (h - 2 * p.2) * v.2
  exact mul_comm _ _

theorem regular_zero {h : ℝ} (hh : 0 < h) {p : M × ℝ} (hp : level h p = 0) :
    Surjective (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (level h) p) := by
  have hn : h - 2 * p.2 ≠ 0 := by
    rcases (zero_iff h p).mp hp with ht | ht
    · rw [ht]
      simpa using ne_of_gt hh
    · rw [ht]
      linarith
  intro y
  change ℝ at y
  refine ⟨(0, y / (h - 2 * p.2)), ?_⟩
  rw [mfderiv_level_apply (I := I)]
  change (h - 2 * p.2) * (y / (h - 2 * p.2)) = y
  field_simp

variable [FiniteDimensional ℝ B] [I.Boundaryless] [IsManifold I ∞ M]

def superlevelAtlas {h : ℝ} (hh : 0 < h) (k : ℕ) (hd : finrank ℝ B = k) :
    SuperlevelAtlas (K := EuclideanSpace ℝ (Fin k)) (I.prod 𝓘(ℝ, ℝ)) (level (M := M) h) :=
  Classical.choice (nonempty_superlevelAtlas (contMDiff_level (I := I) (M := M) h)
    (fun _ hp ↦ regular_zero (I := I) hh hp) k (by
      rw [finrank_prod, finrank_self, hd, Nat.add_comm]))

end NoExoticSixSphere.IntervalSuperlevel
