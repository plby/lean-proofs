import ErdosProblems.Erdos964.ScalarSliceFaceError
import ErdosProblems.Erdos964.UniformSmallErrorLimit

/-!
# The limit of the exact prime-slice counts weighted by the scalar face
-/

namespace Erdos964

open Filter
open scoped Topology

theorem tendsto_scalarSliceFaceSum (m c K : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c)
    (hK : 1 ≤ K) (hKsize : 2 * m + c ≤ K ^ 2)
    (η β : ℝ) (hη : 0 < η) (hηβ : η < β) (hβ1 : β < 1) :
    Tendsto (fun t : ℕ => scalarSliceFaceSum η β m c K t * Real.log (t ^ 2 : ℕ) /
      (t ^ 2 : ℕ)) atTop (𝓝 ((m : ℝ) * scalarPrimeIntegral η β)) := by
  have hβ : 0 < β := hη.trans hηβ
  let E : ℕ → ℝ := fun t => scalarSliceFaceSum η β m c K t -
    (m : ℝ) * (t ^ 2 : ℕ) * scalarPrimeFaceSum η β K t
  let s : ℕ → ℝ := fun t => ((t ^ 2 : ℕ) : ℝ) / Real.log t
  obtain ⟨G, hG, herror⟩ := exists_scalar_slice_face_error m c K hm hc hK hKsize η β hη hβ
  have hs : ∀ᶠ t : ℕ in atTop, 0 < s t := by
    filter_upwards [eventually_ge_atTop 2] with t ht
    have hlogt : 0 < Real.log t := Real.log_pos (by exact_mod_cast (show 1 < t by omega))
    dsimp only [s]
    positivity
  have hsmall : Tendsto (fun t : ℕ => E t / s t) atTop (𝓝 0) := by
    apply tendsto_normalized_uniform_small_error E s G hG hs
    intro ε hε
    obtain ⟨T₀, hT₀, hT⟩ := herror ε hε
    exact eventually_atTop.mpr ⟨T₀, hT⟩
  have hmain := (tendsto_scalarPrimeFaceSum K hK η β hη hηβ hβ1).const_mul (m : ℝ)
  have h := (hsmall.const_mul 2).add hmain
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with t ht
  have hN : ((t ^ 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show (t ^ 2 : ℕ) ≠ 0 by positivity)
  have hlogt : Real.log t ≠ 0 := (Real.log_pos
    (by exact_mod_cast (show 1 < t by omega))).ne'
  have hlogN : Real.log (t ^ 2 : ℕ) = 2 * Real.log t := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  change 2 * (E t / s t) + (m : ℝ) *
    (Real.log (t ^ 2 : ℕ) * scalarPrimeFaceSum η β K t) = _
  dsimp only [E, s]
  rw [hlogN]
  field_simp
  ring

end Erdos964
