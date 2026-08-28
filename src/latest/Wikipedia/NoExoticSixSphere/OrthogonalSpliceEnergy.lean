import Wikipedia.NoExoticSixSphere.OrthogonalAntipodalEnergy

/-!
# Energy across a single path splice

The derivative agrees with the corresponding smooth branch away from the
splice point. That single point does not affect the integral. Consequently
the actual ambient energy is the sum of the two branch energies, even
when the spliced path is not differentiable at the join.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalPathEnergy

open GLOrthonormalization HilbertSchmidt

variable {n : ℕ}

noncomputable def splice (A B : ℝ → Vector n →L[ℝ] Vector n) (c t : ℝ) :
    Vector n →L[ℝ] Vector n := if t ≤ c then A t else B t

theorem deriv_splice_left (A B : ℝ → Vector n →L[ℝ] Vector n) {c t : ℝ} (ht : t < c) :
    deriv (splice A B c) t = deriv A t := by
  have he : splice A B c =ᶠ[nhds t] A :=
    Filter.mem_of_superset (isOpen_Iio.mem_nhds ht) (fun s hs ↦ by
      change s < c at hs
      simp [splice, hs.le])
  exact he.deriv_eq

theorem deriv_splice_right (A B : ℝ → Vector n →L[ℝ] Vector n) {c t : ℝ} (ht : c < t) :
    deriv (splice A B c) t = deriv B t := by
  have he : splice A B c =ᶠ[nhds t] B :=
    Filter.mem_of_superset (isOpen_Ioi.mem_nhds ht) (fun s hs ↦ by
      change c < s at hs
      simp [splice, not_le.mpr hs])
  exact he.deriv_eq

theorem continuous_squareSpeed {A : ℝ → Vector n →L[ℝ] Vector n} (hA : ContDiff ℝ ∞ A) :
    Continuous (fun t ↦ squareNorm (deriv A t)) :=
  Continuous.comp (g := squareNorm (n := n)) (f := deriv A)
    (contDiff_squareNorm (n := n)).continuous (ContDiff.deriv' (n := ∞) hA).continuous

theorem energy_add {A : ℝ → Vector n →L[ℝ] Vector n} (hA : ContDiff ℝ ∞ A)
    (l c u : ℝ) : energy A l u = energy A l c + energy A c u :=
  (intervalIntegral.integral_add_adjacent_intervals
    ((continuous_squareSpeed hA).intervalIntegrable l c)
    ((continuous_squareSpeed hA).intervalIntegrable c u)).symm

theorem energy_splice {A B : ℝ → Vector n →L[ℝ] Vector n}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) {l c u : ℝ} (hlc : l ≤ c) (hcu : c ≤ u) :
    energy (splice A B c) l u = energy A l c + energy B c u := by
  have hL : IntervalIntegrable (fun t ↦ squareNorm (deriv (splice A B c) t))
      MeasureTheory.volume l c := by
    apply ((continuous_squareSpeed hA).intervalIntegrable l c).congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le hlc] at ht
    exact (congrArg squareNorm (deriv_splice_left A B ht.2)).symm
  have hR : IntervalIntegrable (fun t ↦ squareNorm (deriv (splice A B c) t))
      MeasureTheory.volume c u := by
    apply ((continuous_squareSpeed hB).intervalIntegrable c u).congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le hcu] at ht
    exact (congrArg squareNorm (deriv_splice_right A B ht.1)).symm
  have heL : energy (splice A B c) l c = energy A l c := by
    apply intervalIntegral.integral_congr_Ioo_of_le hlc
    intro t ht
    exact congrArg squareNorm (deriv_splice_left A B ht.2)
  have heR : energy (splice A B c) c u = energy B c u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hcu
    intro t ht
    exact congrArg squareNorm (deriv_splice_right A B ht.1)
  have he := (intervalIntegral.integral_add_adjacent_intervals hL hR).symm
  change energy (splice A B c) l u = energy (splice A B c) l c +
    energy (splice A B c) c u at he
  rw [heL, heR] at he
  exact he

end NoExoticSixSphere.OrthogonalPathEnergy
