import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalCorrection
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalCutoff

/-!
# Adding one solved equation to a local primitive

This is the induction step of the local Dolbeault lemma.  It subtracts
the already constructed actual differential, integrates one residual
coefficient, and preserves every previously solved equation.
-/

noncomputable section

open Complex Set Metric
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

theorem extend_partial_primitive
    {S : Finset (Fin 3)} {j : Fin 3} (hj : j ∉ S)
    {f : Fin 3 → Coordinates → ℂ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : Coordinates) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hclosed : IsClosedOn f (polydisc ∅ x r R))
    {u : Coordinates → ℂ} (hu : ContDiff ℝ ∞ u)
    (heq : ∀ q ∈ polydisc S x r R, ∀ i ∈ S, coordinateDbar i u q = f i q) :
    ∃ v : Coordinates → ℂ, ContDiff ℝ ∞ v ∧
      ∀ q ∈ polydisc (insert j S) x r R, ∀ i ∈ insert j S,
        coordinateDbar i v q = f i q := by
  obtain ⟨χ, hχ, hcχ, hχone, hχsupport⟩ := exists_coordinate_cutoff (x j) hr hrR
  let g := subtractDbar f u
  have hg : ∀ i, ContDiff ℝ ∞ (g i) := contDiff_subtractDbar hf hu
  have hgclosed : IsClosedOn g (polydisc ∅ x r R) :=
    isClosedOn_subtractDbar hf hu hclosed
  have hgzero : ∀ i ∈ S, ∀ q ∈ polydisc S x r R, g i q = 0 := by
    intro i hi q hq
    change f i q - coordinateDbar i u q = 0
    rw [heq q hq i hi, sub_self]
  let a := coordinateCorrection j χ (g j)
  have ha : ContDiff ℝ ∞ a := contDiff_coordinateCorrection j hχ hcχ (hg j)
  refine ⟨fun q => u q + a q, hu.add ha, ?_⟩
  intro q hq i hi
  rw [coordinateDbar_add i (hu.differentiable (by simp) q)
    (ha.differentiable (by simp) q)]
  rcases Finset.mem_insert.mp hi with hij | hi
  · subst i
    have hqj : q j ∈ ball (x j) r := by
      simpa only [Finset.mem_insert_self, if_true, mem_ball] using hq j
    have hsolve : coordinateDbar j a q = g j q := by
      rw [coordinateDbar_coordinateCorrection_self j hχ hcχ (hg j) q,
        hχone (q j) hqj, one_mul]
    rw [hsolve]
    change coordinateDbar j u q + (f j q - coordinateDbar j u q) = f j q
    ring
  · have hpreserve : coordinateDbar i a q = 0 :=
      coordinateCorrection_preserves_zero hj hrR.le hχ hcχ hχsupport
        hg hgclosed hgzero hq hi
    rw [hpreserve, add_zero]
    exact heq q (polydisc_mono (Finset.subset_insert j S) x hrR.le hq) i hi

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
