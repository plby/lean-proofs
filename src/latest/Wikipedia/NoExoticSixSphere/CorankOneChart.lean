import Wikipedia.NoExoticSixSphere.CorankOneResidual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The open leading-block chart and its genuine rank-drop locus

The chart is open in the original operator-norm topology. Its singular locus
is the zero set of the smooth residual. There the actual kernel is a specified
one-dimensional graph, so the actual operator rank equals the leading rank.
-/

noncomputable section

open Set Function Module
open scoped ContDiff

namespace NoExoticSixSphere.CorankOne

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def chart : TopologicalSpace.Opens (BlockMap E F) :=
  ⟨{L | Injective (leading L)},
    ContinuousLinearMap.isOpen_injective.preimage
      (contDiff_leading (E := E) (F := F)).continuous⟩

theorem leading_invertible {L : BlockMap E F} (hL : L ∈ chart) :
    (leading L).IsInvertible := by
  have hi : Injective (leading L) := hL
  have hs : Surjective (leading L) :=
    (LinearMap.injective_iff_surjective (f := (leading L).toLinearMap)).mp hi
  exact ⟨(LinearEquiv.ofBijective (leading L).toLinearMap ⟨hi, hs⟩).toContinuousLinearEquiv,
    rfl⟩

theorem contDiffOn_residual : ContDiffOn ℝ ∞ (residual (E := E) (F := F))
    (chart (E := E) (F := F)) :=
  fun L hL ↦ (contDiffAt_residual L (leading_invertible hL)).contDiffWithinAt

theorem singular_iff_residual_zero {L : BlockMap E F} (hL : L ∈ chart) :
    ¬ Injective L ↔ residual L = 0 := by
  rw [injective_iff_residual_ne_zero L (leading_invertible hL), not_not]

theorem kernel_eq_span {L : BlockMap E F} (hL : L ∈ chart) (hr : residual L = 0) :
    L.ker = Submodule.span ℝ {(-(leading L).inverse (column L).1, (1 : ℝ))} := by
  ext v
  rcases v with ⟨x, t⟩
  change L (x, t) = 0 ↔ _
  simp only [kernel_iff L (leading_invertible hL), hr, smul_zero, and_true,
    Submodule.mem_span_singleton]
  constructor
  · intro hx
    refine ⟨t, ?_⟩
    apply Prod.ext
    · change t • (-(leading L).inverse (column L).1) = x
      rw [hx, smul_neg, neg_smul]
    · simp
  · rintro ⟨a, ha⟩
    have ht : a = t := by simpa using congrArg Prod.snd ha
    subst a
    have hx := congrArg Prod.fst ha
    simpa only [Prod.smul_fst, smul_neg, neg_smul] using hx.symm

theorem finrank_range_of_singular {L : BlockMap E F} (hL : L ∈ chart)
    (hr : residual L = 0) : finrank ℝ L.range = finrank ℝ E := by
  have hn : (-(leading L).inverse (column L).1, (1 : ℝ)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Prod.snd h)
  have h := L.toLinearMap.finrank_range_add_finrank_ker
  rw [kernel_eq_span hL hr, finrank_span_singleton hn, finrank_prod, finrank_self] at h
  omega

end NoExoticSixSphere.CorankOne
