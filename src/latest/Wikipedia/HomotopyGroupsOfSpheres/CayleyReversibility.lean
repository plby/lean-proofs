import Wikipedia.NoExoticSixSphere.CayleyInverse

/-!
# Cayley coordinates exchange anticommutation and reversibility

These identities are proved pointwise using the invertibility of `1 + A`.
They provide the restriction of Cayley coordinates to complex-structure loci.
-/

namespace Wikipedia.HomotopyGroupsOfSpheres.CayleyReversibility

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform
  NoExoticSixSphere.OrthogonalPaths

variable {n : ℕ}

theorem fraction_sandwich_of_anticommute (K : SkewOperators n)
    (Q : Vector n →L[ℝ] Vector n) (hQ : Q.comp K.val = -(K.val.comp Q)) :
    (fraction K.val).comp (Q.comp (fraction K.val)) = Q := by
  have hK := one_add_isInvertible K
  have hpoint (y : Vector n) : Q (K.val y) = -(K.val (Q y)) :=
    DFunLike.congr_fun hQ y
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hK.surjective x
  change fraction K.val (Q (fraction K.val ((1 + K.val) y))) = Q ((1 + K.val) y)
  rw [fraction_apply_one_add K.val hK]
  have hminus : Q ((1 - K.val) y) = (1 + K.val) (Q y) := by
    change Q (y - K.val y) = Q y + K.val (Q y)
    rw [map_sub, hpoint, sub_neg_eq_add]
  rw [hminus, fraction_apply_one_add K.val hK]
  change Q y - K.val (Q y) = Q (y + K.val y)
  rw [map_add, hpoint, sub_eq_add_neg]

theorem fraction_anticommute_of_reversible (a : OrthogonalOperators n)
    (Q : Vector n →L[ℝ] Vector n)
    (hQ : Q.comp a.val.val = (inverse a).val.val.comp Q)
    (ha : (1 + a.val.val).IsInvertible) :
    Q.comp (fraction a.val.val) = -((fraction a.val.val).comp Q) := by
  have hpoint (y : Vector n) : Q (a.val.val y) = (inverse a).val.val (Q y) :=
    DFunLike.congr_fun hQ y
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := ha.surjective x
  change Q (fraction a.val.val ((1 + a.val.val) y)) =
    -(fraction a.val.val (Q ((1 + a.val.val) y)))
  rw [fraction_apply_one_add a.val.val ha]
  have hplus : Q ((1 + a.val.val) y) = (1 + a.val.val) ((inverse a).val.val (Q y)) := by
    change Q (y + a.val.val y) =
      (inverse a).val.val (Q y) + a.val.val ((inverse a).val.val (Q y))
    rw [map_add, hpoint, self_apply_inverse]
    exact add_comm _ _
  rw [hplus, fraction_apply_one_add a.val.val ha]
  change Q (y - a.val.val y) =
    -((inverse a).val.val (Q y) - a.val.val ((inverse a).val.val (Q y)))
  rw [map_sub, hpoint, self_apply_inverse]
  abel

end Wikipedia.HomotopyGroupsOfSpheres.CayleyReversibility
