import Wikipedia.NoExoticSixSphere.OrthogonalColumnBundle
import Wikipedia.NoExoticSixSphere.OrthogonalStabilization

/-!
# A column section gives a retraction of orthogonal stabilization

A global section moves the current column back to the distinguished one.
The actual constant-column coordinates then define a continuous retraction.
Composing a nullhomotopy with this retraction contracts the original family,
without imposing a stable-range dimension inequality.
-/

noncomputable section

namespace NoExoticSixSphere.OrthogonalColumnSection

open GLOrthonormalization OrthogonalPaths ColumnFiber OrthogonalStabilization

variable {r : ℕ} (v : UnitSphere (Vector (r + 1)))
  (s : C(UnitSphere (Vector (r + 1)), OrthogonalOperators (r + 1)))
  (hs : ∀ x, (s x).val.val v.val = x.val)

def corrected (a : OrthogonalOperators (r + 1)) : OrthogonalOperators (r + 1) :=
  mul (inverse (s (OrthogonalColumnBundle.projection v a))) a

include hs in
theorem corrected_column (a : OrthogonalOperators (r + 1)) :
    (corrected v s a).val.val v.val = v.val := by
  change (inverse (s (OrthogonalColumnBundle.projection v a))).val.val
    (OrthogonalColumnBundle.projection v a).val = v.val
  rw [← hs (OrthogonalColumnBundle.projection v a)]
  exact inverse_apply_self _ _

theorem continuous_corrected : Continuous (corrected v s) :=
  continuous_mul _ _
    (continuous_inverse _ (s.continuous.comp (OrthogonalColumnBundle.projection v).continuous))
    continuous_id

def retraction : C(OrthogonalOperators (r + 1), OrthogonalOperators r) :=
  ⟨fun a ↦ residual v v (corrected v s a) (corrected_column v s hs a),
    continuous_residual v v (corrected v s) (continuous_corrected v s)
      (corrected_column v s hs)⟩

variable (hbase : s v = identity (r + 1))

include hbase in
theorem retraction_stabilize (a : OrthogonalOperators r) :
    retraction v s hs (stabilize v a) = a := by
  have hp : OrthogonalColumnBundle.projection v (stabilize v a) = v :=
    Subtype.ext (stabilize_column v a)
  have hc : corrected v s (stabilize v a) = stabilize v a := by
    rw [corrected, hp, hbase, inverse_identity, identity_mul]
  change residual v v (corrected v s (stabilize v a))
    (corrected_column v s hs (stabilize v a)) = a
  simp only [hc]
  exact residual_reconstruct v v a

include hs hbase in
theorem nullhomotopic_of_stabilized {X : Type*} [TopologicalSpace X]
    (f : C(X, OrthogonalOperators r)) (c : OrthogonalOperators (r + 1))
    (h : (stabilizeMap v f).Homotopic (ContinuousMap.const X c)) :
    ∃ d, f.Homotopic (ContinuousMap.const X d) := by
  obtain ⟨H⟩ := h
  refine ⟨retraction v s hs c, ⟨{
    toContinuousMap := (retraction v s hs).comp H.toContinuousMap
    map_zero_left := ?_
    map_one_left := ?_
  }⟩⟩
  · intro x
    change retraction v s hs (H (0, x)) = f x
    rw [H.apply_zero]
    exact retraction_stabilize v s hs hbase (f x)
  · intro x
    change retraction v s hs (H (1, x)) = retraction v s hs c
    rw [H.apply_one]
    rfl

end NoExoticSixSphere.OrthogonalColumnSection
