import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameStableRange

/-!
# The actual frame connecting bijection in degree zero

The positive-degree frame comparison does not include the endpoint at pi0.
Here two lifted loops whose orthogonal endpoints are joined are compared
directly in the simply connected total Stiefel space. The connecting map
therefore identifies pi1 of the balanced orbit with actual orthogonal path
components. No group structure on the native zeroth quotient is imposed.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.BalancedFrameComponents

open NoExoticSixSphere GLOrthonormalization CubeFirstCoordinate
open Wikipedia.HomotopyGroupsOfSpheres
open BalancedRealInvolutions FrameProjection

variable {n : ℕ} (A : Stiefel.Space (n + n) n)

theorem join_zero (u : Fin 1 → I) (v : Fin 0 → I) :
    join 0 (u 0, v) = u := by
  funext i
  have hi : i = 0 := by omega
  subst i
  rfl

theorem loops_homotopic_of_endpoints (hn : 1 < n)
    {p q : GenLoop (Fin 1) (BalancedRealInvolutions.Space n) (toBalanced A)}
    (L : CubeLift A p) (K : CubeLift A q)
    (h : GenLoop.Homotopic L.endpoint K.endpoint) : GenLoop.Homotopic p q := by
  obtain ⟨H⟩ := h
  let v : Fin 0 → I := fun i ↦ Fin.elim0 i
  let g := L.endpoint v
  let P : Path A (K.map (1, v)) := {
    toFun t := rightAction (L.map (t, v)) (g⁻¹ * H (t, v))
    continuous_toFun := continuous_rightAction.comp
      ((L.map.continuous.comp (continuous_id.prodMk continuous_const)).prodMk
        (continuous_const.mul
          (H.continuous.comp (continuous_id.prodMk continuous_const))))
    source' := by
      have hH : H (0, v) = g := H.apply_zero v
      rw [L.initial, hH, inv_mul_cancel, rightAction_one]
    target' := by
      have hH : H (1, v) = K.endpoint v := H.apply_one v
      rw [hH]
      have hL : rightAction A g = L.map (1, v) :=
        rightAction_coordinate A _ (L.endpoint_project v).symm
      rw [← hL, ← rightAction_mul, ← mul_assoc, mul_inv_cancel, one_mul]
      exact rightAction_coordinate A _ (K.endpoint_project v).symm }
  let Q : Path A (K.map (1, v)) := {
    toFun t := K.map (t, v)
    continuous_toFun := K.map.continuous.comp (continuous_id.prodMk continuous_const)
    source' := K.initial v
    target' := rfl }
  have hP (t : I) : toBalanced (P t) = p (join 0 (t, v)) :=
    (toBalanced_rightAction (L.map (t, v)) (g⁻¹ * H (t, v))).trans (L.project t v)
  have hQ (t : I) : toBalanced (Q t) = q (join 0 (t, v)) := K.project t v
  let := Stiefel.simplyConnectedSpace hn n
  obtain ⟨T⟩ := SimplyConnectedSpace.paths_homotopic P Q
  refine ⟨{
    toFun z := toBalanced (T (z.1, z.2 0))
    continuous_toFun := (FrameProjection.map n).continuous.comp
      (T.continuous.comp
        (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro u
    change toBalanced (T (0, u 0)) = p u
    exact (congrArg toBalanced (T.apply_zero (u 0))).trans
      ((hP (u 0)).trans (congrArg p (join_zero u v)))
  · intro u
    change toBalanced (T (1, u 0)) = q u
    exact (congrArg toBalanced (T.apply_one (u 0))).trans
      ((hQ (u 0)).trans (congrArg q (join_zero u v)))
  · intro t u hu
    obtain ⟨i, hi⟩ := hu
    have hi0 : i = 0 := Subsingleton.elim _ _
    subst i
    have hb : u 0 ∈ ({0, 1} : Set I) := hi
    change toBalanced (T (t, u 0)) = p u
    exact (congrArg toBalanced (T.eq_fst t hb)).trans
      ((hP (u 0)).trans (congrArg p (join_zero u v)))

theorem connecting_zero_injective (hn : 1 < n) :
    Function.Injective (connecting A 0) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      apply Quotient.sound
      apply loops_homotopic_of_endpoints A hn (chosenLift A p) (chosenLift A q)
      exact Quotient.exact hab

/-- This equivalence is literally the original lift-and-endpoint map. -/
def connectingZeroEquiv (hn : 1 < n) :
    π_ 1 (BalancedRealInvolutions.Space n) (toBalanced A) ≃
      π_ 0 (OrthogonalOperators n) 1 :=
  Equiv.ofBijective (connecting A 0)
    ⟨connecting_zero_injective A hn, connecting_surjective A (by omega)⟩

theorem connectingZeroEquiv_apply (hn : 1 < n)
    (c : π_ 1 (BalancedRealInvolutions.Space n) (toBalanced A)) :
    connectingZeroEquiv A hn c = connecting A 0 c := rfl

def balancedOrthogonalComponentsEquiv (n : ℕ) (hn : 1 < n) :
    π_ 1 (BalancedRealInvolutions.Space n) (BalancedRealInvolutions.standard n) ≃
      π_ 0 (OrthogonalOperators n) 1 :=
  (basepointEqMulEquiv (toBalanced_standardFrame n).symm).toEquiv.trans
    (connectingZeroEquiv (standardFrame n) hn)

end Wikipedia.HopfProblem.DegreeCollapse.BalancedFrameComponents
