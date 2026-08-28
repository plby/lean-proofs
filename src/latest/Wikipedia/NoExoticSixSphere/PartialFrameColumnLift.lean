import Wikipedia.NoExoticSixSphere.PartialFrameColumnFiber
import Wikipedia.NoExoticSixSphere.OrthogonalHomotopyLift

/-!
# Exact lifting of a partial-frame column homotopy

The already constructed orthogonal transport acts on every column of the
original partial frame. The lift preserves its initial family and is fixed
at every parameter where the prescribed column homotopy is stationary.
Consequently a homotopy making the first column constant gives a genuine
rank-reduced representative in its exact fiber.
-/

noncomputable section

open Set unitInterval

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {n r : ℕ}

theorem exists_columnHomotopyRel (v : UnitSphere (Vector r)) (a : C(X, Space n r))
    {g : C(X, UnitSphere (Vector n))} {S : Set X}
    (H : ((column v).comp a).HomotopyRel g S) :
    ∃ b : C(X, Space n r), ∃ G : a.HomotopyRel b S,
      ∀ t x, (column v (G (t, x))) = H (t, x) := by
  obtain ⟨R, hR0, hRcol, hRfix⟩ :=
    OrthogonalPaths.exists_columnTransport H.toHomotopy.toContinuousMap
  let F : C(I × X, Space n r) :=
    ⟨fun z ↦ action (R z) (a z.2), continuous_action R (fun z ↦ a z.2)
      R.continuous (a.continuous.comp continuous_snd)⟩
  let b : C(X, Space n r) :=
    ⟨fun x ↦ F (1, x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hF0 (x : X) : F (0, x) = a x := by
    change action (R (0, x)) (a x) = a x
    rw [hR0, action_identity]
  have hFfix (t : I) (x : X) (hx : x ∈ S) : F (t, x) = a x := by
    change action (R (t, x)) (a x) = a x
    rw [hRfix x (fun u ↦ (H.eq_fst u hx).trans (H.eq_fst 0 hx).symm) t,
      action_identity]
  let G : a.HomotopyRel b S := {
    toContinuousMap := F
    map_zero_left := hF0
    map_one_left := fun _ ↦ rfl
    prop' := hFfix }
  refine ⟨b, G, ?_⟩
  intro t x
  apply Subtype.ext
  change (R (t, x)).val.val ((a x).val v.val) = (H (t, x)).val
  have h0 : (a x).val v.val = (H (0, x)).val :=
    (congrArg Subtype.val (H.apply_zero x)).symm
  rw [h0]
  exact hRcol t x

theorem exists_fixed_column_representative (v : UnitSphere (Vector r))
    (c : UnitSphere (Vector n)) (a : C(X, Space n r))
    (H : ((column v).comp a).Homotopy (ContinuousMap.const X c)) :
    ∃ b : C(X, Space n r), a.Homotopic b ∧ ∀ x, (b x).val v.val = c.val := by
  let HR : ((column v).comp a).HomotopyRel (ContinuousMap.const X c) ∅ :=
    { H with prop' := fun _ _ hx ↦ hx.elim }
  obtain ⟨b, G, hG⟩ := exists_columnHomotopyRel v a HR
  refine ⟨b, ⟨G.toHomotopy⟩, ?_⟩
  intro x
  have h := hG 1 x
  rw [G.apply_one, HR.apply_one] at h
  exact congrArg Subtype.val h

theorem exists_rankReduction_of_column_homotopy
    (v : UnitSphere (Vector (r + 1))) (c : UnitSphere (Vector (n + 1)))
    (a : C(X, Space (n + 1) (r + 1)))
    (H : ((column v).comp a).Homotopy (ContinuousMap.const X c)) :
    ∃ q : C(X, Space n r), a.Homotopic ((ColumnFiber.reconstructionMap v c).comp q) := by
  obtain ⟨b, Hab, hb⟩ := exists_fixed_column_representative v c a H
  let q : C(X, Space n r) :=
    ⟨fun x ↦ ColumnFiber.residual v c (b x) (hb x),
      ColumnFiber.continuous_residual v c b b.continuous hb⟩
  have he : (ColumnFiber.reconstructionMap v c).comp q = b := by
    apply ContinuousMap.ext
    intro x
    exact ColumnFiber.reconstruct_residual v c (b x) (hb x)
  exact ⟨q, he.symm ▸ Hab⟩

end NoExoticSixSphere.Stiefel
