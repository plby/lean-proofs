import Wikipedia.NoExoticSixSphere.PartialFrameColumnLift
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups

/-!
# Native homotopy groups below the complement dimension of partial frames

Apply the proved sphere contraction to the first column of a generalized
loop, lift that homotopy while fixing its whole cube boundary, and extract
the remaining frame in the orthogonal complements. Induction on the number
of columns contracts the original generalized loop relative to its boundary.

The conclusion concerns mathlib's actual cubical homotopy groups. In
particular the partial-frame spaces with three-dimensional complements have
trivial zeroth, first, and second homotopy groups. Their third group is not
computed here.
-/

noncomputable section

open Set
open scoped unitInterval

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

def pole (r : ℕ) : UnitSphere (Vector (r + 1)) :=
  Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)

def baseFrame (c : ℕ) : (r : ℕ) → Space (c + r) r
  | 0 => empty c
  | r + 1 => ColumnFiber.reconstruct (pole r) (pole (c + r)) (baseFrame c r)

instance nonempty_add (c r : ℕ) : Nonempty (Space (c + r) r) := ⟨baseFrame c r⟩

theorem genLoop_homotopic_const_of_lt {m c : ℕ} (hmc : m < c) (r : ℕ)
    (a : Space (c + r) r) (p : GenLoop (Fin m) (Space (c + r) r) a) :
    GenLoop.Homotopic p GenLoop.const := by
  induction r with
  | zero =>
    have he : p = GenLoop.const := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      exact Subsingleton.elim _ _
    rw [he]
  | succ r ih =>
    let v := pole r
    let b : Sphere (c + r) := column v a
    have hab : a.val v.val = b.val := rfl
    let cp : GenLoop (Fin m) (Sphere (c + r)) b :=
      ⟨(column v).comp p.val, fun x hx ↦ congrArg (column v) (p.property x hx)⟩
    obtain ⟨Hcol⟩ := genLoop_homotopic_const_of_homeomorph_sphere
      (by omega : m < c + r) (Homeomorph.refl (Sphere (c + r))) b cp
    obtain ⟨B, G, hG⟩ := exists_columnHomotopyRel v p.val Hcol
    have hB (x : Fin m → unitInterval) : (B x).val v.val = b.val := by
      have h := hG 1 x
      rw [G.apply_one, Hcol.apply_one] at h
      exact congrArg Subtype.val h
    have hBbd (x : Fin m → unitInterval) (hx : x ∈ Cube.boundary (Fin m)) : B x = a :=
      (G.apply_one x).symm.trans ((G.eq_fst 1 hx).trans (p.property x hx))
    let ar : Space (c + r) r := ColumnFiber.residual v b a hab
    let qC : C((Fin m → unitInterval), Space (c + r) r) :=
      ⟨fun x ↦ ColumnFiber.residual v b (B x) (hB x),
        ColumnFiber.continuous_residual v b B B.continuous hB⟩
    have hqbd (x : Fin m → unitInterval) (hx : x ∈ Cube.boundary (Fin m)) : qC x = ar := by
      change ColumnFiber.residual v b (B x) (hB x) = ColumnFiber.residual v b a hab
      apply Subtype.ext
      rw [ColumnFiber.residual_operator, ColumnFiber.residual_operator, hBbd x hx]
    let q : GenLoop (Fin m) (Space (c + r) r) ar := ⟨qC, hqbd⟩
    obtain ⟨Hq⟩ := ih ar q
    let R := ColumnFiber.reconstructionMap v b
    have hstart : R.comp q.val = B := by
      apply ContinuousMap.ext
      intro x
      exact ColumnFiber.reconstruct_residual v b (B x) (hB x)
    have hend : R.comp (GenLoop.const : GenLoop (Fin m) (Space (c + r) r) ar).val =
        (GenLoop.const : GenLoop (Fin m) (Space (c + (r + 1)) (r + 1)) a).val := by
      apply ContinuousMap.ext
      intro x
      exact ColumnFiber.reconstruct_residual v b a hab
    exact ⟨G.trans ((Hq.compContinuousMap R).cast hstart hend)⟩

theorem subsingleton_homotopyGroup_of_lt {m c : ℕ} (hmc : m < c) (r : ℕ)
    (a : Space (c + r) r) : Subsingleton (HomotopyGroup (Fin m) (Space (c + r) r) a) := by
  refine ⟨fun x y ↦ ?_⟩
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q =>
      exact Quotient.sound ((genLoop_homotopic_const_of_lt hmc r a p).trans
        (genLoop_homotopic_const_of_lt hmc r a q).symm)

theorem pathConnectedSpace {c : ℕ} (hc : 0 < c) (r : ℕ) :
    PathConnectedSpace (Space (c + r) r) := by
  let a := baseFrame c r
  let : Subsingleton (HomotopyGroup (Fin 0) (Space (c + r) r) a) :=
    subsingleton_homotopyGroup_of_lt hc r a
  let e : HomotopyGroup (Fin 0) (Space (c + r) r) a ≃ ZerothHomotopy (Space (c + r) r) :=
    HomotopyGroup.pi0EquivZerothHomotopy
  exact pathConnectedSpace_iff_zerothHomotopy.mpr
    ⟨⟨ZerothHomotopy.mk a⟩, e.symm.injective.subsingleton⟩

theorem simplyConnectedSpace {c : ℕ} (hc : 1 < c) (r : ℕ) :
    SimplyConnectedSpace (Space (c + r) r) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨pathConnectedSpace (by omega : 0 < c) r, ?_⟩
  intro a γ
  let : Subsingleton (HomotopyGroup (Fin 1) (Space (c + r) r) a) :=
    subsingleton_homotopyGroup_of_lt hc r a
  let e : HomotopyGroup (Fin 1) (Space (c + r) r) a ≃ FundamentalGroup (Space (c + r) r) a :=
    HomotopyGroup.pi1EquivFundamentalGroup
  have hs : Subsingleton (FundamentalGroup (Space (c + r) r) a) := e.symm.injective.subsingleton
  have he : (Path.Homotopic.Quotient.mk γ : FundamentalGroup (Space (c + r) r) a) =
      Path.Homotopic.Quotient.mk (Path.refl a) := @Subsingleton.elim _ hs _ _
  exact Path.Homotopic.Quotient.eq.mp he

end NoExoticSixSphere.Stiefel
