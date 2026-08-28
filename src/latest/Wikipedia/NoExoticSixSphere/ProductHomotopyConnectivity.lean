import Wikipedia.NoExoticSixSphere.InducedHomotopyMap
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Native product homotopy connectivity

Coordinate homotopies combine while fixing the same cube boundary. Thus
vanishing of the two native homotopy groups gives vanishing for the actual
product. The simple-connectivity statement similarly uses actual projected
path homotopies, not a replacement fundamental group.
-/

noncomputable section

namespace NoExoticSixSphere.HigherHomotopy

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (x : X) (y : Y)

theorem product_genLoop_homotopic {p q : GenLoop N (X × Y) (x, y)}
    (hx : GenLoop.Homotopic (genLoopMap ContinuousMap.fst rfl p)
      (genLoopMap ContinuousMap.fst rfl q))
    (hy : GenLoop.Homotopic (genLoopMap ContinuousMap.snd rfl p)
      (genLoopMap ContinuousMap.snd rfl q)) : GenLoop.Homotopic p q := by
  obtain ⟨H⟩ := hx
  obtain ⟨K⟩ := hy
  exact ⟨{ toFun := fun a ↦ (H a, K a)
           continuous_toFun := H.continuous.prodMk K.continuous
           map_zero_left := fun a ↦ Prod.ext (H.apply_zero a) (K.apply_zero a)
           map_one_left := fun a ↦ Prod.ext (H.apply_one a) (K.apply_one a)
           prop' := fun t a ha ↦ Prod.ext (H.eq_fst t ha) (K.eq_fst t ha) }⟩

theorem product_map_injective : Function.Injective
    (fun a : HomotopyGroup N (X × Y) (x, y) ↦
      (map (z := x) ContinuousMap.fst rfl a, map (z := y) ContinuousMap.snd rfl a)) := by
  intro a b h
  induction a using Quotient.inductionOn with
  | _ p =>
    induction b using Quotient.inductionOn with
    | _ q =>
      exact Quotient.sound (product_genLoop_homotopic x y
        (Quotient.exact (congrArg Prod.fst h)) (Quotient.exact (congrArg Prod.snd h)))

theorem subsingleton_product [Subsingleton (HomotopyGroup N X x)]
    [Subsingleton (HomotopyGroup N Y y)] : Subsingleton (HomotopyGroup N (X × Y) (x, y)) :=
  (product_map_injective (N := N) x y).subsingleton

theorem simplyConnected_product [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    SimplyConnectedSpace (X × Y) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro a γ
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic (γ.map continuous_fst) (Path.refl a.1)
  obtain ⟨K⟩ := SimplyConnectedSpace.paths_homotopic (γ.map continuous_snd) (Path.refl a.2)
  exact ⟨{ toFun := fun p ↦ (H p, K p)
           continuous_toFun := H.continuous.prodMk K.continuous
           map_zero_left := fun p ↦ Prod.ext (H.apply_zero p) (K.apply_zero p)
           map_one_left := fun p ↦ Prod.ext (H.apply_one p) (K.apply_one p)
           prop' := fun t p hp ↦ Prod.ext (H.eq_fst t hp) (K.eq_fst t hp) }⟩

end NoExoticSixSphere.HigherHomotopy
