import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleNormalization
import Mathlib.Topology.Homotopy.Product
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Actual first-homology additivity for pointwise sums of based maps

The addition statement comes from a homotopy between concatenated product
loops and their pointwise product. It concerns the original first
singular-homology map, not an abstract coordinate assignment.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

theorem loopHomologyClass_add_zero {G : Type} [TopologicalSpace G]
    [AddCommGroup G] [IsTopologicalAddGroup G] (p q : Path (0 : G) 0) :
    loopHomologyClass (p.add q) = loopHomologyClass p + loopHomologyClass q := by
  have hp : (p.prod (Path.refl (0 : G))).map continuous_add =
      p.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply,
      Path.cast_coe, add_zero]
  have hq : ((Path.refl (0 : G)).prod q).map continuous_add =
      q.cast (add_zero 0) (add_zero 0) := by
    ext t
    simp only [Path.map_coe, Function.comp_apply, Path.prod_coe, Path.refl_apply,
      Path.cast_coe, zero_add]
  have h : ((p.prod (Path.refl (0 : G))).trans
      ((Path.refl (0 : G)).prod q)).Homotopic (p.prod q) := by
    rw [Path.trans_prod_eq_prod_trans]
    exact ⟨Path.Homotopic.prodHomotopy (Path.Homotopy.transRefl p)
      (Path.Homotopy.reflTrans q)⟩
  have he := loopHomologyClass_homotopic
    (h.map (⟨fun x : G × G => x.1 + x.2, continuous_add⟩ : C(G × G, G)))
  rw [Path.map_trans, loopHomologyClass_trans, hp, hq] at he
  exact he.symm

/-- Pointwise addition of original based maps induces addition on native first homology. -/
theorem inducedH1_add_of_zero {X G : Type} [TopologicalSpace X]
    [PathConnectedSpace X] [TopologicalSpace G] [AddCommGroup G]
    [IsTopologicalAddGroup G] (f g : C(X, G)) (b : X)
    (hf : f b = 0) (hg : g b = 0) :
    inducedHomology (f + g) = inducedHomology f + inducedHomology g := by
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective b a
  let pf : Path (0 : G) 0 := (p.map f.continuous).cast hf.symm hf.symm
  let pg : Path (0 : G) 0 := (p.map g.continuous).cast hg.symm hg.symm
  have h : p.map (f + g).continuous =
      (pf.add pg).cast (by simp only [ContinuousMap.add_apply, hf, hg])
        (by simp only [ContinuousMap.add_apply, hf, hg]) := by
    ext t
    rfl
  simp only [LinearMap.add_apply, inducedHomology_loopHomologyClass]
  rw [h]
  exact loopHomologyClass_add_zero pf pg

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
