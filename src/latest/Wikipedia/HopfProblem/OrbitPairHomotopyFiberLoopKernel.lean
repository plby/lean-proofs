import Wikipedia.HopfProblem.OrbitPairHomotopyFiberLoopInclusion

/-!
# Exactness at the actual homotopy fibre

Transport along a relative nullhomotopy of the projection makes that projection
constant. The endpoint family is then exactly in the native loop-space image.
The transport fixes constant based parameters, hence all generalized-loop faces.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

open NoExoticSixSphere

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem exists_loopFamily_of_projection_nullhomotopy (f : C(X, Y)) (x : X)
    (p : C(Z, Space f (f x))) (S : Set Z) (hp : ∀ z ∈ S, p z = basepoint f x)
    (H : ((projection f (f x)).comp p).HomotopyRel (ContinuousMap.const _ x) S) :
    ∃ q : C(Z, Path (f x) (f x)), (∀ z ∈ S, q z = Path.refl (f x)) ∧
      Nonempty (p.HomotopyRel ((loopInclusion f x).comp q) S) := by
  let Q := transport f (f x) p H.toContinuousMap H.apply_zero
  let qend : C(Z, Space f (f x)) :=
    Q.comp ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩
  have hqend : ∀ z, projection f (f x) (qend z) = x := H.apply_one
  let q := loopFamily f x qend hqend
  have hq : (loopInclusion f x).comp q = qend := loopInclusion_loopFamily f x qend hqend
  let G : p.HomotopyRel ((loopInclusion f x).comp q) S := {
    toContinuousMap := Q
    map_zero_left := transport_initial f (f x) p H.toContinuousMap H.apply_zero
    map_one_left := fun z ↦ (ContinuousMap.congr_fun hq z).symm
    prop' := by
      intro t z hz
      have hH (s : unitInterval) : H (s, z) = x := by
        have he := H.eq_fst s hz
        change H (s, z) = projection f (f x) (p z) at he
        rw [hp z hz] at he
        exact he
      exact (transport_fixed_basepoint f x p H.toContinuousMap H.apply_zero
        z (hp z hz) hH t).trans (hp z hz).symm }
  refine ⟨q, ?_, ⟨G⟩⟩
  intro z hz
  apply loopInclusion_injective f x
  exact (G.fst_eq_snd hz).symm.trans ((hp z hz).trans (loopInclusion_base f x).symm)

theorem exists_loopGenLoop_of_projection_nullhomotopy (f : C(X, Y)) (x : X)
    (p : GenLoop N (Space f (f x)) (basepoint f x))
    (H : ((projection f (f x)).comp p.val).HomotopyRel
      (ContinuousMap.const _ x) (Cube.boundary N)) :
    ∃ q : GenLoop N (Path (f x) (f x)) (Path.refl (f x)),
      GenLoop.Homotopic p (HigherHomotopy.genLoopMap (loopInclusion f x)
        (loopInclusion_base f x) q) := by
  obtain ⟨q, hq, G⟩ := exists_loopFamily_of_projection_nullhomotopy f x p.val
    (Cube.boundary N) p.property H
  exact ⟨⟨q, hq⟩, G⟩

theorem projection_eq_const_iff_exists_loop_class (f : C(X, Y)) (x : X)
    (c : HomotopyGroup N (Space f (f x)) (basepoint f x)) :
    HigherHomotopy.map (projection f (f x)) rfl c =
      (Quotient.mk' GenLoop.const : HomotopyGroup N X x) ↔
        ∃ q : HomotopyGroup N (Path (f x) (f x)) (Path.refl (f x)),
          HigherHomotopy.map (loopInclusion f x) (loopInclusion_base f x) q = c := by
  constructor
  · refine Quotient.inductionOn c ?_
    intro p hp
    obtain ⟨H⟩ := Quotient.exact hp
    obtain ⟨q, hq⟩ := exists_loopGenLoop_of_projection_nullhomotopy f x p H
    exact ⟨Quotient.mk' q, Quotient.sound hq.symm⟩
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn q ?_
    intro q
    rfl

theorem loopInclusion_range_eq_projection_ker [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (x : X) :
    (HigherHomotopy.mapMonoidHom (N := N) (loopInclusion f x)
      (loopInclusion_base f x)).range =
        (HigherHomotopy.mapMonoidHom (N := N) (projection f (f x)) rfl).ker := by
  ext c
  exact (projection_eq_const_iff_exists_loop_class f x c).symm

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
