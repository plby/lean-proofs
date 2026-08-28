import Wikipedia.HomotopyGroupsOfSpheres.HopfBasedLifting

/-! # Injectivity of the Hopf map on the third homotopy group -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres

open HopfProblem HopfProblem.OrbitPair
open HopfProblem.SpecialPeriods HopfProblem.SpecialPeriods.Threefold
open HopfProblem.CuspCircleNormalTrivialization
open HopfProblem.SecondHurewicz

variable (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r) (hr : r < injectiveRadius)

include b hr₀ hr in
/-- A based three-cube lying in a Hopf fiber contracts, because that fiber is a circle. -/
theorem hopf_fiber_cube_nullhomotopic (v : NormalSphere r)
    (q : GenLoop (Fin 3) (NormalSphere r) v)
    (hq : ∀ u, sphereHopfMap r (q u) = sphereHopfMap r v) :
    GenLoop.Homotopic q GenLoop.const := by
  let e := hopfFiberHomeomorph b r hr₀ hr v
  let F : C(Fin 3 → I, {w : NormalSphere r // sphereHopfMap r w = sphereHopfMap r v}) :=
    ⟨fun u => ⟨q u, hq u⟩, q.val.continuous.subtype_mk _⟩
  have he₁ : e.symm ⟨v, rfl⟩ = 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hopfFiberHomeomorph_one b r hr₀ hr v).symm
  let g : GenLoop (Fin 3) Circle 1 :=
    ⟨(e.symm : C(_, _)).comp F, fun u hu => by
      change e.symm (F u) = 1
      have hF : F u = ⟨v, rfl⟩ := Subtype.ext (q.property u hu)
      rw [hF, he₁]⟩
  let k : C(Circle, NormalSphere r) := ⟨fun u => u • v, by fun_prop⟩
  have h := (circle_genLoop_nullhomotopic 1 1 g).comp_continuousMap k
  have hk : k.comp g.val = q.val := by
    apply ContinuousMap.ext
    intro u
    exact congrArg Subtype.val (e.apply_symm_apply (F u))
  have hk₁ : k.comp (GenLoop.const : GenLoop (Fin 3) Circle 1).val =
      (GenLoop.const : GenLoop (Fin 3) (NormalSphere r) v).val := by
    apply ContinuousMap.ext
    intro u
    exact one_smul Circle v
  change (k.comp g.val).HomotopicRel
    (k.comp (GenLoop.const : GenLoop (Fin 3) Circle 1).val) (Cube.boundary (Fin 3)) at h
  rwa [hk, hk₁] at h

include b hr₀ hr in
/-- If the Hopf projection of a based cube contracts, the original cube contracts. -/
theorem hopf_nullhomotopic_of_projection (v : NormalSphere r)
    (p : GenLoop (Fin 3) (NormalSphere r) v)
    (h : GenLoop.Homotopic (mapGenLoop (sphereHopfMap r) v p) GenLoop.const) :
    GenLoop.Homotopic p GenLoop.const := by
  obtain ⟨H⟩ := h
  obtain ⟨L, hL₀, hLp, hLfix⟩ := hopf_exists_homotopy_lift b r hr₀ hr H.toContinuousMap p.val
    (fun u => (H.map_zero_left u).symm)
  have hstationary (u : Fin 3 → I) (hu : u ∈ Cube.boundary (Fin 3)) (t : I) :
      H (t, u) = H (0, u) := (H.eq_fst t hu).trans (H.eq_fst 0 hu).symm
  have hboundary (t : I) (u : Fin 3 → I) (hu : u ∈ Cube.boundary (Fin 3)) :
      L (t, u) = v := (hLfix u (hstationary u hu) t).trans (p.property u hu)
  let q : GenLoop (Fin 3) (NormalSphere r) v :=
    ⟨L.comp ⟨fun u => (1, u), continuous_const.prodMk continuous_id⟩, hboundary 1⟩
  have hpq : GenLoop.Homotopic p q := ⟨{
    toContinuousMap := L
    map_zero_left := hL₀
    map_one_left := fun _ => rfl
    prop' := fun t u hu => hLfix u (hstationary u hu) t
  }⟩
  apply hpq.trans
  apply hopf_fiber_cube_nullhomotopic b r hr₀ hr v q
  intro u
  exact (hLp 1 u).trans (H.map_one_left u)

include b hr₀ hr in
/-- Injectivity of the induced map on Mathlib's third homotopy group. -/
theorem hopf_pi3_injective (v : NormalSphere r) :
    Function.Injective (map (N := Fin 3) (sphereHopfMap r) v) := by
  apply (injective_iff_map_eq_one (map (N := Fin 3) (sphereHopfMap r) v)).mpr
  intro a ha
  induction a using Quotient.inductionOn with
  | h p =>
    exact Quotient.sound (hopf_nullhomotopic_of_projection b r hr₀ hr v p (Quotient.exact ha))

/-- The Hopf map induces a genuine isomorphism between third homotopy groups. -/
def hopfPi3MulEquiv (v : NormalSphere r) :
    π_ 3 (NormalSphere r) v ≃* π_ 3 (MeridianSphere r) (sphereHopfMap r v) :=
  MulEquiv.ofBijective (map (N := Fin 3) (sphereHopfMap r) v)
    ⟨hopf_pi3_injective b r hr₀ hr v, hopf_pi3_surjective b r hr₀ hr v⟩

end Wikipedia.HomotopyGroupsOfSpheres
