import Wikipedia.NoExoticSixSphere.HigherCubeCircleExtension
import Wikipedia.HomotopyGroupsOfSpheres.HopfInjectivity

/-!
# The original Hopf projection induces all higher native isomorphisms

The existing compact homotopy lifts retain every stationary parameter.
The exact higher-cube circle extension makes those lifts based. A lifted
nullhomotopy ends in the actual circle fiber, whose native higher groups
vanish. Thus the ORIGINAL Hopf sphere map induces native isomorphisms in
all degrees at least three, not just its previously checked third group.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HomotopyGroupsOfSpheres
open Wikipedia.HopfProblem Wikipedia.HopfProblem.OrbitPair
open Wikipedia.HopfProblem.SpecialPeriods Wikipedia.HopfProblem.SpecialPeriods.Threefold
open Wikipedia.HopfProblem.CuspCircleNormalTrivialization
open Wikipedia.HopfProblem.SecondHurewicz

namespace NoExoticSixSphere.HigherHopf

variable (b : RiemannSphere) (r : ℝ) (hr₀ : 0 < r) (hr : r < injectiveRadius)

include b hr₀ hr in
theorem based_cube_lift (n : ℕ) (v : NormalSphere r)
    (p : GenLoop (Fin (n + 3)) (MeridianSphere r) (sphereHopfMap r v)) :
    ∃ q : GenLoop (Fin (n + 3)) (NormalSphere r) v,
      mapGenLoop (sphereHopfMap r) v q = p := by
  let H : C(I × (Fin (n + 3) → I), MeridianSphere r) :=
    ⟨fun tu ↦ p (fun i ↦ tu.1 * tu.2 i), by fun_prop⟩
  have hp₀ : p.val 0 = sphereHopfMap r v := p.property 0 ⟨0, Or.inl rfl⟩
  obtain ⟨L, _, hLp, _⟩ := hopf_exists_homotopy_lift b r hr₀ hr H
    (ContinuousMap.const _ v) (fun u ↦ by simpa [H, Pi.zero_def] using hp₀.symm)
  let F : C(Fin (n + 3) → I, NormalSphere r) :=
    L.comp ⟨fun u ↦ (1, u), continuous_const.prodMk continuous_id⟩
  have hF (u : Fin (n + 3) → I) : sphereHopfMap r (F u) = p u := by
    simpa [F, H] using hLp 1 u
  let e := hopfFiberHomeomorph b r hr₀ hr v
  let g₀ : C(Cube.boundary (Fin (n + 3)),
      {w : NormalSphere r // sphereHopfMap r w = sphereHopfMap r v}) := {
    toFun u := ⟨F u.val, (hF u.val).trans (p.property u.val u.property)⟩
    continuous_toFun := (F.continuous.comp continuous_subtype_val).subtype_mk _ }
  let g : C(Cube.boundary (Fin (n + 3)), Circle) := (e.symm : C(_, _)).comp g₀
  obtain ⟨G, hG⟩ := boundary_circle_extension n g
  have hcorrection (u : Fin (n + 3) → I) (hu : u ∈ Cube.boundary (Fin (n + 3))) :
      G u • v = F u := by
    rw [hG ⟨u, hu⟩]
    exact congrArg Subtype.val (e.apply_symm_apply (g₀ ⟨u, hu⟩))
  let q : GenLoop (Fin (n + 3)) (NormalSphere r) v :=
    ⟨⟨fun u ↦ (G u)⁻¹ • F u, by fun_prop⟩, fun u hu ↦ by
      change (G u)⁻¹ • F u = v
      rw [← hcorrection u hu, inv_smul_smul]⟩
  refine ⟨q, ?_⟩
  apply GenLoop.ext
  intro u
  exact (sphereHopfMap_smul r (G u)⁻¹ (F u)).trans (hF u)

include b hr₀ hr in
theorem pi_surjective (n : ℕ) (v : NormalSphere r) :
    Function.Surjective (map (N := Fin (n + 3)) (sphereHopfMap r) v) := by
  intro a
  induction a using Quotient.inductionOn with
  | h p =>
    obtain ⟨q, hq⟩ := based_cube_lift b r hr₀ hr n v p
    refine ⟨⟦q⟧, ?_⟩
    change (⟦mapGenLoop (sphereHopfMap r) v q⟧ :
      π_ (n + 3) (MeridianSphere r) (sphereHopfMap r v)) = ⟦p⟧
    rw [hq]

include b hr₀ hr in
theorem fiber_cube_nullhomotopic (n : ℕ) (v : NormalSphere r)
    (q : GenLoop (Fin (n + 3)) (NormalSphere r) v)
    (hq : ∀ u, sphereHopfMap r (q u) = sphereHopfMap r v) :
    GenLoop.Homotopic q GenLoop.const := by
  let e := hopfFiberHomeomorph b r hr₀ hr v
  let F : C(Fin (n + 3) → I, {w : NormalSphere r // sphereHopfMap r w = sphereHopfMap r v}) :=
    ⟨fun u ↦ ⟨q u, hq u⟩, q.val.continuous.subtype_mk _⟩
  have he₁ : e.symm ⟨v, rfl⟩ = 1 := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hopfFiberHomeomorph_one b r hr₀ hr v).symm
  let g : GenLoop (Fin (n + 3)) Circle 1 :=
    ⟨(e.symm : C(_, _)).comp F, fun u hu ↦ by
      change e.symm (F u) = 1
      have hF : F u = ⟨v, rfl⟩ := Subtype.ext (q.property u hu)
      rw [hF, he₁]⟩
  let k : C(Circle, NormalSphere r) := ⟨fun u ↦ u • v, by fun_prop⟩
  have h := (circle_genLoop_nullhomotopic (n + 1) 1 g).comp_continuousMap k
  have hk : k.comp g.val = q.val := by
    apply ContinuousMap.ext
    intro u
    exact congrArg Subtype.val (e.apply_symm_apply (F u))
  have hk₁ : k.comp (GenLoop.const : GenLoop (Fin (n + 3)) Circle 1).val =
      (GenLoop.const : GenLoop (Fin (n + 3)) (NormalSphere r) v).val := by
    apply ContinuousMap.ext
    intro u
    exact one_smul Circle v
  change (k.comp g.val).HomotopicRel
    (k.comp (GenLoop.const : GenLoop (Fin (n + 3)) Circle 1).val)
      (Cube.boundary (Fin (n + 3))) at h
  rwa [hk, hk₁] at h

include b hr₀ hr in
theorem nullhomotopic_of_projection (n : ℕ) (v : NormalSphere r)
    (p : GenLoop (Fin (n + 3)) (NormalSphere r) v)
    (h : GenLoop.Homotopic (mapGenLoop (sphereHopfMap r) v p) GenLoop.const) :
    GenLoop.Homotopic p GenLoop.const := by
  obtain ⟨H⟩ := h
  obtain ⟨L, hL₀, hLp, hLfix⟩ := hopf_exists_homotopy_lift b r hr₀ hr H.toContinuousMap p.val
    (fun u ↦ (H.map_zero_left u).symm)
  have hstationary (u : Fin (n + 3) → I) (hu : u ∈ Cube.boundary (Fin (n + 3))) (t : I) :
      H (t, u) = H (0, u) := (H.eq_fst t hu).trans (H.eq_fst 0 hu).symm
  have hboundary (t : I) (u : Fin (n + 3) → I) (hu : u ∈ Cube.boundary (Fin (n + 3))) :
      L (t, u) = v := (hLfix u (hstationary u hu) t).trans (p.property u hu)
  let q : GenLoop (Fin (n + 3)) (NormalSphere r) v :=
    ⟨L.comp ⟨fun u ↦ (1, u), continuous_const.prodMk continuous_id⟩, hboundary 1⟩
  have hpq : GenLoop.Homotopic p q := ⟨{
    toContinuousMap := L
    map_zero_left := hL₀
    map_one_left := fun _ ↦ rfl
    prop' := fun t u hu ↦ hLfix u (hstationary u hu) t }⟩
  apply hpq.trans
  apply fiber_cube_nullhomotopic b r hr₀ hr n v q
  intro u
  exact (hLp 1 u).trans (H.map_one_left u)

include b hr₀ hr in
theorem pi_injective (n : ℕ) (v : NormalSphere r) :
    Function.Injective (map (N := Fin (n + 3)) (sphereHopfMap r) v) := by
  apply (injective_iff_map_eq_one (map (N := Fin (n + 3)) (sphereHopfMap r) v)).mpr
  intro a ha
  induction a using Quotient.inductionOn with
  | h p =>
    exact Quotient.sound
      (nullhomotopic_of_projection b r hr₀ hr n v p (Quotient.exact ha))

def piMulEquiv (n : ℕ) (v : NormalSphere r) :
    π_ (n + 3) (NormalSphere r) v ≃*
      π_ (n + 3) (MeridianSphere r) (sphereHopfMap r v) :=
  MulEquiv.ofBijective (map (N := Fin (n + 3)) (sphereHopfMap r) v)
    ⟨pi_injective b r hr₀ hr n v, pi_surjective b r hr₀ hr n v⟩

theorem piMulEquiv_apply (n : ℕ) (v : NormalSphere r) (c : π_ (n + 3) (NormalSphere r) v) :
    piMulEquiv b r hr₀ hr n v c =
      map (N := Fin (n + 3)) (sphereHopfMap r) v c := rfl

theorem piMulEquiv_zero (v : NormalSphere r) :
    piMulEquiv b r hr₀ hr 0 v = hopfPi3MulEquiv b r hr₀ hr v := by
  apply MulEquiv.ext
  intro c
  rfl

end NoExoticSixSphere.HigherHopf
