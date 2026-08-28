import Wikipedia.NoExoticSixSphere.QuaternionicHopfCubeBoundary

/-!
# The actual Hopf connecting map on native homotopy classes

Lift a homotopy of based cubes, fixing all side faces, and read its
terminal face in the original quaternionic fiber. Lift independence
then makes the boundary construction descend to Mathlib's quotient.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

open CubeFirstCoordinate

variable {n : ℕ}

theorem boundaryLoop_homotopic
    {p q : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (boundaryLoop p) (boundaryLoop q) := by
  obtain ⟨F⟩ := h
  let H : C(I × (I × (Fin n → I)), Sphere 4) := F.toContinuousMap.comp
    ⟨fun z ↦ (z.2.1, join n (z.1, z.2.2)),
      continuous_snd.fst.prodMk
        ((join n).continuous.comp (continuous_fst.prodMk continuous_snd.snd))⟩
  have hH₀ (z : I × (Fin n → I)) : H (0, z) = spherePole 4 := by
    change F (z.1, join n (0, z.2)) = spherePole 4
    have hb := (boundary_join_iff n (0, z.2)).mpr (Or.inl rfl)
    exact (F.eq_fst z.1 hb).trans (p.property _ hb)
  have hHb (t s : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
      H (t, (s, u)) = spherePole 4 := by
    have hb := (boundary_join_iff n (t, u)).mpr (Or.inr (Or.inr hu))
    exact (F.eq_fst s hb).trans (p.property _ hb)
  obtain ⟨L, hL₀, hLp, hLfix⟩ := exists_homotopy_lift H
    (ContinuousMap.const _ (spherePole 7)) (fun z ↦ sphereMap_pole.trans (hH₀ z).symm)
  have hLb (t s : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
      L (t, (s, u)) = spherePole 7 :=
    hLfix (s, u) (fun a ↦ (hHb a s u hu).trans (hH₀ (s, u)).symm) t
  let L₀ : CubeLift p := {
    map := L.comp ⟨fun z ↦ (z.1, (0, z.2)),
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩
    initial := fun u ↦ hL₀ (0, u)
    project := fun t u ↦ (hLp t (0, u)).trans (F.map_zero_left (join n (t, u)))
    boundary := fun t u hu ↦ hLb t 0 u hu }
  let L₁ : CubeLift q := {
    map := L.comp ⟨fun z ↦ (z.1, (1, z.2)),
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩
    initial := fun u ↦ hL₀ (1, u)
    project := fun t u ↦ (hLp t (1, u)).trans (F.map_one_left (join n (t, u)))
    boundary := fun t u hu ↦ hLb t 1 u hu }
  have hE (s : I) (u : Fin n → I) : sphereMap (L (1, (s, u))) = spherePole 4 := by
    have hb := (boundary_join_iff n (1, u)).mpr (Or.inr (Or.inl rfl))
    exact (hLp 1 (s, u)).trans ((F.eq_fst s hb).trans (p.property _ hb))
  let E : L₀.endpoint.val.HomotopyRel L₁.endpoint.val (Cube.boundary (Fin n)) := {
    toFun z := unitFiberCoordinate (L (1, z)) (hE z.1 z.2)
    continuous_toFun := continuous_unitFiberCoordinate
      (L.comp ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩)
        (fun z ↦ hE z.1 z.2)
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl
    prop' := fun s u hu ↦ by
      apply unitFiberPoint_injective
      change unitFiberPoint (unitFiberCoordinate (L (1, (s, u))) _) =
        unitFiberPoint (L₀.endpoint u)
      rw [unitFiberPoint_coordinate, L₀.endpoint_point]
      exact (hLb 1 s u hu).trans (hLb 1 0 u hu).symm }
  exact (boundaryLoop_homotopic_endpoint p L₀).trans
    ((show GenLoop.Homotopic L₀.endpoint L₁.endpoint from ⟨E⟩).trans
      (boundaryLoop_homotopic_endpoint q L₁).symm)

def connecting (n : ℕ) :
    HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4) →
      HomotopyGroup (Fin n) FiberGroup 1 :=
  Quotient.map boundaryLoop (fun _ _ h ↦ boundaryLoop_homotopic h)

theorem connecting_mk (p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) :
    connecting n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) =
      (⟦boundaryLoop p⟧ : HomotopyGroup (Fin n) FiberGroup 1) := rfl

theorem connecting_eq_endpoint
    (p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) (L : CubeLift p) :
    connecting n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) =
      (⟦L.endpoint⟧ : HomotopyGroup (Fin n) FiberGroup 1) :=
  Quotient.sound (boundaryLoop_homotopic_endpoint p L)

end NoExoticSixSphere.QuaternionicHopf
