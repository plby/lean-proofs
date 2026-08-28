import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBoundary

/-!
# The connecting map on native homotopy classes

Lifting a homotopy of based cubes proves that the last-face construction
descends to Mathlib's homotopy quotient. No generation or order assertion
is made here.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open NoExoticSixSphere.CubeFirstCoordinate

variable {n : ℕ}

theorem boundaryLoop_homotopic
    {p q : GenLoop (Fin (n + 1)) BaseSphere north} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (boundaryLoop p) (boundaryLoop q) := by
  obtain ⟨F⟩ := h
  let H : C(I × (I × (Fin n → I)), BaseSphere) := F.toContinuousMap.comp
    ⟨fun z => (z.2.1, join n (z.1, z.2.2)),
      continuous_snd.fst.prodMk
        ((join n).continuous.comp (continuous_fst.prodMk continuous_snd.snd))⟩
  have hH₀ (z : I × (Fin n → I)) : H (0, z) = north := by
    change F (z.1, join n (0, z.2)) = north
    have hb := (boundary_join_iff n (0, z.2)).mpr (Or.inl rfl)
    exact (F.eq_fst z.1 hb).trans (p.property _ hb)
  have hHb (t s : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
      H (t, (s, u)) = north := by
    have hb := (boundary_join_iff n (t, u)).mpr (Or.inr (Or.inr hu))
    exact (F.eq_fst s hb).trans (p.property _ hb)
  obtain ⟨L, hL₀, hLp, hLfix⟩ := exists_homotopy_lift H
    (ContinuousMap.const _ 1) (fun z => projection_one.trans (hH₀ z).symm)
  have hLb (t s : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
      L (t, (s, u)) = 1 :=
    hLfix (s, u) (fun a => (hHb a s u hu).trans (hH₀ (s, u)).symm) t
  let L₀ : CubeLift p := {
    map := L.comp ⟨fun z => (z.1, (0, z.2)),
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩
    initial := fun u => hL₀ (0, u)
    project := fun t u => (hLp t (0, u)).trans (F.map_zero_left (join n (t, u)))
    boundary := fun t u hu => hLb t 0 u hu }
  let L₁ : CubeLift q := {
    map := L.comp ⟨fun z => (z.1, (1, z.2)),
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩
    initial := fun u => hL₀ (1, u)
    project := fun t u => (hLp t (1, u)).trans (F.map_one_left (join n (t, u)))
    boundary := fun t u hu => hLb t 1 u hu }
  have hE (s : I) (u : Fin n → I) : L (1, (s, u)) ∈ northSubgroup := by
    change projection (L (1, (s, u))) = north
    have hb := (boundary_join_iff n (1, u)).mpr (Or.inr (Or.inl rfl))
    exact (hLp 1 (s, u)).trans ((F.eq_fst s hb).trans (p.property _ hb))
  let E : L₀.endpoint.val.HomotopyRel L₁.endpoint.val (Cube.boundary (Fin n)) := {
    toFun z := ⟨L (1, (z.1, z.2)), hE z.1 z.2⟩
    continuous_toFun :=
      (L.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
    map_zero_left := fun _ => rfl
    map_one_left := fun _ => rfl
    prop' := fun s u hu => Subtype.ext ((hLb 1 s u hu).trans (hLb 1 0 u hu).symm) }
  exact (boundaryLoop_homotopic_endpoint p L₀).trans
    ((show GenLoop.Homotopic L₀.endpoint L₁.endpoint from ⟨E⟩).trans
      (boundaryLoop_homotopic_endpoint q L₁).symm)

/-- The boundary construction on the actual cubical homotopy quotient. -/
def connecting (n : ℕ) :
    HomotopyGroup (Fin (n + 1)) BaseSphere north → HomotopyGroup (Fin n) northSubgroup 1 :=
  Quotient.map boundaryLoop (fun _ _ h => boundaryLoop_homotopic h)

theorem connecting_mk (p : GenLoop (Fin (n + 1)) BaseSphere north) :
    connecting n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) BaseSphere north) =
      (⟦boundaryLoop p⟧ : HomotopyGroup (Fin n) northSubgroup 1) := rfl

theorem connecting_eq_endpoint (p : GenLoop (Fin (n + 1)) BaseSphere north) (L : CubeLift p) :
    connecting n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) BaseSphere north) =
      (⟦L.endpoint⟧ : HomotopyGroup (Fin n) northSubgroup 1) :=
  Quotient.sound (boundaryLoop_homotopic_endpoint p L)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
