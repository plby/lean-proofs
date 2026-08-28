import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorBoundary

/-!
# The spinor connecting map on native homotopy classes

Homotopies of based cubes lift as compact families. Taking their last faces
in circle coordinates shows that the boundary construction descends to
the native homotopy quotient.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.RankSixComplexProjection.SpinorFibration

open NoExoticSixSphere.CubeFirstCoordinate

variable {d : ℕ} (A : UnitSpinor)

theorem boundaryLoop_homotopic
    {p q : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)}
    (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (boundaryLoop A p) (boundaryLoop A q) := by
  obtain ⟨F⟩ := h
  let H : C(I × (I × (Fin d → I)), OrthogonalComplexStructures.Space 6) := F.toContinuousMap.comp
    ⟨fun z ↦ (z.2.1, join d (z.1, z.2.2)),
      continuous_snd.fst.prodMk
        ((join d).continuous.comp (continuous_fst.prodMk continuous_snd.snd))⟩
  have hH₀ (z : I × (Fin d → I)) : H (0, z) = fromSpinor A := by
    change F (z.1, join d (0, z.2)) = fromSpinor A
    have hb := (boundary_join_iff d (0, z.2)).mpr (Or.inl rfl)
    exact (F.eq_fst z.1 hb).trans (p.property _ hb)
  have hHb (t s : I) (u : Fin d → I) (hu : u ∈ Cube.boundary (Fin d)) :
      H (t, (s, u)) = fromSpinor A := by
    have hb := (boundary_join_iff d (t, u)).mpr (Or.inr (Or.inr hu))
    exact (F.eq_fst s hb).trans (p.property _ hb)
  obtain ⟨L, hL₀, hLp, hLfix⟩ := exists_homotopy_lift H
    (ContinuousMap.const _ A) (fun z ↦ (hH₀ z).symm)
  have hLb (t s : I) (u : Fin d → I) (hu : u ∈ Cube.boundary (Fin d)) :
      L (t, (s, u)) = A :=
    hLfix (s, u) (fun a ↦ (hHb a s u hu).trans (hH₀ (s, u)).symm) t
  let L₀ : CubeLift A p := {
    map := L.comp ⟨fun z ↦ (z.1, (0, z.2)),
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩
    initial := fun u ↦ hL₀ (0, u)
    project := fun t u ↦ (hLp t (0, u)).trans (F.map_zero_left (join d (t, u)))
    boundary := fun t u hu ↦ hLb t 0 u hu }
  let L₁ : CubeLift A q := {
    map := L.comp ⟨fun z ↦ (z.1, (1, z.2)),
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩
    initial := fun u ↦ hL₀ (1, u)
    project := fun t u ↦ (hLp t (1, u)).trans (F.map_one_left (join d (t, u)))
    boundary := fun t u hu ↦ hLb t 1 u hu }
  have hE (s : I) (u : Fin d → I) : fromSpinor (L (1, (s, u))) = fromSpinor A := by
    have hb := (boundary_join_iff d (1, u)).mpr (Or.inr (Or.inl rfl))
    exact (hLp 1 (s, u)).trans ((F.eq_fst s hb).trans (p.property _ hb))
  let E : L₀.endpoint.val.HomotopyRel L₁.endpoint.val (Cube.boundary (Fin d)) := {
    toFun z := coordinate A (L (1, (z.1, z.2))) (hE z.1 z.2).symm
    continuous_toFun := continuous_coordinate_family (fun _ ↦ A) (fun z ↦ L (1, z))
      continuous_const (L.continuous.comp (continuous_const.prodMk continuous_id)) _
    map_zero_left := fun _ ↦ rfl
    map_one_left := fun _ ↦ rfl
    prop' := fun s u hu ↦ by
      change coordinate A (L (1, (s, u))) (hE s u).symm =
        coordinate A (L (1, (0, u))) (hE 0 u).symm
      simp only [hLb 1 s u hu, hLb 1 0 u hu] }
  exact (boundaryLoop_homotopic_endpoint A p L₀).trans
    ((show GenLoop.Homotopic L₀.endpoint L₁.endpoint from ⟨E⟩).trans
      (boundaryLoop_homotopic_endpoint A q L₁).symm)

/-- The actual cubical connecting construction on homotopy classes. -/
def connecting (d : ℕ) :
    HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A) →
      HomotopyGroup (Fin d) (Circle) 1 :=
  Quotient.map (boundaryLoop A) (fun _ _ h ↦ boundaryLoop_homotopic A h)

theorem connecting_mk
    (p : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) :
    connecting A d (⟦p⟧ : HomotopyGroup (Fin (d + 1))
      (OrthogonalComplexStructures.Space 6) (fromSpinor A)) =
      (⟦boundaryLoop A p⟧ : HomotopyGroup (Fin d) (Circle) 1) := rfl

theorem connecting_eq_endpoint
    (p : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A))
    (L : CubeLift A p) :
    connecting A d (⟦p⟧ : HomotopyGroup (Fin (d + 1))
      (OrthogonalComplexStructures.Space 6) (fromSpinor A)) =
      (⟦L.endpoint⟧ : HomotopyGroup (Fin d) (Circle) 1) :=
  Quotient.sound (boundaryLoop_homotopic_endpoint A p L)

end NoExoticSixSphere.RankSixComplexProjection.SpinorFibration
