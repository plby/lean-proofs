import Wikipedia.NoExoticSixSphere.JamesSphereAttachingSourceSphere

/-!
# The actual source-correction tracks depend only on the tail sphere points

On discarded faces the homotopy-extension tracks are prescribed: first
the clocks shrink with tails fixed, and then the tails shrink at zero
clocks. Evaluating the ORIGINAL attaching map removes all dependence
on representatives of collapsed tail-cube faces. Away from those faces,
the tail quotient has singleton fibers. Thus the entire corrected
attaching family, not just its endpoints, respects the tail quotients.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

theorem array_fullBoundary (n : ℕ) (p : fullBoundary n) (i : Fin 2) :
    Cell.array (n + 1) 2 (fullBoundaryHomeomorph n p).val i =
      CubicalSphereSuspension.evaluation n
        (p.val.1 i, SmoothCube.quotient n (p.val.2 i)) := by
  change SmoothCube.quotient (n + 1) (JamesCellCube.block (n + 1) 2
    (JamesCellCube.cube (2 * (n + 1)) (JamesCellCube.unscale (2 * (n + 1))
      (JamesCellCube.pack (n + 1) 2 (fun j ↦ Fin.cons (p.val.1 j) (p.val.2 j))))) i) = _
  rw [JamesCellCube.cube_unscale, JamesCellCube.block_pack]
  exact (CubicalSphereSuspension.evaluation_quotient n (p.val.1 i) (p.val.2 i)).symm

theorem fullAttaching_zero_clocks (n : ℕ) (p : fullBoundary n) (hp : p.val.1 = 0) :
    fullAttaching n p = spherePole (n + 1) := by
  change CellBoundary.attaching (n + 1) (fullBoundaryHomeomorph n p) = _
  rw [UnitalAttaching.attaching_eq_first, array_fullBoundary, hp,
    Pi.zero_apply, CubicalSphereSuspension.evaluation_zero]
  rw [array_fullBoundary, hp, Pi.zero_apply, CubicalSphereSuspension.evaluation_zero]

theorem fullAttaching_poles (n : ℕ) (p : fullBoundary n)
    (hp : ∀ i, SmoothCube.quotient n (p.val.2 i) = spherePole n) :
    fullAttaching n p = spherePole (n + 1) := by
  change CellBoundary.attaching (n + 1) (fullBoundaryHomeomorph n p) = _
  rw [UnitalAttaching.attaching_eq_first, array_fullBoundary, hp,
    CubicalSphereSuspension.evaluation_pole]
  rw [array_fullBoundary, hp, CubicalSphereSuspension.evaluation_pole]

theorem fullAttaching_eq_of_coordinates (n : ℕ) (p q : fullBoundary n)
    (hc : p.val.1 = q.val.1)
    (ht : ∀ i, SmoothCube.quotient n (p.val.2 i) = SmoothCube.quotient n (q.val.2 i)) :
    fullAttaching n p = fullAttaching n q := by
  have ha (i : Fin 2) : Cell.array (n + 1) 2 (fullBoundaryHomeomorph n p).val i =
      Cell.array (n + 1) 2 (fullBoundaryHomeomorph n q).val i := by
    rw [array_fullBoundary, array_fullBoundary, hc, ht]
  change CellBoundary.attaching (n + 1) (fullBoundaryHomeomorph n p) =
    CellBoundary.attaching (n + 1) (fullBoundaryHomeomorph n q)
  rcases UnitalAttaching.boundary_block_pole (n + 1) (fullBoundaryHomeomorph n p) with hp | hp
  · rw [UnitalAttaching.attaching_eq_second _ _ hp,
      UnitalAttaching.attaching_eq_second _ _ ((ha 0).symm.trans hp)]
    exact ha 1
  · rw [UnitalAttaching.attaching_eq_first _ _ hp,
      UnitalAttaching.attaching_eq_first _ _ ((ha 1).symm.trans hp)]
    exact ha 0

theorem fullAttaching_clockStage_eq (n : ℕ) (s : I) (p q : collapsedFaces n)
    (hc : p.val.val.1 = q.val.val.1)
    (ht : ∀ i, SmoothCube.quotient n (p.val.val.2 i) =
      SmoothCube.quotient n (q.val.val.2 i)) :
    fullAttaching n (clockStage n (s, p)).val =
      fullAttaching n (clockStage n (s, q)).val := by
  apply fullAttaching_eq_of_coordinates
  · funext i
    exact congrArg (fun t : I ↦ σ s * t) (congrFun hc i)
  · exact ht

theorem fullAttaching_tailStage (n : ℕ) (s : I) (p : collapsedFaces n) :
    fullAttaching n (tailStage n (s, p)).val = spherePole (n + 1) :=
  fullAttaching_zero_clocks n _ rfl

theorem fullAttaching_contraction_eq (n : ℕ) (s : I) (p q : collapsedFaces n)
    (hc : p.val.val.1 = q.val.val.1)
    (ht : ∀ i, SmoothCube.quotient n (p.val.val.2 i) =
      SmoothCube.quotient n (q.val.val.2 i)) :
    fullAttaching n (collapsedContraction n (s, p)).val =
      fullAttaching n (collapsedContraction n (s, q)).val := by
  change fullAttaching n (((clockHomotopy n).trans (tailHomotopy n)) (s, p)).val =
    fullAttaching n (((clockHomotopy n).trans (tailHomotopy n)) (s, q)).val
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs with hs
  · exact fullAttaching_clockStage_eq n _ p q hc ht
  · exact (fullAttaching_tailStage n _ p).trans (fullAttaching_tailStage n _ q).symm

theorem fullAttaching_contraction_zero_clocks (n : ℕ) (s : I) (p : collapsedFaces n)
    (hp : p.val.val.1 = 0) :
    fullAttaching n (collapsedContraction n (s, p)).val = spherePole (n + 1) := by
  change fullAttaching n (((clockHomotopy n).trans (tailHomotopy n)) (s, p)).val = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs with hs
  · apply fullAttaching_zero_clocks
    funext i
    change σ _ * p.val.val.1 i = 0
    rw [hp, Pi.zero_apply, mul_zero]
  · exact fullAttaching_tailStage n _ p

theorem fullAttaching_contraction_poles (n : ℕ) (s : I) (p : collapsedFaces n)
    (hp : ∀ i, SmoothCube.quotient n (p.val.val.2 i) = spherePole n) :
    fullAttaching n (collapsedContraction n (s, p)).val = spherePole (n + 1) := by
  change fullAttaching n (((clockHomotopy n).trans (tailHomotopy n)) (s, p)).val = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split_ifs with hs
  · exact fullAttaching_poles n _ hp
  · exact fullAttaching_tailStage n _ p

theorem collapsedFaces_of_coordinates (n : ℕ) (p q : fullBoundary n)
    (hc : p.val.1 = q.val.1)
    (ht : ∀ i, SmoothCube.quotient n (p.val.2 i) = SmoothCube.quotient n (q.val.2 i))
    (hp : p ∈ collapsedFaces n) : q ∈ collapsedFaces n := by
  rcases hp with hp | ⟨i, hi⟩
  · exact Or.inl (hc.symm.trans hp)
  · right
    refine ⟨i, (SmoothCube.quotient_eq_pole_iff n _).mp ?_⟩
    exact (ht i).symm.trans (SmoothCube.quotient_boundary n _ hi)

theorem sourceAttachingTrack_respects (n : ℕ) (s : I) (p q : fullBoundary n)
    (hc : p.val.1 = q.val.1)
    (ht : ∀ i, SmoothCube.quotient n (p.val.2 i) = SmoothCube.quotient n (q.val.2 i)) :
    fullAttaching n (sourceExtension n (s, p)) =
      fullAttaching n (sourceExtension n (s, q)) := by
  by_cases hp : p ∈ collapsedFaces n
  · have hq := collapsedFaces_of_coordinates n p q hc ht hp
    change fullAttaching n (sourceExtension n (s, (⟨p, hp⟩ : collapsedFaces n).val)) =
      fullAttaching n (sourceExtension n (s, (⟨q, hq⟩ : collapsedFaces n).val))
    rw [sourceExtension_faces, sourceExtension_faces]
    exact fullAttaching_contraction_eq n s ⟨p, hp⟩ ⟨q, hq⟩ hc ht
  · have hpq : p = q := by
      apply Subtype.ext
      apply Prod.ext hc
      funext i
      rcases (SmoothCube.quotient_eq_iff n _ _).mp (ht i) with he | he
      · exact he
      · exact False.elim (hp (Or.inr ⟨i, he.1⟩))
    rw [hpq]

theorem sourceAttachingTrack_zero_clocks (n : ℕ) (s : I) (p : fullBoundary n)
    (hp : p.val.1 = 0) :
    fullAttaching n (sourceExtension n (s, p)) = spherePole (n + 1) := by
  let p' : collapsedFaces n := ⟨p, Or.inl hp⟩
  change fullAttaching n (sourceExtension n (s, p'.val)) = _
  rw [sourceExtension_faces]
  exact fullAttaching_contraction_zero_clocks n s p' hp

theorem sourceAttachingTrack_poles (n : ℕ) (s : I) (p : fullBoundary n)
    (hp : ∀ i, SmoothCube.quotient n (p.val.2 i) = spherePole n) :
    fullAttaching n (sourceExtension n (s, p)) = spherePole (n + 1) := by
  have hface : p ∈ collapsedFaces n :=
    Or.inr ⟨0, (SmoothCube.quotient_eq_pole_iff n _).mp (hp 0)⟩
  change fullAttaching n (sourceExtension n (s, (⟨p, hface⟩ : collapsedFaces n).val)) = _
  rw [sourceExtension_faces]
  exact fullAttaching_contraction_poles n s ⟨p, hface⟩ hp

end NoExoticSixSphere.JamesSphere.AttachingSquare
