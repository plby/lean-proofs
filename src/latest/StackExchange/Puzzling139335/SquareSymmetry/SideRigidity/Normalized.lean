import StackExchange.Puzzling139335.PlaneIsometries

/-!
# Rigidity at a normalized side

An affine isometry fixing the origin and taking a positive unit coordinate
vector to another positive unit coordinate vector is either a square
symmetry or reverses one inward coordinate. A point strictly inside the
source square whose image stays in the square excludes the latter case.
-/

open Set

namespace Puzzling139335.SquareSymmetry

noncomputable section

open PlaneIsometries

/-- Both coordinates of an interior point of the square are strictly
between the corresponding side coordinates. -/
theorem interior_unitSquare_coordinates {p : Plane} (hp : p ∈ interior unitSquare) :
    p 0 ∈ Ioo (0 : ℝ) 1 ∧ p 1 ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · let f : ℝ → Plane := fun x => !₂[x, p 1]
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hopen : IsOpen (f ⁻¹' interior unitSquare) := isOpen_interior.preimage hf
    have hsub : f ⁻¹' interior unitSquare ⊆ Icc (0 : ℝ) 1 := by
      intro x hx
      exact (interior_subset hx).1
    have heq : f (p 0) = p := by
      ext i
      fin_cases i <;> rfl
    have hmem : p 0 ∈ f ⁻¹' interior unitSquare := by
      change f (p 0) ∈ interior unitSquare
      rwa [heq]
    simpa only [interior_Icc] using (hopen.subset_interior_iff.mpr hsub) hmem
  · let f : ℝ → Plane := fun y => !₂[p 0, y]
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hopen : IsOpen (f ⁻¹' interior unitSquare) := isOpen_interior.preimage hf
    have hsub : f ⁻¹' interior unitSquare ⊆ Icc (0 : ℝ) 1 := by
      intro y hy
      exact (interior_subset hy).2
    have heq : f (p 1) = p := by
      ext i
      fin_cases i <;> rfl
    have hmem : p 1 ∈ f ⁻¹' interior unitSquare := by
      change f (p 1) ∈ interior unitSquare
      rwa [heq]
    simpa only [interior_Icc] using (hopen.subset_interior_iff.mpr hsub) hmem

/-- The two positive coordinate unit vectors can be interchanged, but a
reflection across a supporting side cannot take an interior point back
into the square. -/
theorem normalized_side_coordinate_form (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hzero : e 0 = 0)
    (hside : e (corner 1) = corner 1 ∨ e (corner 1) = corner 3 ∨
      e (corner 3) = corner 1 ∨ e (corner 3) = corner 3)
    {q : Plane} (hq₀ : 0 < q 0) (hq₁ : 0 < q 1) (heq : e q ∈ unitSquare) :
    (∀ p, e p = p) ∨ (∀ p, e p = !₂[p 1, p 0]) := by
  obtain ⟨c, s, _, he | he⟩ := affine_coordinate_classification e
  · have he' (p : Plane) : e p = directCoordinates c s 0 p := by
      simpa only [hzero] using he p
    rcases hside with h | h | h | h
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 1)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 1)).symm.trans h)
      norm_num [directCoordinates, corner, Fin.ext_iff] at h₀ h₁
      refine Or.inl fun p => ?_
      rw [he', h₀, h₁]
      ext i
      fin_cases i <;> simp [directCoordinates]
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 1)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 1)).symm.trans h)
      norm_num [directCoordinates, corner, Fin.ext_iff] at h₀ h₁
      have hnonneg := heq.1.1
      rw [he', h₀, h₁] at hnonneg
      norm_num [directCoordinates] at hnonneg
      linarith
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 3)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 3)).symm.trans h)
      norm_num [directCoordinates, corner, Fin.ext_iff] at h₀ h₁
      have hs : s = -1 := by linarith
      have hnonneg := heq.2.1
      rw [he', h₁, hs] at hnonneg
      norm_num [directCoordinates] at hnonneg
      linarith
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 3)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 3)).symm.trans h)
      norm_num [directCoordinates, corner, Fin.ext_iff] at h₀ h₁
      have hs : s = 0 := by linarith
      refine Or.inl fun p => ?_
      rw [he', h₁, hs]
      ext i
      fin_cases i <;> simp [directCoordinates]
  · have he' (p : Plane) : e p = reversingCoordinates c s 0 p := by
      simpa only [hzero] using he p
    rcases hside with h | h | h | h
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 1)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 1)).symm.trans h)
      norm_num [reversingCoordinates, corner, Fin.ext_iff] at h₀ h₁
      have hnonneg := heq.2.1
      rw [he', h₀, h₁] at hnonneg
      norm_num [reversingCoordinates] at hnonneg
      linarith
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 1)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 1)).symm.trans h)
      norm_num [reversingCoordinates, corner, Fin.ext_iff] at h₀ h₁
      refine Or.inr fun p => ?_
      rw [he', h₀, h₁]
      ext i
      fin_cases i <;> simp [reversingCoordinates]
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 3)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 3)).symm.trans h)
      norm_num [reversingCoordinates, corner, Fin.ext_iff] at h₀ h₁
      have hc : c = 0 := by linarith
      refine Or.inr fun p => ?_
      rw [he', hc, h₀]
      ext i
      fin_cases i <;> simp [reversingCoordinates]
    · have h₀ := congrArg (fun p : Plane => p 0) ((he' (corner 3)).symm.trans h)
      have h₁ := congrArg (fun p : Plane => p 1) ((he' (corner 3)).symm.trans h)
      norm_num [reversingCoordinates, corner, Fin.ext_iff] at h₀ h₁
      have hc : c = -1 := by linarith
      have hnonneg := heq.1.1
      rw [he', hc, h₀] at hnonneg
      norm_num [reversingCoordinates] at hnonneg
      linarith

/-- A normalized side congruence fitting a set with nonempty interior in
the square preserves the whole square. -/
theorem normalized_side_rigidity (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hzero : e 0 = 0)
    (hside : e (corner 1) = corner 1 ∨ e (corner 1) = corner 3 ∨
      e (corner 3) = corner 1 ∨ e (corner 3) = corner 3)
    {P : Set Plane} (hP : P ⊆ unitSquare) (heP : e '' P ⊆ unitSquare)
    (hint : (interior P).Nonempty) : e '' unitSquare = unitSquare := by
  obtain ⟨q, hq⟩ := hint
  have hqcoord := interior_unitSquare_coordinates (interior_mono hP hq)
  have heq := heP (mem_image_of_mem e (interior_subset hq))
  rcases normalized_side_coordinate_form e hzero hside hqcoord.1.1 hqcoord.2.1 heq with
    he | he
  · simp only [he, image_id']
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      rw [he]
      exact ⟨hp.2, hp.1⟩
    · intro p hp
      refine ⟨!₂[p 1, p 0], ?_, ?_⟩
      · exact ⟨hp.2, hp.1⟩
      · rw [he]
        ext i
        fin_cases i <;> rfl

end

end Puzzling139335.SquareSymmetry
