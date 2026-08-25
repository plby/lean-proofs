import StackExchange.Puzzling139335.N4Diagonal.FromDissection.Angles
import StackExchange.Puzzling139335.N4Midline.FullCorners
import StackExchange.Puzzling139335.FourIncidences

/-!
# Packaging ordered actual placements as a diagonal model

Every set in the model is an actual dissection piece.  Reordering the two
remaining corner types only exchanges their two actual placements.
-/

open Set

namespace Puzzling139335.N4Diagonal.FromDissection

open ThreeCorners

noncomputable section

theorem corner_eq_of_mem_piece (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    {i j : Fin 4} (hj : corner j ∈ d.piece i) : j = i := by
  by_contra hji
  exact d.unique_corner_owner_of_four_incidences hN (hOwners j) i (Ne.symm hji) hj

theorem full_origin (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j) :
    UnitPairs.IsFullSquareCorner (d.piece 0) 0 := by
  have hcorner0 : corner 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hfull := d.full_corner_preimage_of_unique_owner 0 0 0
    (AffineIsometryEquiv.refl ℝ Plane) (by simp)
    (d.unique_corner_owner_of_four_incidences hN (hOwners 0))
  change UnitPairs.IsFullSquareCorner (d.piece 0) (corner 0) at hfull
  rwa [hcorner0] at hfull

theorem actual_pieces_cover (d : SquareDissection)
    (e f : Plane ≃ᵃⁱ[ℝ] Plane) {j k : Fin 4}
    (he : e '' d.piece 0 = d.piece j)
    (hf : f '' d.piece 0 = d.piece k)
    (hH : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 2)
    (hOrder : (j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1)) :
    ∀ x ∈ unitSquare,
      x ∈ d.piece 0 ∨ x ∈ ReflectionSeparation.antiDiagonal '' d.piece 0 ∨
        x ∈ e '' d.piece 0 ∨ x ∈ f '' d.piece 0 := by
  intro x hx
  obtain ⟨i, hi⟩ := d.exists_piece_mem hx
  rcases hOrder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inl (by simpa [he] using hi)))
    · exact Or.inr (Or.inl (by simpa [hH] using hi))
    · exact Or.inr (Or.inr (Or.inr (by simpa [hf] using hi)))
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inr (Or.inr (by simpa [hf] using hi)))
    · exact Or.inr (Or.inl (by simpa [hH] using hi))
    · exact Or.inr (Or.inr (Or.inl (by simpa [he] using hi)))

theorem actual_pieces_disjoint (d : SquareDissection)
    (e f : Plane ≃ᵃⁱ[ℝ] Plane) {j k : Fin 4}
    (he : e '' d.piece 0 = d.piece j)
    (hf : f '' d.piece 0 = d.piece k)
    (hH : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 2)
    (hOrder : (j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1)) :
    Pairwise fun i l : Fin 4 =>
      Disjoint (interior (pieces (d.piece 0) e f i))
        (interior (pieces (d.piece 0) e f l)) := by
  have hIndex : Function.Injective (![0, j, 2, k] : Fin 4 → Fin 4) := by
    rcases hOrder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hPiece (i : Fin 4) :
      pieces (d.piece 0) e f i = d.piece (![0, j, 2, k] i) := by
    fin_cases i <;> simp [pieces, he, hf, hH]
  intro i l hil
  rw [hPiece, hPiece]
  exact d.disjoint_interiors (hIndex.ne hil)

/-- Construct the model from already ordered, distinct intrinsic corners.
The hypothesis on each cone comes directly from the three-corner theorem. -/
def orderedModel (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    (hH : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 2)
    (e f : Plane ≃ᵃⁱ[ℝ] Plane) {j k : Fin 4}
    (he : e '' d.piece 0 = d.piece j)
    (hf : f '' d.piece 0 = d.piece k)
    (hOrder : (j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1))
    {p q : Plane} (hp : UnitPairs.IsFullSquareCorner (d.piece 0) p)
    (hq : UnitPairs.IsFullSquareCorner (d.piece 0) q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hpq : p ≠ q)
    (hep : e p = corner j) (hfq : f q = corner k)
    {θ φ : ℝ} (hθ : θ ∈ Icc (Real.pi / 2) Real.pi)
    (hφ : φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2))
    (hConeP : d.piece 0 ⊆ supportCone p θ)
    (hConeQ : d.piece 0 ⊆ supportCone q φ) : Model := by
  have hfull0 := full_origin d hN hOwners
  have hTriangle : d.piece 0 ⊆ lowerTriangle := by
    have hbelow := ReflectionSeparation.antiDiagonal_below_of_bottom_left
      (d.jordan 0) hH (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 2))
      (hOwners 0)
    intro x hx
    exact ⟨(d.piece_subset 0 hx).1.1, (d.piece_subset 0 hx).2.1, hbelow hx⟩
  exact {
    P := d.piece 0
    p := p
    q := q
    θ := θ - Real.pi / 2
    β := φ - Real.pi
    e := e
    f := f
    firstCorner := j
    lastCorner := k
    jordan := d.jordan 0
    triangle := hTriangle
    origin_mem := hfull0.mem
    origin_full := hfull0
    p_mem := hp.mem
    q_mem := hq.mem
    p_ne_origin := hp0
    q_ne_origin := hq0
    p_ne_q := hpq
    p_full := hp
    q_full := hq
    theta_bounds := (shifted_angle_bounds hθ hφ).1
    beta_bounds := (shifted_angle_bounds hθ hφ).2
    first_support := first_support_of_supportCone hConeP
    last_support := last_support_of_supportCone hConeQ
    first_subset := by rw [he]; exact d.piece_subset j
    last_subset := by rw [hf]; exact d.piece_subset k
    first_corner := hep
    last_corner := hfq
    corner_order := hOrder
    origin_only_corner := fun l hl => corner_eq_of_mem_piece d hN hOwners hl
    first_only_corner := by
      intro l hl
      rw [he] at hl
      exact corner_eq_of_mem_piece d hN hOwners hl
    last_only_corner := by
      intro l hl
      rw [hf] at hl
      exact corner_eq_of_mem_piece d hN hOwners hl
    cover := actual_pieces_cover d e f he hf hH hOrder
    disjoint := actual_pieces_disjoint d e f he hf hH hOrder
  }

/-- Apply the three-corner ordering to the two actual unreflected
placements and preserve their actual protected-center alternative. -/
theorem exists_model_of_distinct_preimages (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 4)
    (hOwners : ∀ j : Fin 4, corner j ∈ d.piece j)
    (hH : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 2)
    (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 1)
    (hf : f '' d.piece 0 = d.piece 3)
    (hp0 : e.symm (corner 1) ≠ 0)
    (hq0 : f.symm (corner 3) ≠ 0)
    (hpq : e.symm (corner 1) ≠ f.symm (corner 3))
    (hcenter : squareCenter ∈ interior (d.piece 1) ∨
      squareCenter ∈ interior (d.piece 3)) :
    ∃ m : Model, m.P = d.piece 0 ∧
      (squareCenter ∈ interior (m.e '' m.P) ∨
        squareCenter ∈ interior (m.f '' m.P)) := by
  have hpFull := d.full_corner_preimage_of_unique_owner 0 1 1 e he
    (d.unique_corner_owner_of_four_incidences hN (hOwners 1))
  have hqFull := d.full_corner_preimage_of_unique_owner 0 3 3 f hf
    (d.unique_corner_owner_of_four_incidences hN (hOwners 3))
  have hzero := (full_origin d hN hOwners).mem
  obtain ⟨p, q, θ, φ, hOrder, hθ, hφ, hp, hq,
      _, _, _, _, hConeP, hConeQ⟩ :=
    exists_ordered_frames_of_full_corners (d.piece_subset 0) hzero hpFull hqFull
      hp0 hq0 hpq
  rcases hOrder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · let m := orderedModel d hN hOwners hH e f he hf (Or.inl ⟨rfl, rfl⟩)
      hp hq hp0 hq0 hpq (e.apply_symm_apply _) (f.apply_symm_apply _)
      hθ hφ hConeP hConeQ
    refine ⟨m, rfl, ?_⟩
    change squareCenter ∈ interior (e '' d.piece 0) ∨
      squareCenter ∈ interior (f '' d.piece 0)
    simpa only [he, hf] using hcenter
  · let m := orderedModel d hN hOwners hH f e hf he (Or.inr ⟨rfl, rfl⟩)
      hp hq hq0 hp0 (Ne.symm hpq) (f.apply_symm_apply _) (e.apply_symm_apply _)
      hθ hφ hConeP hConeQ
    refine ⟨m, rfl, ?_⟩
    change squareCenter ∈ interior (f '' d.piece 0) ∨
      squareCenter ∈ interior (e '' d.piece 0)
    simpa only [hf, he] using hcenter.symm

end

end Puzzling139335.N4Diagonal.FromDissection
