import ErdosProblems.Erdos1148.CompactModularInjectivity
import ErdosProblems.Erdos1148.LiftForwardClose

/-! # Concatenation with a quotient cover at an injective compact starting point -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem LiftForwardClose.extend_of_injective_image {η S T : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) {K : Set ModularOrbitSpace}
    (hinj : ∀ g : SL(2, ℝ), modularMk g ∈ K → ∀ u v : SL(2, ℝ),
      EntryCloseOne η u → EntryCloseOne η v →
      modularMk (g * u) = modularMk (g * v) → u = v)
    {E B : Set SL(2, ℝ)} (hE : LiftForwardClose η S E) (hB : LiftForwardClose η T B)
    (hK : ∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ K)
    (himage : ∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ modularMk '' B) :
    LiftForwardClose η (S + T) E := by
  apply hE.append
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ t ht
  obtain ⟨b, hb, hbm⟩ := himage g hg
  obtain ⟨c, hc, hcm⟩ := himage h hh
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff (g * diagonalFlow S) b).mp hbm.symm
  let u := (g * diagonalFlow S)⁻¹ * (h * diagonalFlow S)
  let v := (g * diagonalFlow S)⁻¹ * ((γ : SL(2, ℝ))⁻¹ * c)
  have hu : EntryCloseOne η u := hE g hg h hh S ⟨hS, le_rfl⟩
  have hv : EntryCloseOne η v := by
    have hbc := hB b hb c hc 0 ⟨le_rfl, hT⟩
    simp only [diagonalFlow_zero, mul_one] at hbc
    have heq : v = b⁻¹ * c := by
      rw [← hγ]
      dsimp only [v]
      group
    rwa [heq]
  have hvm : modularMk ((γ : SL(2, ℝ))⁻¹ * c) = modularMk c := by
    simpa using modularMk_integral_mul γ⁻¹ c
  have heqm : modularMk ((g * diagonalFlow S) * u) =
      modularMk ((g * diagonalFlow S) * v) := by
    calc
      _ = modularMk (h * diagonalFlow S) := by simp only [u, mul_inv_cancel_left]
      _ = modularMk c := hcm.symm
      _ = _ := by simpa only [v, mul_inv_cancel_left] using hvm.symm
  have huv := hinj (g * diagonalFlow S) (hK g hg) u v hu hv heqm
  have hγh : (γ : SL(2, ℝ)) * (h * diagonalFlow S) = c := by
    have h := congrArg (fun w : SL(2, ℝ) => (γ : SL(2, ℝ)) * ((g * diagonalFlow S) * w)) huv
    simpa only [u, v, mul_inv_cancel_left] using h
  have heq : ((g * diagonalFlow S) * diagonalFlow t)⁻¹ *
      ((h * diagonalFlow S) * diagonalFlow t) =
      (b * diagonalFlow t)⁻¹ * (c * diagonalFlow t) := by
    rw [← hγ, ← hγh]
    group
  rw [heq]
  exact hB b hb c hc t ht

theorem exists_compact_image_lift_refinement {η S T : ℝ}
    (hS : 0 ≤ S) (hT : 0 ≤ T) {K : Set ModularOrbitSpace}
    (hinj : ∀ g : SL(2, ℝ), modularMk g ∈ K → ∀ u v : SL(2, ℝ),
      EntryCloseOne η u → EntryCloseOne η v →
      modularMk (g * u) = modularMk (g * v) → u = v)
    {E : Set SL(2, ℝ)} (hE : LiftForwardClose η S E)
    (hK : ∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ K)
    {N : ℕ} (B : Fin N → Set SL(2, ℝ)) (hB : ∀ i, LiftForwardClose η T (B i))
    (hcover : ∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ ⋃ i, modularMk '' B i) :
    ∃ C : Fin N → Set SL(2, ℝ), (⋃ i, C i) = E ∧
      ∀ i, LiftForwardClose η (S + T) (C i) := by
  let C : Fin N → Set SL(2, ℝ) := fun i =>
    E ∩ (fun g => modularMk (g * diagonalFlow S)) ⁻¹' (modularMk '' B i)
  refine ⟨C, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun i => Set.inter_subset_left
    · intro g hg
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover g hg)
      exact Set.mem_iUnion.mpr ⟨i, hg, hi⟩
  · intro i
    exact (hE.mono Set.inter_subset_left).extend_of_injective_image hS hT hinj (hB i)
      (fun g hg => hK g hg.1) (fun _ hg => hg.2)

end Erdos1148.DukeArithmetic
