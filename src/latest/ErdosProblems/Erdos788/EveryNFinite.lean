import ErdosProblems.Erdos788.CarryFactorization
import ErdosProblems.Erdos788.Normalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Restricting the finite-field construction to every interval length

This file contains the exact finite part of the "every `N`" step.  It is
independent of the later analytic choice of `p` and `r`.
-/

namespace Erdos788

open Finset

/-- The ordinary and normalized sum-graph definitions coincide. -/
theorem intSumGraph_eq_sumGraph (N : ℕ) (B : Finset ℕ) :
    intSumGraph N B = sumGraph N B := by
  ext x y
  simp only [intSumGraph_adj, sumGraph_adj]

/-- Inclusion of a shorter initial interval into a longer one. -/
def finInitialEmbedding {N M : ℕ} (hNM : N ≤ M) : Fin N ↪ Fin M where
  toFun := Fin.castLE hNM
  inj' := Fin.castLE_injective hNM

/-- Restricting a sum graph to an initial interval cannot increase its
independence number. -/
theorem indepNum_sumGraph_mono_vertices
    {N M : ℕ} (hNM : N ≤ M) (B : Finset ℕ) :
    (sumGraph N B).indepNum ≤ (sumGraph M B).indepNum := by
  classical
  obtain ⟨A, hA⟩ := (sumGraph N B).exists_isNIndepSet_indepNum
  let C : Finset (Fin M) := A.map (finInitialEmbedding hNM)
  have hC : (sumGraph M B).IsIndepSet (C : Set (Fin M)) := by
    intro u hu v hv huv hadj
    change u ∈ C at hu
    change v ∈ C at hv
    rcases Finset.mem_map.mp hu with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hv with ⟨y, hy, rfl⟩
    have hxy : x ≠ y := by
      intro h
      exact huv (congrArg (finInitialEmbedding hNM) h)
    have hsum : x.val + y.val ∈ B := (sumGraph_adj.mp hadj).2
    exact hA.isIndepSet hx hy hxy (sumGraph_adj.mpr ⟨hxy, hsum⟩)
  calc
    (sumGraph N B).indepNum = A.card := hA.card_eq.symm
    _ = C.card := by simp [C]
    _ ≤ (sumGraph M B).indepNum := hC.card_le_indepNum

/-- Delete all colors that cannot be a sum of two distinct vertices of the
first `N` integers. -/
def restrictToAttainable (N : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.filter fun s ↦ s ∈ attainableNormalizedSums N

theorem restrictToAttainable_subset (N : ℕ) (B : Finset ℕ) :
    restrictToAttainable N B ⊆ attainableNormalizedSums N := by
  intro s hs
  exact (Finset.mem_filter.mp hs).2

theorem card_restrictToAttainable_le (N : ℕ) (B : Finset ℕ) :
    (restrictToAttainable N B).card ≤ B.card :=
  Finset.card_filter_le _ _

/-- Removing unattainable sums does not alter the graph. -/
theorem sumGraph_restrictToAttainable (N : ℕ) (B : Finset ℕ) :
    sumGraph N (restrictToAttainable N B) = sumGraph N B := by
  ext x y
  simp only [sumGraph_adj]
  constructor
  · rintro ⟨hxy, hmem⟩
    exact ⟨hxy, (Finset.mem_filter.mp hmem).1⟩
  · rintro ⟨hxy, hmem⟩
    refine ⟨hxy, Finset.mem_filter.mpr ⟨hmem, ?_⟩⟩
    exact (isAttainableNormalizedSum_iff_mem N (x.val + y.val)).mp
      ⟨x, y, hxy, rfl⟩

/-- Carry lifting followed by restriction to any shorter initial interval. -/
theorem carry_lift_restrict
    (p k N : ℕ) (hp : 1 < p) (hNM : N ≤ p ^ k)
    (S : Finset (FFVec p k)) :
    ∃ B : Finset ℕ,
      B ⊆ attainableNormalizedSums N ∧
      B.card ≤ 2 ^ k * S.card ∧
      (sumGraph N B).indepNum ≤ (groupSumGraph S).indepNum := by
  obtain ⟨B, _hBrange, hBcard, hBind⟩ := carry_lift p k hp S
  refine ⟨restrictToAttainable N B, restrictToAttainable_subset N B,
    (card_restrictToAttainable_le N B).trans hBcard, ?_⟩
  rw [sumGraph_restrictToAttainable]
  calc
    (sumGraph N B).indepNum ≤ (sumGraph (p ^ k) B).indepNum :=
      indepNum_sumGraph_mono_vertices hNM B
    _ = (intSumGraph (p ^ k) B).indepNum := by
      rw [intSumGraph_eq_sumGraph]
    _ ≤ (groupSumGraph S).indepNum := hBind

/-- A normalized palette supported on attainable sums gives an exact upper
bound for the original Erdős function. -/
theorem fNat_le_of_normalized_palette
    (n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ attainableNormalizedSums (n - 1)) :
    fNat n ≤ A.card + (sumGraph (n - 1) A).indepNum := by
  classical
  let B := denormalizePalette n A
  have hB : B ⊆ J n := by
    intro b hb
    rw [show B = denormalizePalette n A from rfl, mem_denormalizePalette] at hb
    obtain ⟨s, hsA, hsatt, rfl⟩ := hb
    rw [J, Finset.mem_Ioo]
    rw [attainableNormalizedSums, Finset.mem_Icc] at hsatt
    simp only [sumOffset]
    omega
  have hfilter : A.filter (fun s ↦ s ∈ attainableNormalizedSums (n - 1)) = A :=
    Finset.filter_eq_self.mpr hA
  have hnorm : normalizePalette n B = A := by
    rw [show B = denormalizePalette n A from rfl,
      normalizePalette_denormalizePalette, hfilter]
  have hcard : B.card = A.card := by
    rw [show B = denormalizePalette n A from rfl,
      card_denormalizePalette, hfilter]
  have hscore : graphScore n B =
      A.card + (sumGraph (n - 1) A).indepNum := by
    rw [graphScore, hcard, indepNum_paletteGraph_eq_sumGraph, hnorm]
  rw [fNat_eq_minGraphScore, ← hscore]
  exact minGraphScore_le hB

/-- Exact finite upper bridge from a group palette to `f(N+1)`. -/
theorem fNat_succ_le_of_group_palette
    (p k N : ℕ) (hp : 1 < p) (hNM : N ≤ p ^ k)
    (S : Finset (FFVec p k)) :
    fNat (N + 1) ≤ 2 ^ k * S.card + (groupSumGraph S).indepNum := by
  obtain ⟨B, hBatt, hBcard, hBind⟩ := carry_lift_restrict p k N hp hNM S
  have hf := fNat_le_of_normalized_palette (N + 1) B (by
    simpa using! hBatt)
  exact hf.trans (Nat.add_le_add hBcard hBind)

end Erdos788
