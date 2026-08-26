import ErdosProblems.Erdos394.IntegralLatticeCount

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Integral lattice count retaining the selected reduced first vector
-/

open Module Submodule
open scoped Matrix

namespace Erdos394

/-- Count using a specified integral basis satisfying the reduced conditions,
so the selected first vector remains available to later arguments. -/
theorem integral_lattice_square_count_of_reduced
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (b : Basis (Fin 2) ℤ Λ)
    (S : Finset Λ) {Y D L : ℕ}
    (hD : 0 < D) (hindex : Nat.card ((Fin 2 → ℤ) ⧸ Λ) = D)
    (hL : L = intSupHeight2 (b 0 : Fin 2 → ℤ)) (hLpos : 0 < L)
    (hmin : L ≤ intSupHeight2 (b 1 : Fin 2 → ℤ))
    (hred : (((b 0 : Fin 2 → ℤ) 1).natAbs ≤ ((b 0 : Fin 2 → ℤ) 0).natAbs ∧
        2 * ((b 1 : Fin 2 → ℤ) 0).natAbs ≤ L) ∨
      (((b 0 : Fin 2 → ℤ) 0).natAbs ≤ ((b 0 : Fin 2 → ℤ) 1).natAbs ∧
        2 * ((b 1 : Fin 2 → ℤ) 1).natAbs ≤ L))
    (hpoint : ∀ x ∈ S, ∀ i,
      0 ≤ (x : Fin 2 → ℤ) i ∧ (x : Fin 2 → ℤ) i ≤ (Y : ℤ)) :
    (S.card : ℝ) ≤ (Y : ℝ) ^ 2 / (D : ℝ) +
      40 * ((Y : ℝ) / (L : ℝ)) + 4 := by
  let u : Fin 2 → ℤ := (b 0 : Fin 2 → ℤ)
  let v : Fin 2 → ℤ := (b 1 : Fin 2 → ℤ)
  have hdetAbs : (u 0 * v 1 - u 1 * v 0).natAbs = D := by
    calc
      (u 0 * v 1 - u 1 * v 0).natAbs =
          Nat.card ((Fin 2 → ℤ) ⧸ Λ) := by
        simpa [u, v] using integral_submodule_basis_det_eq_index Λ b
      _ = D := hindex
  have hdet : u 0 * v 1 - u 1 * v 0 ≠ 0 := by
    intro hz
    rw [hz, Int.natAbs_zero] at hdetAbs
    omega
  let bR := realBasisOfIntPair u v hdet
  have hrealBounds := reduced_integral_pair_real_bounds u v L
    (by simpa [u] using hL) hLpos (by simpa [v] using hmin)
    (by simpa [u, v] using hred) hdet
  dsimp at hrealBounds
  rw [hdetAbs] at hrealBounds
  have hdetR :
      |(Pi.basisFun ℝ (Fin 2)).det ![bR 0, bR 1]| = (D : ℝ) := by
    rw [realBasisOfIntPair_det]
    exact_mod_cast hdetAbs
  have huR : supHeight2 (bR 0) = (L : ℝ) := by
    rw [realBasisOfIntPair_zero, supHeight2_intVecToReal]
    exact_mod_cast hL.symm
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  let castΛ : Λ →ₗ[ℤ] (Fin 2 → ℝ) := intVecCastLinear.comp Λ.subtype
  have hbcast : ∀ i, castΛ (b i) = bR i := by
    intro i
    fin_cases i
    · simp [castΛ, bR, u]
    · simp [castΛ, bR, v]
  have hmem (x : Λ) : castΛ x ∈ span ℤ (Set.range bR) := by
    have hsum := congrArg castΛ (b.sum_repr x)
    simp only [map_sum, map_zsmul] at hsum
    simp_rw [hbcast] at hsum
    rw [← hsum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (subset_span (Set.mem_range_self i))
  let emb : Λ ↪ span ℤ (Set.range bR) :=
    { toFun := fun x ↦ ⟨castΛ x, hmem x⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        ext i
        have hi := congrArg (fun z : span ℤ (Set.range bR) ↦ (z : Fin 2 → ℝ) i) hxy
        dsimp [castΛ, intVecCastLinear, intVecToReal] at hi
        exact_mod_cast hi }
  let A : Finset (span ℤ (Set.range bR)) := S.map emb
  have hcard : A.card = S.card := by
    dsimp [A]
    exact Finset.card_map emb
  have hpointR : ∀ g ∈ A, ∀ i,
      0 ≤ (g : Fin 2 → ℝ) i ∧ (g : Fin 2 → ℝ) i ≤ (Y : ℝ) := by
    intro g hg i
    rw [Finset.mem_map] at hg
    obtain ⟨x, hxS, rfl⟩ := hg
    dsimp [emb, castΛ, intVecCastLinear, intVecToReal]
    constructor
    · exact_mod_cast (hpoint x hxS i).1
    · exact_mod_cast (hpoint x hxS i).2
  by_cases hY : Y = 0
  · subst Y
    have hSone : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      apply Subtype.ext
      ext i
      have hx0 := hpoint x hx i
      have hy0 := hpoint y hy i
      fin_cases i <;> omega
    norm_num
    exact_mod_cast hSone.trans (by omega : 1 ≤ 4)
  · have hYposR : (0 : ℝ) < Y := by exact_mod_cast (Nat.pos_of_ne_zero hY)
    have hcount := reduced_basis_square_discrepancy_two bR A
      hYposR hDR hLR hdetR huR.le hrealBounds.1 hrealBounds.2 hpointR
    rw [← hcard]
    exact hcount

/-- Existence form retaining both the reduced integral basis and its height. -/
theorem integral_lattice_square_count_tracked
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (b₀ : Basis (Fin 2) ℤ Λ)
    (S : Finset Λ) {Y D : ℕ}
    (hD : 0 < D) (hindex : Nat.card ((Fin 2 → ℤ) ⧸ Λ) = D)
    (hpoint : ∀ x ∈ S, ∀ i,
      0 ≤ (x : Fin 2 → ℤ) i ∧ (x : Fin 2 → ℤ) i ≤ (Y : ℤ)) :
    ∃ b : Basis (Fin 2) ℤ Λ, ∃ L : ℕ,
      L = intSupHeight2 (b 0 : Fin 2 → ℤ) ∧ 0 < L ∧
      L ≤ intSupHeight2 (b 1 : Fin 2 → ℤ) ∧
      ((((b 0 : Fin 2 → ℤ) 1).natAbs ≤ ((b 0 : Fin 2 → ℤ) 0).natAbs ∧
          2 * ((b 1 : Fin 2 → ℤ) 0).natAbs ≤ L) ∨
       (((b 0 : Fin 2 → ℤ) 0).natAbs ≤ ((b 0 : Fin 2 → ℤ) 1).natAbs ∧
          2 * ((b 1 : Fin 2 → ℤ) 1).natAbs ≤ L)) ∧
      (S.card : ℝ) ≤ (Y : ℝ) ^ 2 / (D : ℝ) +
        40 * ((Y : ℝ) / (L : ℝ)) + 4 := by
  let coord : Λ →ₗ[ℤ] (Fin 2 → ℤ) := Λ.subtype
  obtain ⟨b, L, hL, hLpos, hmin, hred⟩ :=
    exists_supnorm_reduced_integral_basis coord b₀ Subtype.val_injective
  have hL' : L = intSupHeight2 (b 0 : Fin 2 → ℤ) := by simpa [coord] using hL
  have hmin' : L ≤ intSupHeight2 (b 1 : Fin 2 → ℤ) := by simpa [coord] using hmin
  have hred' :
      ((((b 0 : Fin 2 → ℤ) 1).natAbs ≤ ((b 0 : Fin 2 → ℤ) 0).natAbs ∧
          2 * ((b 1 : Fin 2 → ℤ) 0).natAbs ≤ L) ∨
       (((b 0 : Fin 2 → ℤ) 0).natAbs ≤ ((b 0 : Fin 2 → ℤ) 1).natAbs ∧
          2 * ((b 1 : Fin 2 → ℤ) 1).natAbs ≤ L)) := by
    simpa [coord] using hred
  refine ⟨b, L, hL', hLpos, hmin', hred', ?_⟩
  exact integral_lattice_square_count_of_reduced Λ b S hD hindex
    hL' hLpos hmin' hred' hpoint

end Erdos394
