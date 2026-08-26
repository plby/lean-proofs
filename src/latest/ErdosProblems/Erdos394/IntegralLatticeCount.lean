import ErdosProblems.Erdos394.IntegralBasisRealification
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit square count for an abstract full-rank integral lattice
-/

open Module Submodule
open scoped Matrix

namespace Erdos394

/-- Coordinatewise cast, as an integer-linear map into real vectors. -/
def intVecCastLinear : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℝ) where
  toFun := intVecToReal
  map_add' x y := by ext i; simp [intVecToReal]
  map_smul' n x := by ext i; simp [intVecToReal]

@[simp] theorem intVecCastLinear_apply (x : Fin 2 → ℤ) :
    intVecCastLinear x = intVecToReal x := rfl

lemma basisFunInt_det_pair (u v : Fin 2 → ℤ) :
    (Pi.basisFun ℤ (Fin 2)).det ![u, v] = u 0 * v 1 - u 1 * v 0 := by
  rw [Pi.basisFun_det]
  change Matrix.det ![u, v] = _
  rw [Matrix.det_fin_two]
  norm_num

/-- Every integer basis of a full-rank submodule has determinant magnitude
its quotient index. -/
theorem integral_submodule_basis_det_eq_index
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (b : Basis (Fin 2) ℤ Λ) :
    ((b 0 : Fin 2 → ℤ) 0 * (b 1 : Fin 2 → ℤ) 1 -
      (b 0 : Fin 2 → ℤ) 1 * (b 1 : Fin 2 → ℤ) 0).natAbs =
      Nat.card ((Fin 2 → ℤ) ⧸ Λ) := by
  have h := Submodule.natAbs_det_basis_change
    (Pi.basisFun ℤ (Fin 2)) Λ b
  have hfun : Subtype.val ∘ (b : Fin 2 → Λ) =
      ![(b 0 : Fin 2 → ℤ), (b 1 : Fin 2 → ℤ)] := by
    funext i
    fin_cases i <;> rfl
  rw [hfun, basisFunInt_det_pair] at h
  exact h

/-- A finite set of points in a full-rank integral lattice obeys the explicit
sharp-leading count after choosing the reduced basis furnished by F-047. -/
theorem integral_lattice_square_count
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (b₀ : Basis (Fin 2) ℤ Λ)
    (S : Finset Λ) {Y D : ℕ}
    (hD : 0 < D) (hindex : Nat.card ((Fin 2 → ℤ) ⧸ Λ) = D)
    (hpoint : ∀ x ∈ S, ∀ i,
      0 ≤ (x : Fin 2 → ℤ) i ∧ (x : Fin 2 → ℤ) i ≤ (Y : ℤ)) :
    ∃ L : ℕ, 0 < L ∧
      (S.card : ℝ) ≤ (Y : ℝ) ^ 2 / (D : ℝ) +
        40 * ((Y : ℝ) / (L : ℝ)) + 4 := by
  let coord : Λ →ₗ[ℤ] (Fin 2 → ℤ) := Λ.subtype
  have hcoord : Function.Injective coord := Subtype.val_injective
  obtain ⟨b, L, hL, hLpos, hmin, hred⟩ :=
    exists_supnorm_reduced_integral_basis coord b₀ hcoord
  let u : Fin 2 → ℤ := coord (b 0)
  let v : Fin 2 → ℤ := coord (b 1)
  have hdetAbs : (u 0 * v 1 - u 1 * v 0).natAbs = D := by
    calc
      (u 0 * v 1 - u 1 * v 0).natAbs =
          Nat.card ((Fin 2 → ℤ) ⧸ Λ) := by
        simpa [u, v, coord] using integral_submodule_basis_det_eq_index Λ b
      _ = D := hindex
  have hdet : u 0 * v 1 - u 1 * v 0 ≠ 0 := by
    intro hz
    rw [hz, Int.natAbs_zero] at hdetAbs
    omega
  let bR := realBasisOfIntPair u v hdet
  have hrealBounds := reduced_integral_pair_real_bounds u v L
    (by simpa [u, coord] using hL) hLpos
    (by simpa [v, coord] using hmin)
    (by simpa [u, v, coord] using hred) hdet
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
    · simp [castΛ, bR, u, coord]
    · simp [castΛ, bR, v, coord]
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
    refine ⟨L, hLpos, ?_⟩
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
    have hcount' := reduced_basis_square_discrepancy_two bR A
      hYposR hDR hLR hdetR huR.le hrealBounds.1 hrealBounds.2 hpointR
    refine ⟨L, hLpos, ?_⟩
    rw [← hcard]
    exact hcount'

end Erdos394
