import ErdosProblems.Erdos394.ShearBasis
import ErdosProblems.Erdos394.NearestShear

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Existence of a sup-norm reduced basis for an integral rank-two lattice
-/

open Module

namespace Erdos394

/-- Integer sup height in dimension two. -/
def intSupHeight2 (x : Fin 2 → ℤ) : ℕ := max (x 0).natAbs (x 1).natAbs

lemma intSupHeight2_pos_iff (x : Fin 2 → ℤ) : 0 < intSupHeight2 x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    simp [intSupHeight2] at h
  · intro hx
    by_contra h
    have hzero : intSupHeight2 x = 0 := Nat.eq_zero_of_not_pos h
    have h0 : x 0 = 0 := by
      apply Int.natAbs_eq_zero.mp
      exact Nat.eq_zero_of_le_zero (le_max_left _ _ |>.trans_eq hzero)
    have h1 : x 1 = 0 := by
      apply Int.natAbs_eq_zero.mp
      exact Nat.eq_zero_of_le_zero (le_max_right _ _ |>.trans_eq hzero)
    apply hx
    funext i
    fin_cases i
    · exact h0
    · exact h1

/-- Among all two-element integer bases of a fixed rank-two module, one has a
minimal first-vector sup height. -/
theorem exists_basis_minimal_first_height
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (coord : M →ₗ[ℤ] (Fin 2 → ℤ)) (b₀ : Basis (Fin 2) ℤ M)
    (hcoord : Function.Injective coord) :
    ∃ b : Basis (Fin 2) ℤ M,
      (∀ c : Basis (Fin 2) ℤ M,
        intSupHeight2 (coord (b 0)) ≤ intSupHeight2 (coord (c 0))) ∧
      0 < intSupHeight2 (coord (b 0)) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ b : Basis (Fin 2) ℤ M, intSupHeight2 (coord (b 0)) = n
  have hP : ∃ n, P n :=
    ⟨intSupHeight2 (coord (b₀ 0)), b₀, rfl⟩
  let n := Nat.find hP
  obtain ⟨b, hb⟩ := Nat.find_spec hP
  refine ⟨b, ?_, ?_⟩
  · intro c
    rw [hb]
    exact Nat.find_min' hP ⟨c, rfl⟩
  · apply (intSupHeight2_pos_iff (coord (b 0))).mpr
    exact fun hz ↦ (b.ne_zero 0) (hcoord (by simpa using hz))

/-- A minimal first vector followed by one nearest-integer shear gives a basis
whose second vector is no shorter and whose height-realizing coordinate is
reduced by half. -/
theorem exists_supnorm_reduced_integral_basis
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (coord : M →ₗ[ℤ] (Fin 2 → ℤ)) (b₀ : Basis (Fin 2) ℤ M)
    (hcoord : Function.Injective coord) :
    ∃ b : Basis (Fin 2) ℤ M, ∃ L : ℕ,
      L = intSupHeight2 (coord (b 0)) ∧ 0 < L ∧
      L ≤ intSupHeight2 (coord (b 1)) ∧
      (((coord (b 0) 1).natAbs ≤ (coord (b 0) 0).natAbs ∧
          2 * (coord (b 1) 0).natAbs ≤ L) ∨
       ((coord (b 0) 0).natAbs ≤ (coord (b 0) 1).natAbs ∧
          2 * (coord (b 1) 1).natAbs ≤ L)) := by
  obtain ⟨b, hmin, hLpos⟩ :=
    exists_basis_minimal_first_height coord b₀ hcoord
  let u := coord (b 0)
  let v := coord (b 1)
  let L := intSupHeight2 u
  have hL : 0 < L := by simpa [L, u] using hLpos
  by_cases hcoordCase : (u 1).natAbs ≤ (u 0).natAbs
  · have hu0abs : (u 0).natAbs = L := by
      simp [L, intSupHeight2, max_eq_left hcoordCase]
    have hu0 : u 0 ≠ 0 := by
      intro hz
      rw [hz, Int.natAbs_zero] at hu0abs
      omega
    obtain ⟨n, hn⟩ := exists_int_shear_natAbs_le_half (v 0) (u 0) hu0
    let b' := shearSecondBasis b n
    have hb'0 : coord (b' 0) = u := by simp [b', u]
    have hb'1 : coord (b' 1) = v - n • u := by
      simp [b', u, v]
    have hsecond : L ≤ intSupHeight2 (coord (b' 1)) := by
      have hs := hmin (swapBasis b')
      simpa [L, u, hb'0] using hs
    refine ⟨b', L, ?_, hL, hsecond, Or.inl ⟨?_, ?_⟩⟩
    · simpa [hb'0, L]
    · simpa [hb'0, u] using hcoordCase
    · rw [hb'1]
      change 2 * (v 0 - n * u 0).natAbs ≤ L
      simpa [hu0abs] using hn
  · have hreverse : (u 0).natAbs ≤ (u 1).natAbs := by omega
    have hu1abs : (u 1).natAbs = L := by
      simp [L, intSupHeight2, max_eq_right hreverse]
    have hu1 : u 1 ≠ 0 := by
      intro hz
      rw [hz, Int.natAbs_zero] at hu1abs
      omega
    obtain ⟨n, hn⟩ := exists_int_shear_natAbs_le_half (v 1) (u 1) hu1
    let b' := shearSecondBasis b n
    have hb'0 : coord (b' 0) = u := by simp [b', u]
    have hb'1 : coord (b' 1) = v - n • u := by
      simp [b', u, v]
    have hsecond : L ≤ intSupHeight2 (coord (b' 1)) := by
      have hs := hmin (swapBasis b')
      simpa [L, u, hb'0] using hs
    refine ⟨b', L, ?_, hL, hsecond, Or.inr ⟨?_, ?_⟩⟩
    · simpa [hb'0, L]
    · simpa [hb'0, u] using hreverse
    · rw [hb'1]
      change 2 * (v 1 - n * u 1).natAbs ≤ L
      simpa [hu1abs] using hn

end Erdos394
