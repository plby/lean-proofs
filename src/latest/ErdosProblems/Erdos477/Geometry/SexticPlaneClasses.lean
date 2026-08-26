/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Eliminants for the prime-power auxiliary covers of the sextic surface.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.AuxiliaryCover
import ErdosProblems.Erdos477.Counting.ResidueCodes
import ErdosProblems.Erdos477.Geometry.FieldExtension
import ErdosProblems.Erdos477.Geometry.SurfaceElimination

namespace Erdos477.Geometry

open Counting

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

/-- At every level the occupied classes have plane eliminants. Unoccupied
classes are assigned the constant polynomial one, so the family is total. -/
theorem exists_sextic_plane_classes (c : ℤ) (hc : c ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ∃ L : ℝ, 0 < L ∧ ∀ B : ℝ, 1 ≤ B → ∃ r : ℕ,
      (r : ℝ) ≤ (41 : ℝ) / 100 * Real.log B / Real.log p ∧
      L * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ r < L * p ∧
      (∀ t ≤ r, ((sexticBox c B).image (residueCode p t)).card ≤
        3 * p ^ 3 * (p ^ t) ^ 2) ∧
      ∃ P : ℕ → (Fin 3 → ℤ) → MvPolynomial (Fin 2) K,
        (∀ t a, P t a ≠ 0) ∧
        (∀ t ≤ r, ∀ a, ((P t a).totalDegree : ℝ) ≤
          L * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ t) ∧
        ∀ t ≤ r, ∀ z ∈ sexticBox c B,
          MvPolynomial.eval ![(z 1 : K), (z 2 : K)] (P t (residueCode p t z)) = 0 := by
  classical
  obtain ⟨p, hp, L, hL, hcovers⟩ := exists_sextic_refinement_covers c hc
  refine ⟨p, hp, 6 * L, by positivity, ?_⟩
  intro B hB
  obtain ⟨r, _, _, hdepth, hlevels, hlast⟩ := hcovers B hB
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hB0 : 0 < B := by linarith
  have hbound (t : ℕ) : 0 ≤ 6 * L * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ t :=
    le_of_lt (by positivity)
  have hex (t : ℕ) (a : Fin 3 → ℤ) :
      ∃ Q : MvPolynomial (Fin 2) K, Q ≠ 0 ∧
        (t ≤ r → (Q.totalDegree : ℝ) ≤
          6 * L * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ t) ∧
        (t ≤ r → ∀ z ∈ sexticBox c B, residueCode p t z = a →
          MvPolynomial.eval ![(z 1 : K), (z 2 : K)] Q = 0) := by
    by_cases ha : t ≤ r ∧ a ∈ (sexticBox c B).image (residueCode p t)
    · obtain ⟨center, hcenter, hca⟩ := Finset.mem_image.mp ha.2
      obtain ⟨Q, hQ, hdeg2, hdeg, _, heval⟩ := (hlevels t ha.1).2
        (fun k => (center k : ZMod (p ^ t))) (Finset.mem_image.mpr ⟨center, hcenter, rfl⟩)
      let QK := MvPolynomial.map (Int.castRingHom K) Q
      have hQK := integer_auxiliary_field_extension (K := K) c Q hQ hdeg2
      obtain ⟨R, hR, hRdeg, hRzero⟩ := exists_sextic_plane_eliminant
        (c : K) (by exact_mod_cast hc) QK hQK.2.2.2
      refine ⟨R, hR, fun _ => ?_, ?_⟩
      · have hRdeg' : (R.totalDegree : ℝ) ≤ 6 * Q.totalDegree := by
          rw [hQK.2.2.1] at hRdeg
          exact_mod_cast hRdeg
        calc
          _ ≤ 6 * (L * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ t) :=
            hRdeg'.trans (mul_le_mul_of_nonneg_left hdeg (by norm_num))
          _ = _ := by ring
      · intro _ z hz hza
        apply hRzero (fun k => (z k : K))
        · rw [← map_integer_sexticSurface, eval_integer_polynomial_map, eval_sexticSurface]
          have heq := ((mem_sexticBox c B z).mp hz).1
          rw [heq, sub_self, Int.cast_zero]
        · rw [eval_integer_polynomial_map]
          apply Int.cast_eq_zero.mpr
          exact heval z hz ((residueCode_eq_iff p t z center).mp (hza.trans hca.symm))
    · refine ⟨1, one_ne_zero, fun _ => ?_, ?_⟩
      · simpa only [MvPolynomial.totalDegree_one, Nat.cast_zero] using hbound t
      · intro ht z hz hza
        exact (ha ⟨ht, Finset.mem_image.mpr ⟨z, hz, hza⟩⟩).elim
  choose P hP0 hPdeg hPzero using hex
  refine ⟨r, hdepth, ?_, ?_, P, hP0, ?_, ?_⟩
  · calc
      _ = 6 * (L * B ^ ((41 : ℝ) / 100) / (p : ℝ) ^ r) := by ring
      _ < 6 * (L * p) := mul_lt_mul_of_pos_left hlast (by norm_num)
      _ = _ := by ring
  · intro t ht
    exact (card_residueCode_image_le p t hp.ne_zero (sexticBox c B)).trans (hlevels t ht).1
  · intro t ht a
    exact hPdeg t a ht
  · intro t ht z hz
    exact hPzero t (residueCode p t z) ht z hz rfl

#print axioms exists_sextic_plane_classes
-- 'Erdos477.Geometry.exists_sextic_plane_classes' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
