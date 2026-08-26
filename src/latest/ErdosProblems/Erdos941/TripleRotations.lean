import ErdosProblems.Erdos941.EulerTripleMap

/-! # Signed cyclic rotations detect every nonzero linear map modulo an odd prime -/

namespace Erdos941

def tripleCoord (v : Triple) (i : Fin 3) : ℤ := ![v.1, v.2.1, v.2.2] i

def cyclicTriple (v : Triple) : Triple := (v.2.2, v.1, v.2.1)

def flipTriple (i : Fin 3) (v : Triple) : Triple :=
  (2 * tripleCoord v i) • tripleBasis i - v

theorem cyclicTriple_norm (v : Triple) : tripleNorm (cyclicTriple v) = tripleNorm v := by
  dsimp [cyclicTriple, tripleNorm, norm3]
  ring

theorem PrimitiveTriple.cyclic {v : Triple} (hv : PrimitiveTriple v) :
    PrimitiveTriple (cyclicTriple v) := by
  obtain ⟨a, b, c, h⟩ := hv
  refine ⟨c, a, b, ?_⟩
  dsimp [cyclicTriple]
  linear_combination h

theorem flipTriple_norm (i : Fin 3) (v : Triple) :
    tripleNorm (flipTriple i v) = tripleNorm v := by
  fin_cases i <;> norm_num [flipTriple, tripleCoord, tripleBasis, tripleNorm, norm3,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] <;> ring

theorem PrimitiveTriple.flip {v : Triple} (hv : PrimitiveTriple v) (i : Fin 3) :
    PrimitiveTriple (flipTriple i v) := by
  obtain ⟨a, b, c, h⟩ := hv
  fin_cases i
  · refine ⟨a, -b, -c, ?_⟩
    norm_num [flipTriple, tripleCoord, tripleBasis]
    linear_combination h
  · refine ⟨-a, b, -c, ?_⟩
    norm_num [flipTriple, tripleCoord, tripleBasis]
    linear_combination h
  · refine ⟨-a, -b, c, ?_⟩
    norm_num [flipTriple, tripleCoord, tripleBasis,
      show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
    linear_combination h

theorem triple_add_flip (i : Fin 3) (v : Triple) :
    v + flipTriple i v = (2 * tripleCoord v i) • tripleBasis i := by
  unfold flipTriple
  abel

theorem primitive_cyclic_coordinates {v : Triple} (hv : PrimitiveTriple v) (i : Fin 3) :
    ∃ a b c : ℤ, a * tripleCoord v i + b * tripleCoord (cyclicTriple v) i +
      c * tripleCoord (cyclicTriple (cyclicTriple v)) i = 1 := by
  obtain ⟨a, b, c, h⟩ := hv
  fin_cases i
  · refine ⟨a, c, b, ?_⟩
    norm_num [tripleCoord, cyclicTriple]
    linear_combination h
  · refine ⟨b, a, c, ?_⟩
    norm_num [tripleCoord, cyclicTriple]
    linear_combination h
  · refine ⟨c, b, a, ?_⟩
    norm_num [tripleCoord, cyclicTriple]
    linear_combination h

theorem exists_primitive_rotate_nondvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {v : Triple} (hv : PrimitiveTriple v) (T : Triple →ₗ[ℤ] Triple)
    (hT : ∃ i : Fin 3, ¬TripleDivisible p (T (tripleBasis i))) :
    ∃ w : Triple, tripleNorm w = tripleNorm v ∧ PrimitiveTriple w ∧
      ¬TripleDivisible p (T w) := by
  by_contra! hall
  obtain ⟨i, hi⟩ := hT
  have hdiv (u : Triple) (hu : tripleNorm u = tripleNorm v) (hpU : PrimitiveTriple u) :
      TripleDivisible p ((2 * tripleCoord u i) • T (tripleBasis i)) := by
    have hh := (hall u hu hpU).add
      (hall (flipTriple i u) ((flipTriple_norm i u).trans hu) (hpU.flip i))
    rw [← map_add, triple_add_flip, map_smul] at hh
    exact hh
  have h0 := hdiv v rfl hv
  have h1 := hdiv (cyclicTriple v) (cyclicTriple_norm v) hv.cyclic
  have h2 := hdiv (cyclicTriple (cyclicTriple v))
    ((cyclicTriple_norm _).trans (cyclicTriple_norm v)) hv.cyclic.cyclic
  obtain ⟨a, b, c, habc⟩ := primitive_cyclic_coordinates hv i
  have hh := ((h0.smul (r := a)).add (h1.smul (r := b))).add (h2.smul (r := c))
  rw [smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul] at hh
  have hcoef : a * (2 * tripleCoord v i) + b * (2 * tripleCoord (cyclicTriple v) i) +
      c * (2 * tripleCoord (cyclicTriple (cyclicTriple v)) i) = 2 := by
    linear_combination 2 * habc
  rw [hcoef] at hh
  have hpI : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have htwo : ¬(p : ℤ) ∣ 2 := by
    intro h
    have hN : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hN |>.resolve_left hp.ne_one)
  exact hi ⟨(hpI.dvd_mul.mp hh.1).resolve_left htwo,
    (hpI.dvd_mul.mp hh.2.1).resolve_left htwo, (hpI.dvd_mul.mp hh.2.2).resolve_left htwo⟩

end Erdos941
