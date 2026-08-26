/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite local polynomial parametrizations of a sextic graph.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.LocalRoots
import ErdosProblems.Erdos477.Counting.LocalDeterminant

namespace Erdos477.Counting

variable {R : Type*} [CommRing R]

/-- Polynomial evaluation preserves coordinatewise congruences. -/
lemma dvd_eval_sub_eval {σ : Type*} (p : R) (F : MvPolynomial σ R)
    (x y : σ → R) (h : ∀ i, p ∣ x i - y i) :
    p ∣ MvPolynomial.eval x F - MvPolynomial.eval y F := by
  let I : Ideal R := Ideal.span {p}
  let φ := Ideal.Quotient.mk I
  have hxy : φ ∘ x = φ ∘ y := by
    funext i
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h i))
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq.mp
  change φ (MvPolynomial.eval₂ (RingHom.id R) x F) =
    φ (MvPolynomial.eval₂ (RingHom.id R) y F)
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hxy]

/-- A polynomial approximation to the coordinate `z` on the graph
`z^6 = G(x,y)`, near the unit `v`. -/
noncomputable def graphApprox [BinomialRing R] (a : R) (v : Rˣ)
    (G : MvPolynomial (Fin 2) R) (N : ℕ) : MvPolynomial (Fin 2) R :=
  MvPolynomial.C (v : R) * (rootApprox a N).eval₂ MvPolynomial.C
    (MvPolynomial.C ((v⁻¹ : Rˣ) : R) ^ 6 * G - 1)

lemma eval_graphApprox [BinomialRing R] (a : R) (v : Rˣ)
    (G : MvPolynomial (Fin 2) R) (N : ℕ) (x : Fin 2 → R) :
    MvPolynomial.eval x (graphApprox a v G N) =
      (v : R) * (rootApprox a N).eval
        (((v⁻¹ : Rˣ) : R) ^ 6 * MvPolynomial.eval x G - 1) := by
  unfold graphApprox
  rw [map_mul, MvPolynomial.eval_C, Polynomial.hom_eval₂]
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id R := by
    ext r
    simp
  simp only [hc, map_sub, map_mul, map_pow,
    MvPolynomial.eval_C, map_one, Polynomial.eval₂_id]

/-- The local graph approximation agrees to every finite order. The only
geometric hypothesis is the explicit graph equation, with a unit center. -/
theorem pow_dvd_sub_graphApprox [IsLocalRing R] [BinomialRing R]
    (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (v : Rˣ) (G : MvPolynomial (Fin 2) R) (x : Fin 2 → R) (z : R)
    (hz : p ∣ z - (v : R)) (hgraph : z ^ 6 = MvPolynomial.eval x G) (N : ℕ) :
    p ^ N ∣ z - MvPolynomial.eval x (graphApprox a v G N) := by
  let q : R := ((v⁻¹ : Rˣ) : R) * z
  let t : R := ((v⁻¹ : Rˣ) : R) ^ 6 * MvPolynomial.eval x G - 1
  have hq : p ∣ q - 1 := by
    have h := dvd_mul_of_dvd_right hz (((v⁻¹ : Rˣ) : R))
    simpa only [mul_sub, Units.inv_mul, q] using h
  have hroot : q ^ 6 = 1 + t := by
    dsimp only [q, t]
    rw [mul_pow, hgraph]
    ring
  have ht : p ∣ t := by
    have h := hq.trans (sub_one_dvd_pow_sub_one q 6)
    simpa only [hroot, add_sub_cancel_left] using h
  have h := pow_dvd_rootApprox_sub_root a ha p q t hp hq ht hroot N
  have hmul := dvd_mul_of_dvd_right h (v : R)
  rw [eval_graphApprox]
  simpa only [mul_sub, q, ← mul_assoc, Units.mul_inv, one_mul, t] using hmul

/-- Substitute the approximate graph coordinate in a polynomial in three
variables. -/
noncomputable def onGraphApprox [BinomialRing R] (a : R) (v : Rˣ)
    (G : MvPolynomial (Fin 2) R) (N : ℕ) (F : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂ MvPolynomial.C
    ![MvPolynomial.X 0, MvPolynomial.X 1, graphApprox a v G N] F

lemma eval_onGraphApprox [BinomialRing R] (a : R) (v : Rˣ)
    (G : MvPolynomial (Fin 2) R) (N : ℕ) (F : MvPolynomial (Fin 3) R) (x y : R) :
    MvPolynomial.eval ![x, y] (onGraphApprox a v G N F) =
      MvPolynomial.eval ![x, y, MvPolynomial.eval ![x, y] (graphApprox a v G N)] F := by
  unfold onGraphApprox
  rw [← MvPolynomial.eval_assoc]
  have hcoords : MvPolynomial.eval ![x, y] ∘
      ![MvPolynomial.X 0, MvPolynomial.X 1, graphApprox a v G N] =
      ![x, y, MvPolynomial.eval ![x, y] (graphApprox a v G N)] := by
    funext i
    fin_cases i <;> simp
  rw [hcoords]

/-- The graph approximation also approximates every polynomial function on
the graph; its coefficients are uniform across the whole residue class. -/
theorem pow_dvd_eval_sub_onGraphApprox [IsLocalRing R] [BinomialRing R]
    (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (v : Rˣ) (G : MvPolynomial (Fin 2) R) (F : MvPolynomial (Fin 3) R)
    (x y z : R) (hz : p ∣ z - (v : R))
    (hgraph : z ^ 6 = MvPolynomial.eval ![x, y] G) (N : ℕ) :
    p ^ N ∣ MvPolynomial.eval ![x, y, z] F -
      MvPolynomial.eval ![x, y] (onGraphApprox a v G N F) := by
  rw [eval_onGraphApprox]
  apply dvd_eval_sub_eval
  intro i
  fin_cases i
  · simp
  · simp
  · simpa using pow_dvd_sub_graphApprox a ha p hp v G ![x, y] z hz hgraph N

/-- The local determinant estimate for a sextic graph at a unit coordinate. -/
theorem pow_dvd_graph_eval_det [IsLocalRing R] [BinomialRing R]
    {s : ℕ} (a : R) (ha : 6 * a = 1) (p : R) (hp : ¬ IsUnit p)
    (v : Rˣ) (G : MvPolynomial (Fin 2) R) (F : Fin s → MvPolynomial (Fin 3) R)
    (x₀ y₀ : R) (x y z : Fin s → R) (hz : ∀ j, p ∣ z j - (v : R))
    (hgraph : ∀ j, z j ^ 6 = MvPolynomial.eval ![x₀ + p * x j, y₀ + p * y j] G)
    (m : ℕ) :
    p ^ localExponent s m ∣ Matrix.det (Matrix.of fun i j =>
      MvPolynomial.eval ![x₀ + p * x j, y₀ + p * y j, z j] (F i)) := by
  let N := localExponent s m
  let H : Fin s → MvPolynomial (Fin 2) R := fun i => onGraphApprox a v G N (F i)
  apply pow_dvd_det_of_approximation p N N le_rfl _
    (Matrix.of fun i j => MvPolynomial.eval ![x₀ + p * x j, y₀ + p * y j] (H i))
  · intro i j
    exact pow_dvd_eval_sub_onGraphApprox a ha p hp v G (F i)
      (x₀ + p * x j) (y₀ + p * y j) (z j) (hz j) (hgraph j) N
  · exact pow_dvd_polynomial_eval_det_translate p x₀ y₀ H x y m

#print axioms pow_dvd_graph_eval_det
-- 'Erdos477.Counting.pow_dvd_graph_eval_det' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
