/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The resultant root bound for a finite set of common zeroes with distinct projections.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ResultantDegree
import ErdosProblems.Erdos477.Geometry.ResultantNonzero

namespace Erdos477.Geometry

open scoped Polynomial

noncomputable def bivariateEval {K : Type*} [CommRing K] (x y : K) : K[X][X] →+* K :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom x) y

variable {K : Type*} [Field K]

lemma outer_natDegree_le (f : K[X][X]) (m : ℕ)
    (hf : ∀ j, f.coeff j ≠ 0 → (f.coeff j).natDegree + j ≤ m) : f.natDegree ≤ m := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_contra h
  have hbound := hf j h
  omega

lemma resultant_eval_eq_zero_of_common_zero (f g : K[X][X]) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hpos : m ≠ 0 ∨ n ≠ 0)
    (x y : K) (hfx : bivariateEval x y f = 0) (hgx : bivariateEval x y g = 0) :
    (f.resultant g m n).eval x = 0 := by
  obtain ⟨P, Q, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant f g hf hg hpos
  have h' := congrArg (bivariateEval x y) h
  simp only [map_add, map_mul, hfx, hgx, zero_mul, add_zero] at h'
  simpa [bivariateEval] using h'.symm

/-- The elementary projection form of the plane intersection bound. The
projection injectivity and resultant nonvanishing are explicit hypotheses
of this helper and still have to be supplied when it is applied. -/
theorem card_common_zeroes_le_of_projection (f g : K[X][X]) (m n : ℕ)
    (hf : ∀ j, f.coeff j ≠ 0 → (f.coeff j).natDegree + j ≤ m)
    (hg : ∀ j, g.coeff j ≠ 0 → (g.coeff j).natDegree + j ≤ n)
    (hpos : m ≠ 0 ∨ n ≠ 0) (hres : f.resultant g m n ≠ 0)
    (S : Finset (K × K)) (hS : ∀ z ∈ S, bivariateEval z.1 z.2 f = 0 ∧
      bivariateEval z.1 z.2 g = 0)
    (hinj : Set.InjOn Prod.fst (S : Set (K × K))) : S.card ≤ m * n := by
  classical
  have hroots (z : ↥S) : (f.resultant g m n).eval z.val.1 = 0 :=
    resultant_eval_eq_zero_of_common_zero f g m n
      (outer_natDegree_le f m hf) (outer_natDegree_le g n hg) hpos z.val.1 z.val.2
      (hS z.val z.property).1 (hS z.val z.property).2
  have hcard : S.card ≤ (f.resultant g m n).natDegree := by
    by_contra h
    apply hres
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (ι := ↥S) _
      (fun a b hab => Subtype.ext (hinj a.property b.property hab)) hroots
    simpa only [Fintype.card_coe] using Nat.lt_of_not_ge h
  exact hcard.trans (natDegree_resultant_le f g m n hf hg)

lemma no_common_zero_of_constant_outer (f g : K[X][X])
    (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (hfd : f.natDegree = 0) (hgd : g.natDegree = 0) (x y : K) :
    ¬ (bivariateEval x y f = 0 ∧ bivariateEval x y g = 0) := by
  have hfc := Polynomial.eq_C_of_natDegree_eq_zero hfd
  have hgc := Polynomial.eq_C_of_natDegree_eq_zero hgd
  have hfi : Irreducible (f.coeff 0) := by
    have h := hf
    rw [hfc] at h
    exact Irreducible.of_map (f := Polynomial.C) h
  have hnot : ¬ f.coeff 0 ∣ g.coeff 0 := by
    intro h
    apply hfg
    rw [hfc, hgc]
    exact map_dvd Polynomial.C h
  obtain ⟨u, v, huv⟩ := hfi.coprime_iff_not_dvd.mpr hnot
  rintro ⟨hfx, hgx⟩
  rw [hfc] at hfx
  rw [hgc] at hgx
  have hfx' : (f.coeff 0).eval x = 0 := by simpa [bivariateEval] using hfx
  have hgx' : (g.coeff 0).eval x = 0 := by simpa [bivariateEval] using hgx
  have h := congrArg (Polynomial.evalRingHom x) huv
  simp only [map_add, map_mul, map_one, Polynomial.coe_evalRingHom, hfx', hgx',
    mul_zero, add_zero] at h
  exact zero_ne_one h

/-- The remaining hypotheses here concern only the chosen projection;
irreducibility and nondivisibility supply resultant nonvanishing. -/
theorem card_common_zeroes_le_of_irreducible_projection (f g : K[X][X]) (d e : ℕ)
    (hf : ∀ j, f.coeff j ≠ 0 → (f.coeff j).natDegree + j ≤ d)
    (hg : ∀ j, g.coeff j ≠ 0 → (g.coeff j).natDegree + j ≤ e)
    (hirr : Irreducible f) (hfg : ¬ f ∣ g)
    (S : Finset (K × K)) (hS : ∀ z ∈ S, bivariateEval z.1 z.2 f = 0 ∧
      bivariateEval z.1 z.2 g = 0)
    (hinj : Set.InjOn Prod.fst (S : Set (K × K))) : S.card ≤ d * e := by
  classical
  by_cases hpos : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0
  · have hres := resultant_ne_zero_of_irreducible_not_dvd f g hirr hfg
    have hroots (z : ↥S) : (f.resultant g).eval z.val.1 = 0 :=
      resultant_eval_eq_zero_of_common_zero f g f.natDegree g.natDegree le_rfl le_rfl hpos
        z.val.1 z.val.2 (hS z.val z.property).1 (hS z.val z.property).2
    have hcard : S.card ≤ (f.resultant g).natDegree := by
      by_contra h
      apply hres
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (ι := ↥S) _
        (fun a b hab => Subtype.ext (hinj a.property b.property hab)) hroots
      simpa only [Fintype.card_coe] using Nat.lt_of_not_ge h
    exact hcard.trans (natDegree_resultant_le_total f g f.natDegree g.natDegree d e
      (outer_natDegree_le f d hf) (outer_natDegree_le g e hg) hf hg)
  · push Not at hpos
    have hnil : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun z hz =>
      no_common_zero_of_constant_outer f g hirr hfg hpos.1 hpos.2 z.1 z.2 (hS z hz))
    simp only [hnil, Finset.card_empty, zero_le]

#print axioms card_common_zeroes_le_of_projection
-- 'Erdos477.Geometry.card_common_zeroes_le_of_projection' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
