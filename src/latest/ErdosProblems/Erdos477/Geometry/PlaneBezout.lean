/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A finite-point form of the affine plane Bézout bound.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.BivariateEquiv
import ErdosProblems.Erdos477.Geometry.SeparatingProjection
import ErdosProblems.Erdos477.Geometry.Shear

namespace Erdos477.Geometry

variable {K : Type*} [Field K] [Infinite K]

/-- An irreducible plane polynomial of degree `d` and a polynomial of degree
`e` not divisible by it have at most `d*e` distinct common affine zeroes. -/
theorem card_common_zeroes_le (P Q : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hPQ : ¬ P ∣ Q) (S : Finset (K × K))
    (hS : ∀ z ∈ S, MvPolynomial.eval ![z.1, z.2] P = 0 ∧
      MvPolynomial.eval ![z.1, z.2] Q = 0) :
    S.card ≤ P.totalDegree * Q.totalDegree := by
  classical
  obtain ⟨a, ha⟩ := exists_separating_second_slope S
  let τ : K × K → K × K := fun z => (z.2 + a * z.1, z.1)
  let T := S.image τ
  let e := (shearEquiv a).trans (bivariateEquiv K).toRingEquiv
  let f := e P
  let g := e Q
  have hτ : Function.Injective τ := by
    intro z w h
    have hfst := congrArg Prod.fst h
    have hsnd : z.1 = w.1 := congrArg Prod.snd h
    apply Prod.ext hsnd
    change z.2 + a * z.1 = w.2 + a * w.1 at hfst
    rw [hsnd] at hfst
    exact add_right_cancel hfst
  have hcard : T.card = S.card := Finset.card_image_of_injective S hτ
  have hf : Irreducible f := (MulEquiv.irreducible_iff e).mpr hP
  have hfg : ¬ f ∣ g := by
    intro h
    apply hPQ
    simpa only [f, g, RingEquiv.symm_apply_apply] using map_dvd e.symm h
  have hfdegree (j) (hj : f.coeff j ≠ 0) :
      (f.coeff j).natDegree + j ≤ P.totalDegree := by
    have h := bivariateEquiv_coeff_degree (shear a P) j hj
    rwa [totalDegree_shear] at h
  have hgdegree (j) (hj : g.coeff j ≠ 0) :
      (g.coeff j).natDegree + j ≤ Q.totalDegree := by
    have h := bivariateEquiv_coeff_degree (shear a Q) j hj
    rwa [totalDegree_shear] at h
  have hT (z) (hz : z ∈ T) : bivariateEval z.1 z.2 f = 0 ∧
      bivariateEval z.1 z.2 g = 0 := by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    change bivariateEval (w.2 + a * w.1) w.1 (bivariateEquiv K (shear a P)) = 0 ∧
      bivariateEval (w.2 + a * w.1) w.1 (bivariateEquiv K (shear a Q)) = 0
    rw [bivariateEquiv_eval, bivariateEquiv_eval, eval_shear, eval_shear]
    exact hS w hw
  have hproj : Set.InjOn Prod.fst (T : Set (K × K)) := by
    intro z hz w hw hzw
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact congrArg τ (ha hz' hw' hzw)
  rw [← hcard]
  exact card_common_zeroes_le_of_irreducible_projection f g P.totalDegree Q.totalDegree
    hfdegree hgdegree hf hfg T hT hproj

theorem finite_common_zeroes (P Q : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hPQ : ¬ P ∣ Q) :
    {z : K × K | MvPolynomial.eval ![z.1, z.2] P = 0 ∧
      MvPolynomial.eval ![z.1, z.2] Q = 0}.Finite := by
  by_contra h
  obtain ⟨S, hS, hcard⟩ := Set.Infinite.exists_subset_card_eq h
    (P.totalDegree * Q.totalDegree + 1)
  have hbound := card_common_zeroes_le P Q hP hPQ S (fun z hz => hS hz)
  omega

#print axioms card_common_zeroes_le
-- 'Erdos477.Geometry.card_common_zeroes_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
