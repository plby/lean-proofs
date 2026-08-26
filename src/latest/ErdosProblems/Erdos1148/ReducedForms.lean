import ErdosProblems.Erdos1148.ReducedFormBounds
import ErdosProblems.Erdos1148.IntegralFormOrbits

/-! # A bounded representative in every nonsquare integral form orbit -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def shearFormSL (k : ℤ) : SL(2, ℤ) :=
  ⟨!![1, -k; 0, 1], by simp [Matrix.det_fin_two]⟩

def swapFormSL : SL(2, ℤ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

lemma formAction_shearFormSL (k : ℤ) (t : ℤ × ℤ × ℤ) :
    formAction (shearFormSL k) t =
      (t.1, t.2.1 + 2 * t.1 * k, t.2.2 + t.2.1 * k + t.1 * k ^ 2) := by
  rw [formAction, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext <;> dsimp [transform, shearFormSL] <;> ring

lemma formAction_swapFormSL (t : ℤ × ℤ × ℤ) :
    formAction swapFormSL t = (t.2.2, -t.2.1, t.1) := by
  rw [formAction, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext <;> dsimp [transform, swapFormSL] <;> ring

lemma exists_minimal_leading_form (t : ℤ × ℤ × ℤ) :
    ∃ g : SL(2, ℤ), ∀ h : SL(2, ℤ),
      (formAction g t).1.natAbs ≤ (formAction h t).1.natAbs := by
  classical
  let P : ℕ → Prop := fun n => ∃ g : SL(2, ℤ), (formAction g t).1.natAbs = n
  have hP : ∃ n, P n := ⟨_, 1, rfl⟩
  obtain ⟨g, hg⟩ := Nat.find_spec hP
  refine ⟨g, ?_⟩
  intro h
  rw [hg]
  exact Nat.find_min' hP ⟨h, rfl⟩

theorem exists_bounded_integral_form_representative {d : ℤ} (hd : 0 < d)
    (hns : ¬IsSquare d) {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    ∃ g : SL(2, ℤ), |(formAction g t).1| ≤ d ∧
      |(formAction g t).2.1| ≤ d ∧ |(formAction g t).2.2| ≤ d := by
  obtain ⟨g, hmin⟩ := exists_minimal_leading_form t
  have hgd : discr (formAction g t) = d := (discr_formAction g t).trans ht
  have ha := fst_ne_zero_of_nonsquare_discr hns hgd
  obtain ⟨k, hk⟩ := exists_balanced_shear ha (formAction g t).2.1
  let g' := shearFormSL k * g
  let u := formAction g' t
  have hua : u.1 = (formAction g t).1 := by
    dsimp [u, g']
    rw [formAction_mul, formAction_shearFormSL]
  have hub : |u.2.1| ≤ |u.1| := by
    dsimp [u, g']
    simpa only [formAction_mul, formAction_shearFormSL] using hk
  have huc : |u.1| ≤ |u.2.2| := by
    have hm := hmin (swapFormSL * g')
    rw [formAction_mul, formAction_swapFormSL] at hm
    have hz : ((formAction g t).1.natAbs : ℤ) ≤ ((formAction g' t).2.2.natAbs : ℤ) :=
      Int.ofNat_le.mpr hm
    simpa only [Int.natCast_natAbs, ← hua] using hz
  have hud : discr u = d := (discr_formAction g' t).trans ht
  have hua0 : u.1 ≠ 0 := hua ▸ ha
  exact ⟨g', coeff_bounds_of_reduced hd hud hua0 hub huc⟩

theorem finite_integralFormOrbits {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d) :
    Finite (IntegralFormOrbits d) := by
  classical
  let box : Finset (ℤ × ℤ × ℤ) := Finset.Icc (-d, -d, -d) (d, d, d)
  have hrep (q : IntegralFormOrbits d) :
      ∃ u : IntegralDiscrForm d, u.1 ∈ box ∧ integralFormOrbitMk u = q := by
    obtain ⟨g, ha, hb, hc⟩ := exists_bounded_integral_form_representative hd hns q.out.2
    refine ⟨g • q.out, ?_, ?_⟩
    · have ha' := abs_le.mp ha
      have hb' := abs_le.mp hb
      have hc' := abs_le.mp hc
      change formAction g q.out.1 ∈ Finset.Icc (-d, -d, -d) (d, d, d)
      simp only [Finset.mem_Icc, Prod.le_def]
      exact ⟨⟨ha'.1, hb'.1, hc'.1⟩, ha'.2, hb'.2, hc'.2⟩
    · exact (integralFormOrbitMk_action g q.out).trans (Quotient.out_eq q)
  choose u huBox huEq using hrep
  let rep : IntegralFormOrbits d → ↥box := fun q => ⟨(u q).1, huBox q⟩
  apply Finite.of_injective rep
  intro q r heq
  have hval : (u q).1 = (u r).1 := congrArg (fun x : ↥box => x.val) heq
  calc
    q = integralFormOrbitMk (u q) := (huEq q).symm
    _ = integralFormOrbitMk (u r) := congrArg integralFormOrbitMk (Subtype.ext hval)
    _ = r := huEq r

end Erdos1148.DukeArithmetic
