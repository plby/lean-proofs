import Util.Bernays.Coordinates
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Int.Interval

/-!
# Reduction of positive definite integral binary quadratic forms

Choosing the least leading coefficient in an equivalence class, then reducing
the middle coefficient modulo twice that coefficient, gives a reduced form.
The discriminant bounds all three coefficients of a reduced form, so there
are finitely many reduced forms of each fixed discriminant.
-/

namespace BinQuadForm

/-- The inequalities needed for finiteness of reduced forms. No boundary
convention for uniqueness of representatives is imposed. -/
def Reduced (f : BinQuadForm) : Prop := f.PosDef ∧ |f.b| ≤ f.a ∧ f.a ≤ f.c

theorem properEquiv_shear (f : BinQuadForm) (k : ℤ) :
    ProperEquiv f (f.changeVariables 1 k 0 1) :=
  ⟨1, k, 0, 1, by ring, rfl⟩

theorem properEquiv_swap (f : BinQuadForm) :
    ProperEquiv f (f.changeVariables 0 (-1) 1 0) :=
  ⟨0, -1, 1, 0, by norm_num, rfl⟩

theorem shear_a (f : BinQuadForm) (k : ℤ) : (f.changeVariables 1 k 0 1).a = f.a := by
  simp [changeVariables]

theorem shear_b (f : BinQuadForm) (k : ℤ) :
    (f.changeVariables 1 k 0 1).b = f.b + 2 * f.a * k := by
  simp [changeVariables, add_comm]

theorem swap_a (f : BinQuadForm) : (f.changeVariables 0 (-1) 1 0).a = f.c := by
  simp [changeVariables]

theorem exists_reduced {f : BinQuadForm} (hf : f.PosDef) :
    ∃ g : BinQuadForm, ProperEquiv f g ∧ g.Reduced := by
  let P : ℤ → Prop := fun a => ∃ g : BinQuadForm, ProperEquiv f g ∧ g.a = a
  have hbdd : ∃ b : ℤ, ∀ a, P a → b ≤ a := by
    refine ⟨0, ?_⟩
    rintro a ⟨g, hfg, rfl⟩
    exact (hfg.posDef hf).1.le
  have hne : ∃ a, P a := ⟨f.a, f, ProperEquiv.refl f, rfl⟩
  obtain ⟨a, ⟨g, hfg, hga⟩, hmin⟩ := Int.exists_least_of_bdd hbdd hne
  subst a
  have hg := hfg.posDef hf
  let k : ℤ := -((g.b + g.a) / (2 * g.a))
  let h : BinQuadForm := g.changeVariables 1 k 0 1
  have hgh : ProperEquiv g h := g.properEquiv_shear k
  have hfh : ProperEquiv f h := hfg.trans hgh
  have hha : h.a = g.a := g.shear_a k
  have hhb : h.b = (g.b + g.a) % (2 * g.a) - g.a := by
    rw [show h.b = g.b + 2 * g.a * k from g.shear_b k]
    dsimp [k]
    have hdiv := Int.emod_add_mul_ediv (g.b + g.a) (2 * g.a)
    nlinarith
  have hmod₀ : 0 ≤ (g.b + g.a) % (2 * g.a) :=
    Int.emod_nonneg _ (mul_ne_zero (by norm_num) hg.1.ne')
  have hmod₁ : (g.b + g.a) % (2 * g.a) < 2 * g.a :=
    Int.emod_lt_of_pos _ (mul_pos (by norm_num) hg.1)
  refine ⟨h, hfh, hfh.posDef hf, ?_, ?_⟩
  · rw [abs_le, hhb, hha]
    constructor <;> omega
  · have hswap := hmin (h.changeVariables 0 (-1) 1 0).a
      ⟨h.changeVariables 0 (-1) 1 0, hfh.trans h.properEquiv_swap, rfl⟩
    rwa [h.swap_a, ← hha] at hswap

theorem Reduced.discr_bound {f : BinQuadForm} (hf : f.Reduced) :
    3 * f.a ^ 2 ≤ -f.discr := by
  obtain ⟨hpos, hb, hc⟩ := hf
  obtain ⟨hb₀, hb₁⟩ := abs_le.mp hb
  have hbSq : f.b ^ 2 ≤ f.a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb₁) (by linarith : 0 ≤ f.a + f.b)]
  have hac := mul_le_mul_of_nonneg_left hc hpos.1.le
  dsimp [discr]
  nlinarith

theorem Reduced.coeff_bounds {f : BinQuadForm} (hf : f.Reduced) :
    1 ≤ f.a ∧ f.a ≤ -f.discr ∧
      f.discr ≤ f.b ∧ f.b ≤ -f.discr ∧ 1 ≤ f.c ∧ f.c ≤ -f.discr := by
  have ha : 1 ≤ f.a := hf.1.1
  have hc : 1 ≤ f.c := ha.trans hf.2.2
  have hD := hf.discr_bound
  have haD : f.a ≤ -f.discr := by nlinarith
  obtain ⟨hb₀, hb₁⟩ := abs_le.mp hf.2.1
  have hbSq : f.b ^ 2 ≤ f.a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb₁) (by linarith : 0 ≤ f.a + f.b)]
  have hcD : f.c ≤ -f.discr := by
    have hac : f.c ≤ f.a * f.c := by nlinarith
    have hid : 4 * f.a * f.c = f.b ^ 2 - f.discr := by simp [discr]; ring
    nlinarith
  exact ⟨ha, haD, by linarith, hb₁.trans haD, hc, hcD⟩

/-- A finite family containing every reduced form of the given discriminant. -/
noncomputable def reducedForms (Δ : ℤ) : Finset BinQuadForm := by
  classical
  exact (((Finset.Icc 1 (-Δ)).product
    ((Finset.Icc Δ (-Δ)).product (Finset.Icc 1 (-Δ)))).image
      (fun t => ⟨t.1, t.2.1, t.2.2⟩)).filter
        (fun f => f.Reduced ∧ f.discr = Δ)

theorem mem_reducedForms {Δ : ℤ} {f : BinQuadForm} :
    f ∈ reducedForms Δ ↔ f.Reduced ∧ f.discr = Δ := by
  classical
  unfold reducedForms
  constructor
  · intro hf
    exact (Finset.mem_filter.mp hf).2
  · rintro ⟨hf, hΔ⟩
    have hb := hf.coeff_bounds
    apply Finset.mem_filter.mpr
    refine ⟨?_, hf, hΔ⟩
    apply Finset.mem_image.mpr
    refine ⟨(f.a, f.b, f.c), ?_, rfl⟩
    rw [← hΔ]
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb.1, hb.2.1⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb.2.2.1, hb.2.2.2.1⟩,
        Finset.mem_Icc.mpr hb.2.2.2.2⟩⟩

theorem exists_equiv_mem_reducedForms {f : BinQuadForm} (hf : f.PosDef) :
    ∃ g ∈ reducedForms f.discr, ProperEquiv f g := by
  obtain ⟨g, hfg, hg⟩ := exists_reduced hf
  exact ⟨g, mem_reducedForms.mpr ⟨hg, hfg.discr_eq.symm⟩, hfg⟩

end BinQuadForm
