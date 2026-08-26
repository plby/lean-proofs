import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

/-- Finite double-counting: if every object is selected by at least a `1/Q`
fraction of samples (in cleared cardinal form), then some sample selects at
least a `1/Q` fraction of all objects. -/
theorem exists_sample_many
    {Ω C : Type*} [Fintype Ω] [Nonempty Ω] [Fintype C]
    (Sel : Ω → C → Prop) [DecidableRel Sel]
    (Q : ℕ)
    (hcol : ∀ c : C,
      Fintype.card Ω ≤ Q * (Finset.univ.filter fun ω => Sel ω c).card) :
    ∃ ω : Ω, Fintype.card C ≤
      Q * (Finset.univ.filter fun c => Sel ω c).card := by
  classical
  have hdouble :
      ∑ c : C, (Finset.univ.filter fun ω => Sel ω c).card =
        ∑ ω : Ω, (Finset.univ.filter fun c => Sel ω c).card := by
    simp only [Finset.card_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  have hlower : Fintype.card C * Fintype.card Ω ≤
      Q * ∑ c : C, (Finset.univ.filter fun ω => Sel ω c).card := by
    calc
      Fintype.card C * Fintype.card Ω = ∑ _c : C, Fintype.card Ω := by simp
      _ ≤ ∑ c : C, Q * (Finset.univ.filter fun ω => Sel ω c).card := by
        exact Finset.sum_le_sum fun c _ => hcol c
      _ = Q * ∑ c : C, (Finset.univ.filter fun ω => Sel ω c).card := by
        rw [Finset.mul_sum]
  by_contra h
  push_neg at h
  have hupper : Q * ∑ ω : Ω, (Finset.univ.filter fun c => Sel ω c).card <
      Fintype.card Ω * Fintype.card C := by
    calc
      Q * ∑ ω : Ω, (Finset.univ.filter fun c => Sel ω c).card =
          ∑ ω : Ω, Q * (Finset.univ.filter fun c => Sel ω c).card := by
        rw [Finset.mul_sum]
      _ < ∑ _ω : Ω, Fintype.card C := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro ω _
        exact h ω
      _ = Fintype.card Ω * Fintype.card C := by simp
  rw [hdouble, Nat.mul_comm (Fintype.card C) (Fintype.card Ω)] at hlower
  omega

/-- Range form of finite averaging: uniform embeddings of a parameter type
into the sample space, one for each object, produce one sample lying in many
ranges. -/
theorem exists_sample_in_many_ranges
    {Ω C P : Type*} [Fintype Ω] [Nonempty Ω] [Fintype C] [Fintype P]
    [DecidableEq Ω]
    (e : C → P ↪ Ω) (Q : ℕ)
    (hcard : Fintype.card Ω ≤ Q * Fintype.card P) :
    ∃ ω : Ω, Fintype.card C ≤
      Q * (Finset.univ.filter fun c => ω ∈ Set.range (e c)).card := by
  classical
  let Sel : Ω → C → Prop := fun ω c => ω ∈ Set.range (e c)
  have hevent : ∀ c : C,
      (Finset.univ.filter fun ω => Sel ω c).card = Fintype.card P := by
    intro c
    let image := Finset.univ.image (e c)
    have himage : image = Finset.univ.filter fun ω => Sel ω c := by
      ext ω
      simp [image, Sel, Set.mem_range]
    rw [← himage, Finset.card_image_of_injective Finset.univ (e c).injective]
    simp
  apply exists_sample_many Sel Q
  intro c
  rw [hevent c]
  exact hcard

end Erdos538.IsotropicKernel
