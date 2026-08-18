import Mathlib

/-!
# Similarities preserve translational equidecompositions

This file supplies the algebraic conjugation used to pass from the unit
circle-squaring theorem to an arbitrary positive radius.
-/

open Set Function

namespace Erdos1124

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Translation by a fixed vector as an equivalence. -/
def translateEquiv (t : V) : V ≃ V where
  toFun x := t + x
  invFun x := -t + x
  left_inv x := by simp
  right_inv x := by simp

@[simp] lemma translateEquiv_apply (t x : V) : translateEquiv t x = t + x := rfl

@[simp] lemma translateEquiv_symm_apply (t x : V) :
    (translateEquiv t).symm x = -t + x := rfl

/-- Conjugating by a common translation preserves every displacement vector. -/
noncomputable def translateEquidecomp
    (e : Equidecomp V (Multiplicative V)) (t : V) :
    Equidecomp V (Multiplicative V) where
  toPartialEquiv :=
    ((translateEquiv t).symm.transPartialEquiv e.toPartialEquiv).transEquiv
      (translateEquiv t)
  isDecompOn' := by
    refine ⟨e.witness, ?_⟩
    intro x hx
    have hxe : (translateEquiv t).symm x ∈ e.source := hx
    obtain ⟨g, hg, heg⟩ := e.isDecompOn _ hxe
    refine ⟨g, hg, ?_⟩
    have heg' : e (-t + x) = g.toAdd + (-t + x) := by
      rw [← ofAdd_toAdd g, ofAdd_smul] at heg
      exact heg
    change t + e (-t + x) = g.toAdd + x
    rw [heg']
    abel

@[simp] lemma translateEquidecomp_source
    (e : Equidecomp V (Multiplicative V)) (t : V) :
    (translateEquidecomp e t).source = (fun x ↦ t + x) '' e.source := by
  ext x
  simp only [translateEquidecomp, PartialEquiv.transEquiv_source,
    Equiv.transPartialEquiv_source, translateEquiv_symm_apply, mem_preimage, mem_image]
  constructor
  · intro hx
    exact ⟨-t + x, hx, by abel⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [neg_add_cancel_left] using hy

@[simp] lemma translateEquidecomp_target
    (e : Equidecomp V (Multiplicative V)) (t : V) :
    (translateEquidecomp e t).target = (fun x ↦ t + x) '' e.target := by
  ext x
  simp only [translateEquidecomp, PartialEquiv.transEquiv_target,
    Equiv.transPartialEquiv_target, translateEquiv_symm_apply, mem_preimage, mem_image]
  constructor
  · intro hx
    exact ⟨-t + x, hx, by abel⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [neg_add_cancel_left] using hy

/-- Multiplication by a nonzero real scalar as an equivalence. -/
def scaleEquiv (c : ℝ) (hc : c ≠ 0) : V ≃ V where
  toFun x := c • x
  invFun x := c⁻¹ • x
  left_inv x := inv_smul_smul₀ hc x
  right_inv x := smul_inv_smul₀ hc x

@[simp] lemma scaleEquiv_apply (c : ℝ) (hc : c ≠ 0) (x : V) :
    scaleEquiv c hc x = c • x := rfl

@[simp] lemma scaleEquiv_symm_apply (c : ℝ) (hc : c ≠ 0) (x : V) :
    (scaleEquiv c hc).symm x = c⁻¹ • x := rfl

/-- Scaling translation vectors is injective when the scale is nonzero. -/
def scaleTranslationEmbedding (c : ℝ) (hc : c ≠ 0) :
    Multiplicative V ↪ Multiplicative V where
  toFun g := Multiplicative.ofAdd (c • g.toAdd)
  inj' g h hgh := by
    change c • g.toAdd = c • h.toAdd at hgh
    apply (@Multiplicative.toAdd V).injective
    exact (smul_right_injective V hc) hgh

/-- Conjugate a finite translation equidecomposition by a nonzero scalar.
The finite witness is obtained by scaling every displacement vector. -/
noncomputable def scaleEquidecomp
    (e : Equidecomp V (Multiplicative V)) (c : ℝ) (hc : c ≠ 0) :
    Equidecomp V (Multiplicative V) where
  toPartialEquiv :=
    ((scaleEquiv c hc).symm.transPartialEquiv e.toPartialEquiv).transEquiv
      (scaleEquiv c hc)
  isDecompOn' := by
    refine ⟨e.witness.map (scaleTranslationEmbedding c hc), ?_⟩
    intro x hx
    have hxe : (scaleEquiv c hc).symm x ∈ e.source := hx
    obtain ⟨g, hg, heg⟩ := e.isDecompOn _ hxe
    have heg' : e (c⁻¹ • x) = g.toAdd + c⁻¹ • x := by
      rw [← ofAdd_toAdd g, ofAdd_smul] at heg
      simpa [scaleEquiv] using heg
    refine ⟨scaleTranslationEmbedding c hc g,
      Finset.mem_map.mpr ⟨g, hg, rfl⟩, ?_⟩
    change c • e (c⁻¹ • x) = c • g.toAdd + x
    rw [heg', smul_add, smul_inv_smul₀ hc]

@[simp] lemma scaleEquidecomp_source
    (e : Equidecomp V (Multiplicative V)) (c : ℝ) (hc : c ≠ 0) :
    (scaleEquidecomp e c hc).source = (fun x ↦ c • x) '' e.source := by
  ext x
  simp only [scaleEquidecomp, PartialEquiv.transEquiv_source,
    Equiv.transPartialEquiv_source, scaleEquiv_symm_apply, mem_preimage, mem_image]
  constructor
  · intro hx
    exact ⟨c⁻¹ • x, hx, smul_inv_smul₀ hc x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [inv_smul_smul₀ hc] using hy

@[simp] lemma scaleEquidecomp_target
    (e : Equidecomp V (Multiplicative V)) (c : ℝ) (hc : c ≠ 0) :
    (scaleEquidecomp e c hc).target = (fun x ↦ c • x) '' e.target := by
  ext x
  simp only [scaleEquidecomp, PartialEquiv.transEquiv_target,
    Equiv.transPartialEquiv_target, scaleEquiv_symm_apply, mem_preimage, mem_image]
  constructor
  · intro hx
    exact ⟨c⁻¹ • x, hx, smul_inv_smul₀ hc x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [inv_smul_smul₀ hc] using hy

end

end Erdos1124
