import ErdosProblems.Erdos587.HooleyLatticePullback

/-! # Adapted coordinates of the generated lattice, with quantitative box synthesis -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

structure DeltaLatticeModel (X : ConvexProgression) (Γ : AddSubgroup (Fin X.rank → ℤ)) where
  coordinates : Γ.toIntSubmodule ≃ₗ[ℤ] (Fin X.rank → ℤ)
  bound : Fin X.rank → ℝ
  bound_nonneg : ∀ i, 0 ≤ bound i
  cover : ∀ v : Γ.toIntSubmodule, intCastVec v.val ∈ X.body → ∀ i,
    |(coordinates v i : ℝ)| ≤ bound i
  synthesis : ∀ t : ℝ, 0 < t → ∀ u : Fin X.rank → ℤ,
    (∀ i, |(u i : ℝ)| ≤ t * (bound i + 1)) →
      intCastVec (coordinates.symm u).val ∈ bodyDilate (t * ((4 ^ X.rank : ℕ) : ℝ)) X.body

theorem delta_exists_adapted_lattice_model (X : ConvexProgression)
    (Γ : AddSubgroup (Fin X.rank → ℤ)) [Γ.FiniteIndex]
    (hperiod : ∀ i, intCastVec (Γ.index • Pi.single i (1 : ℤ)) ∈ X.body) :
    Nonempty (DeltaLatticeModel X Γ) := by
  let b₀ := deltaFiniteIndexBasis Γ
  let Y := deltaLatticePullback X Γ b₀ hperiod
  obtain ⟨D, hscale, _⟩ := MahlerBoxData.exists_adapted Y
  let b : Module.Basis (Fin X.rank) ℤ (Fin X.rank → ℤ) := D.basis
  let E := latticeCoordinates b
  let C := b₀.equivFun.trans E
  have hq (v : Γ.toIntSubmodule) : deltaLatticeEmbedding Γ b₀ (b₀.equivFun v) = v.val := by
    change (b₀.equivFun.symm (b₀.equivFun v)).val = v.val
    rw [b₀.equivFun.symm_apply_apply]
  refine ⟨{
    coordinates := C
    bound := D.bound
    bound_nonneg := D.bound_nonneg
    cover := ?_
    synthesis := ?_
  }⟩
  · intro v hv i
    have hy : Y.IntPoint (b₀.equivFun v) := by
      apply (deltaLatticePullback_intPoint_iff X Γ b₀ hperiod _).mpr
      rwa [hq]
    have hh := D.cover (b₀.equivFun v) hy i
    have hh' : ((|E (b₀.equivFun v) i| : ℤ) : ℝ) ≤ D.bound i := hh
    calc
      |(C v i : ℝ)| = ((|E (b₀.equivFun v) i| : ℤ) : ℝ) := Int.cast_abs.symm
      _ ≤ D.bound i := hh'
  · intro t ht u hu
    have hgauge : gauge Y.body (intCastVec (E.symm u)) ≤ t * (D.scale : ℝ) := by
      calc
        _ ≤ ∑ i, |(u i : ℝ)| * D.cost i := D.gauge_synthesis_le u
        _ ≤ ∑ i, (t * (D.bound i + 1)) * D.cost i :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hu i) (D.cost_nonneg i))
        _ = t * ∑ i, (D.bound i + 1) * D.cost i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ t * (D.scale : ℝ) := mul_le_mul_of_nonneg_left D.scale_bound ht.le
    have hds : (0 : ℝ) < D.scale := by exact_mod_cast D.scale_pos
    have hmem := MahlerBoxData.mem_bodyDilate_of_gauge_le (mul_pos ht hds) hgauge
    have hfinal := deltaLatticePullback_dilate_mem X Γ b₀ hperiod (t * D.scale) (E.symm u) hmem
    rw [hscale] at hfinal
    exact hfinal

end Erdos587.GeneralizedAP
