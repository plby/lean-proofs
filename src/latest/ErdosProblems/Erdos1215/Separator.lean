import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.Connected.Clopen

open Set Polynomial
open scoped Polynomial Topology

namespace Erdos1215

noncomputable section

theorem exists_small_peak
    (K : Set ℂ) (hKcompact : IsCompact K)
    (hKnorm : ∀ z ∈ K, (1 : ℝ) / 2 ≤ ‖z‖)
    (hcompl : IsPreconnected (insert (0 : ℂ) K)ᶜ) :
    ∃ p : ℂ[X], p.eval 0 = 1 ∧ ∀ z ∈ K, ‖p.eval z‖ < (1 : ℝ) / 2 := by
  let L : Set ℂ := insert 0 K
  have hLcompact : IsCompact L := hKcompact.insert 0
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hLcompact
  let Z : C(L, ℂ) := Polynomial.toContinuousMapOnAlgHom L X
  let S : Subalgebra ℂ C(L, ℂ) := (polynomialFunctions L).topologicalClosure
  have hZpoly : Z ∈ polynomialFunctions L := by
    change Z ∈ (polynomialFunctions L : Set C(L, ℂ))
    rw [polynomialFunctions_coe]
    exact ⟨X, rfl⟩
  let x : S := ⟨Z, Subalgebra.le_topologicalClosure _ hZpoly⟩
  letI : IsClosed (S : Set C(L, ℂ)) := Subalgebra.isClosed_topologicalClosure _
  letI : CompleteSpace S :=
    (Subalgebra.isClosed_topologicalClosure (polynomialFunctions L)).completeSpace_coe
  have hspecZ : spectrum ℂ Z = L := by
    rw [ContinuousMap.spectrum_eq_range]
    ext z
    simp [Z, L]
  have hspecx : spectrum ℂ x = L := by
    rw [Subalgebra.spectrum_eq_of_isPreconnected_compl S x]
    · exact hspecZ
    · have hxval : (x : C(L, ℂ)) = Z := rfl
      rw [hxval, hspecZ]
      exact hcompl
  let q : ℂ[X] := 1 + C 64 * X ^ 3
  have hq_eval (z : ℂ) : q.eval z = 1 + 64 * z ^ 3 := by simp [q]
  have hq_ne (z : ℂ) (hz : z ∈ L) : q.eval z ≠ 0 := by
    rw [hq_eval]
    rcases hz with (rfl | hzK)
    · norm_num
    · intro hz0
      have hnorm : ‖(64 : ℂ) * z ^ 3‖ = 1 := by
        rw [← neg_eq_iff_add_eq_zero.mpr hz0, norm_neg, norm_one]
      norm_num [norm_pow] at hnorm
      have hzlower := hKnorm z hzK
      nlinarith [sq_nonneg ‖z‖, mul_self_nonneg ‖z‖]
  let y : S := aeval x q
  have hzero_not : (0 : ℂ) ∉ spectrum ℂ y := by
    rw [spectrum.map_polynomial_aeval, hspecx]
    rintro ⟨z, hz, hz0⟩
    exact hq_ne z hz (by simpa using hz0)
  have hyunit : IsUnit y := (spectrum.zero_notMem_iff ℂ).mp hzero_not
  let u : Sˣ := hyunit.unit
  let e : S := (↑u⁻¹ : S)
  have he_mul : y * e = 1 := by
    simpa [u, e, hyunit.unit_spec] using u.mul_inv
  have heq (z : L) : q.eval (z : ℂ) * (e : C(L, ℂ)) z = 1 := by
    have hz := congrArg (fun f : S ↦ ((f : C(L, ℂ)) z)) he_mul
    simpa [y, x, Z] using hz
  have he_zero : (e : C(L, ℂ)) ⟨0, mem_insert 0 K⟩ = 1 := by
    have hz := heq ⟨0, mem_insert 0 K⟩
    simpa [q] using hz
  have he_bound (z : ℂ) (hzK : z ∈ K) :
      ‖(e : C(L, ℂ)) ⟨z, mem_insert_of_mem 0 hzK⟩‖ ≤ (1 : ℝ) / 7 := by
    let zL : L := ⟨z, mem_insert_of_mem 0 hzK⟩
    have hprod := congrArg norm (heq zL)
    rw [norm_mul, norm_one] at hprod
    have hw : 8 ≤ ‖(64 : ℂ) * z ^ 3‖ := by
      norm_num [norm_pow]
      have hzlower := hKnorm z hzK
      nlinarith [sq_nonneg ‖z‖, mul_self_nonneg ‖z‖]
    have htri : ‖(64 : ℂ) * z ^ 3‖ ≤ ‖1 + (64 : ℂ) * z ^ 3‖ + 1 := by
      calc
        ‖(64 : ℂ) * z ^ 3‖ = ‖(1 + (64 : ℂ) * z ^ 3) - 1‖ := by ring_nf
        _ ≤ ‖1 + (64 : ℂ) * z ^ 3‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖1 + (64 : ℂ) * z ^ 3‖ + 1 := by norm_num
    have hqnorm : 7 ≤ ‖q.eval z‖ := by
      rw [hq_eval]
      linarith
    change ‖q.eval z‖ * ‖(e : C(L, ℂ)) zL‖ = 1 at hprod
    nlinarith [norm_nonneg ((e : C(L, ℂ)) zL)]
  have he_closure :
      (e : C(L, ℂ)) ∈ closure (polynomialFunctions L : Set C(L, ℂ)) := by
    have he_mem : (e : C(L, ℂ)) ∈ S := e.property
    change (e : C(L, ℂ)) ∈
      ((polynomialFunctions L).topologicalClosure : Set C(L, ℂ)) at he_mem
    rw [Subalgebra.topologicalClosure_coe] at he_mem
    exact he_mem
  have hfreq := mem_closure_iff_frequently.mp he_closure
  rw [Metric.nhds_basis_ball.frequently_iff] at hfreq
  obtain ⟨g, hgball, hgpoly⟩ := hfreq ((1 : ℝ) / 16) (by norm_num)
  rw [Metric.mem_ball, dist_eq_norm] at hgball
  have hgpoly' : g ∈ Set.range (Polynomial.toContinuousMapOnAlgHom L) := by
    rwa [← polynomialFunctions_coe]
  obtain ⟨p, rfl⟩ := hgpoly'
  have hpoint (z : L) :
      ‖p.eval (z : ℂ) - (e : C(L, ℂ)) z‖ < (1 : ℝ) / 16 := by
    exact lt_of_le_of_lt
      (ContinuousMap.norm_coe_le_norm
        (p.toContinuousMapOn L - (e : C(L, ℂ))) z) hgball
  have hp0close : ‖p.eval 0 - 1‖ < (1 : ℝ) / 16 := by
    simpa [he_zero] using hpoint ⟨0, mem_insert 0 K⟩
  have hp0norm : (15 : ℝ) / 16 < ‖p.eval 0‖ := by
    have htri : (1 : ℝ) ≤ ‖p.eval 0 - 1‖ + ‖p.eval 0‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖-(p.eval 0 - 1) + p.eval 0‖ := by congr 1 <;> ring
        _ ≤ ‖-(p.eval 0 - 1)‖ + ‖p.eval 0‖ := norm_add_le _ _
        _ = ‖p.eval 0 - 1‖ + ‖p.eval 0‖ := by rw [norm_neg]
    linarith
  have hp0ne : p.eval 0 ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  let peak : ℂ[X] := C (p.eval 0)⁻¹ * p
  refine ⟨peak, ?_, ?_⟩
  · simp [peak, hp0ne]
  · intro z hzK
    have hpbound : ‖p.eval z‖ < (23 : ℝ) / 112 := by
      have hp := hpoint ⟨z, mem_insert_of_mem 0 hzK⟩
      have he := he_bound z hzK
      have htri : ‖p.eval z‖ ≤
          ‖p.eval z - (e : C(L, ℂ)) ⟨z, mem_insert_of_mem 0 hzK⟩‖ +
            ‖(e : C(L, ℂ)) ⟨z, mem_insert_of_mem 0 hzK⟩‖ := by
        calc
          ‖p.eval z‖ = ‖(p.eval z -
              (e : C(L, ℂ)) ⟨z, mem_insert_of_mem 0 hzK⟩) +
              (e : C(L, ℂ)) ⟨z, mem_insert_of_mem 0 hzK⟩‖ := by
                rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith
    simp only [peak, eval_mul, eval_C, norm_mul, norm_inv]
    rw [inv_mul_lt_iff₀ (by linarith [hp0norm])]
    nlinarith

/-- Polynomial separation of the origin from a compact nonseparating wall
set.  This is the special Lavrentiev consequence needed for the labyrinth. -/
theorem exists_polynomial_separator
    (K : Set ℂ) (hKcompact : IsCompact K)
    (hKnorm : ∀ z ∈ K, (1 : ℝ) / 2 ≤ ‖z‖)
    (hcompl : IsPreconnected (insert (0 : ℂ) K)ᶜ) :
    ∃ h : ℂ[X], h.eval 0 = 0 ∧ ∀ z ∈ K, 1 < (h.eval z).re := by
  obtain ⟨p, hp0, hpK⟩ := exists_small_peak K hKcompact hKnorm hcompl
  let h : ℂ[X] := C 2 * (1 - p)
  refine ⟨h, ?_, ?_⟩
  · simp [h, hp0]
  · intro z hz
    have hp := hpK z hz
    have hpre : (p.eval z).re < (1 : ℝ) / 2 :=
      (Complex.re_le_norm _).trans_lt hp
    norm_num [h, Complex.mul_re]
    linarith

end

end Erdos1215
