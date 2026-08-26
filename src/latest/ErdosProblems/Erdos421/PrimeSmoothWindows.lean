import ErdosProblems.Erdos421.OneSidedSchwartzWindow
import ErdosProblems.Erdos421.PrimePolynomialSupport
import ErdosProblems.Erdos421.LongGaps

/-! # Prime-free integer starts force the corresponding smooth prime window to vanish -/

namespace Erdos421

open Complex
open scoped SchwartzMap

theorem prime_smooth_window_nonzero_witness (M N : ℕ) (σ : ℝ) {δ y : ℝ} (hδ : 0 < δ)
    (hwindow : schwartzDirichletWindow (primeBlockSupport M N) (fun _ ↦ 1) σ
      (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ Real.exp y < p ∧ (p : ℝ) < Real.exp (y + δ) := by
  have hpos : ∀ p ∈ primeBlockSupport M N, 0 < p :=
    fun _ hp ↦ (Finset.mem_filter.mp hp).2.pos
  obtain ⟨p, hp, hlo, hhi⟩ := oneSidedDirichletWindow_nonzero_witness _ _ hpos σ hδ hwindow
  exact ⟨p, (Finset.mem_filter.mp hp).2, hlo, hhi⟩

theorem primeFreeStarts_smooth_window_zero {B H n : ℕ} (hn : n ∈ primeFreeStarts B H)
    (M N : ℕ) (σ : ℝ) {δ y : ℝ} (hδ : 0 < δ)
    (hlo : (n : ℝ) ≤ Real.exp y) (hhi : Real.exp (y + δ) ≤ (n + H : ℕ)) :
    schwartzDirichletWindow (primeBlockSupport M N) (fun _ ↦ 1) σ
      (normalizedSchwartzScale δ hδ oneSidedSchwartzWindow) y = 0 := by
  by_contra hne
  obtain ⟨p, hp, hyp, hpy⟩ := prime_smooth_window_nonzero_witness M N σ hδ hne
  have hnp : n ≤ p := by exact_mod_cast (hlo.trans hyp.le)
  have hpn : p ≤ n + H := by exact_mod_cast (hpy.le.trans hhi)
  exact (Finset.mem_filter.mp hn).2 p (Finset.mem_Icc.mpr ⟨hnp, hpn⟩) hp

end Erdos421
