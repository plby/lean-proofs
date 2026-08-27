import Arxiv.Arxiv2411_18291.IntegralSpan
import Arxiv.Arxiv2411_18291.DecompositionGluing

/-!
# Focusing a signed vector onto a prescribed graph

Choose one clique through each input edge, with every other edge in the
target graph. Subtracting the corresponding weighted clique boundaries
removes every coordinate outside that graph. The clique coefficients are
supported on the chosen family, and integral decomposability is preserved.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem exists_focusing_vector (R E : Hypergraph V r) (F : Finset (Block V q))
    (Q : R → Block V q) (hQ : ∀ e, Q e ∈ F)
    (hroot : ∀ e, e.val ∈ cliqueEdges r (Q e))
    (hrest : ∀ e, (cliqueEdges r (Q e)).erase e.val ⊆ E)
    (J : Block V r → ℤ) (hsupport : ∀ e, e ∉ R → e ∉ E → J e = 0) :
    ∃ Φ : Block V q → ℤ, (∀ P, P ∉ F → Φ P = 0) ∧
      ∀ e, e ∉ E → (J - boundary r Φ) e = 0 := by
  classical
  let Φ : Block V q → ℤ := ∑ e : R, fun P => J e.val * indicator {Q e} P
  have hΦ : ∀ P, P ∉ F → Φ P = 0 := by
    intro P hP
    change (∑ e : R, fun P => J e.val * indicator {Q e} P) P = 0
    rw [Finset.sum_apply]
    apply sum_eq_zero
    intro e _
    have hPQ : P ∉ ({Q e} : Finset (Block V q)) := by
      intro h
      exact hP ((mem_singleton.mp h) ▸ hQ e)
    rw [indicator_apply_of_notMem hPQ, mul_zero]
  have hb : boundary r Φ = ∑ e : R, fun d => J e.val * indicator (cliqueEdges r (Q e)) d := by
    dsimp only [Φ]
    rw [boundary_sum]
    apply sum_congr rfl
    intro e _
    rw [boundary_mul, boundary_indicator_singleton]
  refine ⟨Φ, hΦ, fun e he => ?_⟩
  have hind (d : R) : indicator (cliqueEdges r (Q d)) e = if d.val = e then 1 else 0 := by
    by_cases hd : d.val = e
    · rw [if_pos hd, indicator_apply_of_mem (hd ▸ hroot d)]
    · rw [if_neg hd]
      apply indicator_apply_of_notMem
      intro hmem
      exact he (hrest d (mem_erase.mpr ⟨Ne.symm hd, hmem⟩))
  have hsum : (∑ d : R, J d.val * indicator (cliqueEdges r (Q d)) e) = J e := by
    simp_rw [hind, mul_ite, mul_one, mul_zero]
    by_cases heR : e ∈ R
    · let d : R := ⟨e, heR⟩
      rw [Fintype.sum_eq_single d]
      · simp [d]
      · intro d' hne
        exact if_neg (fun h => hne (Subtype.ext h))
    · rw [hsupport e heR he]
      apply sum_eq_zero
      intro d _
      have hd : d.val ≠ e := fun h => heR (h ▸ d.property)
      simp only [if_neg hd]
  rw [Pi.sub_apply, hb, Finset.sum_apply, hsum, sub_self]

theorem exists_focused_integral_vector (R E : Hypergraph V r) (F : Finset (Block V q))
    (Q : R → Block V q) (hQ : ∀ e, Q e ∈ F)
    (hroot : ∀ e, e.val ∈ cliqueEdges r (Q e))
    (hrest : ∀ e, (cliqueEdges r (Q e)).erase e.val ⊆ E)
    (J : Block V r → ℤ) (hsupport : ∀ e, e ∉ R → e ∉ E → J e = 0)
    (hJ : IntegrallyDecomposable q J) :
    ∃ K : Block V r → ℤ, GeneratedBy F (J - K) ∧
      (∀ e, e ∉ E → K e = 0) ∧ IntegrallyDecomposable q K := by
  obtain ⟨Φ, hΦ, hs⟩ := exists_focusing_vector R E F Q hQ hroot hrest J hsupport
  refine ⟨J - boundary r Φ, ⟨Φ, ?_, hΦ⟩, hs, hJ.sub ⟨Φ, rfl⟩⟩
  simp only [sub_sub_cancel]

end Arxiv2411_18291
