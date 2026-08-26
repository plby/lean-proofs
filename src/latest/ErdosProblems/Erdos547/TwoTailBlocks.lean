import ErdosProblems.Erdos547.GreedyAnchored
import ErdosProblems.Erdos547.SkewDirectedSupport
import ErdosProblems.Erdos547.PieceCombination

/-!
# Building a skew matching on two disjoint tail blocks
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
theorem exists_skew_two_tail_blocks (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d)
    (γ : ℝ) (hγ : 0 < γ) (A P Q : Finset V)
    (hAP : Disjoint A P) (hAQ : Disjoint A Q) (hPQ : Disjoint P Q)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hP : γ * p ≤ (P.card : ℝ)) (hQ : γ * q = (Q.card : ℝ))
    (hfirst : ∀ y ∈ P, p ≤ w.degreeOn (A.filter (G.Adj y)) d)
    (hsecond : ∀ y ∈ Q, p + q ≤ w.degreeOn (A.filter (G.Adj y)) d) :
    ∃ β : SkewMatching G γ, β.Fits w d ∧ β.total = (1 + γ) * (p + q) ∧
      (∀ u ∉ A, β.outLoad u = 0) ∧ (∑ u ∈ Q, β.load u) = (Q.card : ℝ) := by
  classical
  let z := SkewMatching.zero G γ hγ.le
  have hzout (u : V) : z.outLoad u = 0 := by
    simp only [z, SkewMatching.outLoad, SkewMatching.zero, Finset.sum_const_zero, zero_div]
  have hzload (u : V) : z.load u = 0 := by
    simp only [z, SkewMatching.load, SkewMatching.outLoad, SkewMatching.inLoad,
      SkewMatching.zero, Finset.sum_const_zero, mul_zero, zero_div, add_zero]
  have hp₀ : AnchoredPair z z w d c := AnchoredPair.single_left z γ hγ.le w hcd.symm
    (fun u ↦ by rw [hzout]; exact w.nonnegative d u)
  have hP₀ : γ * p + (∑ u ∈ P, (z.load u + z.load u)) ≤ (P.card : ℝ) := by
    simpa only [hzload, add_zero, Finset.sum_const_zero] using hP
  have hA₀ : ∀ y ∈ P, p + (∑ u ∈ A, (z.load u + z.load u)) ≤
      w.degreeOn (A.filter (G.Adj y)) d := by
    simpa only [hzload, add_zero, Finset.sum_const_zero] using hfirst
  obtain ⟨ρ, hρcap, hp₁, htρ, hsρ⟩ := hp₀.third_greedy A P hAP p hp hγ hP₀ hA₀
  have heρ : z.add ρ hρcap = ρ := by
    cases ρ
    simp only [SkewMatching.add, z, SkewMatching.zero, zero_add]
  rw [heρ] at hp₁
  have hrρ : ρ.RunsBetween A P := SkewMatching.runsBetween_of_zero hsρ
  have hρA : (∑ u ∈ A, ρ.load u) = p := by
    rw [hrρ.sum_load_source hAP, htρ]
    field_simp [ne_of_gt ρ.denominator_pos]
  have hρQ (u : V) (hu : u ∈ Q) : ρ.load u = 0 := hrρ.load_zero
    (fun h ↦ Finset.disjoint_left.mp hAQ h hu) (fun h ↦ Finset.disjoint_left.mp hPQ h hu)
  have hQ₁ : γ * q + (∑ u ∈ Q, (ρ.load u + z.load u)) ≤ (Q.card : ℝ) := by
    simp only [hzload, add_zero]
    rw [Finset.sum_eq_zero (fun u hu ↦ hρQ u hu), add_zero, hQ]
  have hA₁ : ∀ y ∈ Q, q + (∑ u ∈ A, (ρ.load u + z.load u)) ≤
      w.degreeOn (A.filter (G.Adj y)) d := by
    simp only [hzload, add_zero, hρA]
    intro y hy
    linarith [hsecond y hy]
  obtain ⟨τ, hτcap, hp₂, htτ, hsτ⟩ := hp₁.third_greedy A Q hAQ q hq hγ hQ₁ hA₁
  have hrτ : τ.RunsBetween A Q := SkewMatching.runsBetween_of_zero hsτ
  refine ⟨ρ.add τ hτcap, hp₂.fits_left, ?_, ?_, ?_⟩
  · rw [SkewMatching.add_total, htρ, htτ]
    ring
  · exact fun _ hu ↦ (hrρ.add hrτ hτcap).outLoad_zero hu
  · simp only [SkewMatching.add_load, Finset.sum_add_distrib]
    rw [Finset.sum_eq_zero (fun u hu ↦ hρQ u hu), zero_add,
      hrτ.sum_load_target hAQ, htτ]
    calc
      γ * ((1 + γ) * q) / (1 + γ) = γ * q := by
        field_simp [ne_of_gt τ.denominator_pos]
      _ = _ := hQ

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_skew_two_tail_blocks
