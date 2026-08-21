import ErdosProblems.Erdos88.SwitchingLower

open scoped BigOperators

namespace Erdos88

/-- The graph-level bounded-window theorem restricted to its canonical
finite vertex types. -/
def KSSSBoundedWindowFin : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ B : ℕ, 0 < B ∧
      (∀ H : ℝ, 0 < H →
        ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            N ≤ n → RamseyFree C G →
            ∀ (e₀ : ℝ) (c : Fin n → ℝ),
              (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
              ∀ x : ℤ,
                Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                    |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
                  K * (n : ℝ) ^ (-(3 / 2 : ℝ))) ∧
      (∀ H A : ℝ, 0 < H → 0 < A →
        ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            N ≤ n → RamseyFree C G →
            ∀ (e₀ : ℝ) (c : Fin n → ℝ),
              (∀ v, 0 ≤ c v ∧ c v ≤ H * n) →
              ∀ x : ℤ,
                |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                    (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                    A * (n : ℝ) ^ (3 / 2 : ℝ) →
                kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                  Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                    |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B))

namespace BoundedWindow

lemma finiteRamseyFree_comap_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) (e : α ≃ β) {C : ℝ}
    (hG : FiniteRamseyFree C G) : FiniteRamseyFree C (G.comap e) := by
  intro S hS
  let T : Finset β := Switching.equivFinsetImage e S
  have hcard : T.card = S.card := by simp [T, Switching.equivFinsetImage]
  have hhom : G.IsClique (T : Set β) ∨ G.IsIndepSet (T : Set β) := by
    rcases hS with hclique | hindep
    · left
      intro x hx y hy hxy
      simp only [T, Switching.equivFinsetImage, Finset.coe_map,
        Set.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hclique hx' hy' (fun h => hxy (congrArg e h))
    · right
      intro x hx y hy hxy hadj
      simp only [T, Switching.equivFinsetImage, Finset.coe_map,
        Set.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hindep hx' hy' (fun h => hxy (congrArg e h)) hadj
  rw [Fintype.card_congr e]
  simpa only [hcard] using hG T hhom

lemma expectation_half_comap_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (e : α ≃ β) (e₀ : ℝ) (c : β → ℝ) :
    Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial (G.comap e) e₀ (fun i => c (e i))) =
      Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G e₀ c) := by
  rw [← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite,
    ← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  apply Switching.uniformExpectation_equiv (Equiv.finsetCongr e)
  intro S
  simpa only [Equiv.finsetCongr_apply, Switching.equivFinsetImage] using
    Switching.perturbedEdgePolynomial_comap_equiv G e e₀ c S

lemma eventProbability_half_comap_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (e : α ≃ β) (e₀ : ℝ) (c : β → ℝ) (x : ℤ) (B : ℕ) :
    Probability.eventProbability (1 / 2 : ℝ) (fun S : Finset α =>
        |Probability.perturbedEdgePolynomial (G.comap e) e₀
          (fun i => c (e i)) S - x| ≤ B) =
      Probability.eventProbability (1 / 2 : ℝ) (fun T : Finset β =>
        |Probability.perturbedEdgePolynomial G e₀ c T - x| ≤ B) := by
  unfold Probability.eventProbability
  rw [← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite,
    ← BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  apply Switching.uniformExpectation_equiv (Equiv.finsetCongr e)
  intro S
  have hpoly := Switching.perturbedEdgePolynomial_comap_equiv G e e₀ c S
  apply if_congr
  · change |Probability.perturbedEdgePolynomial (G.comap e) e₀
        (fun i => c (e i)) S - x| ≤ B ↔
      |Probability.perturbedEdgePolynomial G e₀ c
        (Switching.equivFinsetImage e S) - x| ≤ B
    rw [hpoly]
  · rfl
  · rfl

theorem ksssBoundedWindowFin_of_boundedWindow
    (hBW : KSSSBoundedWindow) : KSSSBoundedWindowFin := by
  intro C hC
  obtain ⟨B, hB, hupper, hlower⟩ := hBW C hC
  refine ⟨B, hB, ?_, ?_⟩
  · intro H hH
    obtain ⟨K, hK, N, hN⟩ := hupper H hH
    refine ⟨K, hK, N, ?_⟩
    intro n G _ hn hG e₀ c hc x
    simpa only [Fintype.card_fin] using
      hN (Fin n) G (by simpa only [Fintype.card_fin] using hn)
        ((finiteRamseyFree_fin_iff C G).2 hG) e₀ c
        (by simpa only [Fintype.card_fin] using hc) x
  · intro H A hH hA
    obtain ⟨kappa, hkappa, N, hN⟩ := hlower H A hH hA
    refine ⟨kappa, hkappa, N, ?_⟩
    intro n G _ hn hG e₀ c hc x hx
    simpa only [Fintype.card_fin] using
      hN (Fin n) G (by simpa only [Fintype.card_fin] using hn)
        ((finiteRamseyFree_fin_iff C G).2 hG) e₀ c
        (by simpa only [Fintype.card_fin] using hc) x
        (by simpa only [Fintype.card_fin] using hx)

theorem ksssBoundedWindow_of_fin
    (hBW : KSSSBoundedWindowFin) : KSSSBoundedWindow := by
  intro C hC
  obtain ⟨B, hB, hupper, hlower⟩ := hBW C hC
  refine ⟨B, hB, ?_, ?_⟩
  · intro H hH
    obtain ⟨K, hK, N, hN⟩ := hupper H hH
    refine ⟨K, hK, N, ?_⟩
    intro V _ _ G _ hn hG e₀ c hc x
    classical
    let n := Fintype.card V
    let e : Fin n ≃ V := (Fintype.equivFin V).symm
    let G' : SimpleGraph (Fin n) := G.comap e
    have hG' : RamseyFree C G' :=
      (finiteRamseyFree_fin_iff C G').1
        (finiteRamseyFree_comap_equiv G e hG)
    have hc' : ∀ i, 0 ≤ c (e i) ∧ c (e i) ≤ H * n := by
      intro i
      simpa only [n] using hc (e i)
    have hb := hN n G' (by simpa only [n] using hn) hG' e₀
      (fun i => c (e i)) hc' x
    have hevent :
        Probability.eventProbability (1 / 2 : ℝ) (fun U =>
            |Probability.perturbedEdgePolynomial G' e₀
              (fun i => c (e i)) U - x| ≤ B) =
          Probability.eventProbability (1 / 2 : ℝ) (fun U =>
            |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) := by
      simpa only [G'] using eventProbability_half_comap_equiv G e e₀ c x B
    rw [hevent] at hb
    simpa only [n] using hb
  · intro H A hH hA
    obtain ⟨kappa, hkappa, N, hN⟩ := hlower H A hH hA
    refine ⟨kappa, hkappa, N, ?_⟩
    intro V _ _ G _ hn hG e₀ c hc x hx
    classical
    let n := Fintype.card V
    let e : Fin n ≃ V := (Fintype.equivFin V).symm
    let G' : SimpleGraph (Fin n) := G.comap e
    have hG' : RamseyFree C G' :=
      (finiteRamseyFree_fin_iff C G').1
        (finiteRamseyFree_comap_equiv G e hG)
    have hc' : ∀ i, 0 ≤ c (e i) ∧ c (e i) ≤ H * n := by
      intro i
      simpa only [n] using hc (e i)
    have hx' : |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial G' e₀ (fun i => c (e i)))| ≤
          A * (n : ℝ) ^ (3 / 2 : ℝ) := by
      have hexpect : Probability.expectation (1 / 2 : ℝ)
          (Probability.perturbedEdgePolynomial G' e₀ (fun i => c (e i))) =
          Probability.expectation (1 / 2 : ℝ)
            (Probability.perturbedEdgePolynomial G e₀ c) := by
        simpa only [G'] using expectation_half_comap_equiv G e e₀ c
      rw [hexpect]
      simpa only [n] using hx
    have hb := hN n G' (by simpa only [n] using hn) hG' e₀
      (fun i => c (e i)) hc' x hx'
    have hevent :
        Probability.eventProbability (1 / 2 : ℝ) (fun U =>
            |Probability.perturbedEdgePolynomial G' e₀
              (fun i => c (e i)) U - x| ≤ B) =
          Probability.eventProbability (1 / 2 : ℝ) (fun U =>
            |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) := by
      simpa only [G'] using eventProbability_half_comap_equiv G e e₀ c x B
    rw [hevent] at hb
    simpa only [n] using hb

theorem ksssBoundedWindow_iff_fin :
    KSSSBoundedWindow ↔ KSSSBoundedWindowFin :=
  ⟨ksssBoundedWindowFin_of_boundedWindow, ksssBoundedWindow_of_fin⟩

end BoundedWindow
end Erdos88
