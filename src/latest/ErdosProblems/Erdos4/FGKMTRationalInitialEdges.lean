import ErdosProblems.Erdos4.FGKMTInitialEdgeConcentration
import ErdosProblems.Erdos4.FGKMTArithmeticIncidence

/-! Instantiate initial conditioned edge concentration with the actual rational sieve weights. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical AffineTuples TupleCollisionMass TupleSurvivalBounds

variable {S P Q : Type*} [Fintype S] [DecidableEq S]
    [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (ell : S → ℕ) (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell l).Prime] [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]
    {k Y : ℕ}

noncomputable def rationalInitialEdgeLaw (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hY : 1 ≤ Y) (targets : Finset ℕ) (p : ℕ) (a : ∀ l, ZMod (ell l)) :
    FiniteLaw (Finset targets) :=
  translatedInitialEdgeLaw ell h hY targets (rationalCenterLaw ell₀ ell₁ b R h hY p) p a

theorem rational_initial_degree_lower_tail (b : ℝ) (R : ℕ) (hk : 1 ≤ k)
    (h : Fin k → ℕ) (hh : Function.Injective h) (hY : 1 ≤ Y)
    (sources targets : Finset ℕ) (q : targets) (hq0 : 1 ≤ q.val) (hqY : q.val ≤ Y)
    {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (hacc : Accurate ell (3 * Y) (3 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p)
    (hshift : ∀ p ∈ sources, ∀ i, h i * p ≤ Y)
    (hZ : ∀ p ∈ sources, 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
    (hatom : ∀ p ∈ sources, ∀ n : TranslatedCenter Y,
      (rationalCenterLaw ell₀ ell₁ b R h hY p).weight n ≤ α)
    (hβ : 0 < rationalSourceIncidence ell₀ ell₁ b R h hY sources (fun _ => 1) q.val) :
    let σ := UnitFourier.unitDensity ell
    let β := rationalSourceIncidence ell₀ ell₁ b R h hY sources (fun _ => 1) q.val
    (conditionalResidueLaw ell (q.val + Y)).prob (fun a =>
      (∑ p : sources,
        (rationalInitialEdgeLaw ell ell₀ ell₁ b R h hY targets p a).prob (fun e => q ∈ e)) <
          β / (6 * σ)) ≤
      76 * ε + 4 * (k : ℝ) * α / (σ ^ (2 * k - 2) * β) +
        80 * (k : ℝ) ^ 2 * α / σ ^ (3 * k - 1) := by
  let μ := fun p => rationalCenterLaw ell₀ ell₁ b R h hY p
  let w := rationalCenterMass ell₀ ell₁ b R h Y
  have hw : ∀ p ∈ sources, ∀ n : TranslatedCenter Y, (μ p).weight n = w p n.val := by
    intro p hp n
    exact (rationalCenterMass_eq_weight ell₀ ell₁ b R h hY p (hZ p hp) n).symm
  have hpoints : ∀ p ∈ sources, ∀ n ∈ Finset.Icc 1 (2 * Y), ∀ t ∈ tuple h p n, t ≤ 3 * Y := by
    intro p hp n hn t ht
    exact (Finset.mem_Icc.mp (translatedSites_subset_window h (hshift p hp) hn ht)).2
  have hbase : (∑ p : sources, hitMass h p (2 * Y) (w p) (q.val + Y)) =
      rationalSourceIncidence ell₀ ell₁ b R h hY sources (fun _ => 1) q.val := by
    unfold rationalSourceIncidence
    simp only [one_mul]
    apply Finset.sum_congr rfl
    intro p _
    exact rationalCenterMass_hitMass ell₀ ell₁ b R h hY p q.val hq0 hqY (hZ p p.property)
  have ht := translated_initial_degree_lower_tail ell hk h hh hY sources targets (3 * Y)
    μ w hw q hε0 hε1 hα hacc hs hpoints hatom (hbase ▸ hβ)
  simpa only [hbase, rationalInitialEdgeLaw, μ] using ht

end Erdos4.FGKMT
