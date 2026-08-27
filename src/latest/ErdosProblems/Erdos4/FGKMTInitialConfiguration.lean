import ErdosProblems.Erdos4.FGKMTRationalInitialEdges
import ErdosProblems.Erdos4.FGKMTInitialSieveSelection
import ErdosProblems.Erdos4.FGKMTVertexRestriction

/-! A deterministic initial configuration with legal edge laws on the good surviving vertices. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical TupleSurvivalBounds

variable {S P Q : Type*} [Fintype S] [DecidableEq S]
    [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (ell : S → ℕ) (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell l).Prime] [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]
    {k Y : ℕ}

theorem exists_rational_initial_configuration (b : ℝ) (R : ℕ) (hk : 1 ≤ k)
    (h : Fin k → ℕ) (hh : Function.Injective h) (hY : 1 ≤ Y)
    (sources targets : Finset ℕ) (bad : Finset targets)
    (htarget : ∀ q ∈ targets, 1 ≤ q ∧ q ≤ Y)
    {ε η α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η) (hα : 0 ≤ α)
    (hacc : Accurate ell (3 * Y) (3 * k) ε)
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p)
    (hshift : ∀ p ∈ sources, ∀ i, h i * p ≤ Y)
    (hZ : ∀ p ∈ sources, 0 < maskedTranslatedNormalizer ell₀ ell₁ b R h Y p)
    (hatom : ∀ p ∈ sources, ∀ n : TranslatedCenter Y,
      (rationalCenterLaw ell₀ ell₁ b R h hY p).weight n ≤ α)
    (hdegree : ∀ q : targets, q ∉ bad → 24 * UnitFourier.unitDensity ell ≤
      rationalSourceIncidence ell₀ ell₁ b R h hY sources (fun _ => 1) q.val)
    (hbudget : ∀ q : targets, q ∉ bad →
      76 * ε + 4 * (k : ℝ) * α /
        (UnitFourier.unitDensity ell ^ (2 * k - 2) *
          rationalSourceIncidence ell₀ ell₁ b R h hY sources (fun _ => 1) q.val) +
        80 * (k : ℝ) ^ 2 * α / UnitFourier.unitDensity ell ^ (3 * k - 1) ≤ η) :
    ∃ (a : ∀ l, ZMod (ell l)) (V : Finset targets) (ν : sources → FiniteLaw (Finset V)),
      V ⊆ initialSurvivors ell Y targets a ∧
      (∀ q ∈ V, q ∉ bad) ∧
      (V.card : ℝ) ≤ 2 * (UnitFourier.unitDensity ell * targets.card + 1) ∧
      ((initialSurvivors ell Y targets a \ V).card : ℝ) ≤
        2 * (UnitFourier.unitDensity ell * ((bad.card : ℝ) + η * targets.card) + 1) ∧
      (∀ v : V, 4 ≤ ∑ p, (ν p).prob (fun e => v ∈ e)) ∧
      (∀ p v, (ν p).prob (fun e => v ∈ e) ≤
        2 * (k : ℝ) * α / UnitFourier.unitDensity ell ^ k) ∧
      (∀ v w : V, v ≠ w → (∑ p, (ν p).prob (fun e => v ∈ e ∧ w ∈ e)) ≤
        2 * (k : ℝ) * α / UnitFourier.unitDensity ell ^ k) ∧
      (∀ p e, 0 < (ν p).weight e → e.card ≤ k ∧
        ∃ r : ZMod p.val, ∀ q ∈ e, (q.val.val : ZMod p.val) = r) := by
  let σ := UnitFourier.unitDensity ell
  let β := fun q : targets => rationalSourceIncidence ell₀ ell₁ b R h hY sources (fun _ => 1) q.val
  let laws := fun (a : ∀ l, ZMod (ell l)) (p : sources) =>
    rationalInitialEdgeLaw ell ell₀ ell₁ b R h hY targets p a
  let E := fun a (q : targets) => (∑ p, (laws a p).prob (fun e => q ∈ e)) < 4
  have hσ : 0 < σ := UnitFourier.unitDensity_pos ell
  have hbad : ∀ q : targets, q ∉ bad →
      (conditionalResidueLaw ell (q.val + Y)).prob (fun a => E a q) ≤ η := by
    intro q hq
    have hβ : 0 < β q := (by positivity : 0 < 24 * σ).trans_le (hdegree q hq)
    have hfour : (4 : ℝ) ≤ β q / (6 * σ) := by
      apply (le_div_iff₀ (by positivity : 0 < 6 * σ)).mpr
      have hd := hdegree q hq
      change 24 * σ ≤ β q at hd
      nlinarith
    have ht := rational_initial_degree_lower_tail ell ell₀ ell₁ b R hk h hh hY sources targets
      q (htarget q q.property).1 (htarget q q.property).2 hε0 hε1 hα hacc hs hshift hZ hatom hβ
    calc
      _ ≤ (conditionalResidueLaw ell (q.val + Y)).prob (fun a =>
          (∑ p, (laws a p).prob (fun e => q ∈ e)) < β q / (6 * σ)) :=
        FiniteLaw.prob_mono _ (fun a ha => ha.trans_le hfour)
      _ ≤ _ := ht.trans (hbudget q hq)
  obtain ⟨a, V, hVS, hgood, hV, hmiss⟩ :=
    exists_initial_sieve_good_vertices ell Y targets bad E hη hbad
  let ν := fun p : sources => (laws a p).restrictVertices V
  let δ := 2 * (k : ℝ) * α / σ ^ k
  have hδ : 0 ≤ δ := by positivity
  have hmarg : ∀ p : sources, ∀ q : targets, (laws a p).prob (fun e => q ∈ e) ≤ δ := by
    intro p q
    exact translatedInitialEdgeLaw_marginal_le ell h hh hY targets
      (rationalCenterLaw ell₀ ell₁ b R h hY p) (hs p p.property).1.pos (hshift p p.property)
      a q (htarget q q.property).1 (htarget q q.property).2 (hatom p p.property)
  refine ⟨a, V, ν, hVS, (fun q hq => (hgood q hq).1), hV, hmiss, ?_, ?_, ?_, ?_⟩
  · intro v
    change 4 ≤ ∑ p, ((laws a p).restrictVertices V).prob (fun e => v ∈ e)
    simp only [FiniteLaw.restrictVertices_vertex]
    exact le_of_not_gt (hgood v.val v.property).2
  · intro p v
    change ((laws a p).restrictVertices V).prob (fun e => v ∈ e) ≤ δ
    rw [FiniteLaw.restrictVertices_vertex]
    exact hmarg p v.val
  · intro v w hvw
    have hvw' : v.val ≠ w.val := fun hh => hvw (Subtype.ext hh)
    change (∑ p, ((laws a p).restrictVertices V).prob (fun e => v ∈ e ∧ w ∈ e)) ≤ δ
    simp only [FiniteLaw.restrictVertices_pair]
    exact translatedInitialEdgeLaw_pair_sum_le ell h hh hY sources targets
      (fun p => rationalCenterLaw ell₀ ell₁ b R h hY p) hs a v.val w.val hvw' hδ
      (fun p hp => hmarg ⟨p, hp⟩ v.val)
  · intro p f hf
    obtain ⟨e, he, hfe⟩ := FiniteLaw.restrictVertices_support (laws a p) V f hf
    have hsize := translatedInitialEdgeLaw_card_le ell h hY targets
      (rationalCenterLaw ell₀ ell₁ b R h hY p) p a e he
    obtain ⟨r, hr⟩ := translatedInitialEdgeLaw_residue ell h hY targets
      (rationalCenterLaw ell₀ ell₁ b R h hY p) p a e he
    refine ⟨?_, r, ?_⟩
    · rw [← hfe]
      exact (restrictedVertexEdge_card_le V e).trans hsize
    · intro q hq
      exact hr q.val ((mem_restrictedVertexEdge V e q).mp (hfe ▸ hq))

end Erdos4.FGKMT
