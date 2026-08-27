import ErdosProblems.Erdos4.FGKMTGeometricCovering

/-! Geometric covering requires degree lower bounds only; thinning supplies equality. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def equalizedRounds (μ : ℕ → I → FiniteLaw (Finset V))
    (m : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdegree : ∀ j < m, ∀ v, (-Real.log ρ) * ρ ^ j ≤ vertexDegree (μ j) v) :
    ℕ → I → FiniteLaw (Finset V) :=
  fun j => if hj : j < m then
    equalizedFamily (μ j) ((-Real.log ρ) * ρ ^ j)
      (mul_pos (neg_pos.mpr (Real.log_neg hρ0 hρ1)) (pow_pos hρ0 j)) (hdegree j hj)
    else fun _ => FiniteLaw.dirac ∅

theorem equalizedRounds_degree (μ : ℕ → I → FiniteLaw (Finset V))
    (m : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdegree : ∀ j < m, ∀ v, (-Real.log ρ) * ρ ^ j ≤ vertexDegree (μ j) v)
    (j : ℕ) (hj : j < m) (v : V) :
    vertexDegree (equalizedRounds μ m ρ hρ0 hρ1 hdegree j) v = (-Real.log ρ) * ρ ^ j := by
  rw [equalizedRounds, dif_pos hj]
  exact equalizedFamily_degree _ _ _ _ _

theorem equalizedRounds_marginal_le (μ : ℕ → I → FiniteLaw (Finset V))
    (m : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdegree : ∀ j < m, ∀ v, (-Real.log ρ) * ρ ^ j ≤ vertexDegree (μ j) v)
    (j : ℕ) (hj : j < m) (i : I) (v : V) :
    (equalizedRounds μ m ρ hρ0 hρ1 hdegree j i).prob (fun e => v ∈ e) ≤
      (μ j i).prob (fun e => v ∈ e) := by
  rw [equalizedRounds, dif_pos hj]
  exact equalizedFamily_marginal_le _ _ _ _ _ _

theorem equalizedRounds_pair_le (μ : ℕ → I → FiniteLaw (Finset V))
    (m : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdegree : ∀ j < m, ∀ v, (-Real.log ρ) * ρ ^ j ≤ vertexDegree (μ j) v)
    (j : ℕ) (hj : j < m) (v w : V) :
    pairDegree (equalizedRounds μ m ρ hρ0 hρ1 hdegree j) v w ≤ pairDegree (μ j) v w := by
  rw [equalizedRounds, dif_pos hj]
  exact equalizedFamily_pairDegree_le _ _ _ _ _ _

theorem equalizedRounds_support (μ : ℕ → I → FiniteLaw (Finset V))
    (m : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hdegree : ∀ j < m, ∀ v, (-Real.log ρ) * ρ ^ j ≤ vertexDegree (μ j) v)
    (j : ℕ) (hj : j < m) (i : I) (f : Finset V)
    (hf : 0 < (equalizedRounds μ m ρ hρ0 hρ1 hdegree j i).weight f) :
    ∃ e, 0 < (μ j i).weight e ∧ f ⊆ e := by
  rw [equalizedRounds, dif_pos hj] at hf
  exact equalizedFamily_support _ _ _ _ _ _ hf

theorem coveredThrough_mono (choice choice' : ℕ → I → Finset V) (m : ℕ)
    (hsub : ∀ j < m, ∀ i, choice j i ⊆ choice' j i) :
    coveredThrough choice m ⊆ coveredThrough choice' m := by
  intro v hv
  obtain ⟨j, hj, hi⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨j, hj,
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hsub j (Finset.mem_range.mp hj) i hvi⟩⟩

theorem enlarge_legal_cover (μ ν : ℕ → I → FiniteLaw (Finset V))
    (m : ℕ) (choice : ℕ → I → Finset V)
    (hlegal : ∀ j < m, ∀ i, choice j i = ∅ ∨ 0 < (ν j i).weight (choice j i))
    (hsupport : ∀ j < m, ∀ i f, 0 < (ν j i).weight f →
      ∃ e, 0 < (μ j i).weight e ∧ f ⊆ e) :
    ∃ choice' : ℕ → I → Finset V,
      (∀ j < m, ∀ i, choice' j i = ∅ ∨ 0 < (μ j i).weight (choice' j i)) ∧
        coveredThrough choice m ⊆ coveredThrough choice' m := by
  have hex : ∀ j i, ∃ e : Finset V, j < m →
      choice j i ⊆ e ∧ (e = ∅ ∨ 0 < (μ j i).weight e) := by
    intro j i
    by_cases hj : j < m
    · rcases hlegal j hj i with he | he
      · exact ⟨∅, fun _ => ⟨by rw [he], Or.inl rfl⟩⟩
      · obtain ⟨e, hmass, hsub⟩ := hsupport j hj i (choice j i) he
        exact ⟨e, fun _ => ⟨hsub, Or.inr hmass⟩⟩
    · exact ⟨∅, fun hh => False.elim (hj hh)⟩
  choose choice' hchoice using hex
  exact ⟨choice', fun j hj i => (hchoice j i hj).2,
    coveredThrough_mono choice choice' m (fun j hj i => (hchoice j i hj).1)⟩

theorem lower_degree_covering (μ : ℕ → I → FiniteLaw (Finset V))
    {m r : ℕ} (hr : 1 ≤ r) {ρ δ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hδ : 0 ≤ δ)
    (hdegree : ∀ j < m, ∀ v, (-Real.log ρ) * ρ ^ j ≤ vertexDegree (μ j) v)
    (scale : ℕ → I → ℝ)
    (hsize : ∀ j < m, ∀ i e, 0 < (μ j i).weight e → e.card ≤ r)
    (hmarginal : ∀ j < m, ∀ i v, (μ j i).prob (fun e => v ∈ e) ≤ scale j i)
    (hscale : ∀ j < m, ∀ i, scale j i ≤ δ)
    (hsquare : ∀ j < m, (∑ i, scale j i ^ 2) ≤ δ ^ 2)
    (hpair : ∀ j < m, ∀ v w, v ≠ w → pairDegree (μ j) v w ≤ δ)
    (hsparse : δ ≤ coveringThreshold r (2 * r) (ρ ^ m) (-Real.log ρ) ^ (4 * 8 ^ m)) :
    ∃ choice : ℕ → I → Finset V,
      (∀ j < m, ∀ i, choice j i = ∅ ∨ 0 < (μ j i).weight (choice j i)) ∧
        ((Finset.univ \ coveredThrough choice m).card : ℝ) ≤
          2 * (Fintype.card V : ℝ) * ρ ^ m := by
  let ν := equalizedRounds μ m ρ hρ0 hρ1 hdegree
  have hνdegree : ∀ j < m, ∀ v, vertexDegree (ν j) v = (-Real.log ρ) * ρ ^ j :=
    equalizedRounds_degree μ m ρ hρ0 hρ1 hdegree
  have hνsupport : ∀ j < m, ∀ i f, 0 < (ν j i).weight f →
      ∃ e, 0 < (μ j i).weight e ∧ f ⊆ e :=
    equalizedRounds_support μ m ρ hρ0 hρ1 hdegree
  have hνsize : ∀ j < m, ∀ i f, 0 < (ν j i).weight f → f.card ≤ r := by
    intro j hj i f hf
    obtain ⟨e, he, hsub⟩ := hνsupport j hj i f hf
    exact (Finset.card_le_card hsub).trans (hsize j hj i e he)
  have hνmarginal : ∀ j < m, ∀ i v, (ν j i).prob (fun e => v ∈ e) ≤ scale j i :=
    fun j hj i v => (equalizedRounds_marginal_le μ m ρ hρ0 hρ1 hdegree j hj i v).trans
      (hmarginal j hj i v)
  have hνpair : ∀ j < m, ∀ v w, v ≠ w → pairDegree (ν j) v w ≤ δ :=
    fun j hj v w hvw => (equalizedRounds_pair_le μ m ρ hρ0 hρ1 hdegree j hj v w).trans
      (hpair j hj v w hvw)
  obtain ⟨choice, hlegal, hcard⟩ := geometric_degree_covering ν hr hρ0 hρ1.le hδ hνdegree
    scale hνsize hνmarginal hscale hsquare hνpair hsparse
  obtain ⟨choice', hlegal', hsub⟩ := enlarge_legal_cover μ ν m choice hlegal hνsupport
  refine ⟨choice', hlegal', ?_⟩
  have hcomp : Finset.univ \ coveredThrough choice' m ⊆ Finset.univ \ coveredThrough choice m := by
    intro v hv
    obtain ⟨hvu, hvnot⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨hvu, fun hh => hvnot (hsub hh)⟩
  have hcount : ((Finset.univ \ coveredThrough choice' m).card : ℝ) ≤
      ((Finset.univ \ coveredThrough choice m).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hcomp
  exact hcount.trans hcard

end Erdos4.FGKMT
