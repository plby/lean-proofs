import ErdosProblems.Erdos755
import Mathlib.Analysis.MeanInequalitiesPow

open Filter Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace
open Finset

namespace Erdos754

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Finite averages used by dependent random choice -/

noncomputable def indicator (P : Prop) : ℝ :=
  @ite ℝ P (Classical.propDecidable P) 1 0

@[simp] lemma indicator_true {P : Prop} (h : P) : indicator P = 1 := by
  simp [indicator, h]

@[simp] lemma indicator_false {P : Prop} (h : ¬ P) : indicator P = 0 := by
  simp [indicator, h]

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  unfold indicator
  split_ifs <;> norm_num

lemma sum_indicator_eq_card_filter (s : Finset V) (p : V → Prop) [DecidablePred p] :
    ∑ x ∈ s, indicator (p x) = ((s.filter p).card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [sum_insert ha, ih, filter_insert]
      by_cases hp : p a
      · rw [indicator_true hp]
        simp [ha, hp]
        ring
      · rw [indicator_false hp]
        simp [ha, hp]

noncomputable def samples (t : ℕ) (A : Finset V) : Finset (Fin t → V) :=
  Fintype.piFinset fun _ => A

lemma mem_samples (t : ℕ) (A : Finset V) (x : Fin t → V) :
    x ∈ samples t A ↔ ∀ i, x i ∈ A := by
  simp [samples]

lemma card_samples (t : ℕ) (A : Finset V) : (samples t A).card = A.card ^ t := by
  simp [samples]

noncomputable def commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) : Finset V :=
  B.filter fun y => ∀ i, G.Adj (q i) y

lemma mem_commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) (y : V) :
    y ∈ commonNeighbors G q B ↔ y ∈ B ∧ ∀ i, G.Adj (q i) y := by
  simp [commonNeighbors]

lemma commonNeighbors_subset_target (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) :
    commonNeighbors G q B ⊆ B := by
  intro y hy
  exact (mem_commonNeighbors G q B y).mp hy |>.1

lemma card_commonNeighbors_eq_sum_indicator
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) :
    ((commonNeighbors G q B).card : ℝ) =
      ∑ y ∈ B, indicator (∀ i, G.Adj (q i) y) := by
  classical
  rw [sum_indicator_eq_card_filter]
  rfl

lemma expect_all_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (t : ℕ) (y : V) :
    𝔼 x ∈ samples t A, indicator (∀ i, G.Adj (x i) y) =
      (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by
  classical
  have hsingle :
      𝔼 z ∈ A, indicator (G.Adj z y) =
        ((A.filter fun z => G.Adj z y).card : ℝ) / A.card := by
    rw [Finset.expect_eq_sum_div_card]
    rw [sum_indicator_eq_card_filter]
  calc
    𝔼 x ∈ samples t A, indicator (∀ i, G.Adj (x i) y) =
        𝔼 x ∈ samples t A, ∏ i, indicator (G.Adj (x i) y) := by
          apply Finset.expect_congr rfl
          intro x hx
          by_cases h : ∀ i, G.Adj (x i) y
          · rw [indicator_true h]
            exact (Finset.prod_eq_one fun i _ => indicator_true (h i)).symm
          · rw [indicator_false h]
            push Not at h
            obtain ⟨i, hi⟩ := h
            exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_false hi)).symm
    _ = (𝔼 z ∈ A, indicator (G.Adj z y)) ^ t := by
      symm
      simpa [samples] using (Finset.expect_pow A (fun z => indicator (G.Adj z y)) t)
    _ = (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by rw [hsingle]

lemma expect_card_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (t : ℕ) :
    𝔼 x ∈ samples t A, ((commonNeighbors G x B).card : ℝ) =
      ∑ y ∈ B, (((A.filter fun z => G.Adj z y).card : ℝ) / A.card) ^ t := by
  classical
  simp_rw [card_commonNeighbors_eq_sum_indicator]
  rw [Finset.expect_sum_comm]
  congr 1
  funext y
  exact expect_all_adjacent G A t y

def edgeMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℕ :=
  ∑ y ∈ B, (A.filter fun z => G.Adj z y).card

lemma sum_degree_ratios
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    ∑ y ∈ B, ((A.filter fun z => G.Adj z y).card : ℝ) / A.card =
      edgeMass G A B / A.card := by
  classical
  simp only [edgeMass, Nat.cast_sum]
  rw [Finset.sum_div]

lemma pow_expect_le_expect_pow {ι : Type*} (S : Finset ι)
    (hS : S.Nonempty) (g : ι → ℝ) (hg : ∀ x ∈ S, 0 ≤ g x) (t : ℕ) :
    (𝔼 x ∈ S, g x) ^ t ≤ 𝔼 x ∈ S, (g x) ^ t := by
  classical
  let w : ι → ℝ := fun _ => (S.card : ℝ)⁻¹
  have hw : ∀ x ∈ S, 0 ≤ w x := fun _ _ => by positivity
  have hw_sum : ∑ x ∈ S, w x = 1 := by simp [w, hS.card_ne_zero]
  have hJ := Real.pow_arith_mean_le_arith_mean_pow S w g hw hw_sum hg t
  simpa [Finset.expect, NNRat.smul_def, w, div_eq_inv_mul, ← Finset.mul_sum] using hJ

lemma samples_nonempty (t : ℕ) {A : Finset V} (hA : A.Nonempty) :
    (samples t A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨fun _ => a, ?_⟩
  simp [samples, ha]

lemma expect_card_commonNeighbors_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdensity : ρ * A.card * B.card ≤ edgeMass G A B)
    (t : ℕ) :
    (ρ ^ t) * B.card ≤
      𝔼 x ∈ samples t A, ((commonNeighbors G x B).card : ℝ) := by
  classical
  let g : V → ℝ := fun y => ((A.filter fun z => G.Adj z y).card : ℝ) / A.card
  have hg : ∀ y ∈ B, 0 ≤ g y := fun _ _ => by positivity
  have hmean : ρ ≤ 𝔼 y ∈ B, g y := by
    rw [Finset.expect_eq_sum_div_card,
      show (∑ y ∈ B, g y) = edgeMass G A B / A.card by exact sum_degree_ratios G A B]
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    rw [div_div]
    apply (le_div_iff₀ (mul_pos hApos hBpos)).2
    simpa [mul_assoc] using hdensity
  have hjensen := pow_expect_le_expect_pow B hB g hg t
  have hpow : ρ ^ t ≤ 𝔼 y ∈ B, (g y) ^ t :=
    (pow_le_pow_left₀ hρ hmean t).trans hjensen
  rw [expect_card_commonNeighbors G A B t]
  rw [Finset.expect_eq_sum_div_card] at hpow
  apply (le_div_iff₀ (by exact_mod_cast hB.card_pos)).mp at hpow
  simpa [g, mul_comm] using hpow

/- Compatibility abbreviations keep the finite-average proof below readable while
the file remains independent of the unrelated Erdős 163 development. -/
namespace DRC
noncomputable abbrev indicator (P : Prop) : ℝ := Erdos754.indicator P

@[simp] lemma indicator_true {P : Prop} (h : P) : indicator P = 1 := by
  simp [indicator, Erdos754.indicator, h]

@[simp] lemma indicator_false {P : Prop} (h : ¬ P) : indicator P = 0 := by
  simp [indicator, Erdos754.indicator, h]

lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by
  simpa [indicator] using Erdos754.indicator_nonneg P

lemma sum_indicator_eq_card_filter (s : Finset V) (p : V → Prop) [DecidablePred p] :
    ∑ x ∈ s, indicator (p x) = ((s.filter p).card : ℝ) := by
  simpa [indicator] using Erdos754.sum_indicator_eq_card_filter s p

abbrev edgeMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℕ := Erdos754.edgeMass G A B

abbrev expect_card_commonNeighbors_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hA : A.Nonempty) (hB : B.Nonempty)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdensity : ρ * A.card * B.card ≤ Erdos754.edgeMass G A B)
    (t : ℕ) :
    (ρ ^ t) * B.card ≤
      𝔼 x ∈ Erdos754.samples t A,
        ((Erdos754.commonNeighbors G x B).card : ℝ) :=
  Erdos754.expect_card_commonNeighbors_lower G hA hB hρ hdensity t

abbrev samples_nonempty (t : ℕ) {A : Finset V} (hA : A.Nonempty) :
    (Erdos754.samples t A).Nonempty := Erdos754.samples_nonempty t hA
end DRC

namespace FiniteDefect
noncomputable abbrev samples (t : ℕ) (A : Finset V) : Finset (Fin t → V) :=
  Erdos754.samples t A

abbrev card_samples (t : ℕ) (A : Finset V) :
    (samples t A).card = A.card ^ t := Erdos754.card_samples t A

noncomputable abbrev commonNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [Fintype ι] (q : ι → V) (B : Finset V) : Finset V :=
  Erdos754.commonNeighbors G q B
end FiniteDefect

lemma expect_eq01 (hV : Nonempty V) :
    (𝔼 q ∈ FiniteDefect.samples 3 (Finset.univ : Finset V),
      indicator (q 0 = q 1)) = 1 / (Fintype.card V : ℝ) := by
  classical
  rw [Finset.expect_eq_sum_div_card, sum_indicator_eq_card_filter,
    card_samples]
  simp only [Finset.card_univ]
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hsamples : (samples 3 (Finset.univ : Finset V)).filter
      (fun q => q 0 = q 1) = Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 1) := by
    ext q; simp [samples]
  have hfilter : (Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 1)).card =
      Fintype.card V ^ 2 := by
    rw [← Fintype.card_coe]
    let e : {q : Fin 3 → V // q 0 = q 1} ≃ V × V := {
      toFun q := (q.1 0, q.1 2)
      invFun z := ⟨![z.1, z.1, z.2], by simp⟩
      left_inv q := by apply Subtype.ext; funext i; fin_cases i <;> simp [q.property]
      right_inv z := by simp }
    simpa [pow_two] using Fintype.card_congr e
  rw [hsamples, hfilter]
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  norm_cast

lemma expect_eq02 (hV : Nonempty V) :
    (𝔼 q ∈ FiniteDefect.samples 3 (Finset.univ : Finset V),
      indicator (q 0 = q 2)) = 1 / (Fintype.card V : ℝ) := by
  classical
  rw [Finset.expect_eq_sum_div_card, sum_indicator_eq_card_filter,
    card_samples]
  simp only [Finset.card_univ]
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hsamples : (samples 3 (Finset.univ : Finset V)).filter
      (fun q => q 0 = q 2) = Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 2) := by
    ext q; simp [samples]
  have hfilter : (Finset.univ.filter (fun q : Fin 3 → V => q 0 = q 2)).card =
      Fintype.card V ^ 2 := by
    rw [← Fintype.card_coe]
    let e : {q : Fin 3 → V // q 0 = q 2} ≃ V × V := {
      toFun q := (q.1 0, q.1 1)
      invFun z := ⟨![z.1, z.2, z.1], by simp⟩
      left_inv q := by apply Subtype.ext; funext i; fin_cases i <;> simp [q.property]
      right_inv z := by simp }
    simpa [pow_two] using Fintype.card_congr e
  rw [hsamples, hfilter]
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  norm_cast

lemma expect_eq12 (hV : Nonempty V) :
    (𝔼 q ∈ FiniteDefect.samples 3 (Finset.univ : Finset V),
      indicator (q 1 = q 2)) = 1 / (Fintype.card V : ℝ) := by
  classical
  rw [Finset.expect_eq_sum_div_card, sum_indicator_eq_card_filter,
    card_samples]
  simp only [Finset.card_univ]
  have hn : Fintype.card V ≠ 0 := Fintype.card_ne_zero
  have hsamples : (samples 3 (Finset.univ : Finset V)).filter
      (fun q => q 1 = q 2) = Finset.univ.filter (fun q : Fin 3 → V => q 1 = q 2) := by
    ext q; simp [samples]
  have hfilter : (Finset.univ.filter (fun q : Fin 3 → V => q 1 = q 2)).card =
      Fintype.card V ^ 2 := by
    rw [← Fintype.card_coe]
    let e : {q : Fin 3 → V // q 1 = q 2} ≃ V × V := {
      toFun q := (q.1 0, q.1 1)
      invFun z := ⟨![z.1, z.2, z.2], by simp⟩
      left_inv q := by apply Subtype.ext; funext i; fin_cases i <;> simp [q.property]
      right_inv z := by simp }
    simpa [pow_two] using Fintype.card_congr e
  rw [hsamples, hfilter]
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp
  norm_cast

lemma edgeMass_univ_eq_sum_degree (G : SimpleGraph V) [DecidableRel G.Adj] :
    DRC.edgeMass G (Finset.univ : Finset V) Finset.univ = ∑ v, G.degree v := by
  classical
  unfold DRC.edgeMass
  apply Finset.sum_congr rfl
  intro v hv
  rw [← G.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simpa [G.mem_neighborFinset] using G.adj_comm w v

lemma exists_injective_commonNeighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 48 ≤ Fintype.card V)
    (hdeg : ∀ v, (Fintype.card V : ℝ) / 2 + 100 ≤ G.degree v) :
    ∃ q : Fin 3 → V, Function.Injective q ∧
      (Fintype.card V : ℝ) / 16 ≤
        (FiniteDefect.commonNeighbors G q (Finset.univ : Finset V)).card := by
  classical
  let n : ℝ := Fintype.card V
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hU : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hmass : (1 / 2 : ℝ) * (Finset.univ : Finset V).card *
      (Finset.univ : Finset V).card ≤
      DRC.edgeMass G (Finset.univ : Finset V) Finset.univ := by
    have hEM : (DRC.edgeMass G (Finset.univ : Finset V) Finset.univ : ℝ) =
        ∑ v : V, (G.degree v : ℝ) := by
      rw [edgeMass_univ_eq_sum_degree]
      norm_cast
    rw [hEM]
    calc
      (1 / 2 : ℝ) * (Finset.univ : Finset V).card *
          (Finset.univ : Finset V).card =
          ∑ _v : V, ((Fintype.card V : ℝ) / 2) := by
            simp [Finset.card_univ]
            ring
      _ ≤ ∑ v : V, (G.degree v : ℝ) := by
            apply Finset.sum_le_sum
            intro v hv
            exact le_trans (by linarith : (Fintype.card V : ℝ) / 2 ≤
              (Fintype.card V : ℝ) / 2 + 100) (hdeg v)
      _ = ∑ v : V, (G.degree v : ℝ) := rfl
  have hX := DRC.expect_card_commonNeighbors_lower G hU hU
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) hmass 3
  let Ω := FiniteDefect.samples 3 (Finset.univ : Finset V)
  let X : (Fin 3 → V) → ℝ := fun q =>
    (FiniteDefect.commonNeighbors G q (Finset.univ : Finset V)).card
  let P : (Fin 3 → V) → ℝ := fun q =>
    (Fintype.card V : ℝ) *
      (DRC.indicator (q 0 = q 1) + DRC.indicator (q 0 = q 2) + DRC.indicator (q 1 = q 2))
  have hΩ : Ω.Nonempty := DRC.samples_nonempty 3 hU
  have hX' : (n / 8) ≤ 𝔼 q ∈ Ω, X q := by
    norm_num at hX
    simpa [n, Ω, X, div_eq_mul_inv, mul_comm] using hX
  have hP : (𝔼 q ∈ Ω, P q) = 3 := by
    dsimp [Ω, P]
    simp_rw [mul_add]
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib]
    simp_rw [mul_comm (Fintype.card V : ℝ)]
    rw [← Finset.expect_mul, ← Finset.expect_mul, ← Finset.expect_mul,
      expect_eq01 hV, expect_eq02 hV, expect_eq12 hV]
    have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
    ring
  have hobj : n / 16 ≤ 𝔼 q ∈ Ω, (X q - P q) := by
    rw [Finset.expect_sub_distrib, hP]
    have hn : (48 : ℝ) ≤ n := by
      dsimp [n]
      exact_mod_cast hcard
    linarith
  obtain ⟨q, hqΩ, hq⟩ := Finset.exists_le_of_le_expect hΩ hobj
  have hXle : X q ≤ n := by
    dsimp [X, n]
    exact_mod_cast Finset.card_le_card
      (commonNeighbors_subset_target G q (Finset.univ : Finset V))
  have hpos : 0 < n / 16 := by
    have hn : (0 : ℝ) < n := by
      dsimp [n]
      exact_mod_cast Fintype.card_pos
    positivity
  have h01 : q 0 ≠ q 1 := by
    intro h
    have hPge : n ≤ P q := by
      dsimp [P]
      rw [DRC.indicator_true h]
      have hnonneg : 0 ≤ DRC.indicator (q 0 = q 2) + DRC.indicator (q 1 = q 2) :=
        add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _)
      nlinarith
    linarith
  have h02 : q 0 ≠ q 2 := by
    intro h
    have hPge : n ≤ P q := by
      dsimp [P]
      rw [DRC.indicator_true h]
      have hnonneg : 0 ≤ DRC.indicator (q 0 = q 1) + DRC.indicator (q 1 = q 2) :=
        add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _)
      nlinarith
    linarith
  have h12 : q 1 ≠ q 2 := by
    intro h
    have hPge : n ≤ P q := by
      dsimp [P]
      rw [DRC.indicator_true h]
      have hnonneg : 0 ≤ DRC.indicator (q 0 = q 1) + DRC.indicator (q 0 = q 2) :=
        add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _)
      nlinarith
    linarith
  have hinj : Function.Injective q := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hPnonneg : 0 ≤ P q := by
    dsimp [P]
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    exact mul_nonneg hn (add_nonneg
      (add_nonneg (DRC.indicator_nonneg _) (DRC.indicator_nonneg _))
      (DRC.indicator_nonneg _))
  have hqX : n / 16 ≤ X q := by linarith
  exact ⟨q, hinj, by simpa [n, X] using hqX⟩

def neighborsIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : Finset V :=
  S.filter fun w => G.Adj v w

lemma exists_injective_fin3_of_card_ge_three (S : Finset V) (hS : 3 ≤ S.card) :
    ∃ f : Fin 3 → V, Function.Injective f ∧ ∀ i, f i ∈ S := by
  classical
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hS
  let f : Fin 3 → V := fun i =>
    ((T.equivFin).symm (Fin.cast hTcard.symm i) : T)
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    dsimp [f] at hij
    have hcast : Fin.cast hTcard.symm i = Fin.cast hTcard.symm j := by
      apply T.equivFin.symm.injective
      exact Subtype.ext hij
    exact (Fin.cast_injective hTcard.symm) hcast
  · intro i
    exact hTS ((T.equivFin).symm (Fin.cast hTcard.symm i)).property

lemma sum_card_neighborsIn_eq_sum_degree_on
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∑ v : V, (neighborsIn G S v).card = ∑ w ∈ S, G.degree w := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun v w : V => G.Adj v w) (s := (Finset.univ : Finset V)) (t := S)
  calc
    ∑ v : V, (neighborsIn G S v).card =
        ∑ v ∈ (Finset.univ : Finset V),
          (Finset.bipartiteAbove (fun v w : V => G.Adj v w) S v).card := by
            apply Finset.sum_congr rfl
            intro v hv
            congr 1
    _ = ∑ w ∈ S,
          (Finset.bipartiteBelow (fun v w : V => G.Adj v w)
            (Finset.univ : Finset V) w).card := hdc
    _ = ∑ w ∈ S, G.degree w := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [← G.card_neighborFinset_eq_degree]
            congr 1
            ext v
            simpa [Finset.bipartiteBelow, G.mem_neighborFinset] using G.adj_comm v w

def Saturated33 (G : SimpleGraph V) : Prop :=
  ∀ (f g : Fin 3 → V), Function.Injective f → Function.Injective g →
    (∀ i j, G.Adj (f i) (g j)) →
    ∀ x y, (∀ j, G.Adj x (g j)) → (∀ i, G.Adj y (f i)) → G.Adj x y

lemma card_neighborsIn_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : V) : (neighborsIn G S v).card ≤ S.card :=
  Finset.card_filter_le _ _

lemma card_neighborsIn_le_two_of_not_three
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V)
    (h : ¬ 3 ≤ (neighborsIn G S v).card) :
    (neighborsIn G S v).card ≤ 2 := by omega

lemma sum_neighborsIn_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (A : Finset V) (hA : ∀ v, v ∈ A ↔ 3 ≤ (neighborsIn G S v).card) :
    (∑ v : V, (neighborsIn G S v).card : ℕ) ≤ A.card * S.card + 2 * Fintype.card V := by
  classical
  calc
    (∑ v : V, (neighborsIn G S v).card : ℕ) ≤
        ∑ v : V, if v ∈ A then S.card else 2 := by
          apply Finset.sum_le_sum
          intro v hv
          by_cases hvA : v ∈ A
          · simp [hvA, card_neighborsIn_le_card]
          · simp [hvA]
            exact card_neighborsIn_le_two_of_not_three G S v (by simpa [hA v] using hvA)
    _ = A.card * S.card + ((Finset.univ.filter fun v : V => v ∉ A).card) * 2 := by
          change (∑ v ∈ (Finset.univ : Finset V), if v ∈ A then S.card else 2) = _
          rw [Finset.sum_ite]
          simp [mul_comm]
    _ ≤ A.card * S.card + 2 * Fintype.card V := by
          have hle : (Finset.univ.filter fun v : V => v ∉ A).card ≤ Fintype.card V := by
            simpa using Finset.card_filter_le (Finset.univ : Finset V) (fun v => v ∉ A)
          omega

lemma low_degree_of_saturated33
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] (hSat : Saturated33 G) :
    ∃ v : V, (G.degree v : ℝ) ≤ (Fintype.card V : ℝ) / 2 + 100 := by
  classical
  by_cases hsmall : Fintype.card V < 48
  · obtain ⟨v⟩ := (inferInstance : Nonempty V)
    refine ⟨v, ?_⟩
    have hdeg : G.degree v ≤ Fintype.card V := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (by simp)
    have hdegR : (G.degree v : ℝ) ≤ Fintype.card V := by exact_mod_cast hdeg
    have hn : (Fintype.card V : ℝ) < 48 := by exact_mod_cast hsmall
    nlinarith
  · have hcard : 48 ≤ Fintype.card V := by omega
    by_contra hnone
    push Not at hnone
    have hdeg : ∀ v, (Fintype.card V : ℝ) / 2 + 100 ≤ G.degree v := by
      intro v
      exact (le_of_lt (hnone v))
    obtain ⟨q, hqinj, hqB⟩ := exists_injective_commonNeighbors G hcard hdeg
    let B := FiniteDefect.commonNeighbors G q (Finset.univ : Finset V)
    have hBcard : 3 ≤ B.card := by
      have hBreal : (3 : ℝ) ≤ B.card := by
        have h48R : (48 : ℝ) ≤ Fintype.card V := by exact_mod_cast hcard
        calc
          (3 : ℝ) ≤ (Fintype.card V : ℝ) / 16 := by nlinarith
          _ ≤ B.card := hqB
      exact_mod_cast hBreal
    let A := (Finset.univ : Finset V).filter fun v => 3 ≤ (neighborsIn G B v).card
    have hAiff (v : V) : v ∈ A ↔ 3 ≤ (neighborsIn G B v).card := by simp [A]
    have hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
      intro a ha b hb
      obtain ⟨g, hginj, hgmem⟩ := exists_injective_fin3_of_card_ge_three
        (neighborsIn G B a) ((hAiff a).mp ha)
      have hcross : ∀ i j, G.Adj (q i) (g j) := by
        intro i j
        have hgjB : g j ∈ B := (Finset.mem_filter.mp (hgmem j)).1
        exact (mem_commonNeighbors G q (Finset.univ : Finset V) (g j)).mp hgjB |>.2 i
      apply hSat q g hqinj hginj hcross a b
      · intro j
        exact (Finset.mem_filter.mp (hgmem j)).2
      · intro i
        have hb' := (mem_commonNeighbors G q (Finset.univ : Finset V) b).mp hb |>.2 i
        exact (G.adj_comm _ _).mp hb'
    have hsumB : ∑ v : V, (neighborsIn G B v).card = ∑ b ∈ B, G.degree b :=
      sum_card_neighborsIn_eq_sum_degree_on G B
    have hlowB : (B.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) ≤
        (∑ v : V, (neighborsIn G B v).card : ℕ) := by
      rw [hsumB, Nat.cast_sum]
      calc
        (B.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) =
            ∑ _b ∈ B, ((Fintype.card V : ℝ) / 2 + 100) := by
              simp [mul_add]
        _ ≤ ∑ b ∈ B, (G.degree b : ℝ) := by
          exact Finset.sum_le_sum fun b hb => hdeg b
    have huppB : ((∑ v : V, (neighborsIn G B v).card : ℕ) : ℝ) ≤
        (A.card : ℝ) * B.card + 2 * Fintype.card V := by
      exact_mod_cast sum_neighborsIn_le G B A hAiff
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hBcard)
    have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
    have hAreal : (Fintype.card V : ℝ) / 2 + 68 ≤ A.card := by
      have hdiv : 2 * (Fintype.card V : ℝ) / B.card ≤ 32 := by
        apply (div_le_iff₀ hBpos).2
        have hb16 : (Fintype.card V : ℝ) / 16 ≤ B.card := hqB
        nlinarith
      have hmain := hlowB.trans huppB
      apply (le_of_sub_nonneg ?_)
      nlinarith
    have hAcard : 3 ≤ A.card := by
      have h : (3 : ℝ) ≤ A.card := by
        calc
          (3 : ℝ) ≤ (Fintype.card V : ℝ) / 2 + 68 := by nlinarith
          _ ≤ A.card := hAreal
      exact_mod_cast h
    let B' := (Finset.univ : Finset V).filter fun v => 3 ≤ (neighborsIn G A v).card
    have hB'iff (v : V) : v ∈ B' ↔ 3 ≤ (neighborsIn G A v).card := by simp [B']
    have hAB' : ∀ a ∈ A, ∀ b ∈ B', G.Adj a b := by
      intro a ha b hb
      obtain ⟨f, hfinj, hfmem⟩ := exists_injective_fin3_of_card_ge_three
        (neighborsIn G A b) ((hB'iff b).mp hb)
      obtain ⟨g, hginj, hgmem⟩ := exists_injective_fin3_of_card_ge_three B hBcard
      have hcross : ∀ i j, G.Adj (g i) (f j) := by
        intro i j
        exact (G.adj_comm _ _).mp
          (hAB (f j) ((Finset.mem_filter.mp (hfmem j)).1) (g i) (hgmem i))
      have hb' : G.Adj b a := by
        apply hSat g f hginj hfinj hcross b a
        · intro j; exact (Finset.mem_filter.mp (hfmem j)).2
        · intro i; exact hAB a ha (g i) (hgmem i)
      exact (G.adj_comm _ _).mp hb'
    have hsumA : ∑ v : V, (neighborsIn G A v).card = ∑ a ∈ A, G.degree a :=
      sum_card_neighborsIn_eq_sum_degree_on G A
    have hlowA : (A.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) ≤
        (∑ v : V, (neighborsIn G A v).card : ℕ) := by
      rw [hsumA, Nat.cast_sum]
      calc
        (A.card : ℝ) * ((Fintype.card V : ℝ) / 2 + 100) =
            ∑ _a ∈ A, ((Fintype.card V : ℝ) / 2 + 100) := by
              simp [mul_add]
        _ ≤ ∑ a ∈ A, (G.degree a : ℝ) := by
          exact Finset.sum_le_sum fun a ha => hdeg a
    have huppA : ((∑ v : V, (neighborsIn G A v).card : ℕ) : ℝ) ≤
        (B'.card : ℝ) * A.card + 2 * Fintype.card V := by
      exact_mod_cast sum_neighborsIn_le G A B' hB'iff
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hAcard)
    have hB'real : (Fintype.card V : ℝ) / 2 + 96 ≤ B'.card := by
      have hdiv : 2 * (Fintype.card V : ℝ) / A.card ≤ 4 := by
        apply (div_le_iff₀ hApos).2
        have ha2 : (Fintype.card V : ℝ) / 2 ≤ A.card := by linarith
        nlinarith
      have hmain := hlowA.trans huppA
      apply (le_of_sub_nonneg ?_)
      nlinarith
    have hdisj : Disjoint A B' := by
      apply Finset.disjoint_left.2
      intro z hzA hzB'
      exact G.irrefl (hAB' z hzA z hzB')
    have hcardunion : A.card + B'.card ≤ Fintype.card V := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (by simp)
    have hcontr : (Fintype.card V : ℝ) + 164 ≤ A.card + B'.card := by
      linarith
    have hcardunionR : (A.card + B'.card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hcardunion
    linarith

lemma saturated33_induce
    (G : SimpleGraph V) (S : Set V) (hSat : Saturated33 G) :
    Saturated33 (G.induce S) := by
  intro f g hf hg hcross x y hx hy
  let f' : Fin 3 → V := fun i => (f i : V)
  let g' : Fin 3 → V := fun j => (g j : V)
  have hf' : Function.Injective f' := by
    intro i j h
    apply hf
    exact Subtype.ext h
  have hg' : Function.Injective g' := by
    intro i j h
    apply hg
    exact Subtype.ext h
  have hcross' : ∀ i j, G.Adj (f' i) (g' j) := hcross
  exact hSat f' g' hf' hg' hcross' x y hx hy

theorem card_edgeFinset_le_quarter_add_linear_of_saturated33 :
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Saturated33 G →
      (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 + 101 * Fintype.card V := by
  intro V instV G instAdj hSat
  classical
  generalize hn : Fintype.card V = n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
      by_cases hV : Nonempty V
      · letI := hV
        obtain ⟨v, hvdeg⟩ := low_degree_of_saturated33 G hSat
        let S : Set V := {v}ᶜ
        let J := G.induce S
        have hcardS : Fintype.card S = n - 1 := by
          change Fintype.card {x : V // x ≠ v} = n - 1
          have hone : Fintype.card {x : V // x = v} = 1 := by
            let e : {x : V // x = v} ≃ PUnit.{0} := {
              toFun _ := PUnit.unit
              invFun _ := ⟨v, rfl⟩
              left_inv x := by apply Subtype.ext; exact x.property.symm
              right_inv _ := rfl }
            simpa using Fintype.card_congr e
          calc
            Fintype.card {x : V // x ≠ v} =
                Fintype.card V - Fintype.card {x : V // x = v} := by
                  exact Fintype.card_subtype_compl (fun x : V => x = v)
            _ = n - 1 := by rw [hone, hn]
        have hnpos : 0 < n := by
          rw [← hn]
          exact Fintype.card_pos
        have hJ : (J.edgeFinset.card : ℝ) ≤
            (Fintype.card S : ℝ) ^ 2 / 4 + 101 * Fintype.card S := by
          have hJ' := ih (n - 1) (by omega) J (saturated33_induce G S hSat) hcardS
          simpa [hcardS] using hJ'
        have hdegNat : G.degree v ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset v
        have hsplit : G.edgeFinset.card = J.edgeFinset.card + G.degree v := by
          rw [← Nat.sub_add_cancel hdegNat,
            ← G.card_edgeFinset_deleteIncidenceSet v,
            ← G.card_edgeFinset_induce_compl_singleton v]
        rw [hsplit, Nat.cast_add]
        rw [hcardS] at hJ
        have hnsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        rw [hnsub] at hJ
        have hdeg' : (G.degree v : ℝ) ≤ (n : ℝ) / 2 + 100 := by
          rw [← hn]
          exact hvdeg
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
        nlinarith
      · haveI : IsEmpty V := not_nonempty_iff.mp hV
        have hn0 : n = 0 := by
          rw [← hn]
          exact Fintype.card_eq_zero
        subst n
        have he := G.card_edgeFinset_le_card_choose_two
        rw [hn0] at he
        norm_num at he
        subst G
        simp [hn0]

/-! ## Euclidean rectangle completion -/

abbrev E4 := EuclideanSpace ℝ (Fin 4)

lemma pair_vsub_mem_vectorSpan (a b : E4) :
    b - a ∈ vectorSpan ℝ (Set.range ![a, b]) := by
  exact vsub_mem_vectorSpan ℝ ⟨1, rfl⟩ ⟨0, rfl⟩

lemma finrank_E4 : Module.finrank ℝ E4 = 4 := by simp [E4]

lemma vectorSpan_eq_orthogonal_of_cross
    (f g : Fin 3 → E4) (hf : Function.Injective f) (hg : Function.Injective g)
    (r : ℝ) (hcross : ∀ i j, dist (f i) (g j) = r) :
    vectorSpan ℝ (Set.range f) = (vectorSpan ℝ (Set.range g))ᗮ := by
  let U := vectorSpan ℝ (Set.range f)
  let W := vectorSpan ℝ (Set.range g)
  have hUW : U ⟂ W := Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq f g r hcross
  have hle : U ≤ Wᗮ := Submodule.isOrtho_iff_le.mp hUW
  have hU : Module.finrank ℝ U = 2 :=
    Erdos755.finrank_vectorSpan_fin3_of_equidistant f hf (g 0) r (fun i => hcross i 0)
  have hW : Module.finrank ℝ W = 2 :=
    Erdos755.finrank_vectorSpan_fin3_of_equidistant g hg (f 0) r
      (fun j => by simpa [dist_comm] using hcross 0 j)
  have hsum := Submodule.finrank_add_finrank_orthogonal W
  have hWperp : Module.finrank ℝ Wᗮ = 2 := by
    rw [hW, finrank_E4] at hsum
    omega
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hU, hWperp])

lemma orthogonal_quadrilateral
    {x a y b : E4} (horth : inner ℝ (x - a) (y - b) = 0) :
    ‖x - y‖ ^ 2 + ‖a - b‖ ^ 2 = ‖x - b‖ ^ 2 + ‖a - y‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
  simp only [inner_sub_left, inner_sub_right] at horth
  nlinarith

/-- In four dimensions, two transverse triples at one common distance have the
rectangle-completion property used in Swanepoel's argument. -/
lemma dist_eq_of_cross_completion
    (f g : Fin 3 → E4) (hf : Function.Injective f) (hg : Function.Injective g)
    (r : ℝ) (hr : 0 < r) (hcross : ∀ i j, dist (f i) (g j) = r)
    (x y : E4) (hx : ∀ j, dist x (g j) = r) (hy : ∀ i, dist y (f i) = r) :
    dist x y = r := by
  let U := vectorSpan ℝ (Set.range f)
  let W := vectorSpan ℝ (Set.range g)
  have hUW : U ⟂ W := Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq f g r hcross
  have hUeq : U = Wᗮ := vectorSpan_eq_orthogonal_of_cross f g hf hg r hcross
  have hWeq : W = Uᗮ := by
    have hWU : W ⟂ U := hUW.symm
    have hle : W ≤ Uᗮ := Submodule.isOrtho_iff_le.mp hWU
    have hW : Module.finrank ℝ W = 2 :=
      Erdos755.finrank_vectorSpan_fin3_of_equidistant g hg (f 0) r
        (fun j => by simpa [dist_comm] using hcross 0 j)
    have hU : Module.finrank ℝ U = 2 :=
      Erdos755.finrank_vectorSpan_fin3_of_equidistant f hf (g 0) r (fun i => hcross i 0)
    have hsum := Submodule.finrank_add_finrank_orthogonal U
    have hUperp : Module.finrank ℝ Uᗮ = 2 := by
      rw [hU, finrank_E4] at hsum
      omega
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hW, hUperp])
  have hxspan : x - f 0 ∈ U := by
    have hp : vectorSpan ℝ (Set.range ![f 0, x]) ⟂ W :=
      Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq ![f 0, x] g r (by
        intro i j
        fin_cases i
        · exact hcross 0 j
        · exact hx j)
    have hxperp : x - f 0 ∈ Wᗮ :=
      (Submodule.isOrtho_iff_le.mp hp) (pair_vsub_mem_vectorSpan (f 0) x)
    rwa [hUeq]
  have hyspan : y - g 0 ∈ W := by
    have hp : vectorSpan ℝ (Set.range ![g 0, y]) ⟂ U :=
      Erdos755.vectorSpan_range_isOrtho_of_cross_dist_eq ![g 0, y] f r (by
        intro j i
        fin_cases j
        · simpa [dist_comm] using hcross i 0
        · simpa [dist_comm] using hy i)
    have hyperp : y - g 0 ∈ Uᗮ :=
      (Submodule.isOrtho_iff_le.mp hp) (pair_vsub_mem_vectorSpan (g 0) y)
    rwa [hWeq]
  have hxspan' : x - f 0 ∈ Submodule.span ℝ (Set.range (fun i => f i - f 0)) := by
    have hxspanv : x - f 0 ∈ Submodule.span ℝ (Set.range (fun i => f i -ᵥ f 0)) := by
      rw [← vectorSpan_range_eq_span_range_vsub_right ℝ f 0]
      exact hxspan
    simpa only [vsub_eq_sub] using hxspanv
  have hyspan' : y - g 0 ∈ Submodule.span ℝ (Set.range (fun j => g j - g 0)) := by
    have hyspanv : y - g 0 ∈ Submodule.span ℝ (Set.range (fun j => g j -ᵥ g 0)) := by
      rw [← vectorSpan_range_eq_span_range_vsub_right ℝ g 0]
      exact hyspan
    simpa only [vsub_eq_sub] using hyspanv
  have horth : inner ℝ (x - f 0) (y - g 0) = 0 :=
    Erdos755.inner_eq_zero_of_mem_orthogonal_spans
      (u := fun i => f i - f 0) (v := fun j => g j - g 0)
      (fun i j => by
        have hmemi : f i - f 0 ∈ U := vsub_mem_vectorSpan ℝ ⟨i, rfl⟩ ⟨0, rfl⟩
        have hmemj : g j - g 0 ∈ W := vsub_mem_vectorSpan ℝ ⟨j, rfl⟩ ⟨0, rfl⟩
        exact hUW.inner_eq hmemi hmemj)
      hxspan' hyspan'
  have hquad := orthogonal_quadrilateral horth
  have hy0 : dist (f 0) y = r := by simpa [dist_comm] using hy 0
  rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm,
    hx 0, hcross 0 0, hy0] at hquad
  have hsquare : dist x y ^ 2 = r ^ 2 := by nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare) with h | h
  · exact h
  · have : 0 ≤ dist x y := dist_nonneg
    nlinarith

/-! ## Fixed-distance graphs -/

noncomputable def distanceGraph {W : Type*} (p : W → E4)
    (_hp : Function.Injective p) (r : ℝ) (hr : 0 < r) : SimpleGraph W where
  Adj x y := dist (p x) (p y) = r
  symm.symm := by intro x y h; simpa [dist_comm] using h
  loopless.irrefl := by
    intro x h
    have : (0 : ℝ) = r := by simpa using h
    linarith

noncomputable instance distanceGraph.instDecidableRelAdj {W : Type*} (p : W → E4)
    (hp : Function.Injective p) (r : ℝ) (hr : 0 < r) :
    DecidableRel (distanceGraph p hp r hr).Adj := Classical.decRel _

lemma distanceGraph_saturated33 {W : Type*} (p : W → E4)
    (hp : Function.Injective p) (r : ℝ) (hr : 0 < r) :
    Saturated33 (distanceGraph p hp r hr) := by
  intro f g hf hg hcross x y hx hy
  let f' : Fin 3 → E4 := fun i => p (f i)
  let g' : Fin 3 → E4 := fun j => p (g j)
  have hf' : Function.Injective f' := hp.comp hf
  have hg' : Function.Injective g' := hp.comp hg
  exact dist_eq_of_cross_completion f' g' hf' hg' r hr hcross (p x) (p y) hx hy

lemma directed_indicator_eq_twice_edges {W : Type*} [Fintype W]
    (G : SimpleGraph W) [DecidableRel G.Adj] :
    (∑ x : W, ∑ y : W, DRC.indicator (G.Adj x y)) =
      2 * (G.edgeFinset.card : ℝ) := by
  classical
  calc
    (∑ x : W, ∑ y : W, DRC.indicator (G.Adj x y)) =
        ∑ x : W, (G.degree x : ℝ) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [DRC.sum_indicator_eq_card_filter]
          rw [← G.card_neighborFinset_eq_degree]
          have hfilter : (Finset.univ.filter fun y : W => G.Adj x y) =
              G.neighborFinset x := by
            ext y
            simp [G.mem_neighborFinset]
          rw [hfilter]
    _ = 2 * (G.edgeFinset.card : ℝ) := by
          rw [← Nat.cast_sum, G.sum_degrees_eq_twice_card_edges]
          norm_cast

/-! ## Fiberwise counting -/

noncomputable def fiber {W : Type*} [Fintype W] (c : W → ℝ) (t : ℝ) : Finset W :=
  Finset.univ.filter fun x => c x = t

lemma sum_eq_eq_fibers {W : Type*} [Fintype W]
    (c : W → ℝ) (w : W → W → ℝ) :
    ∑ x : W, ∑ y : W, (if c x = c y then w x y else 0) =
      ∑ t ∈ (Finset.univ.image c), ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, w x y := by
  classical
  symm
  calc
    ∑ t ∈ (Finset.univ.image c), ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, w x y =
        ∑ t ∈ (Finset.univ.image c),
          ∑ x ∈ (Finset.univ : Finset W) with c x = t,
            ∑ y ∈ (Finset.univ : Finset W) with c y = t, w x y := by rfl
    _ = ∑ t ∈ (Finset.univ.image c),
          ∑ x ∈ (Finset.univ : Finset W) with c x = t,
            ∑ y ∈ (Finset.univ : Finset W) with c y = c x, w x y := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro x hx
          have hxt : c x = t := (Finset.mem_filter.mp hx).2
          rw [hxt]
    _ = ∑ x ∈ (Finset.univ : Finset W),
          ∑ y ∈ (Finset.univ : Finset W) with c y = c x, w x y := by
          rw [Finset.sum_fiberwise_of_maps_to (g := c)
            (s := (Finset.univ : Finset W)) (t := Finset.univ.image c)]
          intro x hx
          exact Finset.mem_image_of_mem c hx
    _ = ∑ x : W, ∑ y : W, (if c x = c y then w x y else 0) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_filter]
          congr 1
          funext y
          by_cases h : c x = c y <;> simp [h, eq_comm]

lemma sum_fiber_card {W : Type*} [Fintype W] (c : W → ℝ) :
    ∑ t ∈ (Finset.univ.image c), (fiber c t).card = Fintype.card W := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise (f := c)
    (s := (Finset.univ : Finset W)) (t := Finset.univ.image c)
    (fun x hx => Finset.mem_image_of_mem c hx)
  simpa [fiber] using h.symm

lemma sum_eq_indicator_eq_sum_fiber_sq {W : Type*} [Fintype W] (c : W → ℝ) :
    ∑ x : W, ∑ y : W, DRC.indicator (c x = c y) =
      ∑ t ∈ (Finset.univ.image c), ((fiber c t).card : ℝ) ^ 2 := by
  classical
  rw [show (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) =
      ∑ x : W, ∑ y : W, (if c x = c y then (1 : ℝ) else 0) by
        simp [DRC.indicator, Erdos754.indicator]]
  rw [sum_eq_eq_fibers]
  apply Finset.sum_congr rfl
  intro t ht
  simp [pow_two]

lemma total_le_of_same_le {W : Type*} [Fintype W]
    (c : W → ℝ) (fav : W → W → Prop)
    (hboth : ∀ x y, c x ≠ c y → fav x y → fav y x → False)
    (hSame :
      ∑ x : W, ∑ y : W,
          (if c x = c y then DRC.indicator (fav x y) else 0) ≤
        (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) / 2 +
          202 * Fintype.card W) :
    ∑ x : W, ∑ y : W, DRC.indicator (fav x y) ≤
      (Fintype.card W : ℝ) ^ 2 / 2 + 202 * Fintype.card W := by
  classical
  let S : ℝ := ∑ x : W, ∑ y : W, DRC.indicator (fav x y)
  let I : ℝ := ∑ x : W, ∑ y : W,
    (if c x = c y then DRC.indicator (fav x y) else 0)
  let E : ℝ := ∑ x : W, ∑ y : W, DRC.indicator (c x = c y)
  let R : ℝ := ∑ x : W, ∑ y : W,
    (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1)
  have hpair : ∀ x y,
      DRC.indicator (fav x y) + DRC.indicator (fav y x) ≤
        (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1) := by
    intro x y
    by_cases hxy : c x = c y
    · simp [hxy]
    · by_cases h1 : fav x y
      · by_cases h2 : fav y x
        · exact False.elim (hboth x y hxy h1 h2)
        · simp [hxy, h1, h2, DRC.indicator]
      · by_cases h2 : fav y x <;> simp [hxy, h1, h2, DRC.indicator]
  have htwice : 2 * S =
      ∑ x : W, ∑ y : W,
        (DRC.indicator (fav x y) + DRC.indicator (fav y x)) := by
    dsimp [S]
    have hsplit :
        (∑ x : W, ∑ y : W,
          (DRC.indicator (fav x y) + DRC.indicator (fav y x))) =
        (∑ x : W, ∑ y : W, DRC.indicator (fav x y)) +
          (∑ x : W, ∑ y : W, DRC.indicator (fav y x)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_add_distrib]
    have hswap : (∑ x : W, ∑ y : W, DRC.indicator (fav y x)) =
        ∑ x : W, ∑ y : W, DRC.indicator (fav x y) := by rw [Finset.sum_comm]
    rw [hsplit, hswap]
    ring
  have hRbound : 2 * S ≤ R := by
    rw [htwice]
    exact Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpair x y
  have hR : R = 2 * I + ((Fintype.card W : ℝ) ^ 2 - E) := by
    dsimp [R, I, E]
    have hsplit :
        (∑ x : W, ∑ y : W,
          (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1)) =
        (∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav x y) else 0)) +
        (∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav y x) else 0)) +
        (∑ x : W, ∑ y : W, (if c x = c y then (0 : ℝ) else 1)) := by
      calc
        (∑ x : W, ∑ y : W,
          (if c x = c y then DRC.indicator (fav x y) + DRC.indicator (fav y x) else 1)) =
          ∑ x : W, ∑ y : W,
            ((if c x = c y then DRC.indicator (fav x y) else 0) +
              (if c x = c y then DRC.indicator (fav y x) else 0) +
              (if c x = c y then (0 : ℝ) else 1)) := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            by_cases h : c x = c y <;> simp [h]
        _ = _ := by simp_rw [Finset.sum_add_distrib]
    rw [hsplit]
    have hswap :
        (∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav y x) else 0)) =
        ∑ x : W, ∑ y : W, (if c x = c y then DRC.indicator (fav x y) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : c x = c y
      · rw [if_pos h.symm, if_pos h]
      · have h' : c y ≠ c x := Ne.symm h
        rw [if_neg h', if_neg h]
    rw [hswap]
    have hpartition :
        (∑ x : W, ∑ y : W, (if c x = c y then (0 : ℝ) else 1)) +
        (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) =
          (Fintype.card W : ℝ) ^ 2 := by
      have hpoint :
          (∑ x : W, ∑ y : W,
            ((if c x = c y then (0 : ℝ) else 1) + DRC.indicator (c x = c y))) =
            (Fintype.card W : ℝ) ^ 2 := by
        calc
          (∑ x : W, ∑ y : W,
            ((if c x = c y then (0 : ℝ) else 1) + DRC.indicator (c x = c y))) =
              ∑ x : W, ∑ y : W, (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro x hx
                apply Finset.sum_congr rfl
                intro y hy
                by_cases h : c x = c y <;> simp [h, DRC.indicator]
          _ = (Fintype.card W : ℝ) ^ 2 := by simp [pow_two]
      rw [← hpoint]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_add_distrib]
    linarith
  have hSame' : I ≤ E / 2 + 202 * Fintype.card W := by simpa [I, E] using hSame
  rw [hR] at hRbound
  linarith

lemma same_le_of_fiber_bounds {W : Type*} [Fintype W]
    (c : W → ℝ) (fav : W → W → Prop)
    (hFiber : ∀ t ∈ Finset.univ.image c,
      ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, DRC.indicator (fav x y) ≤
        ((fiber c t).card : ℝ) ^ 2 / 2 + 202 * (fiber c t).card) :
    ∑ x : W, ∑ y : W,
        (if c x = c y then DRC.indicator (fav x y) else 0) ≤
      (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) / 2 +
        202 * Fintype.card W := by
  classical
  rw [sum_eq_eq_fibers]
  calc
    ∑ t ∈ Finset.univ.image c,
        ∑ x ∈ fiber c t, ∑ y ∈ fiber c t, DRC.indicator (fav x y) ≤
      ∑ t ∈ Finset.univ.image c,
        (((fiber c t).card : ℝ) ^ 2 / 2 + 202 * (fiber c t).card) := by
          exact Finset.sum_le_sum hFiber
    _ = (∑ x : W, ∑ y : W, DRC.indicator (c x = c y)) / 2 +
        202 * Fintype.card W := by
          have hcardR : (∑ t ∈ Finset.univ.image c, ((fiber c t).card : ℝ)) =
              Fintype.card W := by
            exact_mod_cast sum_fiber_card c
          rw [sum_eq_indicator_eq_sum_fiber_sq]
          simp_rw [Finset.sum_add_distrib]
          rw [Finset.sum_div, ← Finset.mul_sum, hcardR]

/-- A favorite-distance relation; the strict positivity is kept separately. -/
def IsFavorite {W : Type*} (p : W → E4) (c : W → ℝ) (x y : W) : Prop :=
  x ≠ y ∧ dist (p x) (p y) = c x

lemma fiber_directed_bound {W : Type*} [Fintype W]
    (p : W → E4) (hp : Function.Injective p) (c : W → ℝ) (hc : ∀ x, 0 < c x)
    (F : Finset W) (t : ℝ) (hFt : ∀ x ∈ F, c x = t) :
    ∑ x ∈ F, ∑ y ∈ F, DRC.indicator (IsFavorite p c x y) ≤
      ((F.card : ℝ) ^ 2 / 2 + 202 * F.card) := by
  classical
  by_cases hF : F.Nonempty
  · obtain ⟨x0, hx0⟩ := hF
    have ht : 0 < t := by rw [← hFt x0 hx0]; exact hc x0
    let q : F → E4 := fun x => p x
    have hq : Function.Injective q := by
      intro x y h
      apply Subtype.ext
      exact hp h
    let G := distanceGraph q hq t ht
    have hG := card_edgeFinset_le_quarter_add_linear_of_saturated33 G
      (distanceGraph_saturated33 q hq t ht)
    have hdir := directed_indicator_eq_twice_edges G
    have hsum :
        (∑ x ∈ F, ∑ y ∈ F, DRC.indicator (IsFavorite p c x y)) =
          ∑ x : F, ∑ y : F, DRC.indicator (G.Adj x y) := by
      rw [← Finset.sum_coe_sort F
        (fun x => ∑ y ∈ F, DRC.indicator (IsFavorite p c x y))]
      apply Finset.sum_congr rfl
      intro x hx
      rw [← Finset.sum_coe_sort F
        (fun y => DRC.indicator (IsFavorite p c (x : W) y))]
      apply Finset.sum_congr rfl
      intro y hy
      have hcx : c x = t := hFt x x.property
      by_cases hxy : x = y
      · subst y
        simp [G, distanceGraph, IsFavorite]
      · simp [G, distanceGraph, q, IsFavorite, hxy, hcx]
    rw [hsum, hdir]
    have hcard : Fintype.card F = F.card := by simpa using Fintype.card_coe F
    rw [hcard] at hG
    nlinarith
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [hF0]

/-- The Swanepoel-type favorite-distance bound, with an explicit absolute constant. -/
theorem favorite_distance_sum_le {W : Type*} [Fintype W]
    (p : W → E4) (hp : Function.Injective p) (c : W → ℝ) (hc : ∀ x, 0 < c x) :
    ∑ x : W, ∑ y : W, DRC.indicator (IsFavorite p c x y) ≤
      (Fintype.card W : ℝ) ^ 2 / 2 + 202 * Fintype.card W := by
  classical
  apply total_le_of_same_le c (IsFavorite p c)
  · intro x y hxy h1 h2
    have hdist : c x = c y := by
      calc
        c x = dist (p x) (p y) := h1.2.symm
        _ = dist (p y) (p x) := dist_comm _ _
        _ = c y := h2.2
    exact hxy hdist
  · apply same_le_of_fiber_bounds c (IsFavorite p c)
    intro t ht
    apply fiber_directed_bound p hp c hc (fiber c t) t
    intro x hx
    exact (Finset.mem_filter.mp hx).2

/-! ## The extremal function in Problem 754 -/

/-- The number of other points at the prescribed positive distance from `x`. -/
noncomputable def favoriteDegree (P : Finset E4) (c : P → ℝ) (x : P) : ℕ :=
  open scoped Classical in
  (Finset.univ.filter fun y : P => IsFavorite (fun z : P => (z : E4)) c x y).card

/-- A value `k` is attainable for a set of `n` points when every point has at least
`k` other points at its own prescribed positive distance. -/
def Attainable (n k : ℕ) : Prop :=
  ∃ P : Finset E4, P.card = n ∧
    ∃ c : P → ℝ, (∀ x, 0 < c x) ∧ ∀ x, k ≤ favoriteDegree P c x

/-- The maximal minimum favorite-distance degree for `n` points.  The empty case is
set to zero, as the problem concerns positive numbers of points. -/
noncomputable def f (n : ℕ) : ℕ :=
  if n = 0 then 0 else sSup {k : ℕ | Attainable n k}

lemma sum_favoriteDegree_eq (P : Finset E4) (c : P → ℝ) :
    ∑ x : P, (favoriteDegree P c x : ℝ) =
      ∑ x : P, ∑ y : P,
        DRC.indicator (IsFavorite (fun z : P => (z : E4)) c x y) := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  unfold favoriteDegree
  rw [DRC.sum_indicator_eq_card_filter]

lemma attainable_bddAbove (n : ℕ) (hn : n ≠ 0) : BddAbove {k : ℕ | Attainable n k} := by
  classical
  refine ⟨n, ?_⟩
  intro k hk
  rcases hk with ⟨P, hP, c, hc, hk⟩
  have hPempty : P.Nonempty := by
    apply Finset.card_pos.mp
    rw [hP]
    omega
  obtain ⟨x, hx⟩ := hPempty
  let xP : P := ⟨x, hx⟩
  have hdeg : favoriteDegree P c xP ≤ Fintype.card P := by
    unfold favoriteDegree
    simpa using Finset.card_filter_le (Finset.univ : Finset P)
      (fun y : P => IsFavorite (fun z : P => (z : E4)) c xP y)
  simpa [hP] using (hk xP).trans hdeg

lemma attainable_nonempty (n : ℕ) : {k : ℕ | Attainable n k}.Nonempty := by
  obtain ⟨P, hP⟩ := Finset.exists_card_eq (α := E4) n
  refine ⟨0, P, hP, (fun _ => 1), ?_, ?_⟩
  · intro x
    norm_num
  · intro x
    omega

lemma attainable_cast_le (n k : ℕ) (hn : n ≠ 0) (hk : Attainable n k) :
    (k : ℝ) ≤ (n : ℝ) / 2 + 202 := by
  rcases hk with ⟨P, hP, c, hc, hk⟩
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    rw [hP]
    omega
  have hsumlow : (n : ℝ) * k ≤ ∑ x : P, (favoriteDegree P c x : ℝ) := by
    rw [← hP]
    calc
      (P.card : ℝ) * k = ∑ _x : P, (k : ℝ) := by simp
      _ ≤ ∑ x : P, (favoriteDegree P c x : ℝ) := by
        exact Finset.sum_le_sum fun x hx => by exact_mod_cast hk x
  have hsumup : ∑ x : P, (favoriteDegree P c x : ℝ) ≤
      (n : ℝ) ^ 2 / 2 + 202 * n := by
    rw [sum_favoriteDegree_eq]
    have h := favorite_distance_sum_le (fun z : P => (z : E4))
      (fun _ _ hxy => Subtype.ext hxy) c hc
    simpa [hP] using h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  nlinarith

/-- Erdős Problem 754: the maximal favorite-distance degree is at most `n / 2`
plus an absolute constant. -/
theorem erdos_754 : ∃ C : ℝ, ∀ n : ℕ, (f n : ℝ) ≤ (n : ℝ) / 2 + C := by
  refine ⟨202, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    simp [f]
  · have hmem : f n ∈ {k : ℕ | Attainable n k} := by
      rw [f, if_neg hn]
      exact Nat.sSup_mem (attainable_nonempty n) (attainable_bddAbove n hn)
    exact attainable_cast_le n (f n) hn hmem

end Erdos754
