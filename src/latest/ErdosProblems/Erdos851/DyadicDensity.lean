import Mathlib
import Util.Density
import ErdosProblems.Erdos851.Elementary

/-!
# From dyadic exceptional-set estimates to lower density

The analytic part of the argument supplies a bound on every sufficiently
large dyadic shell.  This file turns that hypothesis into a bound for every
large prefix, and then into a lower-density estimate for the complement.
-/

open Filter
open scoped Topology

namespace Erdos851

/-- Number of exceptional integers in the half-open prefix `[0,N)`. -/
noncomputable def exceptionalPrefixCount (B : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => n ∈ B).card

/-- Number of exceptional integers in the dyadic shell `(X,2X]`. -/
noncomputable def exceptionalDyadicCount (B : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((dyadicInterval X).filter fun n => n ∈ B).card

/-- A computable-predicate view of `exceptionalDyadicCount`.  This bridge is
useful because the noncomputable definition and a local `classical` block may
choose proposition-decision procedures which are not definitionally equal. -/
theorem exceptionalDyadicCount_eq_filter_card (B : Set ℕ)
    [DecidablePred (fun n => n ∈ B)] (X : ℕ) :
    exceptionalDyadicCount B X =
      ((dyadicInterval X).filter fun n => n ∈ B).card := by
  classical
  unfold exceptionalDyadicCount
  apply congrArg Finset.card
  apply Finset.ext
  intro n
  simp

/-- A prefix splits into a prefix of essentially half the length and one
dyadic shell. -/
theorem exceptionalPrefixCount_le_half_add_dyadic
    (B : Set ℕ) (N : ℕ) (_hN : 4 ≤ N) :
    exceptionalPrefixCount B N ≤
      exceptionalPrefixCount B (N / 2 + 1) + exceptionalDyadicCount B (N / 2) := by
  classical
  let P := (Finset.range N).filter fun n => n ∈ B
  let Q := (Finset.range (N / 2 + 1)).filter fun n => n ∈ B
  let D := (dyadicInterval (N / 2)).filter fun n => n ∈ B
  have hsubset : P ⊆ Q ∪ D := by
    intro n hn
    have hnP := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp hnP.1
    by_cases hnHalf : n ≤ N / 2
    · exact Finset.mem_union_left D (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hnP.2⟩)
    · apply Finset.mem_union_right Q
      apply Finset.mem_filter.mpr
      refine ⟨?_, hnP.2⟩
      simp only [dyadicInterval, Finset.mem_Ioc]
      omega
  calc
    exceptionalPrefixCount B N = P.card := by
      simp only [exceptionalPrefixCount, P]
    _ ≤ (Q ∪ D).card := Finset.card_le_card hsubset
    _ ≤ Q.card + D.card := Finset.card_union_le Q D
    _ = exceptionalPrefixCount B (N / 2 + 1) +
        exceptionalDyadicCount B (N / 2) := by
      simp only [exceptionalPrefixCount, exceptionalDyadicCount, Q, D]

/-- The exceptional count in a prefix never exceeds the prefix length. -/
theorem exceptionalPrefixCount_le (B : Set ℕ) (N : ℕ) :
    exceptionalPrefixCount B N ≤ N := by
  classical
  rw [exceptionalPrefixCount]
  have hsub : ((Finset.range N).filter fun n => n ∈ B) ⊆ Finset.range N := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  simpa using Finset.card_le_card hsub

/-- A shell estimate with slope `δ` gives a uniform affine prefix estimate
with any larger slope `c`.  The explicit cutoff hypotheses isolate all
Archimedean bookkeeping from the induction. -/
theorem exceptionalPrefixCount_le_affine_of_dyadic
    (B : Set ℕ) {δ c C : ℝ} {M : ℕ}
    (hM : 2 ≤ M) (hδc : δ < c) (hc : 0 ≤ c)
    (hgap : c ≤ (c - δ) * M)
    (hshell : ∀ X, M ≤ X →
      (exceptionalDyadicCount B X : ℝ) ≤ δ * X)
    (hbase : ∀ N, N < 2 * M →
      (exceptionalPrefixCount B N : ℝ) ≤ c * N + C) :
    ∀ N, (exceptionalPrefixCount B N : ℝ) ≤ c * N + C := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hsmall : N < 2 * M
      · exact hbase N hsmall
      · have hN : 4 ≤ N := by omega
        let X := N / 2
        have hXM : M ≤ X := by
          dsimp [X]
          omega
        have hnext : X + 1 < N := by
          dsimp [X]
          omega
        have hrec := exceptionalPrefixCount_le_half_add_dyadic B N hN
        have hrec' :
            (exceptionalPrefixCount B N : ℝ) ≤
              exceptionalPrefixCount B (X + 1) + exceptionalDyadicCount B X := by
          exact_mod_cast hrec
        have hind := ih (X + 1) hnext
        have hind' :
            (exceptionalPrefixCount B (X + 1) : ℝ) ≤ c * ((X : ℝ) + 1) + C := by
          norm_num at hind ⊢
          exact hind
        have hs := hshell X hXM
        have hcoef : 0 ≤ c - δ := (sub_pos.mpr hδc).le
        have hXM' : (M : ℝ) ≤ X := by exact_mod_cast hXM
        have hgapX : c ≤ (c - δ) * X :=
          hgap.trans (mul_le_mul_of_nonneg_left hXM' hcoef)
        have hdouble : (2 : ℝ) * X ≤ N := by
          exact_mod_cast (show 2 * X ≤ N by
            dsimp [X]
            omega)
        calc
          (exceptionalPrefixCount B N : ℝ) ≤
              exceptionalPrefixCount B (X + 1) + exceptionalDyadicCount B X := hrec'
          _ ≤ (c * ((X : ℝ) + 1) + C) + δ * X := add_le_add hind' hs
          _ ≤ c * N + C := by
            nlinarith

/-- An eventual dyadic-shell bound with slope `δ` gives an eventual prefix
bound with every strictly larger slope. -/
theorem eventually_exceptionalPrefixCount_le_of_dyadic
    (B : Set ℕ) {δ η : ℝ} (hδ : 0 ≤ δ) (hδη : δ < η)
    (hshell : ∀ᶠ X : ℕ in atTop,
      (exceptionalDyadicCount B X : ℝ) ≤ δ * X) :
    ∀ᶠ N : ℕ in atTop, (exceptionalPrefixCount B N : ℝ) ≤ η * N := by
  let c : ℝ := (δ + η) / 2
  have hδc : δ < c := by
    dsimp [c]
    linarith
  have hcη : c < η := by
    dsimp [c]
    linarith
  have hc : 0 ≤ c := hδ.trans (le_of_lt hδc)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hshell
  obtain ⟨M₁, hM₁⟩ := exists_nat_ge (c / (c - δ))
  let M := max 2 (max X₀ M₁)
  have hM : 2 ≤ M := le_max_left _ _
  have hX₀M : X₀ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM₁M : M₁ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hden : 0 < c - δ := sub_pos.mpr hδc
  have hratio : c / (c - δ) ≤ (M : ℝ) := by
    exact hM₁.trans (by exact_mod_cast hM₁M)
  have hgap : c ≤ (c - δ) * M := by
    have := (div_le_iff₀ hden).mp hratio
    simpa [mul_comm] using this
  have hshellM : ∀ X, M ≤ X →
      (exceptionalDyadicCount B X : ℝ) ≤ δ * X := by
    intro X hMX
    exact hX₀ X (hX₀M.trans hMX)
  let C : ℝ := 2 * M
  have hbase : ∀ N, N < 2 * M →
      (exceptionalPrefixCount B N : ℝ) ≤ c * N + C := by
    intro N hNM
    have hcount : (exceptionalPrefixCount B N : ℝ) ≤ N := by
      exact_mod_cast exceptionalPrefixCount_le B N
    have hNM' : (N : ℝ) ≤ 2 * M := by exact_mod_cast (Nat.le_of_lt hNM)
    have hcN : 0 ≤ c * (N : ℝ) := mul_nonneg hc (Nat.cast_nonneg N)
    dsimp [C]
    nlinarith
  have hall : ∀ N, (exceptionalPrefixCount B N : ℝ) ≤ c * N + C :=
    exceptionalPrefixCount_le_affine_of_dyadic B hM hδc hc hgap hshellM hbase
  obtain ⟨K, hK⟩ := exists_nat_ge (C / (η - c))
  refine eventually_atTop.mpr ⟨K, ?_⟩
  intro N hKN
  have hpos : 0 < η - c := sub_pos.mpr hcη
  have hratioN : C / (η - c) ≤ (N : ℝ) :=
    hK.trans (by exact_mod_cast hKN)
  have habsorb : C ≤ (η - c) * N := by
    have := (div_le_iff₀ hpos).mp hratioN
    simpa [mul_comm] using this
  have hglobal := hall N
  nlinarith

/-- Prefix count as the `ncard` appearing in `Set.partialDensity`. -/
theorem exceptionalPrefixCount_eq_ncard (B : Set ℕ) (N : ℕ) :
    exceptionalPrefixCount B N = (B ∩ Set.Iio N).ncard := by
  classical
  rw [exceptionalPrefixCount]
  have hset : B ∩ Set.Iio N =
      ↑((Finset.range N).filter fun n => n ∈ B) := by
    ext n
    simp [and_comm]
  rw [hset, Set.ncard_coe_finset]

/-- The prefix counts of a set and its complement partition the prefix. -/
theorem exceptionalPrefixCount_compl_add (B : Set ℕ) (N : ℕ) :
    exceptionalPrefixCount Bᶜ N + exceptionalPrefixCount B N = N := by
  classical
  simpa only [exceptionalPrefixCount, Set.mem_compl_iff,
    Finset.card_range, add_comm] using
    (Finset.card_filter_add_card_filter_not (s := Finset.range N)
      (p := fun n ↦ n ∈ B))

/-- Over the natural numbers, partial density is the exceptional prefix count
divided by the prefix length. -/
theorem partialDensity_eq_exceptionalPrefixCount (B : Set ℕ) (N : ℕ) :
    B.partialDensity Set.univ N = (exceptionalPrefixCount B N : ℝ) / N := by
  rw [Set.partialDensity]
  simp only [Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  rw [exceptionalPrefixCount_eq_ncard]

/-- The final generic transfer: an eventual dyadic-shell exceptional bound
of slope `δ` implies lower density at least `1-δ` for the good set. -/
theorem one_sub_le_lowerDensity_compl_of_dyadic
    (B : Set ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hshell : ∀ᶠ X : ℕ in atTop,
      (exceptionalDyadicCount B X : ℝ) ≤ δ * X) :
    1 - δ ≤ Bᶜ.lowerDensity := by
  rw [Set.lowerDensity]
  refine (Filter.le_liminf_iff'
    (isCoboundedUnder_ge_of_le atTop fun N =>
      Set.partialDensity_le_one Bᶜ Set.univ N)
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall fun N =>
      show 0 ≤ Bᶜ.partialDensity Set.univ N by positivity))).2 ?_
  intro y hy
  let η : ℝ := (δ + (1 - y)) / 2
  have hδη : δ < η := by
    dsimp [η]
    linarith
  have hηy : η < 1 - y := by
    dsimp [η]
    linarith
  have hpref := eventually_exceptionalPrefixCount_le_of_dyadic B hδ hδη hshell
  filter_upwards [hpref, eventually_gt_atTop 0] with N hN hNpos
  rw [partialDensity_eq_exceptionalPrefixCount]
  have hpartition := exceptionalPrefixCount_compl_add B N
  have hpartition' :
      (exceptionalPrefixCount Bᶜ N : ℝ) + exceptionalPrefixCount B N = N := by
    exact_mod_cast hpartition
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
  apply (le_div_iff₀ hNpos').2
  nlinarith

/-- Assembly lemma for a representation-count argument.  If the positive
support of `R X` fills at least a `1-δ` proportion of every sufficiently
large dyadic shell, and every point of that support has the desired
certificate `G`, then `G` has lower density at least `1-δ`. -/
theorem one_sub_le_lowerDensity_of_eventually_dyadic_support
    (G : Set ℕ) (R : ℕ → ℕ → ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsupport : ∀ᶠ X : ℕ in atTop,
      (1 - δ) * X ≤
        (((dyadicInterval X).filter fun a => 0 < R X a).card : ℝ))
    (hcertificate : ∀ X a, a ∈ dyadicInterval X → 0 < R X a → a ∈ G) :
    1 - δ ≤ G.lowerDensity := by
  have hbad : ∀ᶠ X : ℕ in atTop,
      (exceptionalDyadicCount Gᶜ X : ℝ) ≤ δ * X := by
    filter_upwards [hsupport] with X hsupportX
    classical
    let good := (dyadicInterval X).filter fun a => 0 < R X a
    let bad := (dyadicInterval X).filter fun a => a ∈ Gᶜ
    have hdisjoint : Disjoint good bad := by
      rw [Finset.disjoint_left]
      intro a hagood habad
      have hagood' := Finset.mem_filter.mp hagood
      have habad' := Finset.mem_filter.mp habad
      exact habad'.2 (hcertificate X a hagood'.1 hagood'.2)
    have hunion : good ∪ bad ⊆ dyadicInterval X := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_filter.mp ha).1
      · exact (Finset.mem_filter.mp ha).1
    have hcard : good.card + bad.card ≤ X := by
      calc
        good.card + bad.card = (good ∪ bad).card :=
          (Finset.card_union_of_disjoint hdisjoint).symm
        _ ≤ (dyadicInterval X).card := Finset.card_le_card hunion
        _ = X := by simp [dyadicInterval, two_mul]
    have hcard' : (good.card : ℝ) + bad.card ≤ X := by exact_mod_cast hcard
    have hsupportX' : (1 - δ) * X ≤ (good.card : ℝ) := by
      simpa only [good] using hsupportX
    rw [exceptionalDyadicCount_eq_filter_card]
    change (bad.card : ℝ) ≤ δ * X
    nlinarith
  have h := one_sub_le_lowerDensity_compl_of_dyadic Gᶜ hδ hbad
  simpa using h

end Erdos851
