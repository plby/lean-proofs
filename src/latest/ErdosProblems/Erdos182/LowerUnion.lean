/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos182.LowerCounting
import ErdosProblems.Erdos182.LowerCombinatorics
import ErdosProblems.Erdos182.LowerAsymptotic

/-! # The all-scales union bound in the PRS lower construction -/

namespace Erdos182

open scoped BigOperators Classical

noncomputable section

/-- The exponential summands in the lower construction are powers of the
first summand. -/
lemma exp_neg_nat_succ_mul_half (y : ℝ) (x : ℕ) :
    Real.exp (-(((x + 1 : ℕ) : ℝ) * y / 2)) =
      Real.exp (-(y / 2)) ^ (x + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A finite initial segment of the relevant exponential series is bounded
by twice its first term once that term is at most `1/2`. -/
lemma sum_exp_neg_succ_mul_half_le (m : ℕ) (y : ℝ)
    (hhalf : Real.exp (-(y / 2)) ≤ (1 / 2 : ℝ)) :
    ∑ x ∈ Finset.range m, Real.exp (-(((x + 1 : ℕ) : ℝ) * y / 2)) ≤
      2 * Real.exp (-(y / 2)) := by
  let q : ℝ := Real.exp (-(y / 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  calc
    ∑ x ∈ Finset.range m, Real.exp (-(((x + 1 : ℕ) : ℝ) * y / 2)) =
        ∑ x ∈ Finset.range m, q * q ^ x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [exp_neg_nat_succ_mul_half, pow_succ']
    _ ≤ ∑ x ∈ Finset.range m, q * (1 / 2 : ℝ) ^ x := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hq0 hhalf x) hq0
    _ = q * ∑ x ∈ Finset.range m, (1 / 2 : ℝ) ^ x := by
      rw [Finset.mul_sum]
    _ ≤ q * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le m) hq0
    _ = 2 * Real.exp (-(y / 2)) := by simp [q, mul_comm]

/-- The dependent finite index type for all pairs `(i,x)` with
`1 ≤ x ≤ cutoff i`.  The `Fin` coordinate stores `x-1`. -/
abbrev PRSBadIndex (L : ℕ) (cutoff : Fin L → ℕ) :=
  Σ i : Fin L, Fin (cutoff i)

/-- A simultaneous finite union bound for every scale and positive set size. -/
theorem exists_mem_avoiding_prs_events_of_exp_bound
    {Ω : Type*} {L : ℕ} (space : Finset Ω) (cutoff : Fin L → ℕ)
    (bad : (i : Fin L) → Fin (cutoff i) → Finset Ω) (y : ℝ)
    (hspace : space.Nonempty)
    (_hsub : ∀ i x, bad i x ⊆ space)
    (hhalf : Real.exp (-(y / 2)) ≤ (1 / 2 : ℝ))
    (hbound : ∀ i x,
      ((bad i x).card : ℝ) / space.card ≤
        Real.exp (-((((x : ℕ) + 1 : ℕ) : ℝ) * y / 2)))
    (herror : 2 * (L : ℝ) * Real.exp (-(y / 2)) < 1) :
    ∃ ω ∈ space, ∀ i x, ω ∉ bad i x := by
  classical
  let event : PRSBadIndex L cutoff → Finset Ω := fun e ↦ bad e.1 e.2
  have hsum :
      (∑ e : PRSBadIndex L cutoff,
          ((event e).card : ℝ) / space.card) < 1 := by
    calc
      (∑ e : PRSBadIndex L cutoff,
          ((event e).card : ℝ) / space.card) =
          ∑ i : Fin L, ∑ x : Fin (cutoff i),
            ((bad i x).card : ℝ) / space.card := by
              rw [Fintype.sum_sigma]
      _ ≤ ∑ _i : Fin L, 2 * Real.exp (-(y / 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          (∑ x : Fin (cutoff i),
              ((bad i x).card : ℝ) / space.card) ≤
              ∑ x : Fin (cutoff i),
                Real.exp (-((((x : ℕ) + 1 : ℕ) : ℝ) * y / 2)) := by
            apply Finset.sum_le_sum
            intro x hx
            exact hbound i x
          _ = ∑ x ∈ Finset.range (cutoff i),
                Real.exp (-(((x + 1 : ℕ) : ℝ) * y / 2)) := by
            change (∑ x : Fin (cutoff i),
              (fun z : ℕ ↦ Real.exp (-(((z + 1 : ℕ) : ℝ) * y / 2))) x) = _
            exact Fin.sum_univ_eq_sum_range
              (fun z : ℕ ↦ Real.exp (-(((z + 1 : ℕ) : ℝ) * y / 2)))
              (cutoff i)
          _ ≤ 2 * Real.exp (-(y / 2)) :=
            sum_exp_neg_succ_mul_half_le (cutoff i) y hhalf
      _ = 2 * (L : ℝ) * Real.exp (-(y / 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      _ < 1 := herror
  obtain ⟨ω, hωspace, hω⟩ :=
    exists_mem_avoiding_of_sum_card_div_lt_one
      space event hspace hsum
  exact ⟨ω, hωspace, fun i x ↦ hω ⟨i, x⟩⟩

/-- Division-free version of the simultaneous union bound.  This is the form
produced directly by the fixed-event cardinal counts. -/
theorem exists_mem_avoiding_prs_events_of_mul_bounds
    {Ω : Type*} {L : ℕ} (space : Finset Ω) (cutoff : Fin L → ℕ)
    (bad : (i : Fin L) → Fin (cutoff i) → Finset Ω)
    (numer denom : (i : Fin L) → Fin (cutoff i) → ℕ) (y : ℝ)
    (hspace : space.Nonempty)
    (hsub : ∀ i x, bad i x ⊆ space)
    (hdenom : ∀ i x, 0 < denom i x)
    (hcount : ∀ i x,
      (bad i x).card * denom i x ≤ numer i x * space.card)
    (hcoeff : ∀ i x,
      (numer i x : ℝ) / denom i x ≤
        Real.exp (-((((x : ℕ) + 1 : ℕ) : ℝ) * y / 2)))
    (hhalf : Real.exp (-(y / 2)) ≤ (1 / 2 : ℝ))
    (herror : 2 * (L : ℝ) * Real.exp (-(y / 2)) < 1) :
    ∃ ω ∈ space, ∀ i x, ω ∉ bad i x := by
  apply exists_mem_avoiding_prs_events_of_exp_bound
    space cutoff bad y hspace hsub hhalf
  · intro i x
    calc
      ((bad i x).card : ℝ) / space.card ≤
          (numer i x : ℝ) / denom i x := by
        have hs : (0 : ℝ) < space.card := by
          exact_mod_cast Finset.card_pos.mpr hspace
        have hd : (0 : ℝ) < denom i x := by
          exact_mod_cast hdenom i x
        rw [div_le_div_iff₀ hs hd]
        exact_mod_cast hcount i x
      _ ≤ Real.exp (-((((x : ℕ) + 1 : ℕ) : ℝ) * y / 2)) :=
        hcoeff i x
  · exact herror

/-! ## Coordinate-demand specialization -/

/-- The union of all prescribed-edge witnesses attached to the `x`-element
candidate vertex sets. -/
def prsDemandUnion
    {U C V : Type*} [Fintype U] [Fintype C]
    (allowed : C → Finset V) (x : ℕ)
    (family : Finset U → Finset (CoordinateDemand C V)) :
    Finset (FiniteChoiceOutcome C V) :=
  ((Finset.univ : Finset U).powersetCard x).biUnion fun S ↦
    (family S).biUnion (CoordinateDemand.outcomes allowed)

/-- The complete coordinate-counting and all-scales union bound.  At index
`(i,z)`, the actual candidate-set size is `z+1`; `edgeCount (z+1)` prescribed
edges witness the bad event. -/
theorem exists_choice_avoiding_all_prs_demands
    {U C V : Type*} [Fintype U] [Fintype C]
    {L : ℕ} (allowed : C → Finset V) (cutoff : Fin L → ℕ)
    (family : (i : Fin L) → Fin (cutoff i) →
      Finset U → Finset (CoordinateDemand C V))
    (edgeCount : ℕ → ℕ) (b : Fin L → ℕ) (y : ℝ)
    (hspace : (finiteChoiceSpace allowed).Nonempty)
    (hb : ∀ i, 0 < b i)
    (hfamily : ∀ (i : Fin L) (z : Fin (cutoff i)) S,
      S ∈ (Finset.univ : Finset U).powersetCard ((z : ℕ) + 1) →
      (family i z S).card ≤
        (((z : ℕ) + 1).choose 2).choose (edgeCount ((z : ℕ) + 1)))
    (hcard : ∀ (i : Fin L) (z : Fin (cutoff i)) S,
      S ∈ (Finset.univ : Finset U).powersetCard ((z : ℕ) + 1) →
      ∀ d ∈ family i z S,
        d.coords.card = edgeCount ((z : ℕ) + 1))
    (hlower : ∀ (i : Fin L) (z : Fin (cutoff i)) S,
      S ∈ (Finset.univ : Finset U).powersetCard ((z : ℕ) + 1) →
      ∀ d ∈ family i z S, ∀ c ∈ d.coords,
        b i ≤ (allowed c).card)
    (hcoeff : ∀ (i : Fin L) (z : Fin (cutoff i)),
      (((Fintype.card U).choose ((z : ℕ) + 1) *
          ((((z : ℕ) + 1).choose 2).choose
            (edgeCount ((z : ℕ) + 1))) : ℕ) : ℝ) /
          ((b i) ^ edgeCount ((z : ℕ) + 1) : ℕ) ≤
        Real.exp (-(((((z : ℕ) + 1 : ℕ) : ℝ)) * y / 2)))
    (hhalf : Real.exp (-(y / 2)) ≤ (1 / 2 : ℝ))
    (herror : 2 * (L : ℝ) * Real.exp (-(y / 2)) < 1) :
    ∃ ω ∈ finiteChoiceSpace allowed,
      ∀ (i : Fin L) (z : Fin (cutoff i)),
        ω ∉ prsDemandUnion allowed ((z : ℕ) + 1) (family i z) := by
  classical
  let space := finiteChoiceSpace allowed
  let bad : (i : Fin L) → Fin (cutoff i) →
      Finset (FiniteChoiceOutcome C V) := fun i z ↦
        space ∩ prsDemandUnion allowed ((z : ℕ) + 1) (family i z)
  let numer : (i : Fin L) → Fin (cutoff i) → ℕ := fun _i z ↦
    (Fintype.card U).choose ((z : ℕ) + 1) *
      (((z : ℕ) + 1).choose 2).choose (edgeCount ((z : ℕ) + 1))
  let denom : (i : Fin L) → Fin (cutoff i) → ℕ := fun i z ↦
    (b i) ^ edgeCount ((z : ℕ) + 1)
  obtain ⟨ω, hωspace, hω⟩ :=
    exists_mem_avoiding_prs_events_of_mul_bounds
      space cutoff bad numer denom y hspace
      (fun _i _z ↦ Finset.inter_subset_left)
      (fun i _z ↦ pow_pos (hb i) _) (by
        intro i z
        calc
          (bad i z).card * denom i z ≤
              (prsDemandUnion allowed ((z : ℕ) + 1) (family i z)).card *
                denom i z :=
            Nat.mul_le_mul_right _ (Finset.card_le_card Finset.inter_subset_right)
          _ ≤ numer i z * space.card := by
            simpa only [prsDemandUnion, denom, numer, space] using
              card_bad_candidate_sets_mul_pow_le
                allowed ((z : ℕ) + 1) (edgeCount ((z : ℕ) + 1)) (b i)
                  (family i z) (hfamily i z) (hcard i z) (hlower i z))
      hcoeff hhalf herror
  refine ⟨ω, hωspace, ?_⟩
  intro i z hωbad
  exact hω i z (Finset.mem_inter.mpr ⟨hωspace, hωbad⟩)

/-! ## The shifted PRS layers -/

/-- At union-bound index `j`, candidate sets may have sizes from one through
`1000 * b_(j+1)`.  The denominator in the prescribed-edge estimate is the
preceding layer size `b_j`. -/
def prsBadCutoff (n : ℕ) (j : Fin (prsLayerCount n - 1)) : ℕ :=
  1000 * prsLayerSize n ((j : ℕ) + 1)

/-- Concrete shifted-layer adapter.  It turns the exact one-event estimate
for original scale `i=j+1` into one admissible coordinate choice avoiding
all scales and all positive sizes simultaneously. -/
theorem exists_choice_avoiding_shifted_prs_demands
    {U C V : Type*} [Fintype U] [Fintype C]
    (n : ℕ) (allowed : C → Finset V)
    (family : (j : Fin (prsLayerCount n - 1)) → Fin (prsBadCutoff n j) →
      Finset U → Finset (CoordinateDemand C V))
    (hU : Fintype.card U ≤ n)
    (hcount : 2 ≤ prsLayerCount n)
    (hlayer : ∀ i < prsLayerCount n, 0 < prsLayerSize n i)
    (hspace : (finiteChoiceSpace allowed).Nonempty)
    (hfamily : ∀ (j : Fin (prsLayerCount n - 1))
        (z : Fin (prsBadCutoff n j)) S,
      S ∈ (Finset.univ : Finset U).powersetCard ((z : ℕ) + 1) →
      (family j z S).card ≤
        (((z : ℕ) + 1).choose 2).choose (prsBadEdgeCount ((z : ℕ) + 1)))
    (hdemandCard : ∀ (j : Fin (prsLayerCount n - 1))
        (z : Fin (prsBadCutoff n j)) S,
      S ∈ (Finset.univ : Finset U).powersetCard ((z : ℕ) + 1) →
      ∀ d ∈ family j z S,
        d.coords.card = prsBadEdgeCount ((z : ℕ) + 1))
    (htarget : ∀ (j : Fin (prsLayerCount n - 1))
        (z : Fin (prsBadCutoff n j)) S,
      S ∈ (Finset.univ : Finset U).powersetCard ((z : ℕ) + 1) →
      ∀ d ∈ family j z S, ∀ c ∈ d.coords,
        prsLayerSize n (j : ℕ) ≤ (allowed c).card)
    (honeEvent : ∀ i, 1 ≤ i → i < prsLayerCount n →
      ∀ x, 1 ≤ x → x ≤ 1000 * prsLayerSize n i →
        (n.choose x : ℝ) *
            ((x.choose 2).choose (prsBadEdgeCount x) : ℝ) /
              (prsLayerSize n (i - 1) : ℝ) ^ prsBadEdgeCount x ≤
          Real.exp (-(x : ℝ) * prsY n / 2))
    (hhalf : Real.exp (-(prsY n / 2)) ≤ (1 / 2 : ℝ))
    (herror : 2 * (prsLayerCount n : ℝ) *
      Real.exp (-(prsY n / 2)) < 1) :
    ∃ ω ∈ finiteChoiceSpace allowed,
      ∀ (j : Fin (prsLayerCount n - 1)) (z : Fin (prsBadCutoff n j)),
        ω ∉ prsDemandUnion allowed ((z : ℕ) + 1) (family j z) := by
  apply exists_choice_avoiding_all_prs_demands
    (L := prsLayerCount n - 1) allowed (prsBadCutoff n) family prsBadEdgeCount
      (fun j ↦ prsLayerSize n (j : ℕ)) (prsY n) hspace
  · intro j
    apply hlayer (j : ℕ)
    omega
  · exact hfamily
  · exact hdemandCard
  · exact htarget
  · intro j z
    have hj : (j : ℕ) + 1 < prsLayerCount n := by omega
    have hz : (z : ℕ) + 1 ≤
        1000 * prsLayerSize n ((j : ℕ) + 1) := by
      exact z.isLt
    have h := honeEvent ((j : ℕ) + 1) (by omega) hj
      ((z : ℕ) + 1) (by omega) hz
    norm_num only [Nat.cast_mul, Nat.cast_pow]
    calc
      ((Fintype.card U).choose ((z : ℕ) + 1) : ℝ) *
            (((z : ℕ) + 1).choose 2).choose
              (prsBadEdgeCount ((z : ℕ) + 1)) /
            (prsLayerSize n (j : ℕ) : ℝ) ^
              prsBadEdgeCount ((z : ℕ) + 1) ≤
          (n.choose ((z : ℕ) + 1) : ℝ) *
            (((z : ℕ) + 1).choose 2).choose
              (prsBadEdgeCount ((z : ℕ) + 1)) /
            (prsLayerSize n (j : ℕ) : ℝ) ^
              prsBadEdgeCount ((z : ℕ) + 1) := by
        gcongr
      _ ≤ Real.exp (-((((z : ℕ) + 1 : ℕ) : ℝ) * prsY n / 2)) := by
        rw [show -((((z : ℕ) + 1 : ℕ) : ℝ) * prsY n / 2) =
          -(((z : ℕ) + 1 : ℕ) : ℝ) * prsY n / 2 by ring]
        simpa only [Nat.add_sub_cancel] using h
  · exact hhalf
  · calc
      2 * ((prsLayerCount n - 1 : ℕ) : ℝ) *
            Real.exp (-(prsY n / 2)) ≤
          2 * (prsLayerCount n : ℝ) * Real.exp (-(prsY n / 2)) := by
        gcongr
        exact_mod_cast Nat.sub_le (prsLayerCount n) 1
      _ < 1 := herror

end


end Erdos182
