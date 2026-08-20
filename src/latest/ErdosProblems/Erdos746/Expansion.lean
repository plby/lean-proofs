import ErdosProblems.Erdos746.Asymptotics
import ErdosProblems.Erdos746.BinomialBounds
import ErdosProblems.Erdos746.Model

/-!
# Expansion estimates and finite couplings for Erdős 746

This file contains the finite combinatorial core of the first-exposure
argument.  For a fixed set `S`, the edges from distinct outside vertices
into `S` form disjoint bundles.  `NeighborPattern α β` is the corresponding
finite sample space: a vertex of `β` is assigned the subset of `α` to which
it is joined.  We count exactly the patterns having a prescribed number of
nonempty bundles.  This is the finite counting statement underlying the
binomial law

`|N(S)| ~ Bin(|β|, 1 - (1-p)^|α|)`.

The second part packages the three size ranges of the expansion union bound
without probability-theory boilerplate.  The last part gives the exact
binomial-coefficient identity and a finite coupling/transfer lemma used to
pass from the binomial exposure to a uniform fixed-size layer.
-/

open scoped BigOperators

namespace Erdos746

section NeighborPatterns

variable (α β : Type*) [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- The edge bundles from a fixed vertex set `α` to outside vertices `β`.
For `f : NeighborPattern α β`, the set `f b` records the neighbors of `b`
inside `α`. -/
abbrev NeighborPattern := β → Finset α

/-- Outside vertices which have at least one neighbor in the fixed set. -/
def occupiedVertices [DecidableEq β] (f : NeighborPattern α β) : Finset β :=
  Finset.univ.filter fun b ↦ (f b).Nonempty

/-- Patterns with exactly `r` outside neighbors. -/
abbrev NeighborPatternOfCard (r : ℕ) :=
  {f : NeighborPattern α β // (occupiedVertices α β f).card = r}

/-- A nonempty subset of the fixed set. -/
abbrev NonemptyFinset := {s : Finset α // s.Nonempty}

@[simp]
theorem card_nonemptyFinset :
    Fintype.card (NonemptyFinset α) = 2 ^ Fintype.card α - 1 := by
  classical
  calc
    Fintype.card (NonemptyFinset α) =
        Fintype.card {s : Finset α // s ≠ ∅} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun s ↦
        Finset.nonempty_iff_ne_empty)
    _ = Fintype.card (Finset α) -
        Fintype.card {s : Finset α // s = ∅} :=
      Fintype.card_subtype_compl (fun s : Finset α ↦ s = ∅)
    _ = 2 ^ Fintype.card α - 1 := by simp

/-- A code for a neighbor pattern: first choose its `r` occupied outside
vertices, then choose a nonempty subset of `α` for each chosen vertex. -/
abbrev NeighborPatternCode (r : ℕ) :=
  Σ T : {T : Finset β // T.card = r}, (b : ↥T.1) → NonemptyFinset α

/-- Exact coding equivalence for fixed-set neighbor patterns. -/
noncomputable def neighborPatternEquivCode (r : ℕ) :
    NeighborPatternOfCard α β r ≃ NeighborPatternCode α β r where
  toFun f :=
    ⟨⟨occupiedVertices α β f.1, f.2⟩,
      fun b ↦ ⟨f.1 b.1, by
        have hb : b.1 ∈ occupiedVertices α β f.1 := b.2
        simpa [occupiedVertices] using hb⟩⟩
  invFun c :=
    ⟨fun b ↦ if hb : b ∈ c.1.1 then c.2 ⟨b, hb⟩ else ∅, by
      classical
      have hsupp : occupiedVertices α β
          (fun b ↦ if hb : b ∈ c.1.1 then c.2 ⟨b, hb⟩ else ∅) = c.1.1 := by
        ext b
        by_cases hb : b ∈ c.1.1
        · simp [occupiedVertices, hb, (c.2 ⟨b, hb⟩).2]
        · simp [occupiedVertices, hb]
      rw [hsupp, c.1.2]⟩
  left_inv f := by
    apply Subtype.ext
    funext b
    by_cases hb : b ∈ occupiedVertices α β f.1
    · simp only [hb, dite_true]
    · have hempty : f.1 b = ∅ := by
        simpa [occupiedVertices, Finset.not_nonempty_iff_eq_empty] using hb
      simp [hb, hempty]
  right_inv c := by
    let f : NeighborPattern α β :=
      fun b ↦ if hb : b ∈ c.1.1 then c.2 ⟨b, hb⟩ else ∅
    have hsupp : occupiedVertices α β f = c.1.1 := by
      ext b
      by_cases hb : b ∈ c.1.1
      · simp [f, occupiedVertices, hb, (c.2 ⟨b, hb⟩).2]
      · simp [f, occupiedVertices, hb]
    have hfirst :
        (⟨occupiedVertices α β f, by rw [hsupp, c.1.2]⟩ :
          {T : Finset β // T.card = r}) = c.1 := by
      exact Subtype.ext hsupp
    apply Sigma.ext hfirst
    apply Function.hfunext
      (congrArg (fun T : Finset β ↦ ↥T) hsupp)
    intro b b' hbb
    apply heq_of_eq
    apply Subtype.ext
    have hcoe : (b : β) = (b' : β) := by
      apply (Subtype.heq_iff_coe_eq (fun x ↦ by rw [hsupp])).mp
      exact hbb
    simp [f, hcoe, b'.2]

/-- **Fixed-set neighbor counting law.**

If the fixed set has `s` vertices and its complement has `b` vertices,
then the number of edge-bundle configurations with exactly `r` outside
neighbors is

`choose b r * (2^s - 1)^r`.

For independent edge probability `p`, replacing the cardinality of each
nonempty bundle by its total Bernoulli weight gives the usual binomial law
with success parameter `1 - (1-p)^s`. -/
theorem card_neighborPatternOfCard (r : ℕ) :
    Fintype.card (NeighborPatternOfCard α β r) =
      (Fintype.card β).choose r * (2 ^ Fintype.card α - 1) ^ r := by
  classical
  rw [Fintype.card_congr (neighborPatternEquivCode α β r), Fintype.card_sigma]
  calc
    (∑ T : {T : Finset β // T.card = r},
        Fintype.card ((b : ↥T.1) → NonemptyFinset α)) =
        ∑ _T : {T : Finset β // T.card = r},
          (2 ^ Fintype.card α - 1) ^ r := by
      apply Finset.sum_congr rfl
      intro T _
      simp [card_nonemptyFinset, T.2]
    _ = Fintype.card {T : Finset β // T.card = r} *
        (2 ^ Fintype.card α - 1) ^ r := by simp
    _ = (Fintype.card β).choose r *
        (2 ^ Fintype.card α - 1) ^ r := by rw [Fintype.card_finset_len]

/-- The `r = 0` case: there is exactly one pattern with no outside
neighbor, namely the all-empty pattern. -/
@[simp]
theorem card_neighborPatternOfCard_zero :
    Fintype.card (NeighborPatternOfCard α β 0) = 1 := by
  simp [card_neighborPatternOfCard]

/-! ### Weighted form: the exact binomial bundle law -/

/-- Bernoulli weight of one edge bundle. -/
def edgeBundleWeight (p : ℝ) (s : Finset α) : ℝ :=
  p ^ s.card * (1 - p) ^ (Fintype.card α - s.card)

theorem edgeBundleWeight_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (s : Finset α) : 0 ≤ edgeBundleWeight α p s := by
  unfold edgeBundleWeight
  positivity

/-- Total Bernoulli weight of all nonempty bundles. -/
def occupiedBundleWeight (p : ℝ) : ℝ :=
  ∑ s : NonemptyFinset α, edgeBundleWeight α p s.1

/-- The Bernoulli weights of all subsets of a finite type sum to one. -/
theorem sum_edgeBundleWeight (p : ℝ) :
    (∑ s : Finset α, edgeBundleWeight α p s) = 1 := by
  classical
  change (∑ s : Finset α,
    p ^ s.card * (1 - p) ^ (Fintype.card α - s.card)) = 1
  rw [show (Finset.univ : Finset (Finset α)) =
      (Finset.univ : Finset α).powerset by simp]
  change (∑ s ∈ (Finset.univ : Finset α).powerset,
    p ^ s.card * (1 - p) ^ ((Finset.univ : Finset α).card - s.card)) = 1
  calc
    (∑ s ∈ (Finset.univ : Finset α).powerset,
        p ^ s.card * (1 - p) ^ ((Finset.univ : Finset α).card - s.card)) =
      ∑ k ∈ Finset.range ((Finset.univ : Finset α).card + 1),
        ((Finset.univ : Finset α).card).choose k •
          (p ^ k * (1 - p) ^ ((Finset.univ : Finset α).card - k)) :=
      Finset.sum_powerset_apply_card
        (fun k ↦ p ^ k *
          (1 - p) ^ ((Finset.univ : Finset α).card - k))
    _ = ∑ k ∈ Finset.range ((Finset.univ : Finset α).card + 1),
        p ^ k * (1 - p) ^ ((Finset.univ : Finset α).card - k) *
          (((Finset.univ : Finset α).card).choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [nsmul_eq_mul]
      ring
    _ = (p + (1 - p)) ^ (Finset.univ : Finset α).card :=
      (add_pow p (1 - p) (Finset.univ : Finset α).card).symm
    _ = 1 := by ring

/-- Consequently a bundle is nonempty with total weight
`1 - (1-p)^|α|`. -/
theorem occupiedBundleWeight_eq (p : ℝ) :
    occupiedBundleWeight α p = 1 - (1 - p) ^ Fintype.card α := by
  classical
  let e : {s : Finset α // s ≠ ∅} ≃ NonemptyFinset α :=
    Equiv.subtypeEquivRight fun s ↦ Finset.nonempty_iff_ne_empty.symm
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne
    (edgeBundleWeight α p) (∅ : Finset α)
  have hnonempty :
      (∑ s : {s : Finset α // s ≠ ∅}, edgeBundleWeight α p s.1) =
        occupiedBundleWeight α p := by
    exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
  rw [sum_edgeBundleWeight α p, hnonempty] at hsplit
  simp only [edgeBundleWeight, Finset.card_empty, pow_zero, one_mul,
    Nat.sub_zero] at hsplit
  linarith

/-- Weight of a code with `r` occupied outside vertices. -/
def neighborPatternCodeWeight (p : ℝ) (r : ℕ)
    (c : NeighborPatternCode α β r) : ℝ :=
  ((1 - p) ^ Fintype.card α) ^ (Fintype.card β - r) *
    ∏ b, edgeBundleWeight α p (c.2 b).1

theorem neighborPatternCodeWeight_nonneg {p : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (r : ℕ) (c : NeighborPatternCode α β r) :
    0 ≤ neighborPatternCodeWeight α β p r c := by
  unfold neighborPatternCodeWeight
  apply mul_nonneg
  · exact pow_nonneg (pow_nonneg (sub_nonneg.mpr hp₁) _) _
  · exact Finset.prod_nonneg fun b _ ↦
      edgeBundleWeight_nonneg α hp₀ hp₁ (c.2 b).1

/-- **Exact weighted fixed-set neighbor law.**  The total weight of the
codes with `r` occupied outside vertices is the `r`th binomial mass with
success parameter `1 - (1-p)^|α|`. -/
theorem sum_neighborPatternCodeWeight (p : ℝ) (r : ℕ) :
    (∑ c : NeighborPatternCode α β r,
        neighborPatternCodeWeight α β p r c) =
      ((Fintype.card β).choose r : ℝ) *
        (1 - (1 - p) ^ Fintype.card α) ^ r *
        ((1 - p) ^ Fintype.card α) ^ (Fintype.card β - r) := by
  classical
  rw [Fintype.sum_sigma]
  simp only [neighborPatternCodeWeight]
  calc
    (∑ T : {T : Finset β // T.card = r},
        ∑ g : (b : ↥T.1) → NonemptyFinset α,
          ((1 - p) ^ Fintype.card α) ^ (Fintype.card β - r) *
            ∏ b, edgeBundleWeight α p (g b).1) =
      ∑ T : {T : Finset β // T.card = r},
        ((1 - p) ^ Fintype.card α) ^ (Fintype.card β - r) *
          occupiedBundleWeight α p ^ r := by
      apply Finset.sum_congr rfl
      intro T _
      rw [← Finset.mul_sum]
      congr 1
      rw [← Fintype.prod_sum
        (fun (_b : ↥T.1) (s : NonemptyFinset α) ↦ edgeBundleWeight α p s.1)]
      simp only [occupiedBundleWeight]
      simp [T.2]
    _ = ((Fintype.card β).choose r : ℝ) *
        ((1 - p) ^ Fintype.card α) ^ (Fintype.card β - r) *
          occupiedBundleWeight α p ^ r := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_finset_len]
      ring
    _ = ((Fintype.card β).choose r : ℝ) *
        (1 - (1 - p) ^ Fintype.card α) ^ r *
        ((1 - p) ^ Fintype.card α) ^ (Fintype.card β - r) := by
      rw [occupiedBundleWeight_eq]
      ring

/-- The preceding formula, exposed directly as Mathlib-style binomial
mass.  This is the adapter used by the three-range lower-tail estimates. -/
theorem sum_neighborPatternCodeWeight_eq_binomialTerm (p : ℝ) (r : ℕ) :
    (∑ c : NeighborPatternCode α β r,
        neighborPatternCodeWeight α β p r c) =
      binomialTerm (Fintype.card β)
        (1 - (1 - p) ^ Fintype.card α) r := by
  rw [sum_neighborPatternCodeWeight]
  unfold binomialTerm
  ring

/-- Bernoulli mass on an actual fixed-cardinality neighbor pattern, obtained
by transporting the explicit code weight through `neighborPatternEquivCode`.
This formulation is convenient when a graph exposure has already produced a
function `β → Finset α` rather than its support-and-values code. -/
noncomputable def neighborPatternFiberWeight (p : ℝ) (r : ℕ)
    (f : NeighborPatternOfCard α β r) : ℝ :=
  neighborPatternCodeWeight α β p r (neighborPatternEquivCode α β r f)

theorem neighborPatternFiberWeight_nonneg {p : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (r : ℕ) (f : NeighborPatternOfCard α β r) :
    0 ≤ neighborPatternFiberWeight α β p r f :=
  neighborPatternCodeWeight_nonneg α β hp₀ hp₁ r
    (neighborPatternEquivCode α β r f)

/-- The exact binomial law indexed by genuine neighbor patterns. -/
theorem sum_neighborPatternFiberWeight_eq_binomialTerm (p : ℝ) (r : ℕ) :
    (∑ f : NeighborPatternOfCard α β r,
        neighborPatternFiberWeight α β p r f) =
      binomialTerm (Fintype.card β)
        (1 - (1 - p) ^ Fintype.card α) r := by
  classical
  calc
    (∑ f : NeighborPatternOfCard α β r,
        neighborPatternFiberWeight α β p r f) =
        ∑ c : NeighborPatternCode α β r,
          neighborPatternCodeWeight α β p r c := by
            exact Fintype.sum_equiv (neighborPatternEquivCode α β r)
              _ _ (fun _ ↦ rfl)
    _ = binomialTerm (Fintype.card β)
        (1 - (1 - p) ^ Fintype.card α) r :=
      sum_neighborPatternCodeWeight_eq_binomialTerm α β p r

/-- Summing the exact fiber law over all neighborhood sizes below `K`
gives the corresponding binomial lower tail. -/
theorem sum_neighborPatternFiberWeight_lt_eq_binomialLowerTail
    (p : ℝ) (K : ℕ) :
    (∑ r ∈ Finset.range K,
        ∑ f : NeighborPatternOfCard α β r,
          neighborPatternFiberWeight α β p r f) =
      binomialLowerTail (Fintype.card β) K
        (1 - (1 - p) ^ Fintype.card α) := by
  classical
  unfold binomialLowerTail
  apply Finset.sum_congr rfl
  intro r _
  exact sum_neighborPatternFiberWeight_eq_binomialTerm α β p r

end NeighborPatterns

section ThreeRanges

variable {Ω : Type*}

/-- The finite mass of an event.  This elementary definition is convenient
for finite random graph models and does not require selecting a particular
normalization. -/
def finiteEventMass (sample : Finset Ω) (weight : Ω → ℝ)
    (event : Ω → Prop) [DecidablePred event] : ℝ :=
  ∑ ω ∈ sample with event ω, weight ω

theorem finiteEventMass_nonneg (sample : Finset Ω) (weight : Ω → ℝ)
    (event : Ω → Prop) [DecidablePred event]
    (hweight : ∀ ω ∈ sample, 0 ≤ weight ω) :
    0 ≤ finiteEventMass sample weight event := by
  exact Finset.sum_nonneg fun ω hω ↦ hweight ω (Finset.mem_filter.mp hω).1

theorem finiteEventMass_mono (sample : Finset Ω) (weight : Ω → ℝ)
    (A B : Ω → Prop) [DecidablePred A] [DecidablePred B]
    (hweight : ∀ ω ∈ sample, 0 ≤ weight ω)
    (hAB : ∀ ω ∈ sample, A ω → B ω) :
    finiteEventMass sample weight A ≤ finiteEventMass sample weight B := by
  unfold finiteEventMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, hAB ω hω.1 hω.2⟩
  · intro ω hω _
    exact hweight ω (Finset.mem_filter.mp hω).1

/-- The three exhaustive size ranges used in the first-exposure expansion
argument.  The endpoints deliberately overlap; this makes applications
robust under floor and ceiling choices. -/
inductive ExpansionRange (smallCut mediumCut size : ℕ) : Prop
  | small (h : size ≤ smallCut)
  | medium (h₁ : smallCut ≤ size) (h₂ : size ≤ mediumCut)
  | large (h : mediumCut ≤ size)

theorem expansionRange_total {smallCut mediumCut size : ℕ}
    (hcuts : smallCut ≤ mediumCut) :
    ExpansionRange smallCut mediumCut size := by
  by_cases hs : size ≤ smallCut
  · exact .small hs
  by_cases hm : size ≤ mediumCut
  · exact .medium (Nat.le_of_lt (Nat.lt_of_not_ge hs)) hm
  · exact .large (Nat.le_of_lt (Nat.lt_of_not_ge hm))

/-- The piecewise pointwise bound used for the three size ranges. -/
def threeRangeBound (index : Ω → ℕ) (smallCut mediumCut : ℕ)
    (smallBound mediumBound largeBound : ℕ → ℝ) (ω : Ω) : ℝ :=
  if index ω ≤ smallCut then smallBound (index ω)
  else if index ω ≤ mediumCut then mediumBound (index ω)
  else largeBound (index ω)

/-- Finite union bound, split into the three size ranges.  `index` is the
size of the bad witness (in the graph application, `|S|`).  This is the
finite summation step behind equations (5), (6), and (9) of the writeup. -/
theorem threeRange_union_bound
    (witnesses : Finset Ω) (weight : Ω → ℝ) (index : Ω → ℕ)
    (smallCut mediumCut : ℕ) (smallBound mediumBound largeBound : ℕ → ℝ)
    (hweight : ∀ ω ∈ witnesses, 0 ≤ weight ω)
    (hsmall : ∀ ω ∈ witnesses, index ω ≤ smallCut →
      weight ω ≤ smallBound (index ω))
    (hmedium : ∀ ω ∈ witnesses, smallCut < index ω →
      index ω ≤ mediumCut → weight ω ≤ mediumBound (index ω))
    (hlarge : ∀ ω ∈ witnesses, mediumCut < index ω →
      weight ω ≤ largeBound (index ω)) :
    (∑ ω ∈ witnesses, weight ω) ≤
      ∑ ω ∈ witnesses,
        threeRangeBound index smallCut mediumCut
          smallBound mediumBound largeBound ω := by
  classical
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hs : index ω ≤ smallCut
  · simpa [threeRangeBound, hs] using hsmall ω hω hs
  · have hs' : smallCut < index ω := Nat.lt_of_not_ge hs
    by_cases hm : index ω ≤ mediumCut
    · simpa [threeRangeBound, hs, hm] using hmedium ω hω hs' hm
    · have hm' : mediumCut < index ω := Nat.lt_of_not_ge hm
      simpa [threeRangeBound, hs, hm] using hlarge ω hω hm'

end ThreeRanges

section Coupling

/-- The elementary weighted union bound on a finite sample space. -/
theorem sum_filter_or_le_add {Ω : Type*} (sample : Finset Ω)
    (weight : Ω → ℝ) (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q]
    (hweight : ∀ ω ∈ sample, 0 ≤ weight ω) :
    (∑ ω ∈ sample with P ω ∨ Q ω, weight ω) ≤
      (∑ ω ∈ sample with P ω, weight ω) +
      ∑ ω ∈ sample with Q ω, weight ω := by
  classical
  let A := sample.filter P
  let B := sample.filter Q
  have hor : sample.filter (fun ω ↦ P ω ∨ Q ω) = A ∪ B := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_union]
    aesop
  change (∑ ω ∈ sample with P ω ∨ Q ω, weight ω) ≤
    (∑ ω ∈ A, weight ω) + ∑ ω ∈ B, weight ω
  rw [hor, show A ∪ B = A ∪ (B \ A) by ext; simp]
  rw [Finset.sum_union Finset.disjoint_sdiff]
  apply add_le_add_right
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
  intro ω hω _
  exact hweight ω (by
    have := (Finset.mem_filter.mp hω).1
    exact this)

/-- The binomial-coefficient identity behind uniform completion: choosing
an `m`-set and then a `j`-subset is the same as choosing the `j`-set and
then its `m-j` new elements. -/
theorem choose_completion_identity {N j m : ℕ} (hjm : j ≤ m) :
    N.choose m * m.choose j = N.choose j * (N - j).choose (m - j) :=
  Nat.choose_mul hjm

/-- A finite weighted form of the coupling inequality

`P(H ∉ A) ≤ P(X ∉ A) + P(K > m₀)`.

The sample point `ω` contains both coupled objects.  On `¬exceptional ω`,
the relation `R (X ω) (H ω)` holds; an increasing property transfers along
`R`.  No independence or choice of probability library is hidden here. -/
theorem finite_coupling_failure_bound
    {Ω X Y : Type*} (sample : Finset Ω) (weight : Ω → ℝ)
    (left : Ω → X) (right : Ω → Y) (R : X → Y → Prop)
    (propertyX : X → Prop) (propertyY : Y → Prop)
    (exceptional : Ω → Prop)
    [DecidablePred propertyX] [DecidablePred propertyY]
    [DecidablePred exceptional]
    (hweight : ∀ ω ∈ sample, 0 ≤ weight ω)
    (hrelation : ∀ ω ∈ sample, ¬ exceptional ω → R (left ω) (right ω))
    (hincreasing : ∀ x y, R x y → propertyX x → propertyY y) :
    finiteEventMass sample weight (fun ω ↦ ¬ propertyY (right ω)) ≤
      finiteEventMass sample weight (fun ω ↦ ¬ propertyX (left ω)) +
      finiteEventMass sample weight exceptional := by
  classical
  unfold finiteEventMass
  calc
    (∑ ω ∈ sample with ¬propertyY (right ω), weight ω) ≤
        ∑ ω ∈ sample with
          (¬propertyX (left ω)) ∨ exceptional ω, weight ω := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro ω hω
              simp only [Finset.mem_filter] at hω ⊢
              refine ⟨hω.1, ?_⟩
              by_cases he : exceptional ω
              · exact Or.inr he
              · exact Or.inl fun hp ↦ hω.2
                  (hincreasing _ _ (hrelation ω hω.1 he) hp)
            · intro ω hω _
              exact hweight ω (Finset.mem_filter.mp hω).1
    _ ≤ (∑ ω ∈ sample with ¬propertyX (left ω), weight ω) +
        ∑ ω ∈ sample with exceptional ω, weight ω := by
          exact sum_filter_or_le_add sample weight
            (fun ω ↦ ¬propertyX (left ω)) exceptional hweight

end Coupling

end Erdos746
