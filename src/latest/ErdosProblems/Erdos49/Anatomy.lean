import ErdosProblems.Erdos49.SecondaryGlobal
import ErdosProblems.Erdos49.RankinBounds

/-!
# Prime-factor anatomy for Erdős Problem 49

This file gives the finite decomposition behind Tao's argument.  We split the
prime-factor list (with multiplicity) at `L`.  Away from six explicitly
defined exceptional conditions, the large factors either give a primary
representation or a secondary representation.
-/

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Prime factors at most `L`, retained with multiplicity. -/
def smallFactors (L n : ℕ) : List ℕ :=
  n.primeFactorsList.filter (· ≤ L)

/-- Prime factors larger than `L`, retained with multiplicity. -/
def largeFactors (L n : ℕ) : List ℕ :=
  n.primeFactorsList.filter (L < ·)

/-- The product of all prime factors at most `L`. -/
def smallPart (L n : ℕ) : ℕ := (smallFactors L n).prod

lemma factors_product {L n : ℕ} (hn : n ≠ 0) :
    smallPart L n * (largeFactors L n).prod = n := by
  calc
    smallPart L n * (largeFactors L n).prod = n.primeFactorsList.prod := by
      simpa [smallPart, smallFactors, largeFactors, Nat.not_le] using
        (List.prod_map_filter_mul_prod_map_filter_not
          (p := fun q : ℕ ↦ q ≤ L) (f := id) n.primeFactorsList)
    _ = n := Nat.prod_primeFactorsList hn

lemma prime_of_mem_smallFactors {L n q : ℕ} (hq : q ∈ smallFactors L n) :
    q.Prime := by
  exact Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)

lemma le_of_mem_smallFactors {L n q : ℕ} (hq : q ∈ smallFactors L n) :
    q ≤ L := of_decide_eq_true (List.mem_filter.mp hq).2

lemma prime_of_mem_largeFactors {L n q : ℕ} (hq : q ∈ largeFactors L n) :
    q.Prime := by
  exact Nat.prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)

lemma lt_of_mem_largeFactors {L n q : ℕ} (hq : q ∈ largeFactors L n) :
    L < q := of_decide_eq_true (List.mem_filter.mp hq).2

lemma smallFactors_prime (L n : ℕ) :
    ∀ q ∈ smallFactors L n, q.Prime := fun _ hq ↦ prime_of_mem_smallFactors hq

lemma largeFactors_prime (L n : ℕ) :
    ∀ q ∈ largeFactors L n, q.Prime := fun _ hq ↦ prime_of_mem_largeFactors hq

lemma smallPart_pos (L n : ℕ) : 0 < smallPart L n := by
  unfold smallPart
  exact List.prod_pos fun q hq ↦ (prime_of_mem_smallFactors hq).pos

lemma smallPart_smooth (L n : ℕ) : Smooth L (smallPart L n) := by
  rw [smooth_iff_prime_divisors]
  refine ⟨(smallPart_pos L n).ne', ?_⟩
  intro p hp hpdvd
  rw [smallPart, hp.prime.dvd_prod_iff] at hpdvd
  obtain ⟨q, hq, hpq⟩ := hpdvd
  have hqprime := prime_of_mem_smallFactors hq
  have hp_eq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime).mp hpq
  simpa [hp_eq] using le_of_mem_smallFactors hq

lemma largeFactors_sortedLE (L n : ℕ) : (largeFactors L n).SortedLE := by
  exact (List.Pairwise.sublist List.filter_sublist
    (Nat.primeFactorsList_sorted n).pairwise).sortedLE

/-- Failure of the large-square exceptional condition makes the retained
large factor list strictly increasing. -/
lemma largeFactors_sortedLT {L n : ℕ} (hnodup : (largeFactors L n).Nodup) :
    (largeFactors L n).SortedLT :=
  (largeFactors_sortedLE L n).sortedLT_of_nodup hnodup

lemma list_prod_coprime_prime {l : List ℕ} {p : ℕ}
    (hl : ∀ q ∈ l, q.Prime) (hp : p.Prime) (hnot : p ∉ l) :
    l.prod.Coprime p := by
  rw [Nat.coprime_list_prod_left_iff]
  intro q hq
  exact (Nat.coprime_primes (hl q hq) hp).2 fun hqp ↦ hnot (hqp ▸ hq)

lemma le_head_of_sortedGT {p q : ℕ} {l : List ℕ}
    (hs : (p :: l).SortedGT) (hq : q ∈ p :: l) : q ≤ p := by
  rcases List.mem_cons.mp hq with rfl | hq
  · exact le_rfl
  · exact ((List.pairwise_cons.mp hs.pairwise).1 q hq).le

/-- A short list of large prime cofactors supplies all of the arithmetic
side conditions in `SecondaryRep`. -/
lemma secondaryRep_of_list
    {N L n d p : ℕ} {qs : List ℕ}
    (hd : 0 < d) (hp : p.Prime) (hLp : L < p)
    (hqsPrime : ∀ q ∈ qs, q.Prime)
    (hqsLarge : ∀ q ∈ qs, p * L < q)
    (hqsNonempty : qs ≠ [])
    (hdp : d.Coprime p)
    (hcop : ∀ q ∈ qs, (d * p).Coprime q)
    (hlen : qs.length ≤ 2)
    (hnfac : n = d * p * qs.prod) (hnN : n ≤ N) :
    SecondaryRep N L n d p qs.prod := by
  have hqsPos : 0 < qs.prod :=
    List.prod_pos fun q hq ↦ (hqsPrime q hq).pos
  have hdps : (d * p).Coprime qs.prod := by
    rw [Nat.coprime_list_prod_right_iff]
    exact hcop
  have hpfSub : qs.prod.primeFactors ⊆ qs.toFinset := by
    intro q hq
    have hqPrime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ qs.prod := Nat.dvd_of_mem_primeFactors hq
    rw [hqPrime.prime.dvd_prod_iff] at hqdvd
    obtain ⟨r, hr, hqr⟩ := hqdvd
    have hrPrime := hqsPrime r hr
    have : q = r := (Nat.prime_dvd_prime_iff_eq hqPrime hrPrime).mp hqr
    simpa [this] using hr
  have hcard : qs.prod.primeFactors.card ≤ 2 := by
    calc
      qs.prod.primeFactors.card ≤ qs.toFinset.card := Finset.card_le_card hpfSub
      _ ≤ qs.length := List.toFinset_card_le qs
      _ ≤ 2 := hlen
  have hlarge : ∀ q ∈ qs.prod.primeFactors, p * L < q := by
    intro q hq
    exact hqsLarge q (List.mem_toFinset.mp (hpfSub hq))
  exact ⟨hd, hp, hLp, hqsPos, by
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil qs hqsNonempty
    exact (hqsLarge q hq).trans_le
      (Nat.le_of_dvd hqsPos (List.dvd_prod hq)),
    hdp, hdps, hcard, hlarge, hnfac, hnN⟩

/-- Convenient ordered-list form of `secondaryRep_of_list`.  Every factor of
`df` is smaller than the distinguished prime, and every cofactor in `qs` is
larger than `pL`; these inequalities imply all required coprimalities. -/
lemma secondaryRep_of_ordered_lists
    {N L n p : ℕ} {df qs : List ℕ}
    (hL : 0 < L) (hp : p.Prime) (hLp : L < p)
    (hdfPrime : ∀ q ∈ df, q.Prime) (hdfLt : ∀ q ∈ df, q < p)
    (hqsPrime : ∀ q ∈ qs, q.Prime)
    (hqsLarge : ∀ q ∈ qs, p * L < q)
    (hqsNonempty : qs ≠ []) (hlen : qs.length ≤ 2)
    (hnfac : n = df.prod * p * qs.prod) (hnN : n ≤ N) :
    SecondaryRep N L n df.prod p qs.prod := by
  have hdfPos : 0 < df.prod :=
    List.prod_pos fun q hq ↦ (hdfPrime q hq).pos
  have hdp : df.prod.Coprime p :=
    list_prod_coprime_prime hdfPrime hp fun hpMem ↦
      (Nat.lt_irrefl p (hdfLt p hpMem))
  have hcop : ∀ q ∈ qs, (df.prod * p).Coprime q := by
    intro q hq
    have hqPrime := hqsPrime q hq
    have hpqLt : p < q :=
      (Nat.le_mul_of_pos_right p hL).trans_lt (hqsLarge q hq)
    have hdfq : df.prod.Coprime q :=
      list_prod_coprime_prime hdfPrime hqPrime fun hqMem ↦ by
        have hlt := hdfLt q hqMem
        omega
    have hpq : p.Coprime q :=
      (Nat.coprime_primes hp hqPrime).2 hpqLt.ne
    exact hdfq.mul_left hpq
  exact secondaryRep_of_list hdfPos hp hLp hqsPrime hqsLarge
    hqsNonempty hdp hcop hlen hnfac hnN

/-- The small-value exceptional piece. -/
def smallExceptional (N L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n ↦ n * L ≤ N

/-- The smooth exceptional piece. -/
def smoothExceptional (N R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (Smooth R)

/-- Repetition among the prime factors larger than `L`. -/
def squareExceptional (N L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n ↦ ¬(largeFactors L n).Nodup

/-- An overlarge `L`-smooth part. -/
def smoothTailExceptional (N L D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n ↦ D < smallPart L n

/-- Arithmetic predicate defining the two-large-prime cluster. -/
def PairCluster (L D R n : ℕ) : Prop :=
  ∃ d p₂ p₁, 0 < d ∧ d ≤ D ∧ Smooth L d ∧
    p₂.Prime ∧ p₁.Prime ∧ R < p₂ * L ∧
    p₂ ≤ p₁ ∧ p₁ ≤ p₂ * L ∧ n = d * p₂ * p₁

/-- The two-large-prime cluster. -/
def pairExceptional (N L D R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (PairCluster L D R)

/-- Arithmetic predicate defining the three-large-prime cluster. -/
def TripleCluster (L R n : ℕ) : Prop :=
  ∃ d p₃ p₂ p₁, 0 < d ∧ p₃.Prime ∧ p₂.Prime ∧ p₁.Prime ∧
    R < p₃ * L ^ 2 ∧ p₃ ≤ p₂ ∧ p₂ ≤ p₁ ∧
    p₁ ≤ p₃ * L ^ 2 ∧ n = d * p₃ * p₂ * p₁

/-- The three-large-prime cluster. -/
def tripleExceptional (N L R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (TripleCluster L R)

/-- The union of all six exceptional pieces. -/
def exceptionalSet (N L D R : ℕ) : Finset ℕ :=
  smallExceptional N L ∪ smoothExceptional N R ∪
    squareExceptional N L ∪ smoothTailExceptional N L D ∪
    pairExceptional N L D R ∪ tripleExceptional N L R

lemma exists_largeFactor_gt_of_not_smooth {L R n : ℕ}
    (hn : n ≠ 0) (hLR : L < R) (hnot : ¬Smooth R n) :
    ∃ q ∈ largeFactors L n, R < q := by
  rw [smooth_iff_prime_divisors] at hnot
  simp only [hn, ne_eq, not_false_eq_true, true_and] at hnot
  push_neg at hnot
  obtain ⟨q, hqPrime, hqDvd, hRq⟩ := hnot
  refine ⟨q, ?_, hRq⟩
  apply List.mem_filter.mpr
  constructor
  · exact (Nat.mem_primeFactorsList hn).2 ⟨hqPrime, hqDvd⟩
  · exact decide_eq_true (hLR.trans hRq)

/-- Every nonexceptional integer has either the primary or secondary
factorization used by the two packing estimates. -/
theorem regular_mem_primary_or_secondary
    {N L D R n : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hL : 0 < L)
    (hLR : L < R) (hDR : D < R) (h8DR : 8 * D ^ 2 ≤ R)
    (hnsmall : N < n * L) (hnonsmooth : ¬Smooth R n)
    (hnodup : (largeFactors L n).Nodup)
    (hsmallD : smallPart L n ≤ D)
    (hpair : ¬PairCluster L D R n)
    (htriple : ¬TripleCluster L R n) :
    n ∈ primarySet N L D ∨ n ∈ secondarySet N L := by
  have hn0 : n ≠ 0 := by
    have hn1 := (Finset.mem_Icc.mp hn).1
    omega
  obtain ⟨q₀, hq₀Large, hRq₀⟩ :=
    exists_largeFactor_gt_of_not_smooth hn0 hLR hnonsmooth
  generalize hg : (largeFactors L n).reverse = g
  have hq₀g : q₀ ∈ g := by
    rw [← hg]
    simpa using hq₀Large
  have hprodg : smallPart L n * g.prod = n := by
    rw [← hg, List.prod_reverse]
    exact factors_product hn0
  have hsortg : g.SortedGT := by
    rw [← hg]
    exact (largeFactors_sortedLT hnodup).reverse
  have hprimeg : ∀ q ∈ g, q.Prime := by
    intro q hq
    apply prime_of_mem_largeFactors
    have : q ∈ (largeFactors L n).reverse := by rwa [hg]
    simpa using this
  have hlargeg : ∀ q ∈ g, L < q := by
    intro q hq
    apply lt_of_mem_largeFactors
    have : q ∈ (largeFactors L n).reverse := by rwa [hg]
    simpa using this
  cases g with
  | nil => simp at hq₀g
  | cons p₁ t₁ =>
      have hRp₁ : R < p₁ :=
        hRq₀.trans_le (le_head_of_sortedGT hsortg hq₀g)
      have hp₁Prime : p₁.Prime := hprimeg p₁ (by simp)
      cases t₁ with
      | nil =>
          left
          apply mem_primarySet.mpr
          refine ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2,
            smallPart L n, p₁, ?_⟩
          refine ⟨smallPart_pos L n, hsmallD, smallPart_smooth L n,
            hp₁Prime, hDR.trans hRp₁, h8DR.trans hRp₁.le, ?_,
            (Finset.mem_Icc.mp hn).2⟩
          simpa using hprodg.symm
      | cons p₂ t₂ =>
          have hpw₁ := (List.pairwise_cons.mp hsortg.pairwise).1
          have hp₂p₁ : p₂ < p₁ := hpw₁ p₂ (by simp)
          have hp₂Prime : p₂.Prime := hprimeg p₂ (by simp)
          have hLp₂ : L < p₂ := hlargeg p₂ (by simp)
          cases t₂ with
          | nil =>
              by_cases hgap : p₂ * L < p₁
              · right
                apply mem_secondarySet.mpr
                refine ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2,
                  (smallFactors L n).prod, p₂, [p₁].prod, ?_⟩
                apply secondaryRep_of_ordered_lists
                    (N := N) (n := n) (p := p₂)
                    (df := smallFactors L n) (qs := [p₁])
                    hL hp₂Prime hLp₂
                · exact smallFactors_prime L n
                · intro r hr
                  exact (le_of_mem_smallFactors hr).trans_lt hLp₂
                · simp [hp₁Prime]
                · simpa using hgap
                · simp
                · simp
                · calc
                    n = smallPart L n * [p₁, p₂].prod := hprodg.symm
                    _ = (smallFactors L n).prod * p₂ * [p₁].prod := by
                      simp [smallPart]
                      ring
                · exact (Finset.mem_Icc.mp hn).2
              · exfalso
                apply hpair
                refine ⟨smallPart L n, p₂, p₁, smallPart_pos L n,
                  hsmallD, smallPart_smooth L n, hp₂Prime, hp₁Prime,
                  ?_, hp₂p₁.le, Nat.le_of_not_gt hgap, ?_⟩
                · exact hRp₁.trans_le (Nat.le_of_not_gt hgap)
                · calc
                    n = smallPart L n * [p₁, p₂].prod := hprodg.symm
                    _ = smallPart L n * p₂ * p₁ := by simp; ring
          | cons p₃ rest =>
              have hpw₂ := (List.pairwise_cons.mp
                (List.pairwise_cons.mp hsortg.pairwise).2).1
              have hpw₃ := (List.pairwise_cons.mp
                (List.pairwise_cons.mp
                  (List.pairwise_cons.mp hsortg.pairwise).2).2).1
              have hp₃p₂ : p₃ < p₂ := hpw₂ p₃ (by simp)
              have hp₃Prime : p₃.Prime := hprimeg p₃ (by simp)
              have hLp₃ : L < p₃ := hlargeg p₃ (by simp)
              have hrestPrime : ∀ r ∈ rest, r.Prime := by
                intro r hr
                exact hprimeg r (by simp [hr])
              have hrestLt : ∀ r ∈ rest, r < p₃ := hpw₃
              by_cases hgap₃₂ : p₃ * L < p₂
              · right
                apply mem_secondarySet.mpr
                let df := smallFactors L n ++ rest
                refine ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2,
                  df.prod, p₃, [p₂, p₁].prod, ?_⟩
                apply secondaryRep_of_ordered_lists
                    (N := N) (n := n) (p := p₃)
                    (df := df) (qs := [p₂, p₁])
                    hL hp₃Prime hLp₃
                · intro r hr
                  rcases List.mem_append.mp hr with hr | hr
                  · exact prime_of_mem_smallFactors hr
                  · exact hrestPrime r hr
                · intro r hr
                  rcases List.mem_append.mp hr with hr | hr
                  · exact (le_of_mem_smallFactors hr).trans_lt hLp₃
                  · exact hrestLt r hr
                · simp [hp₂Prime, hp₁Prime]
                · intro r hr
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                  rcases hr with rfl | rfl
                  · exact hgap₃₂
                  · exact hgap₃₂.trans hp₂p₁
                · simp
                · simp
                · calc
                    n = smallPart L n * (p₁ :: p₂ :: p₃ :: rest).prod :=
                      hprodg.symm
                    _ = df.prod * p₃ * [p₂, p₁].prod := by
                      dsimp only [df]
                      simp [smallPart]
                      ring
                · exact (Finset.mem_Icc.mp hn).2
              · have hp₂le : p₂ ≤ p₃ * L := Nat.le_of_not_gt hgap₃₂
                by_cases hgap₃₁ : p₃ * L ^ 2 < p₁
                · right
                  apply mem_secondarySet.mpr
                  let df := smallFactors L n ++ p₃ :: rest
                  refine ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2,
                    df.prod, p₂, [p₁].prod, ?_⟩
                  apply secondaryRep_of_ordered_lists
                      (N := N) (n := n) (p := p₂)
                      (df := df) (qs := [p₁])
                      hL hp₂Prime hLp₂
                  · intro r hr
                    rcases List.mem_append.mp hr with hr | hr
                    · exact prime_of_mem_smallFactors hr
                    · rcases List.mem_cons.mp hr with rfl | hr
                      · exact hp₃Prime
                      · exact hrestPrime r hr
                  · intro r hr
                    rcases List.mem_append.mp hr with hr | hr
                    · exact (le_of_mem_smallFactors hr).trans_lt hLp₂
                    · rcases List.mem_cons.mp hr with rfl | hr
                      · exact hp₃p₂
                      · exact (hrestLt r hr).trans hp₃p₂
                  · simp [hp₁Prime]
                  · intro r hr
                    have hp₂Lle : p₂ * L ≤ p₃ * L ^ 2 := by
                      calc
                        p₂ * L ≤ (p₃ * L) * L := Nat.mul_le_mul_right L hp₂le
                        _ = p₃ * L ^ 2 := by ring
                    simp at hr
                    subst r
                    exact hp₂Lle.trans_lt hgap₃₁
                  · simp
                  · simp
                  · calc
                      n = smallPart L n * (p₁ :: p₂ :: p₃ :: rest).prod :=
                        hprodg.symm
                      _ = df.prod * p₂ * [p₁].prod := by
                        dsimp only [df]
                        simp [smallPart]
                        ring
                  · exact (Finset.mem_Icc.mp hn).2
                · exfalso
                  apply htriple
                  refine ⟨smallPart L n * rest.prod, p₃, p₂, p₁,
                    Nat.mul_pos (smallPart_pos L n)
                      (List.prod_pos fun r hr ↦ (hrestPrime r hr).pos),
                    hp₃Prime, hp₂Prime, hp₁Prime, ?_, hp₃p₂.le,
                    hp₂p₁.le, Nat.le_of_not_gt hgap₃₁, ?_⟩
                  · exact hRp₁.trans_le (Nat.le_of_not_gt hgap₃₁)
                  · calc
                      n = smallPart L n * (p₁ :: p₂ :: p₃ :: rest).prod :=
                        hprodg.symm
                      _ = (smallPart L n * rest.prod) * p₃ * p₂ * p₁ := by
                        simp
                        ring

/-- Finite cover form of the anatomy decomposition. -/
theorem anatomy_cover
    {N L D R : ℕ} (hL : 0 < L) (hLR : L < R)
    (hDR : D < R) (h8DR : 8 * D ^ 2 ≤ R) :
    Finset.Icc 1 N ⊆
      primarySet N L D ∪ secondarySet N L ∪ exceptionalSet N L D R := by
  intro n hn
  by_cases hE : n ∈ exceptionalSet N L D R
  · simp [hE]
  have hnsmall : N < n * L := by
    by_contra h
    apply hE
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hn, Nat.le_of_not_gt h⟩
  have hnonsmooth : ¬Smooth R n := by
    intro hs
    apply hE
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hn, hs⟩
  have hnodup : (largeFactors L n).Nodup := by
    by_contra h
    apply hE
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hn, h⟩
  have hsmallD : smallPart L n ≤ D := by
    by_contra h
    apply hE
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hn, Nat.lt_of_not_ge h⟩
  have hpair : ¬PairCluster L D R n := by
    intro hp
    apply hE
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hn, hp⟩
  have htriple : ¬TripleCluster L R n := by
    intro ht
    apply hE
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hn, ht⟩
  rcases regular_mem_primary_or_secondary hn hL hLR hDR h8DR
    hnsmall hnonsmooth hnodup hsmallD hpair htriple with hp | hs
  · simp [hp]
  · simp [hs]

#print axioms anatomy_cover

end

end Erdos49
