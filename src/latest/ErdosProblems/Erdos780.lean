/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 780.
https://www.erdosproblems.com/forum/thread/780

Informal authors:
- Noga Alon
- Péter Frankl
- László Lovász

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos780.md
-/
import ErdosProblems.Erdos95.External.Tucker
import ErdosProblems.Erdos780.External.Erdos780Core
import ErdosProblems.Erdos780.External.PrimeResolution

/-!
# Erdős Problem 780

Informal authors: Noga Alon, Peter Frankl, László Lovász
Formal authors: Aristotle Contributors

If the `r`-subsets of an `n`-element set are colored with `t` colors and
`k * r + (t - 1) * (k - 1) ≤ n`, one color contains `k` pairwise disjoint
edges.

Reference: https://www.erdosproblems.com/780
-/

namespace Erdos780

abbrev Edge (n r : ℕ) := {s : Finset (Fin n) // s.card = r}

def HasMonoMatching {n r t : ℕ} (c : Edge n r → Fin t) (k : ℕ) : Prop :=
  ∃ color : Fin t, ∃ e : Fin k → Edge n r,
    (∀ i, c (e i) = color) ∧
    ∀ i j : Fin k, i ≠ j → Disjoint (e i).1 (e j).1

/-- Send an edge along an injection of finite vertex sets. -/
def Edge.map {m n r : ℕ} (f : Fin m ↪ Fin n) (e : Edge m r) : Edge n r :=
  ⟨e.1.map f, (Finset.card_map f).trans e.2⟩

@[simp] theorem Edge.coe_map {m n r : ℕ} (f : Fin m ↪ Fin n) (e : Edge m r) :
    (Edge.map f e).1 = e.1.map f := rfl

/-- Restrict a coloring on `Fin n` to the copy of `Fin m` selected by `f`. -/
def restrictColor {m n r t : ℕ} (f : Fin m ↪ Fin n) (c : Edge n r → Fin t) :
    Edge m r → Fin t := fun e ↦ c (e.map f)

/-- A matching for the restriction is a matching for the original coloring. -/
theorem HasMonoMatching.of_restrict {m n r t k : ℕ} (f : Fin m ↪ Fin n)
    (c : Edge n r → Fin t) (h : HasMonoMatching (restrictColor f c) k) :
    HasMonoMatching c k := by
  obtain ⟨color, e, hmono, hdisj⟩ := h
  refine ⟨color, fun i ↦ (e i).map f, ?_, ?_⟩
  · exact hmono
  · intro i j hij
    exact (Finset.disjoint_map f).2 (hdisj i j hij)

/-- Throw away matching edges along an injection of index sets. -/
theorem HasMonoMatching.reindex {n r t k l : ℕ} {c : Edge n r → Fin t}
    (h : HasMonoMatching c k) (f : Fin l ↪ Fin k) : HasMonoMatching c l := by
  obtain ⟨color, e, hmono, hdisj⟩ := h
  refine ⟨color, e ∘ f, fun i ↦ hmono (f i), ?_⟩
  intro i j hij
  exact hdisj (f i) (f j) (f.injective.ne hij)

theorem HasMonoMatching.mono {n r t k l : ℕ} {c : Edge n r → Fin t}
    (h : HasMonoMatching c k) (hlk : l ≤ k) : HasMonoMatching c l :=
  h.reindex (Fin.castLEEmb hlk)

/-- The first `r` vertices, regarded as an `r`-edge. -/
def initialEdge {n r : ℕ} (h : r ≤ n) : Edge n r :=
  ⟨Finset.univ.map (Fin.castLEEmb h), by simp⟩

/-- The matching-size-one boundary case. -/
theorem hasMonoMatching_one {n r t : ℕ} (c : Edge n r → Fin t) (hr : r ≤ n) :
    HasMonoMatching c 1 := by
  let e₀ := initialEdge hr
  refine ⟨c e₀, fun _ ↦ e₀, fun _ ↦ rfl, ?_⟩
  intro i j hij
  exact (hij (Subsingleton.elim i j)).elim

/-- Vertices in the `i`th block of a canonical `k`-by-`r` rectangle. -/
def blockEmbedding {n k r : ℕ} (h : k * r ≤ n) (i : Fin k) : Fin r ↪ Fin n where
  toFun j := Fin.castLE h (finProdFinEquiv (i, j))
  inj' := by
    intro a b hab
    have hab' : finProdFinEquiv (i, a) = finProdFinEquiv (i, b) :=
      (Fin.castLEEmb h).injective hab
    exact congrArg Prod.snd (finProdFinEquiv.injective hab')

def blockEdge {n k r : ℕ} (h : k * r ≤ n) (i : Fin k) : Edge n r :=
  ⟨Finset.univ.map (blockEmbedding h i), by simp⟩

theorem blockEdge_disjoint {n k r : ℕ} (h : k * r ≤ n) {i j : Fin k}
    (hij : i ≠ j) : Disjoint (blockEdge h i).1 (blockEdge h j).1 := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  simp only [blockEdge, Finset.mem_map, Finset.mem_univ, true_and] at hxi hxj
  obtain ⟨a, rfl⟩ := hxi
  obtain ⟨b, hab⟩ := hxj
  apply hij
  have hab' : finProdFinEquiv (i, a) = finProdFinEquiv (j, b) :=
    (Fin.castLEEmb h).injective hab.symm
  exact congrArg Prod.fst (finProdFinEquiv.injective hab')

/-- With one color, the canonical block decomposition gives the result. -/
theorem hasMonoMatching_one_color {n r k : ℕ} (c : Edge n r → Fin 1)
    (h : k * r ≤ n) : HasMonoMatching c k := by
  refine ⟨⟨0, by omega⟩, blockEdge h, ?_, ?_⟩
  · intro i
    exact Subsingleton.elim _ _
  · intro i j hij
    exact blockEdge_disjoint h hij

/-- A singleton edge at a specified vertex. -/
def singletonEdge {n : ℕ} (x : Fin n) : Edge n 1 := ⟨{x}, by simp⟩

@[simp] theorem singletonEdge_injective {n : ℕ} :
    Function.Injective (singletonEdge : Fin n → Edge n 1) := by
  intro x y h
  have h' : ({x} : Finset (Fin n)) = {y} := congrArg Subtype.val h
  simpa using h'

theorem singletonEdge_disjoint {n : ℕ} {x y : Fin n} (hxy : x ≠ y) :
    Disjoint (singletonEdge x).1 (singletonEdge y).1 := by
  simp [singletonEdge, hxy]

/-- For singleton edges, the theorem is the ordinary finite pigeonhole principle. -/
theorem hasMonoMatching_singletons {n t k : ℕ} (hk : 1 ≤ k) (ht : 1 ≤ t)
    (hn : k + (t - 1) * (k - 1) ≤ n) (c : Edge n 1 → Fin t) :
    HasMonoMatching c k := by
  let vertexColor : Fin n → Fin t := fun x ↦ c (singletonEdge x)
  have hmul : t * (k - 1) < n := by
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have ht' : t - 1 + 1 = t := Nat.sub_add_cancel ht
    nlinarith
  obtain ⟨color, hcolor⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card vertexColor (by simpa using hmul)
  let S : Finset (Fin n) := Finset.univ.filter fun x ↦ vertexColor x = color
  have hkS : k ≤ S.card := by
    dsimp [S]
    simpa only [Nat.lt_iff_add_one_le, Nat.sub_add_cancel hk] using hcolor
  have hkS' : Fintype.card (Fin k) ≤ S.card := by simpa using hkS
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hkS'
  refine ⟨color, fun i ↦ singletonEdge (f i), ?_, ?_⟩
  · intro i
    have hfi : f i ∈ S := hf (Set.mem_range_self i)
    simpa [S, vertexColor] using hfi
  · intro i j hij
    exact singletonEdge_disjoint (f.injective.ne hij)

/-- The exact assertion, factored so the multiplicative reduction can quantify over parameters. -/
def ResolutionStatement (k : ℕ) : Prop :=
  ∀ n r t : ℕ, 1 ≤ r → 1 ≤ t →
    k * r + (t - 1) * (k - 1) ≤ n →
    ∀ c : Edge n r → Fin t, HasMonoMatching c k

/-- A bundled witness, convenient when a matching must be chosen repeatedly. -/
structure MonoMatchingData {n r t : ℕ} (c : Edge n r → Fin t) (k : ℕ) where
  color : Fin t
  edges : Fin k → Edge n r
  mono : ∀ i, c (edges i) = color
  disjoint : ∀ i j, i ≠ j → Disjoint (edges i).1 (edges j).1

theorem HasMonoMatching.nonemptyData {n r t k : ℕ} {c : Edge n r → Fin t}
    (h : HasMonoMatching c k) : Nonempty (MonoMatchingData c k) := by
  obtain ⟨color, edges, hmono, hdisjoint⟩ := h
  exact ⟨⟨color, edges, hmono, hdisjoint⟩⟩

noncomputable def HasMonoMatching.get {n r t k : ℕ} {c : Edge n r → Fin t}
    (h : HasMonoMatching c k) : MonoMatchingData c k :=
  Classical.choice h.nonemptyData

/-- Choose an enumeration of the support of an edge. -/
noncomputable def Edge.supportEmbedding {n R : ℕ} (S : Edge n R) : Fin R ↪ Fin n :=
  Classical.choose <| Function.Embedding.exists_of_card_eq_finset (by simpa using S.2.symm)

@[simp] theorem Edge.univ_map_supportEmbedding {n R : ℕ} (S : Edge n R) :
    Finset.univ.map S.supportEmbedding = S.1 :=
  Classical.choose_spec <| Function.Embedding.exists_of_card_eq_finset (by simpa using S.2.symm)

theorem Edge.map_supportEmbedding_subset {n R r : ℕ} (S : Edge n R) (e : Edge R r) :
    (e.map S.supportEmbedding).1 ⊆ S.1 := by
  rw [← S.univ_map_supportEmbedding]
  exact (Finset.map_subset_map (f := S.supportEmbedding)).2 (Finset.subset_univ e.1)

theorem hasMonoMatching_zero {n r t : ℕ} (ht : 1 ≤ t) (c : Edge n r → Fin t) :
    HasMonoMatching c 0 := by
  refine ⟨⟨0, ht⟩, Fin.elim0, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem resolutionStatement_zero : ResolutionStatement 0 := by
  intro n r t _hr ht _hn c
  exact hasMonoMatching_zero ht c

/-- Alon--Frankl--Lovász product reduction for matching multiplicities. -/
theorem ResolutionStatement.mul {a b : ℕ}
    (hA : ResolutionStatement a) (hB : ResolutionStatement b) :
    ResolutionStatement (a * b) := by
  by_cases ha0 : a = 0
  · simpa [ha0] using resolutionStatement_zero
  by_cases hb0 : b = 0
  · simpa [hb0] using resolutionStatement_zero
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 ha0
  have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.2 hb0
  intro n r t hr ht hn c
  let R : ℕ := a * r + (t - 1) * (a - 1)
  have hR : 1 ≤ R := by
    dsimp [R]
    nlinarith
  have localHas : ∀ S : Edge n R,
      HasMonoMatching (restrictColor S.supportEmbedding c) a := by
    intro S
    exact hA R r t hr ht (by simp [R]) (restrictColor S.supportEmbedding c)
  let localData : ∀ S : Edge n R,
      MonoMatchingData (restrictColor S.supportEmbedding c) a :=
    fun S ↦ (localHas S).get
  let blockColor : Edge n R → Fin t := fun S ↦ (localData S).color
  have hnBlocks : b * R + (t - 1) * (b - 1) ≤ n := by
    have ha' : a - 1 + 1 = a := Nat.sub_add_cancel ha
    have hb' : b - 1 + 1 = b := Nat.sub_add_cancel hb
    have hab : 1 ≤ a * b := Nat.mul_pos ha hb
    have hab' : a * b - 1 + 1 = a * b := Nat.sub_add_cancel hab
    have hfactor : b * (a - 1) + (b - 1) = a * b - 1 := by
      nlinarith
    calc
      b * R + (t - 1) * (b - 1) =
          a * b * r + (t - 1) * (b * (a - 1) + (b - 1)) := by
            dsimp [R]
            ring
      _ = a * b * r + (t - 1) * (a * b - 1) := by rw [hfactor]
      _ ≤ n := hn
  let outer : MonoMatchingData blockColor b :=
    (hB n R t hR ht hnBlocks blockColor).get
  let finalEdges : Fin (a * b) → Edge n r := fun q ↦
    let ij := finProdFinEquiv.symm q
    ((localData (outer.edges ij.2)).edges ij.1).map
      (outer.edges ij.2).supportEmbedding
  refine ⟨outer.color, finalEdges, ?_, ?_⟩
  · intro q
    let ij := finProdFinEquiv.symm q
    calc
      c (finalEdges q) = (localData (outer.edges ij.2)).color := by
        exact (localData (outer.edges ij.2)).mono ij.1
      _ = blockColor (outer.edges ij.2) := rfl
      _ = outer.color := outer.mono ij.2
  · intro q q' hqq'
    let ij := finProdFinEquiv.symm q
    let ij' := finProdFinEquiv.symm q'
    have hij_ne : ij ≠ ij' := fun h ↦ hqq' (finProdFinEquiv.symm.injective h)
    by_cases hj : ij.2 = ij'.2
    · have hi : ij.1 ≠ ij'.1 := by
        intro hi
        exact hij_ne (Prod.ext hi hj)
      have hd := (localData (outer.edges ij.2)).disjoint ij.1 ij'.1 hi
      have hdmap := (Finset.disjoint_map (outer.edges ij.2).supportEmbedding).2 hd
      change Disjoint
        (((localData (outer.edges ij.2)).edges ij.1).map
          (outer.edges ij.2).supportEmbedding).1
        (((localData (outer.edges ij'.2)).edges ij'.1).map
          (outer.edges ij'.2).supportEmbedding).1
      rw [← hj]
      exact hdmap
    · rw [Finset.disjoint_left]
      intro x hx hx'
      have hx_block : x ∈ (outer.edges ij.2).1 :=
        Edge.map_supportEmbedding_subset (outer.edges ij.2)
          ((localData (outer.edges ij.2)).edges ij.1) (by simpa [finalEdges, ij] using hx)
      have hx'_block : x ∈ (outer.edges ij'.2).1 :=
        Edge.map_supportEmbedding_subset (outer.edges ij'.2)
          ((localData (outer.edges ij'.2)).edges ij'.1) (by simpa [finalEdges, ij'] using hx')
      exact (Finset.disjoint_left.mp (outer.disjoint ij.2 ij'.2 hj) hx_block) hx'_block

private theorem color_ne_of_no_pair {n r t : ℕ} {c : Edge n r → Fin t}
    (hno : ¬ HasMonoMatching c 2) {a b : Edge n r} (hdisj : Disjoint a.1 b.1) :
    c a ≠ c b := by
  intro hcolor
  apply hno
  refine ⟨c a, ![a, b], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hcolor]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hdisj.symm]

/-- The `k = 2` case, obtained from the repository's unconditional Kneser--Lovász theorem. -/
theorem resolution_two : ResolutionStatement 2 := by
  intro n r t hr ht hn c
  have htwo : 2 * r ≤ n := by omega
  have hcolors : t ≤ n - 2 * r + 1 := by omega
  by_contra hno
  apply (ProofsInTheBook.Chapter39.chapter39_unconditional hr htwo).2
  refine ⟨fun e ↦ Fin.castLE hcolors (c e), ?_⟩
  intro a b hab
  have hcab : c a ≠ c b :=
    color_ne_of_no_pair hno
      ((ProofsInTheBook.Chapter39.kneserGraph_adj_iff a b).mp hab).2
  exact (Fin.castLEEmb hcolors).injective.ne hcab

theorem resolution_one : ResolutionStatement 1 := by
  intro n r t _hr _ht hn c
  exact hasMonoMatching_one c (by omega)

/-- Once the theorem is known for prime multiplicities, the AFL product reduction
and strong induction give every multiplicity. -/
theorem resolution_all_of_prime
    (hprime : ∀ p : ℕ, p.Prime → ResolutionStatement p) :
    ∀ k : ℕ, ResolutionStatement k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk0 : k = 0
      · simpa [hk0] using resolutionStatement_zero
      by_cases hk1 : k = 1
      · simpa [hk1] using resolution_one
      by_cases hkp : k.Prime
      · exact hprime k hkp
      have hk2 : 2 ≤ k := by omega
      obtain ⟨a, b, ha, hb, hab⟩ :=
        (Nat.not_prime_iff_exists_mul_eq hk2).mp hkp
      simpa [hab] using ResolutionStatement.mul (ih a ha) (ih b hb)

/-- The prime-multiplicity case supplied by the proved `Z/p` Tucker lemma and
the Alon--Frankl--Lovász prime reduction. -/
theorem resolution_prime (p : ℕ) (hp : p.Prime) : ResolutionStatement p := by
  have hscratch : Erdos780Scratch.ResolutionStatement p :=
    PrimeResolutionScratch.primeResolution Erdos780Core.zpTucker_alpha hp
  intro n r t hr ht hn c
  have hmatching := hscratch n r t hr ht hn c
  simpa only [HasMonoMatching, Erdos780Scratch.HasMonoMatching] using hmatching

/-- **Erdős Problem 780 (Alon--Frankl--Lovász).** If the `r`-subsets of
an `n`-element set are colored with `t` colors and
`k * r + (t - 1) * (k - 1) ≤ n`, then one color contains `k` pairwise
disjoint edges. -/
theorem erdos_780 {n k r t : ℕ} (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : Edge n r → Fin t) :
    HasMonoMatching c k :=
  resolution_all_of_prime resolution_prime k n r t hr ht hn c

#print axioms erdos_780

end Erdos780
