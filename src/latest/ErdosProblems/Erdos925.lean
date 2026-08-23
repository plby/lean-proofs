/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 925.
https://www.erdosproblems.com/forum/thread/925

Informal authors:
- Noga Alon
- Vojtěch Rödl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos925.md
-/
import ErdosProblems.Erdos920.Construction
import ErdosProblems.Erdos920.Ordering

/-!
# Erdős Problem 925

This file proves the negative answer to Erdős Problem 925.  The exact graph
statement is encoded by `AdmitsTriangleFreeTwoColoring`: the edges are the
disjoint union of two triangle-free spanning subgraphs.  The construction
uses the projective `D*` graph already formalized for Erdős Problem 920,
the factorial-saving ordering lemma, and an exact double count over vertex
permutations.  It gives counterexamples on
`Ω(m^3 / log(m)^6)` vertices with independence number below `m`, which is
enough to rule out every exponent `1/3 + δ`, `δ > 0`.

The detailed mathematical proof, including the sharper published
Alon--Rödl estimate, is in `tex/925.tex`.
-/

open Filter Real
open scoped Topology BigOperators

namespace Erdos925

noncomputable section

/-- An exact two-coloring of the edges of `G`, with neither color containing a triangle. -/
def AdmitsTriangleFreeTwoColoring {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ red blue : SimpleGraph V,
    Disjoint red blue ∧ red ⊔ blue = G ∧ red.CliqueFree 3 ∧ blue.CliqueFree 3

/-- The proposed affirmative answer, including the constant hidden in `≫`. -/
def ProposedBound : Prop :=
  ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧ ∃ threshold : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), threshold ≤ n →
      AdmitsTriangleFreeTwoColoring G →
        c * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ≤ (G.indepNum : ℝ)

/-- A three-color Ramsey lower-bound witness, with the third color represented by
the complement of the union of the first two.  Overlap is harmless here: it is
removed when producing the exact edge coloring of the final graph. -/
def ThreeColorCounterexample (m n : ℕ) : Prop :=
  ∃ red blue : SimpleGraph (Fin n), red.CliqueFree 3 ∧ blue.CliqueFree 3 ∧
    (red ⊔ blue).IndepSetFree m

lemma indepSetFree_iff_indepNum_lt {V : Type*} [Finite V]
    {G : SimpleGraph V} {m : ℕ} : G.IndepSetFree m ↔ G.indepNum < m := by
  constructor
  · intro hfree
    by_contra hnot
    have hmle : m ≤ G.indepNum := Nat.le_of_not_gt hnot
    obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
    have hmcard : m ≤ S.card := by simpa [hS.card_eq] using hmle
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hmcard
    exact hfree T ⟨hS.isIndepSet.mono (Finset.coe_subset.mpr hTS), hTcard⟩
  · intro hlt T hT
    have hcardle : T.card ≤ G.indepNum := hT.isIndepSet.card_le_indepNum
    have hmle : m ≤ G.indepNum := by simpa [hT.card_eq] using hcardle
    omega

/-- Overlapping triangle-free copies give an exact disjoint two-coloring after
removing the red edges from the blue class. -/
lemma admitsTriangleFreeTwoColoring_sup
    {V : Type*} {red blue : SimpleGraph V}
    (hred : red.CliqueFree 3) (hblue : blue.CliqueFree 3) :
    AdmitsTriangleFreeTwoColoring (red ⊔ blue) := by
  refine ⟨red, blue \ red, disjoint_sdiff_self_right, ?_, hred, ?_⟩
  · exact sup_sdiff_self red blue
  · exact hblue.anti sdiff_le

/-- Exact bridge from a ternary Ramsey counterexample to a graph in Problem 925. -/
lemma threeColorCounterexample_bridge {m n : ℕ} (h : ThreeColorCounterexample m n) :
    ∃ G : SimpleGraph (Fin n),
      AdmitsTriangleFreeTwoColoring G ∧ G.indepNum < m := by
  rcases h with ⟨red, blue, hred, hblue, hfree⟩
  exact ⟨red ⊔ blue, admitsTriangleFreeTwoColoring_sup hred hblue,
    indepSetFree_iff_indepNum_lt.mp hfree⟩

/-! ## Exact double counting over permutations -/

section PermutationCount

variable {V : Type*} [Fintype V] [DecidableEq V]

def finsetEquivOfPerm (S T : Finset V) (perm : Equiv.Perm V)
    (h : S.map perm.toEmbedding = T) : S ≃ T where
  toFun x := ⟨perm x, by
    rw [← h]
    exact Finset.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  invFun y := ⟨perm.symm y, by
    have hy : y.1 ∈ S.map perm.toEmbedding := by rw [h]; exact y.property
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    have hxeq : x = perm.symm y := by
      apply perm.injective
      simpa using hxy
    simpa [← hxeq] using hx⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

lemma map_compl_of_map_eq (S T : Finset V) (perm : Equiv.Perm V)
    (h : S.map perm.toEmbedding = T) :
    Sᶜ.map perm.toEmbedding = Tᶜ := by
  ext y
  simp only [Finset.mem_map, Finset.mem_compl]
  constructor
  · rintro ⟨x, hx, rfl⟩ hmem
    apply hx
    have : perm x ∈ S.map perm.toEmbedding := by simpa [h] using hmem
    simpa using this
  · intro hy
    refine ⟨perm.symm y, ?_, by simp⟩
    intro hx
    apply hy
    have : y ∈ S.map perm.toEmbedding :=
      Finset.mem_map.mpr ⟨perm.symm y, hx, by simp⟩
    simpa [h] using this

def permPieces (S T : Finset V) :
    {perm : Equiv.Perm V // S.map perm.toEmbedding = T} →
      (S ≃ T) × ((Sᶜ : Finset V) ≃ (Tᶜ : Finset V)) := fun perm =>
  (finsetEquivOfPerm S T perm.1 perm.2,
    finsetEquivOfPerm Sᶜ Tᶜ perm.1 (map_compl_of_map_eq S T perm.1 perm.2))

lemma permPieces_injective (S T : Finset V) :
    Function.Injective (permPieces S T) := by
  intro perm ρ h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ S
  · exact congrArg (fun e : S ≃ T => (e ⟨x, hx⟩ : V)) (congrArg Prod.fst h)
  · exact congrArg
      (fun e : (Sᶜ : Finset V) ≃ (Tᶜ : Finset V) => (e ⟨x, by simpa⟩ : V))
      (congrArg Prod.snd h)

lemma card_perm_mapping_finset_le (S T : Finset V) (hcard : S.card = T.card) :
    Fintype.card {perm : Equiv.Perm V // S.map perm.toEmbedding = T} ≤
      S.card.factorial * (Fintype.card V - S.card).factorial := by
  let eST : S ≃ T := S.equivOfCardEq hcard
  have hcompCard : (Sᶜ : Finset V).card = (Tᶜ : Finset V).card := by
    rw [Finset.card_compl, Finset.card_compl, hcard]
  let eComp : (Sᶜ : Finset V) ≃ (Tᶜ : Finset V) :=
    (Sᶜ : Finset V).equivOfCardEq hcompCard
  calc
    Fintype.card {perm : Equiv.Perm V // S.map perm.toEmbedding = T} ≤
        Fintype.card ((S ≃ T) × ((Sᶜ : Finset V) ≃ (Tᶜ : Finset V))) :=
      Fintype.card_le_of_injective (permPieces S T) (permPieces_injective S T)
    _ = S.card.factorial * (Fintype.card V - S.card).factorial := by
      rw [Fintype.card_prod, Fintype.card_equiv eST, Fintype.card_equiv eComp]
      simp

def mapsFinsetFiber (S T : Finset V) : Finset (Equiv.Perm V) :=
  Finset.univ.filter fun perm => S.map perm.toEmbedding = T

lemma card_mapsFinsetFiber_le (S T : Finset V) (hcard : S.card = T.card) :
    (mapsFinsetFiber S T).card ≤
      S.card.factorial * (Fintype.card V - S.card).factorial := by
  rw [show (mapsFinsetFiber S T).card =
      Fintype.card {perm : Equiv.Perm V // S.map perm.toEmbedding = T} by
    rw [Fintype.card_subtype]
    rfl]
  exact card_perm_mapping_finset_le S T hcard

def badPerms (A : Finset (Finset V)) : Finset (Equiv.Perm V) :=
  Finset.univ.filter fun perm => ∃ S ∈ A, S.map perm.toEmbedding ∈ A

lemma badPerms_subset_biUnion (A : Finset (Finset V)) :
    badPerms A ⊆ A.biUnion (fun S => A.biUnion (fun T => mapsFinsetFiber S T)) := by
  intro perm hperm
  simp only [badPerms, Finset.mem_filter, Finset.mem_univ, true_and] at hperm
  obtain ⟨S, hSA, hmapA⟩ := hperm
  simp only [Finset.mem_biUnion]
  refine ⟨S, hSA, S.map perm.toEmbedding, hmapA, ?_⟩
  simp [mapsFinsetFiber]

lemma card_badPerms_le (A : Finset (Finset V)) (m : ℕ)
    (hA : ∀ S ∈ A, S.card = m) :
    (badPerms A).card ≤ A.card ^ 2 * m.factorial *
      (Fintype.card V - m).factorial := by
  calc
    (badPerms A).card ≤
        (A.biUnion (fun S => A.biUnion (fun T => mapsFinsetFiber S T))).card :=
      Finset.card_le_card (badPerms_subset_biUnion A)
    _ ≤ ∑ S ∈ A, ∑ T ∈ A, (mapsFinsetFiber S T).card := by
      exact (Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun _ _ =>
        Finset.card_biUnion_le)
    _ ≤ ∑ _S ∈ A, ∑ _T ∈ A,
        m.factorial * (Fintype.card V - m).factorial := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      simpa [hA S hS] using
        card_mapsFinsetFiber_le S T ((hA S hS).trans (hA T hT).symm)
    _ = A.card ^ 2 * m.factorial * (Fintype.card V - m).factorial := by
      simp [pow_two]
      ring

theorem exists_perm_avoiding_family (A : Finset (Finset V)) (m : ℕ)
    (hA : ∀ S ∈ A, S.card = m) (hm : m ≤ Fintype.card V)
    (hsmall : A.card ^ 2 < (Fintype.card V).choose m) :
    ∃ perm : Equiv.Perm V, ∀ S ∈ A, S.map perm.toEmbedding ∉ A := by
  have hbadBound := card_badPerms_le A m hA
  have hfacpos : 0 < m.factorial * (Fintype.card V - m).factorial := by positivity
  have hbadlt : (badPerms A).card < Fintype.card (Equiv.Perm V) := by
    rw [Fintype.card_perm]
    calc
      (badPerms A).card ≤ A.card ^ 2 * m.factorial *
          (Fintype.card V - m).factorial := hbadBound
      _ < (Fintype.card V).choose m * m.factorial *
          (Fintype.card V - m).factorial := by
        simpa [mul_assoc] using (Nat.mul_lt_mul_right hfacpos).2 hsmall
      _ = (Fintype.card V).factorial :=
        Nat.choose_mul_factorial_mul_factorial hm
  obtain ⟨perm, _hperm, hpermgood⟩ := Finset.exists_mem_notMem_of_card_lt_card hbadlt
  refine ⟨perm, ?_⟩
  intro S hSA hmapA
  apply hpermgood
  simp only [badPerms, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨S, hSA, hmapA⟩

theorem exists_two_triangleFree_copies_indepSetFree
    (H : SimpleGraph V) [DecidableRel H.Adj] (m : ℕ)
    (htriangle : H.CliqueFree 3) (hm : m ≤ Fintype.card V)
    (hsmall : ((H.indepSetFinset m).card) ^ 2 <
      (Fintype.card V).choose m) :
    ∃ perm : Equiv.Perm V,
      H.CliqueFree 3 ∧ (H.comap perm.toEmbedding).CliqueFree 3 ∧
        (H ⊔ H.comap perm.toEmbedding).IndepSetFree m := by
  obtain ⟨perm, hperm⟩ := exists_perm_avoiding_family (H.indepSetFinset m) m
    (fun S hS => (SimpleGraph.mem_indepSetFinset_iff.mp hS).card_eq) hm hsmall
  refine ⟨perm, htriangle, ?_, ?_⟩
  · exact SimpleGraph.CliqueFree.comap
      (SimpleGraph.Embedding.comap perm.toEmbedding H).isContained htriangle
  · intro S hS
    have hSinH : S ∈ H.indepSetFinset m := by
      apply SimpleGraph.mem_indepSetFinset_iff.mpr
      refine ⟨?_, hS.card_eq⟩
      intro x hx y hy hxy hxyH
      exact hS.isIndepSet hx hy hxy (Or.inl hxyH)
    have hmapInH : S.map perm.toEmbedding ∈ H.indepSetFinset m := by
      apply SimpleGraph.mem_indepSetFinset_iff.mpr
      refine ⟨?_, by simpa using hS.card_eq⟩
      intro x hx y hy hxy hxyH
      obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
      have hxy' : x' ≠ y' := fun h => hxy (congrArg perm h)
      exact hS.isIndepSet hx' hy' hxy' (Or.inr hxyH)
    exact hperm S hSinH hmapInH

end PermutationCount

/-! ## From one projective witness to two triangle-free color classes -/

/-- The standard elementary lower bound for a binomial coefficient. -/
lemma choose_ge_pow (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((n : ℝ) / k) ^ k ≤ (n.choose k : ℝ) := by
  field_simp
  have hprod : (∏ i ∈ Finset.range k, (n - i : ℝ)) ≥
      (n / k : ℝ) ^ k * (Nat.factorial k) := by
    have hprod' : (∏ i ∈ Finset.range k, (n - i : ℝ)) ≥
        (∏ i ∈ Finset.range k, (n / k : ℝ)) *
          (∏ i ∈ Finset.range k, (k - i : ℝ)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod
        (fun _ _ => mul_nonneg
          (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (sub_nonneg.mpr (Nat.cast_le.mpr (by
            linarith [Finset.mem_range.mp ‹_›]))))
        (fun i hi => by
          nlinarith
            [show (i : ℝ) + 1 ≤ k by
              norm_cast
              linarith [Finset.mem_range.mp hi],
             show (n : ℝ) ≥ k by exact_mod_cast hkn,
             div_mul_cancel₀ (n : ℝ)
               (show (k : ℝ) ≠ 0 by positivity)])
    convert hprod' using 1
    norm_num [Finset.prod_range_succ']
    exact congrArg₂ _ (by ring)
      (Nat.recOn k (by norm_num) fun n ih => by
        simp_all +decide [Nat.factorial_succ, Finset.prod_range_succ']
        ring)
  have hbinom : (Nat.choose n k : ℝ) =
      (∏ i ∈ Finset.range k, (n - i : ℝ)) / (Nat.factorial k) := by
    field_simp
    rw_mod_cast [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    rw [Nat.descFactorial_eq_prod_range]
    rw [Nat.cast_prod, Finset.prod_congr rfl fun x hx =>
      Int.subNatNat_of_le (by linarith [Finset.mem_range.mp hx])]
  rw [hbinom, le_div_iff₀]
  · exact hprod
  · positivity

/-- The numerical core of the two-copy argument. -/
lemma count_square_lt_choose
    {N m q I F : ℕ} {C : ℝ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hq : 1 ≤ q) (hC : 0 < C)
    (hN : (q : ℝ) ^ 3 / 4 ≤ (N : ℝ))
    (hscale : 4 * Real.exp 1 ^ 2 * C ^ 2 * (q : ℝ) < (m : ℝ))
    (horder : I * m.factorial ≤ F)
    (hforward : (F : ℝ) ≤ (C * (q : ℝ) ^ 2) ^ m) :
    I ^ 2 < N.choose m := by
  let A : ℝ := (m : ℝ) / Real.exp 1
  let B : ℝ := C * (q : ℝ) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hfac := Erdos920.factorial_lower_bound m
  have horderR : (I : ℝ) * (m.factorial : ℝ) ≤ (F : ℝ) := by
    exact_mod_cast horder
  have hI : (I : ℝ) ≤ (B / A) ^ m := by
    calc
      (I : ℝ) ≤ (F : ℝ) / (m.factorial : ℝ) :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < m.factorial)).2 horderR
      _ ≤ B ^ m / (m.factorial : ℝ) :=
        div_le_div_of_nonneg_right hforward (by positivity)
      _ ≤ B ^ m / A ^ m := by
        exact div_le_div_of_nonneg_left (pow_nonneg hB.le m) (pow_pos hA m) hfac
      _ = (B / A) ^ m := by
        dsimp [A]
        rw [← div_pow]
  have hbase : (B / A) ^ 2 < (N : ℝ) / m := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hscale' := mul_lt_mul_of_pos_right hscale (pow_pos hqR 3)
    calc
      (B / A) ^ 2 =
          (Real.exp 1 ^ 2 * C ^ 2 * (q : ℝ) ^ 4) / (m : ℝ) ^ 2 := by
        dsimp [A, B]
        field_simp
      _ < (q : ℝ) ^ 3 / (4 * (m : ℝ)) := by
        rw [div_lt_div_iff₀ (sq_pos_of_pos hmR) (by positivity)]
        nlinarith
      _ = ((q : ℝ) ^ 3 / 4) / m := by ring
      _ ≤ (N : ℝ) / m := div_le_div_of_nonneg_right hN hmR.le
  have hIpow : (I : ℝ) ^ 2 ≤ ((B / A) ^ 2) ^ m := by
    calc
      (I : ℝ) ^ 2 ≤ ((B / A) ^ m) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg I) hI 2
      _ = ((B / A) ^ 2) ^ m := by ring
  have hpows : ((B / A) ^ 2) ^ m < ((N : ℝ) / m) ^ m :=
    pow_lt_pow_left₀ hbase (sq_nonneg _) (by omega)
  have hreal : (I : ℝ) ^ 2 < (N.choose m : ℝ) :=
    hIpow.trans_lt (hpows.trans_le (choose_ge_pow N m hm hmN))
  exact_mod_cast hreal

open Erdos920
open Erdos920.RamseyPackaging

/-- One projective `DStarWitness 2` gives the two triangle-free color classes
needed for Problem 925 under the explicit two-copy numerical inequality. -/
theorem dStarWitness_two_triangleFree_copies
    {m q : ℕ} {C : ℝ} (W : DStarWitness 2 m q C)
    (hq : 1 ≤ q) (hC : 0 < C)
    (hmcard : m ≤ @Fintype.card W.V W.fintypeV)
    (hscale : 4 * Real.exp 1 ^ 2 * C ^ 2 * (q : ℝ) < (m : ℝ)) :
    ∃ R B : SimpleGraph W.V,
      R.CliqueFree 3 ∧ B.CliqueFree 3 ∧ (R ⊔ B).IndepSetFree m ∧
        (q : ℝ) ^ 3 / 4 ≤ (@Fintype.card W.V W.fintypeV : ℝ) := by
  classical
  let _ : Fintype W.V := W.fintypeV
  let _ : LinearOrder W.V := LinearOrder.lift' (Fintype.equivFin W.V)
    (Fintype.equivFin W.V).injective
  let D : W.V → W.V → Prop := W.D.arc
  have htfree : TransitiveTournamentFree D 3 := by
    intro v hv htv
    apply W.transitiveTournamentFree
    exact ⟨v, hv, fun i j hij => htv hij⟩
  obtain ⟨perm, hclique, horder⟩ :=
    exists_cliqueFree_forwardGraph_factorial_bound (D := D) htfree m
  let H : SimpleGraph W.V := forwardGraph D perm
  have hcount_eq :
      (forwardIndependentFinset D m).card =
        @Digraph.forwardIndependentTupleCount W.V W.fintypeV W.D m := by
    simp only [forwardIndependentFinset, Digraph.forwardIndependentTupleCount,
      Finset.card_filter, D]
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
  have hforward : ((forwardIndependentFinset D m).card : ℝ) ≤
      (C * (q : ℝ) ^ 2) ^ m := by
    rw [hcount_eq]
    exact W.forward_bound
  have hm : 1 ≤ m := by
    have hleft : 0 < 4 * Real.exp 1 ^ 2 * C ^ 2 * (q : ℝ) := by positivity
    exact_mod_cast hleft.trans hscale
  have hN : (q : ℝ) ^ 3 / 4 ≤ (Fintype.card W.V : ℝ) := by
    simpa using W.vertex_lower
  have hsmall : ((H.indepSetFinset m).card) ^ 2 <
      (Fintype.card W.V).choose m :=
    count_square_lt_choose hm hmcard hq hC hN hscale horder hforward
  obtain ⟨copyPerm, hHclique, hcopyclique, hfree⟩ :=
    exists_two_triangleFree_copies_indepSetFree H m hclique hmcard hsmall
  exact ⟨H, H.comap copyPerm.toEmbedding, hHclique, hcopyclique, hfree, hN⟩

/-- Every fixed positive multiple of `log(m)^2` is eventually below `m`. -/
lemma eventually_mul_log_sq_le (K : ℝ) (hK : 0 < K) :
    ∀ᶠ m : ℕ in atTop, K * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) := by
  have heps : 0 < K⁻¹ := inv_pos.mpr hK
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id_eq,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hm
  calc
    K * Real.log (m : ℝ) ^ 2 ≤ K * (K⁻¹ * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hm hK.le
    _ = (m : ℝ) := by field_simp

/-- The lower prime scale eventually exceeds any fixed positive integer threshold. -/
lemma eventually_nat_le_prime_lower_scale (C : ℝ) (hC : 0 < C)
    (Q : ℕ) (hQ : 0 < Q) :
    ∀ᶠ m : ℕ in atTop,
      (Q : ℝ) ≤ (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) := by
  have hK : 0 < 8 * C * (Q : ℝ) := by positivity
  have hbound := eventually_mul_log_sq_le (8 * C * (Q : ℝ)) hK
  have hmLarge : ∀ᶠ m : ℕ in atTop, 1 < (m : ℝ) := by
    exact_mod_cast (eventually_gt_atTop (1 : ℕ))
  filter_upwards [hbound, hmLarge] with m hm hm1
  have hden : 0 < 8 * C * Real.log (m : ℝ) ^ 2 := by
    have : 0 < Real.log (m : ℝ) := Real.log_pos hm1
    positivity
  rw [le_div_iff₀ hden]
  nlinarith

/-! ## The final analytic contradiction -/

lemma eventual_ramsey_lower_bound_beats_power
    (logPower : ℕ) {A c δ : ℝ} (hA : 0 < A) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) < c * (A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ logPower) ^
        ((1 : ℝ) / 3 + δ) := by
  let q : ℝ := (1 : ℝ) / 3 + δ
  have hq : 0 < q := by dsimp [q]; positivity
  let s : ℝ := δ / q
  have hs : 0 < s := div_pos hδ hq
  have hlogLittle :
      (fun x : ℝ => Real.log x ^ (logPower : ℝ)) =o[atTop] (fun x : ℝ => x ^ s) :=
    isLittleO_log_rpow_rpow_atTop logPower hs
  have hlogLittleNat :
      (fun m : ℕ => Real.log (m : ℝ) ^ (logPower : ℝ)) =o[atTop]
        (fun m : ℕ => (m : ℝ) ^ s) :=
    hlogLittle.comp_tendsto tendsto_natCast_atTop_atTop
  have hlogBoundNorm := hlogLittleNat.def (show (0 : ℝ) < 1 by norm_num)
  have hmLarge : ∀ᶠ m : ℕ in atTop, 1 < (m : ℝ) := by
    exact_mod_cast (eventually_gt_atTop (1 : ℕ))
  have hlogBound : ∀ᶠ m : ℕ in atTop,
      Real.log (m : ℝ) ^ logPower ≤ (m : ℝ) ^ s := by
    filter_upwards [hlogBoundNorm, hmLarge] with m hm hm1
    have hlog_nonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1.le
    have hmpos : 0 < (m : ℝ) := lt_trans zero_lt_one hm1
    simp only [Real.norm_eq_abs] at hm
    rw [abs_of_pos (Real.rpow_pos_of_pos hmpos s)] at hm
    simpa [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg, Real.rpow_natCast] using hm
  have hgrowth : Tendsto (fun m : ℕ => A ^ q * (m : ℝ) ^ (2 * δ)) atTop atTop := by
    have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ (2 * δ)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    exact Tendsto.const_mul_atTop (Real.rpow_pos_of_pos hA q) ht
  have hconstGrowth : ∀ᶠ m : ℕ in atTop, 1 / c < A ^ q * (m : ℝ) ^ (2 * δ) :=
    hgrowth.eventually (eventually_gt_atTop (1 / c))
  filter_upwards [hmLarge, hlogBound, hconstGrowth] with m hm1 hlog hgrow
  have hmpos : 0 < (m : ℝ) := lt_trans zero_lt_one hm1
  have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos hm1
  have hdenpos : 0 < Real.log (m : ℝ) ^ logPower := pow_pos hlogpos _
  have hbase :
      A * (m : ℝ) ^ (3 - s) ≤
        A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ logPower := by
    rw [le_div_iff₀ hdenpos]
    have hm3eq : (m : ℝ) ^ (3 : ℕ) = (m : ℝ) ^ (3 : ℝ) := by
      simp
    have hcalc : (m : ℝ) ^ (3 - s) * (m : ℝ) ^ s = (m : ℝ) ^ (3 : ℝ) := by
      rw [← Real.rpow_add hmpos]
      congr 1
      ring
    calc
      A * (m : ℝ) ^ (3 - s) * Real.log (m : ℝ) ^ logPower
          ≤ A * (m : ℝ) ^ (3 - s) * (m : ℝ) ^ s := by gcongr
      _ = A * (m : ℝ) ^ (3 : ℝ) := by rw [mul_assoc, hcalc]
      _ = A * (m : ℝ) ^ (3 : ℕ) := by rw [hm3eq]
  have hbasepos : 0 < A * (m : ℝ) ^ (3 - s) := by positivity
  have hrpowbase :
      (A * (m : ℝ) ^ (3 - s)) ^ q ≤
        (A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ logPower) ^ q :=
    Real.rpow_le_rpow hbasepos.le hbase hq.le
  have hexponent : q * (3 - s) = 1 + 2 * δ := by
    dsimp [q, s]
    field_simp
    ring
  have hnormalized :
      (A * (m : ℝ) ^ (3 - s)) ^ q =
        A ^ q * ((m : ℝ) * (m : ℝ) ^ (2 * δ)) := by
    rw [Real.mul_rpow hA.le (Real.rpow_nonneg _ _)]
    rw [← Real.rpow_mul hmpos.le]
    rw [mul_comm (3 - s) q, hexponent, Real.rpow_add hmpos, Real.rpow_one]
    positivity
  have hone : 1 < c * (A ^ q * (m : ℝ) ^ (2 * δ)) := by
    calc
      1 = c * (1 / c) := by field_simp
      _ < c * (A ^ q * (m : ℝ) ^ (2 * δ)) := mul_lt_mul_of_pos_left hgrow hc
  have hmainSmall :
      (m : ℝ) < c * (A * (m : ℝ) ^ (3 - s)) ^ q := by
    rw [hnormalized]
    calc
      (m : ℝ) = (m : ℝ) * 1 := by ring
      _ < (m : ℝ) * (c * (A ^ q * (m : ℝ) ^ (2 * δ))) :=
        mul_lt_mul_of_pos_left hone hmpos
      _ = c * (A ^ q * ((m : ℝ) * (m : ℝ) ^ (2 * δ))) := by ring
  exact hmainSmall.trans_le (mul_le_mul_of_nonneg_left hrpowbase hc.le)

theorem no_eventual_cubic_log_witness
    {A c δ : ℝ} (hA : 0 < A) (hc : 0 < c) (hδ : 0 < δ)
    (hwitness : ∀ᶠ m : ℕ in atTop, ∃ N α : ℕ,
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) ≤ (N : ℝ) ∧
      α < m ∧ c * (N : ℝ) ^ ((1 : ℝ) / 3 + δ) ≤ (α : ℝ)) : False := by
  have hbeats := eventual_ramsey_lower_bound_beats_power 6 hA hc hδ
  have hmLarge : ∀ᶠ m : ℕ in atTop, 1 < (m : ℝ) := by
    exact_mod_cast (eventually_gt_atTop (1 : ℕ))
  have hfalse : ∀ᶠ _m : ℕ in atTop, False := by
    filter_upwards [hbeats, hmLarge, hwitness] with m hbeat hmLarge hw
    rcases hw with ⟨N, α, hN, hα, hclaimed⟩
    have hmpos : 0 < (m : ℝ) := lt_trans zero_lt_one hmLarge
    have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos hmLarge
    have hbasepos :
        0 < A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) := by
      positivity
    have hrpow_le :
        (A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ)) ^
            ((1 : ℝ) / 3 + δ) ≤
          (N : ℝ) ^ ((1 : ℝ) / 3 + δ) :=
      Real.rpow_le_rpow hbasepos.le hN (by positivity)
    have hm_lt_alpha_real : (m : ℝ) < (α : ℝ) :=
      hbeat.trans_le ((mul_le_mul_of_nonneg_left hrpow_le hc.le).trans hclaimed)
    have hm_lt_alpha : m < α := by exact_mod_cast hm_lt_alpha_real
    omega
  exact hfalse.exists.choose_spec

theorem eventual_counterexamples_refute_proposedBound
    {A : ℝ} (hA : 0 < A)
    (hwitness : ∀ᶠ m : ℕ in atTop, ∃ n : ℕ,
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) ∧
      ThreeColorCounterexample m n) :
    ¬ ProposedBound := by
  rintro ⟨δ, c, hδ, hc, threshold, hpower⟩
  have hbaseLargeRaw :=
    eventual_ramsey_lower_bound_beats_power 6 hA (show (0 : ℝ) < 1 by norm_num)
      (show (0 : ℝ) < 2 / 3 by norm_num)
  have hbaseLarge : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) < A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) := by
    filter_upwards [hbaseLargeRaw] with m hm
    have hexponent : (1 : ℝ) / 3 + 2 / 3 = 1 := by norm_num
    rw [hexponent, Real.rpow_one] at hm
    simpa using hm
  have hmThreshold : ∀ᶠ m : ℕ in atTop, threshold ≤ m := eventually_ge_atTop threshold
  have hnumeric : ∀ᶠ m : ℕ in atTop, ∃ n α : ℕ,
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) ∧
      α < m ∧ c * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ≤ (α : ℝ) := by
    filter_upwards [hwitness, hbaseLarge, hmThreshold] with m hw hlarge hmThreshold
    rcases hw with ⟨n, hn, hcounterexample⟩
    obtain ⟨G, hcolor, hindep⟩ := threeColorCounterexample_bridge hcounterexample
    have hm_lt_n : m < n := by exact_mod_cast hlarge.trans_le hn
    refine ⟨n, G.indepNum, hn, hindep, ?_⟩
    exact hpower n G (hmThreshold.trans hm_lt_n.le) hcolor
  exact no_eventual_cubic_log_witness hA hc hδ hnumeric

/-! ## The eventual projective counterexamples -/

/-- The checked projective `D*` construction supplies the cubic-over-log-six
family of ternary Ramsey counterexamples used in the final contradiction. -/
theorem projective_eventual_counterexamples :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ m : ℕ in atTop, ∃ n : ℕ,
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) ≤ (n : ℝ) ∧
        ThreeColorCounterexample m n := by
  let Build : Erdos920.Construction.ProjectiveBuildTheorem 1 :=
    Erdos920.Construction.projectiveBuildTheorem 1 (by omega)
  let C : ℝ := Build.C
  have hC : 0 < C := Build.C_pos
  let logTarget : ℝ := 4 * Real.exp 1 ^ 2 * C
  let Q : ℕ := max Build.qThreshold (Nat.ceil (Real.exp (logTarget + 1)))
  have hceilPos : 0 < Nat.ceil (Real.exp (logTarget + 1)) :=
    Nat.ceil_pos.mpr (Real.exp_pos _)
  have hQ : 0 < Q := hceilPos.trans_le (Nat.le_max_right _ _)
  let A : ℝ := 1 / (4 * (8 * C) ^ 3)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  have hprime := Erdos920.PrimeScale.eventually_exists_prime_scale C hC
  have hthreshold := eventually_nat_le_prime_lower_scale C hC Q hQ
  have hmTwo : ∀ᶠ m : ℕ in atTop, 2 ≤ m := eventually_ge_atTop 2
  have hbaseLargeRaw :=
    eventual_ramsey_lower_bound_beats_power 6 hA (show (0 : ℝ) < 1 by norm_num)
      (show (0 : ℝ) < 2 / 3 by norm_num)
  have hbaseLarge : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) < A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) := by
    filter_upwards [hbaseLargeRaw] with m hm
    have hexponent : (1 : ℝ) / 3 + 2 / 3 = 1 := by norm_num
    rw [hexponent, Real.rpow_one] at hm
    simpa using hm
  filter_upwards [hprime, hthreshold, hmTwo, hbaseLarge] with
    m hprime hthreshold hmTwo hbaseLarge
  rcases hprime with ⟨q, hqPrime, hqTwo, hqm, hqLower, hbudget⟩
  have hQqReal : (Q : ℝ) ≤ (q : ℝ) := hthreshold.trans hqLower
  have hQq : Q ≤ q := by exact_mod_cast hQqReal
  have hbuildThreshold : Build.qThreshold ≤ q :=
    (Nat.le_max_left _ _).trans hQq
  let _ : Fact q.Prime := ⟨hqPrime⟩
  obtain ⟨hforward, _hside, _haverage⟩ :=
    Build.build m q hqPrime hbuildThreshold hqTwo hqm hqLower hbudget
  let W : DStarWitness 2 m q C :=
    Erdos920.ConcreteWitness.ofForwardBound q 2 m C (by omega) hforward
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hceilExp : Real.exp (logTarget + 1) ≤
      (Nat.ceil (Real.exp (logTarget + 1)) : ℝ) := by
    exact_mod_cast Nat.le_ceil (Real.exp (logTarget + 1))
  have hexpLeQ : Real.exp (logTarget + 1) ≤ (Q : ℝ) :=
    hceilExp.trans (by exact_mod_cast Nat.le_max_right Build.qThreshold _)
  have hexpLeq : Real.exp (logTarget + 1) ≤ (q : ℝ) :=
    hexpLeQ.trans hQqReal
  have hlogq : logTarget + 1 ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp (logTarget + 1)]
    exact Real.log_le_log (Real.exp_pos _) hexpLeq
  have hlogTarget : 0 < logTarget := by dsimp [logTarget]; positivity
  have hlogSq : logTarget < Real.log (q : ℝ) ^ 2 := by
    have hlogqNonneg : 0 ≤ Real.log (q : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqTwo.trans' (by omega : 1 ≤ 2))
    nlinarith [sq_nonneg (Real.log (q : ℝ) - (logTarget + 1))]
  have hscale : 4 * Real.exp 1 ^ 2 * C ^ 2 * (q : ℝ) < (m : ℝ) := by
    calc
      4 * Real.exp 1 ^ 2 * C ^ 2 * (q : ℝ) =
          logTarget * (C * (q : ℝ)) := by dsimp [logTarget]; ring
      _ < Real.log (q : ℝ) ^ 2 * (C * (q : ℝ)) :=
        mul_lt_mul_of_pos_right hlogSq (mul_pos hC hqPos)
      _ = C * (q : ℝ) * Real.log (q : ℝ) ^ 2 := by ring
      _ ≤ (m : ℝ) := hbudget
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hmTwo)
  have hprimeCube :
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) ≤
        (q : ℝ) ^ 3 / 4 := by
    have hden : 0 < 8 * C * Real.log (m : ℝ) ^ 2 := by positivity
    have hscaleNonneg : 0 ≤ (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) :=
      div_nonneg (Nat.cast_nonneg _) hden.le
    have hp := pow_le_pow_left₀ hscaleNonneg hqLower 3
    calc
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) =
          ((m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2)) ^ 3 / 4 := by
        dsimp [A]
        field_simp
      _ ≤ (q : ℝ) ^ 3 / 4 := div_le_div_of_nonneg_right hp (by norm_num)
  have hcardLower :
      A * (m : ℝ) ^ (3 : ℕ) / Real.log (m : ℝ) ^ (6 : ℕ) ≤
        (@Fintype.card W.V W.fintypeV : ℝ) :=
    hprimeCube.trans W.vertex_lower
  have hmCard : m ≤ @Fintype.card W.V W.fintypeV := by
    have hlt : m < @Fintype.card W.V W.fintypeV := by
      exact_mod_cast hbaseLarge.trans_le hcardLower
    exact hlt.le
  obtain ⟨red, blue, hred, hblue, hfree, _hvertices⟩ :=
    dStarWitness_two_triangleFree_copies W hqPrime.one_le hC hmCard hscale
  let _ : Fintype W.V := W.fintypeV
  let e : W.V ≃ Fin (Fintype.card W.V) := Fintype.equivFin W.V
  let red' : SimpleGraph (Fin (Fintype.card W.V)) := red.map e.toEmbedding
  let blue' : SimpleGraph (Fin (Fintype.card W.V)) := blue.map e.toEmbedding
  have hred' : red'.CliqueFree 3 :=
    (SimpleGraph.Iso.cliqueFree_iff (SimpleGraph.Iso.map e red)).mp hred
  have hblue' : blue'.CliqueFree 3 :=
    (SimpleGraph.Iso.cliqueFree_iff (SimpleGraph.Iso.map e blue)).mp hblue
  have hfree' : (red' ⊔ blue').IndepSetFree m := by
    have hmapped : ((red ⊔ blue).map e.toEmbedding).IndepSetFree m :=
      (SimpleGraph.Iso.indepSetFree_iff (SimpleGraph.Iso.map e (red ⊔ blue))).mp hfree
    have hmapSup : (red ⊔ blue).map e.toEmbedding = red' ⊔ blue' := by
      ext x y
      change ((red ⊔ blue).map e.toEmbedding).Adj x y ↔
        (red.map e.toEmbedding).Adj x y ∨ (blue.map e.toEmbedding).Adj x y
      simp only [SimpleGraph.map_adj]
      constructor
      · rintro ⟨u, v, huv, hux, hvy⟩
        change red.Adj u v ∨ blue.Adj u v at huv
        rcases huv with huv | huv
        · exact Or.inl ⟨u, v, huv, hux, hvy⟩
        · exact Or.inr ⟨u, v, huv, hux, hvy⟩
      · rintro (⟨u, v, huv, hux, hvy⟩ | ⟨u, v, huv, hux, hvy⟩)
        · exact ⟨u, v, Or.inl huv, hux, hvy⟩
        · exact ⟨u, v, Or.inr huv, hux, hvy⟩
    rwa [hmapSup] at hmapped
  exact ⟨Fintype.card W.V, by simpa using hcardLower,
    red', blue', hred', hblue', hfree'⟩

/-! ## Resolution -/

theorem erdos_925 : ¬ ProposedBound := by
  obtain ⟨A, hA, hwitness⟩ := projective_eventual_counterexamples
  exact eventual_counterexamples_refute_proposedBound hA hwitness

#print axioms Erdos925.erdos_925

end

end Erdos925
