/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 281.
https://www.erdosproblems.com/forum/thread/281

Informal authors:
- Neel Somani
- GPT-5.2 Pro

Formal authors:
- Aristotle
- Gemini 3.0 Flash
- JakeMallen

URLs:
- https://www.erdosproblems.com/forum/thread/281#post-3445
- https://chatgpt.com/share/696ac45b-70d8-8003-9ca4-320151e0816e
-/
/-
Let $n_1 < n_2 < \cdots$ be an infinite sequence such that, for
any choice of congruence classes $a_i\pmod{n_i}$, the set of
integers not satisfying any of the congruences $a_i\pmod{n_i}$
has density $0$.

We prove that for every $\epsilon>0$ there exists some $k$ such
that, for every choice of congruence classes $a_i$, the density
of integers not satisfying any of the congruences
$a_i\pmod{n_i}$ for $1\leq i\leq k$ is less than $\epsilon$.
-/

import Mathlib

namespace Erdos281

set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.refine false
set_option linter.style.multiGoal false
set_option linter.style.emptyLine false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Filter Topology Classical

open scoped BigOperators

/- Strictly increasing sequence n₁ < n₂ < ⋯ indexed by naturals. -/
variable {n : ℕ → ℕ} (hmono : StrictMono n) (hnpos : ∀ i, 0 < n i)

/- The space of choices for residues modulo n i. -/
def Choice (n : ℕ → ℕ) := ∀ i : ℕ, ZMod (n i)

/- The set of integers m such that m mod n i avoids a i for all i < k. -/
def avoidPrefix (n : ℕ → ℕ) (a : Choice n) (k : ℕ) : Set ℤ :=
  {m | ∀ i : ℕ, i < k → (m : ZMod (n i)) ≠ a i}

/- The set of integers m such that m mod n i avoids a i for all i. -/
def avoidAll (n : ℕ → ℕ) (a : Choice n) : Set ℤ :=
  {m | ∀ i : ℕ, (m : ZMod (n i)) ≠ a i}

/-- Two-sided natural density sequence on ℤ using [-N,N]. -/
noncomputable def densSeqZ (S : Set ℤ) (N : ℕ) : ℝ :=
  (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (· ∈ S)).card : ℝ) / (2 * (N : ℝ) + 1)

/-
Period of the first k moduli.
-/
def period (n : ℕ → ℕ) (k : ℕ) : ℕ := (Finset.range k).lcm n

/- The period of the first k moduli is positive. -/
lemma period_pos (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (k : ℕ) : 0 < period n k := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by intros h; obtain ⟨ i, hi ⟩ := h; specialize hnpos i; aesop ) )

/-
Residues avoiding congruences modulo period.
-/
def avoidPrefixMod (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (k : ℕ) : Finset (ZMod (period n k)) :=
  let L := period n k
  haveI : NeZero L := ⟨ne_of_gt (period_pos n hnpos k)⟩
  Finset.univ.filter fun x => ∀ i, (hi : i < k) →
    let d : ℕ := n i
    have hd : d ∣ L := Finset.dvd_lcm (Finset.mem_range.mpr hi)
    ZMod.castHom (show d ∣ L from hd) (ZMod d) x ≠ a i

/-- Two-sided natural density exists and equals d. -/
def HasIntDensity (S : Set ℤ) (d : ℝ) : Prop :=
  Tendsto (densSeqZ S) atTop (𝓝 d)

/- The hypothesis of Erdos Problem 281. -/
def Erdos281Hyp (n : ℕ → ℕ) (_hmono : StrictMono n) (_hnpos : ∀ i, 0 < n i) : Prop :=
  ∀ a : Choice n, HasIntDensity (avoidAll n a) 0

/- The conclusion of Erdos Problem 281. -/
def Erdos281Concl (n : ℕ → ℕ) (_hmono : StrictMono n) (_hnpos : ∀ i, 0 < n i) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ k : ℕ, ∀ a : Choice n,
      ∃ d : ℝ, HasIntDensity (avoidPrefix n a k) d ∧ d < ε

/-
The profinite integers ZHat.
-/
def ZHat := { x : ∀ k : ℕ+, ZMod k | ∀ (m k : ℕ+) (h : m ∣ k), ZMod.castHom (show (m : ℕ) ∣ (k : ℕ) from PNat.dvd_iff.mp h) (ZMod m) (x k) = x m }

/-
Coercion from ZHat to the product of ZMod k.
-/
instance : Coe ZHat (∀ k : ℕ+, ZMod k) := ⟨Subtype.val⟩

/-
Topology on ZHat.
-/
instance : TopologicalSpace ZHat := TopologicalSpace.induced Subtype.val inferInstance

/-
Zero element of ZHat.
-/
instance : Zero ZHat := ⟨⟨0, by
  exact fun m k h => by simp +decide ;⟩⟩

/-
Addition and negation on ZHat.
-/
instance : Add ZHat := ⟨fun x y => ⟨x.1 + y.1, by
  intros m k h
  simp only [Pi.add_apply, map_add]
  rw [x.2 m k h, y.2 m k h]⟩⟩

instance : Neg ZHat := ⟨fun x => ⟨-x.1, by
  intros m k h
  simp only [Pi.neg_apply, map_neg]
  rw [x.2 m k h]⟩⟩

/-
Subtraction on ZHat.
-/
instance : Sub ZHat := ⟨fun x y => ⟨x.1 - y.1, by
  intros m k h
  simp only [Pi.sub_apply, map_sub]
  rw [x.2 m k h, y.2 m k h]⟩⟩

/-
Scalar multiplication on ZHat.
-/
instance : SMul ℕ ZHat := ⟨fun n x => ⟨n • x.1, by
  intros m k h
  simp only [Pi.smul_apply, map_nsmul]
  rw [x.2 m k h]⟩⟩

instance : SMul ℤ ZHat := ⟨fun n x => ⟨n • x.1, by
  intros m k h
  simp only [Pi.smul_apply, map_zsmul]
  rw [x.2 m k h]⟩⟩

/-
Additive commutative group structure on ZHat.
-/
instance : AddCommGroup ZHat :=
  { (inferInstance : Add ZHat), (inferInstance : Neg ZHat), (inferInstance : Zero ZHat) with
    sub := fun x y => ⟨x.1 - y.1, by
      intros m k h
      simp only [Pi.sub_apply, map_sub]
      rw [x.2 m k h, y.2 m k h]⟩
    nsmul := fun n x => ⟨n • x.1, by
      intros m k h
      simp only [Pi.smul_apply, map_nsmul]
      rw [x.2 m k h]⟩
    zsmul := fun n x => ⟨n • x.1, by
      intros m k h
      simp only [Pi.smul_apply, map_zsmul]
      rw [x.2 m k h]⟩
    add_assoc := by
      exact fun x y z => Subtype.ext <| add_assoc _ _ _
    zero_add := by
      simp +zetaDelta at *;
      exact fun a ha => Subtype.ext <| zero_add a
    add_zero := by
      simp +zetaDelta at *;
      exact fun a ha => Subtype.ext <| add_zero a
    neg_add_cancel := by
      simp +zetaDelta at *;
      intro a ha;
      exact Subtype.ext <| funext fun k => neg_add_cancel _
    add_comm := by
      exact fun a b => Subtype.ext <| funext fun k => add_comm _ _
    nsmul_zero := by
      aesop
    nsmul_succ := by
      intros n a; ext k; simp [add_mul]; rfl
    zsmul_zero' := by
      intros a; ext k; simp; rfl
    zsmul_succ' := by
      intros n a; ext k; simp [Nat.succ_eq_add_one, add_smul]; rfl
    zsmul_neg' := by
      simp +decide [ Int.negSucc_eq ];
      intro n a ha; congr; ext k; simp +decide [ add_mul, add_comm ] ;
    sub_eq_add_neg := by
      intro x y
      apply Subtype.ext
      funext k
      change x.1 k - y.1 k = x.1 k + - y.1 k
      rw [sub_eq_add_neg] }

/-
Compactness of ZHat.
-/
instance : CompactSpace ZHat := ⟨by
convert isCompact_univ_iff.mpr ?_;
-- Since `ZMod k` is finite, it is compact. The product of compact spaces is compact by Tychonoff's theorem.
have h_compact : IsCompact (Set.pi Set.univ fun k : ℕ+ => Set.univ : Set (∀ k : ℕ+, ZMod k)) := by
  exact isCompact_univ_pi fun k => isCompact_univ;
refine' isCompact_iff_compactSpace.mp _;
convert h_compact.of_isClosed_subset _ _;
· simp +decide [ ZHat ];
  simp +decide only [Set.setOf_forall];
  refine' isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun hij => isClosed_eq _ _;
  · fun_prop (disch := solve_by_elim);
  · exact continuous_apply i;
· aesop_cat⟩

/-
Hausdorff property of ZHat.
-/
instance : T2Space ZHat := inferInstance

/-
Continuous addition on ZHat.
-/
instance : ContinuousAdd ZHat := ⟨by
-- The projection maps are continuous, and the addition on each component is continuous. Therefore, the sum of the projections is continuous.
have h_proj_cont : ∀ k : ℕ+, Continuous (fun p : ZHat × ZHat => p.1.val k + p.2.val k) := by
  exact fun k => Continuous.add ( continuous_apply k |> Continuous.comp <| continuous_subtype_val.comp continuous_fst ) ( continuous_apply k |> Continuous.comp <| continuous_subtype_val.comp continuous_snd );
refine' Continuous.subtype_mk _ _;
exact continuous_pi_iff.mpr fun k => h_proj_cont k⟩

/-
Continuous negation on ZHat.
-/
instance : ContinuousNeg ZHat := ⟨by
  have h_proj_cont : ∀ k : ℕ+, Continuous (fun p : ZHat => -p.val k) := by
    exact fun k => Continuous.neg (Continuous.comp (continuous_apply k) continuous_subtype_val)
  refine' Continuous.subtype_mk _ _
  exact continuous_pi_iff.mpr fun k => h_proj_cont k⟩

/-
Topological group structure on ZHat.
-/
instance : IsTopologicalAddGroup ZHat := ⟨⟩

/-
Measurable structure of ZHat.
-/
instance : MeasurableSpace ZHat := borel ZHat

instance : BorelSpace ZHat := ⟨rfl⟩

/-
Normalized Haar measure on ZHat.
-/
noncomputable def haar : MeasureTheory.Measure ZHat :=
  let K : TopologicalSpace.PositiveCompacts ZHat :=
    { carrier := Set.univ
      isCompact' := isCompact_univ
      interior_nonempty' := by
        simp +decide [ Set.Nonempty ] }
  let μ := MeasureTheory.Measure.addHaarMeasure K
  (μ Set.univ)⁻¹ • μ

instance : MeasureTheory.IsFiniteMeasure haar := by
  unfold haar; infer_instance

/-
Projections and cylinders on ZHat.
-/
def proj (n : ℕ) [NeZero n] (x : ZHat) : ZMod n :=
  x.val ⟨n, NeZero.pos n⟩

def cylinder (n : ℕ) [NeZero n] (a : ZMod n) : Set ZHat :=
  {x | proj n x = a}

/-
Definitions of Ck and C.
-/
def Ck (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (k : ℕ) : Set ZHat :=
  ⋂ (i : ℕ) (_ : i < k),
    haveI : NeZero (n i) := ⟨ne_of_gt (hnpos i)⟩
    (cylinder (n i) (a i))ᶜ

def C (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) : Set ZHat :=
  ⋂ (k : ℕ), Ck n hnpos a k


/-
avoidPrefix is periodic.
-/
lemma avoidPrefix_periodic (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (k : ℕ) :
  Function.Periodic (fun m : ℤ => m ∈ avoidPrefix n a k) (period n k : ℤ) := by
    intro m; simp +decide [ avoidPrefix ] ;
    -- Since period n k is a multiple of each n i for i < k, adding period n k to m does not change the residue modulo n i.
    have h_period_mod : ∀ i < k, (m + period n k : ZMod (n i)) = m := by
      intros i hi
      have h_div : n i ∣ period n k := by
        exact Finset.dvd_lcm ( Finset.mem_range.mpr hi );
      cases h_div ; aesop;
    grind


/-
The set Ck is the preimage of the set of avoiding residues modulo the period.
-/
lemma Ck_eq_preimage (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (k : ℕ) :
  Ck n hnpos a k = {x : ZHat | @proj (period n k) ⟨ne_of_gt (period_pos n hnpos k)⟩ x ∈ avoidPrefixMod n hnpos a k} := by
    ext x
    simp only [Ck, cylinder, Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
    unfold avoidPrefixMod proj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx i hi
      have hdiv : n i ∣ period n k := Finset.dvd_lcm (Finset.mem_range.mpr hi)
      have hcompat :
          ZMod.castHom hdiv (ZMod (n i)) (x.val ⟨period n k, period_pos n hnpos k⟩) =
            x.val ⟨n i, hnpos i⟩ := by
        simpa only [PNat.dvd_iff] using
          x.property ⟨n i, hnpos i⟩ ⟨period n k, period_pos n hnpos k⟩
            (PNat.dvd_iff.mpr hdiv)
      intro h
      exact hx i hi (by simpa [hcompat] using h)
    · intro hx i hi
      have hdiv : n i ∣ period n k := Finset.dvd_lcm (Finset.mem_range.mpr hi)
      have hcompat :
          ZMod.castHom hdiv (ZMod (n i)) (x.val ⟨period n k, period_pos n hnpos k⟩) =
            x.val ⟨n i, hnpos i⟩ := by
        simpa only [PNat.dvd_iff] using
          x.property ⟨n i, hnpos i⟩ ⟨period n k, period_pos n hnpos k⟩
            (PNat.dvd_iff.mpr hdiv)
      intro h
      exact hx i hi (by simpa [hcompat] using h)

private def negSuccIntEmbedding : ℕ ↪ ℤ where
  toFun t := -(((t + 1 : ℕ) : ℤ))
  inj' := by
    intro a b h
    simp at h
    omega

private lemma int_Icc_neg_eq_negSucc_union_cast (N : ℕ) :
    Finset.Icc (-(N : ℤ)) (N : ℤ) =
      (Finset.range N).map negSuccIntEmbedding ∪
        (Finset.range (N + 1)).map Nat.castEmbedding := by
  ext z
  constructor
  · intro hz
    rw [Finset.mem_Icc] at hz
    rw [Finset.mem_union]
    by_cases hzneg : z < 0
    · left
      refine Finset.mem_map.mpr ⟨((-z - 1).toNat), ?_, ?_⟩
      · simp
        have hcast : ((-z).toNat : ℤ) = -z := by
          rw [Int.toNat_of_nonneg]
          omega
        omega
      · simp [negSuccIntEmbedding]
        have hcast : ((-z).toNat : ℤ) = -z := by
          rw [Int.toNat_of_nonneg]
          omega
        omega
    · right
      refine Finset.mem_map.mpr ⟨z.toNat, ?_, ?_⟩
      · simp
        omega
      · simp
        omega
  · intro hz
    rw [Finset.mem_union] at hz
    rw [Finset.mem_Icc]
    rcases hz with hz | hz
    · rcases Finset.mem_map.mp hz with ⟨t, ht, rfl⟩
      simp [negSuccIntEmbedding] at ht ⊢
      omega
    · rcases Finset.mem_map.mp hz with ⟨t, ht, rfl⟩
      simp at ht
      change -(N : ℤ) ≤ (t : ℤ) ∧ (t : ℤ) ≤ (N : ℤ)
      omega

private lemma abs_count_sub_mul_div_le_of_bounds {q M L c count : ℝ}
    (hL : 0 < L) (hc0 : 0 ≤ c) (hcL : c ≤ L)
    (hqle : q * L ≤ M) (hMlt : M < (q + 1) * L)
    (hlow : q * c ≤ count) (hup : count ≤ (q + 1) * c) :
    |count - M * c / L| ≤ L := by
  rw [abs_sub_le_iff]
  constructor
  · have hqc_le : q * c ≤ M * c / L := by
      have hq_le_div : q ≤ M / L := (le_div_iff₀ hL).2 hqle
      have hq_c := mul_le_mul_of_nonneg_right hq_le_div hc0
      convert hq_c using 1
      ring
    have hcount_le : count ≤ M * c / L + L := by nlinarith
    linarith
  · have hM_le : M ≤ (q + 1) * L := le_of_lt hMlt
    have hM_sub_le : M - L ≤ q * L := by nlinarith
    have hleft_le : M * c / L - L ≤ q * c := by
      have haux : (M - L) * c / L ≤ q * c := by
        have hdiv_le : (M - L) / L ≤ q := (div_le_iff₀ hL).2 hM_sub_le
        have hmul := mul_le_mul_of_nonneg_right hdiv_le hc0
        convert hmul using 1
        ring
      have hleft_aux : M * c / L - L ≤ (M - L) * c / L := by
        have hrewrite : (M - L) * c / L = M * c / L - c := by
          field_simp [hL.ne']
        rw [hrewrite]
        linarith
      exact hleft_aux.trans haux
    have hcount_ge : M * c / L - L ≤ count := by nlinarith
    linarith

private lemma periodic_nat_count_mul (p : ℕ → Prop) [DecidablePred p] (L : ℕ)
    (hp : Function.Periodic p L) :
    ∀ q, ((Finset.range (q * L)).filter p).card =
      q * ((Finset.range L).filter p).card := by
  intro q
  induction q with
  | zero =>
      simp
  | succ q ih =>
      rw [Nat.succ_mul]
      rw [Finset.range_add_eq_union]
      rw [Finset.filter_union]
      rw [Finset.card_union_of_disjoint]
      · rw [ih]
        have hblock := Nat.filter_Ico_card_eq_of_periodic (q * L) L p hp
        have hmap_set :
            (Finset.range L).map (addLeftEmbedding (q * L)) =
              Finset.Ico (q * L) (q * L + L) := by
          ext x
          constructor
          · intro hx
            rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
            simp [Finset.mem_Ico] at hy ⊢
            omega
          · intro hx
            simp [Finset.mem_Ico] at hx
            refine Finset.mem_map.mpr ⟨x - q * L, ?_, ?_⟩
            · simp
              omega
            · simp
              omega
        rw [hmap_set, hblock, Nat.count_eq_card_filter_range]
        ring
      · simp [Finset.disjoint_left]
        intro x hx hxl
        omega

private lemma periodic_nat_count_error (p : ℕ → Prop) [DecidablePred p]
    (L : ℕ) (hL : 0 < L) (hp : Function.Periodic p L) (M : ℕ) :
    |(((Finset.range M).filter p).card : ℝ) -
        (M : ℝ) * (((Finset.range L).filter p).card : ℝ) / (L : ℝ)| ≤ (L : ℝ) := by
  let c := ((Finset.range L).filter p).card
  let q := M / L
  let count := ((Finset.range M).filter p).card
  have hmul := periodic_nat_count_mul p L hp
  have hqL_le : q * L ≤ M := by
    exact Nat.div_mul_le_self M L
  have hM_lt_succ : M < (q + 1) * L := by
    simpa [q, mul_comm] using Nat.lt_mul_div_succ M hL
  have hsubset_low : Finset.range (q * L) ⊆ Finset.range M := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hqL_le)
  have hsubset_high : Finset.range M ⊆ Finset.range ((q + 1) * L) := by
    intro x hx
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (le_of_lt hM_lt_succ))
  have hlow_nat : q * c ≤ count := by
    dsimp [count, c]
    rw [← hmul q]
    exact Finset.card_le_card (Finset.filter_subset_filter p hsubset_low)
  have hup_nat : count ≤ (q + 1) * c := by
    dsimp [count, c]
    calc
      ((Finset.range M).filter p).card ≤
          ((Finset.range ((q + 1) * L)).filter p).card :=
        Finset.card_le_card (Finset.filter_subset_filter p hsubset_high)
      _ = (q + 1) * ((Finset.range L).filter p).card := hmul (q + 1)
  have hc_le_L : c ≤ L := by
    simpa using Finset.card_filter_le (Finset.range L) p
  have hL_real : (0 : ℝ) < L := by exact_mod_cast hL
  have hqle_real : (q : ℝ) * (L : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqL_le
  have hMlt_real : (M : ℝ) < ((q : ℝ) + 1) * (L : ℝ) := by
    exact_mod_cast hM_lt_succ
  have hlow_real : (q : ℝ) * (c : ℝ) ≤ (count : ℝ) := by exact_mod_cast hlow_nat
  have hup_real : (count : ℝ) ≤ ((q : ℝ) + 1) * (c : ℝ) := by exact_mod_cast hup_nat
  have hc0_real : (0 : ℝ) ≤ c := by positivity
  have hcL_real : (c : ℝ) ≤ L := by exact_mod_cast hc_le_L
  simpa [c, count] using
    abs_count_sub_mul_div_le_of_bounds hL_real hc0_real hcL_real
      hqle_real hMlt_real hlow_real hup_real

/-
A periodic set has a natural density equal to the proportion of elements in one period.
-/
lemma dens_periodic (S : Set ℤ) (L : ℕ) (hL : 0 < L) (hper : ∀ n, n ∈ S ↔ n + L ∈ S) :
  HasIntDensity S (((Finset.range L).filter (fun x : ℕ => (x : ℤ) ∈ S)).card / L) := by
  classical
  let c := ((Finset.range L).filter (fun x : ℕ => (x : ℤ) ∈ S)).card
  let ppos : ℕ → Prop := fun t => (t : ℤ) ∈ S
  let pneg : ℕ → Prop := fun t => -(((t + 1 : ℕ) : ℤ)) ∈ S
  have hppos : Function.Periodic ppos L := by
    intro t
    apply propext
    simpa [ppos, add_comm, add_left_comm, add_assoc] using (hper (t : ℤ)).symm
  have hpneg : Function.Periodic pneg L := by
    intro t
    apply propext
    have h := hper (-(((((t + L) + 1 : ℕ) : ℤ))))
    have hshift : -(((((t + L) + 1 : ℕ) : ℤ))) + (L : ℤ) =
        -(((t + 1 : ℕ) : ℤ)) := by
      omega
    rw [hshift] at h
    simpa [pneg] using h
  have hneg_period_count : ((Finset.range L).filter pneg).card = c := by
    refine Finset.card_bij (fun t _ => L - 1 - t) ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨htL, htS⟩
      have ht_lt : t < L := Finset.mem_range.mp htL
      have ht_succ_le : t + 1 ≤ L := Nat.succ_le_of_lt ht_lt
      have hmap_lt : L - 1 - t < L := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmap_lt, ?_⟩
      have hshift : -(((t + 1 : ℕ) : ℤ)) + (L : ℤ) = ((L - 1 - t : ℕ) : ℤ) := by
        omega
      have hs' := (hper (-(((t + 1 : ℕ) : ℤ)))).1 htS
      rw [hshift] at hs'
      simpa [ppos] using hs'
    · intro t₁ ht₁ t₂ ht₂ h_eq
      have ht₁_lt : t₁ < L := Finset.mem_range.mp (Finset.mem_filter.mp ht₁).1
      have ht₂_lt : t₂ < L := Finset.mem_range.mp (Finset.mem_filter.mp ht₂).1
      change L - 1 - t₁ = L - 1 - t₂ at h_eq
      omega
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyL, hyS⟩
      refine ⟨L - 1 - y, ?_, ?_⟩
      · have hy_lt : y < L := Finset.mem_range.mp hyL
        have hy_succ_le : y + 1 ≤ L := Nat.succ_le_of_lt hy_lt
        have hpre_lt : L - 1 - y < L := by omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpre_lt, ?_⟩
        have hshift : -((((L - 1 - y) + 1 : ℕ) : ℤ)) + (L : ℤ) = (y : ℤ) := by
          omega
        have hyS' : -((((L - 1 - y) + 1 : ℕ) : ℤ)) + (L : ℤ) ∈ S := by
          rw [hshift]
          simpa [ppos] using hyS
        exact (hper (-((((L - 1 - y) + 1 : ℕ) : ℤ)))).2 hyS'
      · have hy_lt : y < L := Finset.mem_range.mp hyL
        change L - 1 - (L - 1 - y) = y
        omega
  have hpos_error (M : ℕ) :
      |(((Finset.range M).filter ppos).card : ℝ) -
          (M : ℝ) * (c : ℝ) / (L : ℝ)| ≤ (L : ℝ) := by
    simpa [c, ppos] using periodic_nat_count_error ppos L hL hppos M
  have hneg_error (M : ℕ) :
      |(((Finset.range M).filter pneg).card : ℝ) -
          (M : ℝ) * (c : ℝ) / (L : ℝ)| ≤ (L : ℝ) := by
    simpa [hneg_period_count] using periodic_nat_count_error pneg L hL hpneg M
  have hsplit_count (N : ℕ) :
      ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun z : ℤ => z ∈ S)).card =
        ((Finset.range N).filter pneg).card +
          ((Finset.range (N + 1)).filter ppos).card := by
    rw [int_Icc_neg_eq_negSucc_union_cast N]
    rw [Finset.filter_union]
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.filter_map, Finset.filter_map, Finset.card_map, Finset.card_map]
      simp only [Function.comp_def, pneg, ppos, negSuccIntEmbedding]
      rfl
    · rw [Finset.disjoint_left]
      intro z hzneg hzpos
      rcases Finset.mem_filter.mp hzneg with ⟨hzneg_map, _⟩
      rcases Finset.mem_filter.mp hzpos with ⟨hzpos_map, _⟩
      rcases Finset.mem_map.mp hzneg_map with ⟨t, ht, htz⟩
      rcases Finset.mem_map.mp hzpos_map with ⟨u, hu, huz⟩
      simp [negSuccIntEmbedding] at ht hu htz huz
      omega
  change Tendsto (densSeqZ S) atTop (𝓝 ((c : ℝ) / (L : ℝ)))
  have hbound (N : ℕ) :
      |densSeqZ S N - (c : ℝ) / (L : ℝ)| ≤
        (2 * (L : ℝ)) / (2 * (N : ℝ) + 1) := by
    let A : ℝ := (((Finset.range N).filter pneg).card : ℝ)
    let B : ℝ := (((Finset.range (N + 1)).filter ppos).card : ℝ)
    let D : ℝ := 2 * (N : ℝ) + 1
    have hDpos : 0 < D := by
      dsimp [D]
      positivity
    have hA : |A - (N : ℝ) * (c : ℝ) / (L : ℝ)| ≤ (L : ℝ) := by
      simpa [A] using hneg_error N
    have hB : |B - ((N + 1 : ℕ) : ℝ) * (c : ℝ) / (L : ℝ)| ≤ (L : ℝ) := by
      simpa [B] using hpos_error (N + 1)
    have hsum :
        |(A + B) - D * (c : ℝ) / (L : ℝ)| ≤ 2 * (L : ℝ) := by
      have hrewrite :
          (A + B) - D * (c : ℝ) / (L : ℝ) =
            (A - (N : ℝ) * (c : ℝ) / (L : ℝ)) +
              (B - ((N + 1 : ℕ) : ℝ) * (c : ℝ) / (L : ℝ)) := by
        dsimp [D]
        norm_num
        ring
      rw [hrewrite]
      calc
        |(A - (N : ℝ) * (c : ℝ) / (L : ℝ)) +
            (B - ((N + 1 : ℕ) : ℝ) * (c : ℝ) / (L : ℝ))|
            ≤ |A - (N : ℝ) * (c : ℝ) / (L : ℝ)| +
                |B - ((N + 1 : ℕ) : ℝ) * (c : ℝ) / (L : ℝ)| := abs_add_le _ _
        _ ≤ (L : ℝ) + (L : ℝ) := add_le_add hA hB
        _ = 2 * (L : ℝ) := by ring
    have hdens_eq : densSeqZ S N = (A + B) / D := by
      unfold densSeqZ
      rw [hsplit_count N]
      dsimp [A, B, D]
      norm_num
    rw [hdens_eq]
    have hdiff :
        (A + B) / D - (c : ℝ) / (L : ℝ) =
          ((A + B) - D * (c : ℝ) / (L : ℝ)) / D := by
      field_simp [hDpos.ne']
    rw [hdiff, abs_div, abs_of_pos hDpos]
    simpa [D] using div_le_div_of_nonneg_right hsum (le_of_lt hDpos)
  have hbound_tendsto :
      Tendsto (fun N : ℕ => (2 * (L : ℝ)) / (2 * (N : ℝ) + 1)) atTop (𝓝 0) := by
    have hden_nat : Tendsto (fun N : ℕ => 2 * N + 1) atTop atTop :=
      tendsto_atTop_mono (fun N => by omega : ∀ N : ℕ, N ≤ 2 * N + 1) tendsto_id
    have hconst :
        Tendsto (fun M : ℕ => (2 * (L : ℝ)) / (M : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (2 * (L : ℝ))
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using hconst.comp hden_nat
  have habs_tendsto :
      Tendsto (fun N : ℕ => |densSeqZ S N - (c : ℝ) / (L : ℝ)|) atTop (𝓝 0) :=
    squeeze_zero (fun N => abs_nonneg _) hbound hbound_tendsto
  have hdiff_tendsto :
      Tendsto (fun N : ℕ => densSeqZ S N - (c : ℝ) / (L : ℝ)) atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 habs_tendsto
  simpa [sub_eq_add_neg, add_assoc] using hdiff_tendsto.add_const ((c : ℝ) / (L : ℝ))

/-
  The number of avoiding integers in one period equals the number of avoiding residues.
  -/
lemma card_avoidPrefix_inter_range_eq_card_avoidPrefixMod (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (k : ℕ) :
  ((Finset.range (period n k)).filter (fun m : ℕ => (m : ℤ) ∈ avoidPrefix n a k)).card = (avoidPrefixMod n hnpos a k).card := by
    classical
    let L := period n k
    have hLpos : 0 < L := period_pos n hnpos k
    haveI : NeZero L := ⟨ne_of_gt hLpos⟩
    have hmem_iff (m : ℕ) (hm : m < L) :
        (m : ℤ) ∈ avoidPrefix n a k ↔ (m : ZMod L) ∈ avoidPrefixMod n hnpos a k := by
      simp only [avoidPrefix, avoidPrefixMod, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · intro hm_avoid i hi
        have hdiv : n i ∣ L := by
          simpa [L, period] using Finset.dvd_lcm (Finset.mem_range.mpr hi : i ∈ Finset.range k)
        intro h
        exact hm_avoid i hi (by simpa [ZMod.cast_natCast] using h)
      · intro hm_avoid i hi
        have hdiv : n i ∣ L := by
          simpa [L, period] using Finset.dvd_lcm (Finset.mem_range.mpr hi : i ∈ Finset.range k)
        exact by
          simpa [ZMod.cast_natCast] using hm_avoid i hi
    refine Finset.card_bij (fun m _ => (m : ZMod L)) ?_ ?_ ?_
    · intro m hm
      rcases Finset.mem_filter.mp hm with ⟨hm_range, hm_avoid⟩
      exact (hmem_iff m (Finset.mem_range.mp hm_range)).1 hm_avoid
    · intro m₁ hm₁ m₂ hm₂ h_eq
      rcases Finset.mem_filter.mp hm₁ with ⟨hm₁_range, _⟩
      rcases Finset.mem_filter.mp hm₂ with ⟨hm₂_range, _⟩
      have hval := congr_arg ZMod.val h_eq
      have hm₁_val : (m₁ : ZMod L).val = m₁ := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hm₁_range)]
      have hm₂_val : (m₂ : ZMod L).val = m₂ := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hm₂_range)]
      simpa [hm₁_val, hm₂_val] using hval
    · intro x hx
      refine ⟨x.val, ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr x.val_lt,
            (hmem_iff x.val x.val_lt).2 (by simpa using hx)⟩
      · exact ZMod.natCast_zmod_val x

/-
The natural density of the avoiding set is the proportion of avoiding residues in one period.
-/
instance : MeasureTheory.Measure.IsAddHaarMeasure haar where
  toIsFiniteMeasureOnCompacts := by unfold haar; infer_instance
  toIsAddLeftInvariant := by unfold haar; infer_instance
  toIsOpenPosMeasure := by
    unfold haar
    apply MeasureTheory.Measure.isOpenPosMeasure_smul
    · simp;

/-
The pushforward of the Haar measure to a finite quotient is an additive Haar measure.
-/
lemma map_proj_haar_is_add_haar (m : ℕ) [NeZero m] :
  MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.Measure.map (proj m) haar) := by
    -- The projection map `proj m` is continuous.
    have h_proj_cont : Continuous (proj m) := by
      exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val;
    have h_proj_surj : Function.Surjective (proj m) := by
      intro x
      obtain ⟨y, hy⟩ : ∃ y : ℕ, (y : ZMod m) = x := by
        exact ⟨ x.val, by simp +decide ⟩;
      use ⟨fun k => (y : ZMod k), by
        exact fun m k h => by aesop;⟩
      generalize_proofs at *;
      aesop;
    have h_proj_hom : ∀ x y : ZHat, proj m (x + y) = proj m x + proj m y := by
      aesop;
    have h_pushforward_add_haar : ∀ (μ : MeasureTheory.Measure ZHat), MeasureTheory.Measure.IsAddHaarMeasure μ → MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.Measure.map (proj m) μ) := by
      intro μ hμ;
      refine' { .. };
      · intro g;
        ext s hs;
        rw [ MeasureTheory.Measure.map_apply ];
        · rw [ MeasureTheory.Measure.map_apply, MeasureTheory.Measure.map_apply ];
          · -- Since proj m is surjective, there exists some x in ZHat such that proj m x = g.
            obtain ⟨x, hx⟩ : ∃ x : ZHat, proj m x = g := by
              exact h_proj_surj g;
            -- Since proj m is a homomorphism, we have proj m (x + y) = proj m x + proj m y.
            have h_hom : ∀ y : ZHat, proj m (x + y) = proj m x + proj m y := by
              exact fun y => h_proj_hom x y;
            rw [ show ( proj m ⁻¹' ( ( fun x => g + x ) ⁻¹' s ) ) = ( fun y => x + y ) ⁻¹' ( proj m ⁻¹' s ) by ext y; simp [hx, h_hom] ];
            exact MeasureTheory.measure_preimage_add _ _ _;
          · exact h_proj_cont.measurable;
          · exact hs;
          · exact h_proj_cont.measurable;
          · exact hs.preimage (measurable_const.add measurable_id);
        · exact measurable_const.add measurable_id;
        · exact hs;
      · intro U hU hU_nonempty
        have h_preimage_nonempty : (proj m ⁻¹' U).Nonempty := by
          exact hU_nonempty.elim fun x hx => by obtain ⟨ y, rfl ⟩ := h_proj_surj x; exact ⟨ y, hx ⟩ ;
        rw [ MeasureTheory.Measure.map_apply ];
        · have h_preimage_open : IsOpen (proj m ⁻¹' U) := by
            exact h_proj_cont.isOpen_preimage _ hU;
          exact IsOpen.measure_ne_zero _ h_preimage_open h_preimage_nonempty;
        · exact h_proj_cont.measurable;
        · exact hU.measurableSet;
    exact h_pushforward_add_haar _ (by
    unfold haar;
    constructor)

/-
The pushforward of the Haar measure to a finite quotient is the normalized counting measure.
-/
lemma map_proj_haar_eq_normalized_count (m : ℕ) [NeZero m] :
  MeasureTheory.Measure.map (proj m) haar = (m : ENNReal)⁻¹ • MeasureTheory.Measure.count := by
    classical
    let μp : MeasureTheory.Measure (ZMod m) := MeasureTheory.Measure.map (proj m) haar
    let ν : MeasureTheory.Measure (ZMod m) := (m : ENNReal)⁻¹ • MeasureTheory.Measure.count
    let K : TopologicalSpace.PositiveCompacts (ZMod m) :=
      { carrier := Set.univ
        isCompact' := isCompact_univ
        interior_nonempty' := by
          simp [Set.Nonempty] }
    haveI : MeasureTheory.Measure.IsAddHaarMeasure μp := by
      dsimp [μp]
      exact map_proj_haar_is_add_haar m
    haveI : MeasureTheory.Measure.IsAddLeftInvariant ν := by
      dsimp [ν]
      infer_instance
    haveI : MeasureTheory.IsFiniteMeasure ν := by
      dsimp [ν]
      exact MeasureTheory.Measure.smul_finite MeasureTheory.Measure.count
        (ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne m))
    haveI : MeasureTheory.SigmaFinite ν := inferInstance
    have h_proj_cont : Continuous (proj m) := by
      exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val
    have h_haar_univ : haar (Set.univ : Set ZHat) = 1 := by
      unfold haar
      simp
    have hμp_univ : μp (Set.univ : Set (ZMod m)) = 1 := by
      dsimp [μp]
      rw [MeasureTheory.Measure.map_apply]
      · simpa using h_haar_univ
      · exact h_proj_cont.measurable
      · exact MeasurableSet.univ
    have hν_univ : ν (Set.univ : Set (ZMod m)) = 1 := by
      dsimp [ν]
      have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne m
      have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
      simpa [MeasureTheory.Measure.count_apply, ZMod.card] using
        ENNReal.inv_mul_cancel hm0 hmtop
    calc
      μp = μp K • MeasureTheory.Measure.addHaarMeasure K :=
        MeasureTheory.Measure.addHaarMeasure_unique μp K
      _ = ν K • MeasureTheory.Measure.addHaarMeasure K := by simp [K, hμp_univ, hν_univ]
      _ = ν := (MeasureTheory.Measure.addHaarMeasure_unique ν K).symm

/-
The Haar measure of the preimage of a set in a finite quotient is the normalized cardinality of the set.
-/
lemma haar_preimage_proj_eq_card_div (m : ℕ) [NeZero m] (S : Set (ZMod m)) :
  haar {x : ZHat | proj m x ∈ S} = S.toFinset.card / m := by
    classical
    have h_proj_cont : Continuous (proj m) := by
      exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val
    have hS : MeasurableSet S := S.to_countable.measurableSet
    have h :=
      congr_arg (fun μ : MeasureTheory.Measure (ZMod m) => μ S)
        (map_proj_haar_eq_normalized_count m)
    change (MeasureTheory.Measure.map (proj m) haar) S =
      ((m : ENNReal)⁻¹ • MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod m)) S at h
    rw [MeasureTheory.Measure.map_apply h_proj_cont.measurable hS] at h
    calc
      haar {x : ZHat | proj m x ∈ S}
          = ((m : ENNReal)⁻¹ • MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod m)) S := h
      _ = S.toFinset.card / m := by
        rw [MeasureTheory.Measure.smul_apply]
        rw [MeasureTheory.Measure.count_apply hS]
        rw [div_eq_mul_inv]
        rw [mul_comm (S.toFinset.card : ENNReal) (m : ENNReal)⁻¹]
        congr 1
        exact_mod_cast (Set.encard_eq_coe_toFinset_card S)

/-
The natural density of the set of integers avoiding the first k congruences is equal to the Haar measure of the corresponding set in the profinite integers.
-/
theorem finite_density_haarmeasure (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (k : ℕ) :
  HasIntDensity (avoidPrefix n a k) (haar (Ck n hnpos a k)).toReal := by
    have h_haar_val : (haar (Ck n hnpos a k)).toReal = (avoidPrefixMod n hnpos a k).card / (period n k : ℝ) := by
      rw [ Ck_eq_preimage n hnpos a k ]
      haveI : NeZero (period n k) := ⟨ne_of_gt (period_pos n hnpos k)⟩
      erw [ haar_preimage_proj_eq_card_div (period n k) (avoidPrefixMod n hnpos a k : Set _) ]
      rw [ ENNReal.toReal_div ]
      norm_cast; congr!; ext; simp
    rw [ h_haar_val ]
    have h_dens := dens_periodic (avoidPrefix n a k) (period n k) (period_pos n hnpos k) (fun m => Iff.of_eq (avoidPrefix_periodic n hnpos a k m).symm)
    rw [ card_avoidPrefix_inter_range_eq_card_avoidPrefixMod n hnpos a k ] at h_dens
    exact h_dens

/-
Integers can be cast to profinite integers.
-/
instance : IntCast ZHat where
  intCast n := ⟨fun k => (n : ZMod k), fun _ _ _ => by simp⟩

/-
Define a shifted choice of residues by subtracting the projection of x from a.
-/
def shiftChoice (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (x : ZHat) : Choice n :=
  fun i =>
    haveI : NeZero (n i) := ⟨ne_of_gt (hnpos i)⟩
    a i - proj (n i) x

/-
An integer m is in the avoidance set for the shifted choice iff x + m is in the avoidance set for the original choice.
-/
lemma mem_avoidAll_shift_iff (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (x : ZHat) (m : ℤ) :
  m ∈ avoidAll n (shiftChoice n hnpos a x) ↔ x + (m : ZHat) ∈ C n hnpos a := by
    unfold C;
    unfold Ck avoidAll;
    simp +decide [ shiftChoice, cylinder ];
    constructor;
    · intro h i j hj; have := h j; simp_all +decide [ proj ] ;
      exact fun h' => h j <| by simpa [ sub_eq_iff_eq_add ] using eq_sub_of_add_eq' h';
    · intro h i hi; specialize h ( i + 1 ) i; simp_all +decide [ eq_sub_iff_add_eq, add_comm ] ;
      exact h ( by simpa [ proj ] using hi )

/-
The integral of the density sequence of the shifted set is equal to the Haar measure of the set.
-/
lemma integral_densSeq_eq_haar (S : Set ZHat) (hS : MeasurableSet S) (N : ℕ) :
  ∫ x, densSeqZ {m : ℤ | x + (m : ZHat) ∈ S} N ∂haar = (haar S).toReal := by
    unfold densSeqZ
    rw [MeasureTheory.integral_div]
    simp_rw [Finset.card_filter, Set.mem_setOf_eq]
    push_cast
    rw [MeasureTheory.integral_finset_sum]
    · have h_inv (m : ℤ) : ∫ x : ZHat, (if x + ↑m ∈ S then (1 : ℝ) else 0) ∂haar = (haar S).toReal := by
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by rw [add_comm]))]
        rw [MeasureTheory.integral_add_left_eq_self (fun x => if x ∈ S then (1 : ℝ) else 0) (m : ZHat)]
        exact MeasureTheory.integral_indicator_one hS
      simp_rw [h_inv, Finset.sum_const, nsmul_eq_mul]
      have h_card : (Finset.Icc (-N : ℤ) N).card = 2 * N + 1 := by
        simp [Int.card_Icc, sub_neg_eq_add]; norm_cast; ring
      rw [h_card]; push_cast
      have h_div : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
      field_simp [h_div];
    · intro m _
      apply MeasureTheory.Integrable.indicator (MeasureTheory.integrable_const 1)
      exact hS.preimage (continuous_add_const _ |>.measurable)

/-
If the set of return times to S has density 0 for every starting point, then S has Haar measure 0.
-/
lemma haar_zero_of_null_density (S : Set ZHat) (hS : MeasurableSet S)
  (h_null : ∀ x : ZHat, HasIntDensity {m : ℤ | x + (m : ZHat) ∈ S} 0) : haar S = 0 := by
    -- By definition of HasIntDensity, we know that the limit of the integral of densities is the integral of the limit.
    have h_integral : Filter.Tendsto (fun N : ℕ => ∫ x, densSeqZ (fun m => x + (m : ZHat) ∈ S) N ∂haar) Filter.atTop (𝓝 0) := by
      convert MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _;
      rotate_left;
      use fun x => 0;
      use fun x => 1;
      · intro n;
        refine' Measurable.aestronglyMeasurable _;
        refine' Measurable.div_const _ _;
        refine' Measurable.comp ( show Measurable ( fun x : ℕ => ( x : ℝ ) ) from by measurability ) _;
        simp +decide only [Finset.card_filter];
        refine' Finset.measurable_sum _ fun i hi => _;
        refine' Measurable.ite _ measurable_const measurable_const;
        exact hS.preimage ( show Measurable ( fun x : ZHat => x + ( i : ZHat ) ) from measurable_id.add_const _ );
      · norm_num +zetaDelta at *;
      · intro N; filter_upwards [ ] with x; rw [ Real.norm_of_nonneg ];
        · refine' div_le_one_of_le₀ _ _ <;> norm_cast <;> norm_num;
          exact le_trans ( Finset.card_filter_le _ _ ) ( by norm_num; linarith );
        · exact div_nonneg ( Nat.cast_nonneg _ ) ( by positivity );
      · exact Filter.Eventually.of_forall fun x => h_null x;
      · norm_num;
    contrapose! h_integral;
    -- By Lemma 25, the integral of the density sequence of the shifted set is equal to the Haar measure of the set.
    have h_integral_eq : ∀ N : ℕ, ∫ x, densSeqZ (fun m => x + (m : ZHat) ∈ S) N ∂haar = (haar S).toReal := by
      exact fun N => integral_densSeq_eq_haar S hS N;
    simp_all +decide [ ENNReal.toReal_ne_zero ]

/-
The set Ck is measurable.
-/
lemma measurable_Ck (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) (k : ℕ) :
  MeasurableSet (Ck n hnpos a k) := by
    refine' MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi => _;
    refine' MeasurableSet.compl _;
    -- The projection map is continuous, hence the preimage of a closed set under a continuous map is closed.
    have h_proj_cont : Continuous (fun x : ZHat => x.val ⟨n i, hnpos i⟩) := by
      exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val;
    exact h_proj_cont.measurable ( MeasurableSingletonClass.measurableSet_singleton _ )

/-
The set C is measurable.
-/
lemma measurable_C (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (a : Choice n) :
  MeasurableSet (C n hnpos a) := by
    exact MeasurableSet.iInter fun k => measurable_Ck n hnpos a k

/-
If the hypothesis holds, then the Haar measure of the avoidance set is 0.
-/
lemma haar_zero_from_density_zero (n : ℕ → ℕ) (hmono : StrictMono n) (hnpos : ∀ i, 0 < n i)
    (h : Erdos281Hyp n hmono hnpos) (a : Choice n) :
  haar (C n hnpos a) = 0 := by
    apply haar_zero_of_null_density
    · exact measurable_C n hnpos a
    · intro x
      -- We use .symm because the lemma has (shifted ∈ avoidAll ↔ x + m ∈ C)
      -- but convert wants (x + m ∈ C ↔ shifted ∈ avoidAll)
      convert h (shiftChoice n hnpos a x) using 1
      ext m
      exact (mem_avoidAll_shift_iff n hnpos a x m).symm

/-
The sequence of Haar measures of the finite avoidance sets converges to 0.
-/
lemma pointwise_convergence (n : ℕ → ℕ) (hmono : StrictMono n) (hnpos : ∀ i, 0 < n i)
    (h : Erdos281Hyp n hmono hnpos) (a : Choice n) :
  Tendsto (fun k => haar (Ck n hnpos a k)) atTop (𝓝 0) := by
    -- 1. Continuity of measure from above for a decreasing sequence of sets.
    have h_measure : Tendsto (fun k => haar (Ck n hnpos a k)) atTop (𝓝 (haar (⋂ k, Ck n hnpos a k))) := by
      -- Prove Ck is antitone (decreasing)
      have h_decreasing : Antitone (fun k => Ck n hnpos a k) := by
        intro k l hkl
        simp only [Ck, Set.le_eq_subset]
        exact Set.biInter_subset_biInter_left (fun i hi => (Nat.lt_of_lt_of_le hi hkl))
      -- Apply the theorem and provide arguments in the correct order
      apply MeasureTheory.tendsto_measure_iInter_atTop
      · exact fun k => (measurable_Ck n hnpos a k).nullMeasurableSet
      · exact h_decreasing
      · -- The finiteness of the measure
        use 0
        exact MeasureTheory.measure_ne_top haar _
    -- 2. Link the intersection to the set C, which has measure 0.
    have h_haar_zero : haar (⋂ k, Ck n hnpos a k) = 0 := by
      change haar (C n hnpos a) = 0
      exact haar_zero_from_density_zero n hmono hnpos h a
    -- 3. Conclusion
    rw [h_haar_zero] at h_measure
    exact h_measure

/-
Define the function fk(a) = haar(Ck(a)).
-/
noncomputable def fk (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (k : ℕ) : Choice n → ℝ :=
  fun a => (haar (Ck n hnpos a k)).toReal

/-
The space of choices is a topological space (product topology).
-/
instance (n : ℕ → ℕ) : TopologicalSpace (Choice n) := Pi.topologicalSpace

/-
The function fk is continuous.
-/
lemma continuous_fk (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) (k : ℕ) :
  Continuous (fk n hnpos k) := by
    refine' continuous_iff_continuousAt.mpr _;
    intro a;
    -- The projection to the first k coordinates is continuous.
    have h_proj_cont : ContinuousAt (fun a : Choice n => fun i : Fin k => a i) a := by
      exact continuousAt_pi.2 fun i => continuousAt_apply _ _;
    -- The measure function on the finite quotient is continuous (since the space is discrete).
    have h_measure_cont : Continuous (fun a : ∀ i : Fin k, ZMod (n i) => (haar {x : ZHat | ∀ i : Fin k, @proj (n i) ⟨ne_of_gt (hnpos i)⟩ x ≠ a i}).toReal) := by
      refine' continuous_of_discreteTopology;
    convert h_measure_cont.continuousAt.comp h_proj_cont using 1;
    ext; simp [fk, Ck];
    congr with x ; simp +decide [ cylinder ];
    exact ⟨ fun h i => h i i.2, fun h i hi => h ⟨ i, hi ⟩ ⟩

/-
The sequence of functions fk is antitone (decreasing).
-/
lemma antitone_fk (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) :
  Antitone (fk n hnpos) := by
    refine' antitone_nat_of_succ_le _;
    intro k a; refine' ENNReal.toReal_mono _ _;
    · exact MeasureTheory.measure_ne_top _ _;
    · refine' MeasureTheory.measure_mono _;
      exact Set.biInter_subset_biInter_left ( Set.Iio_subset_Iio ( Nat.le_succ _ ) )

/-
The space of choices is compact.
-/
instance Choice.compactSpace (n : ℕ → ℕ) (hnpos : ∀ i, 0 < n i) : CompactSpace (Choice n) := by
  haveI : ∀ i, NeZero (n i) := fun i => ⟨ne_of_gt (hnpos i)⟩
  haveI : ∀ i, Finite (ZMod (n i)) := fun i => inferInstance
  haveI : ∀ i, CompactSpace (ZMod (n i)) := fun i => Finite.compactSpace
  exact Pi.compactSpace

/-
The sequence of functions fk converges uniformly to 0.
-/
lemma fk_uniform_convergence (n : ℕ → ℕ) (hmono : StrictMono n) (hnpos : ∀ i, 0 < n i)
    (h : Erdos281Hyp n hmono hnpos) : TendstoUniformly (fk n hnpos) 0 atTop := by
      -- Apply Dini's theorem to the sequence of functions fk.
      have h_pointwise : ∀ a : Choice n, Tendsto (fun k => fk n hnpos k a) atTop (nhds 0) := by
        intro a
        unfold fk
        have h_haar := pointwise_convergence n hmono hnpos h a
        exact ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp h_haar
      have h_monotone : Antitone (fk n hnpos) := antitone_fk n hnpos
      haveI : CompactSpace (Choice n) := Choice.compactSpace n hnpos
      have h_continuous : ∀ k, Continuous (fk n hnpos k) := fun k => continuous_fk n hnpos k

      rw [ Metric.tendstoUniformly_iff ]
      intro ε hε_pos
      have h_open_cover : ∀ a : Choice n, ∃ U : Set (Choice n), IsOpen U ∧ a ∈ U ∧ ∃ N : ℕ, ∀ k ≥ N, ∀ b ∈ U, fk n hnpos k b < ε := by
        intro a
        obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, fk n hnpos k a < ε := by
          simpa using h_pointwise a |> fun h => h.eventually (gt_mem_nhds hε_pos)
        exact ⟨ { b | fk n hnpos N b < ε }, isOpen_lt (h_continuous N) continuous_const, hN N le_rfl, N, fun k hk b hb => lt_of_le_of_lt (h_monotone hk b) hb ⟩
      choose U hU_open hU_mem hU_N using h_open_cover
      choose N hN using hU_N
      obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover U (fun a _ => (hU_open a).mem_nhds (hU_mem a))
      rw [ Filter.eventually_atTop ]
      use t.sup N
      intro k hk a
      obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (ht.2 (Set.mem_univ a))
      obtain ⟨hb_mem, hb_a⟩ := Set.mem_iUnion.1 hb
      specialize hN b k (le_trans (Finset.le_sup hb_mem) hk) a hb_a
      unfold fk at *
      simpa using hN

/-
The main theorem: The hypothesis implies the conclusion (uniform finite-stage control).
-/
theorem Erdos_281 (n : ℕ → ℕ) (hmono : StrictMono n) (hnpos : ∀ i, 0 < n i)
    (h : Erdos281Hyp n hmono hnpos) : Erdos281Concl n hmono hnpos := by
  intro ε hε
  -- 1. Get the uniform threshold k from Dini's Theorem
  have h_unif := (Metric.tendstoUniformly_iff.1 (fk_uniform_convergence n hmono hnpos h)) ε hε
  rw [Filter.eventually_atTop] at h_unif
  obtain ⟨k, hk⟩ := h_unif

  use k
  intro a
  -- 2. Use Haar measure of Ck as the density d
  refine ⟨(haar (Ck n hnpos a k)).toReal, finite_density_haarmeasure n hnpos a k, ?_⟩
  -- 3. Uniform convergence gives fk ... < ε, and fk ≡ haar(Ck)
  specialize hk k (le_refl k) a
  simpa [fk] using hk

#print axioms Erdos_281
-- 'Erdos281.Erdos_281' depends on axioms: [propext, choice, Quot.sound]

end Erdos281
