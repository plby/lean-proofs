/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Aristotle (Harmonic)
-/

/-
# Erdős Problem 1098 (B.H. Neumann's Theorem)

If the non-commuting graph of a group G contains no infinite complete subgraph,
then there is a finite bound on the size of complete subgraphs.

This is equivalent to: G has no infinite set of pairwise non-commuting elements
if and only if the center Z(G) has finite index in G.

Reference: B.H. Neumann, "A problem of Paul Erdős on groups",
J. Austral. Math. Soc. 21 (Series A) (1976), 467-472.
-/
import Mathlib

set_option linter.style.setOption false
set_option linter.style.openClassical false
set_option linter.style.maxHeartbeats false
set_option linter.style.refine false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.multiGoal false
set_option linter.style.longLine false
set_option linter.flexible false

open scoped Classical

noncomputable section

/-! ## Infinite Ramsey Theorem for Pairs -/

theorem Set.Infinite.exists_infinite_partition {α : Type*} {S : Set α}
    (hS : S.Infinite) (P : α → Prop) :
    (S ∩ {x | P x}).Infinite ∨ (S ∩ {x | ¬P x}).Infinite := by
  exact Classical.or_iff_not_imp_left.2 fun h => by
    simpa [Classical.not_not] using hS.diff (Set.not_infinite.1 h)

theorem ramsey_step (S : Set ℕ) (hS : S.Infinite) (r : ℕ → ℕ → Prop) :
    ∃ x ∈ S, ∃ T ⊆ S, T.Infinite ∧ (∀ t ∈ T, x < t) ∧
      ((∀ t ∈ T, r x t) ∨ (∀ t ∈ T, ¬r x t)) := by
  obtain ⟨x, hx⟩ : ∃ x ∈ S, (S ∩ {t | x < t}).Infinite := by
    obtain ⟨x, hx⟩ := hS.nonempty
    exact ⟨x, hx, hS.diff (Set.finite_le_nat x) |> Set.Infinite.mono fun y hy => by aesop⟩
  obtain ⟨T, hT⟩ : ∃ T ⊆ S ∩ {t | x < t}, T.Infinite ∧
      ((∀ t ∈ T, r x t) ∨ (∀ t ∈ T, ¬r x t)) := by
    have := Set.Infinite.exists_infinite_partition hx.2 (fun t => r x t)
    exact this.elim (fun h => ⟨_, Set.inter_subset_left, h, Or.inl fun t ht => ht.2⟩)
      fun h => ⟨_, Set.inter_subset_left, h, Or.inr fun t ht => ht.2⟩
  exact ⟨x, hx.1, T, fun t ht => hT.1 ht |>.1, hT.2.1, fun t ht => hT.1 ht |>.2, hT.2.2⟩

set_option maxHeartbeats 400000 in
theorem ramsey_sequence (r : ℕ → ℕ → Prop) :
    ∃ (x : ℕ → ℕ) (S : ℕ → Set ℕ) (c : ℕ → Bool),
      StrictMono x ∧
      (∀ n, (S n).Infinite) ∧
      (∀ n, S (n + 1) ⊆ S n) ∧
      (∀ n, x n ∈ S n) ∧
      (∀ n, ∀ t ∈ S (n + 1), x n < t) ∧
      (∀ n, if c n then ∀ t ∈ S (n + 1), r (x n) t
                   else ∀ t ∈ S (n + 1), ¬r (x n) t) := by
  have h_step : ∀ S : Set ℕ, S.Infinite → ∃ x ∈ S, ∃ T ⊆ S, T.Infinite ∧
      (∀ t ∈ T, x < t) ∧ ((∀ t ∈ T, r x t) ∨ (∀ t ∈ T, ¬r x t)) := by
    exact fun S hS => ramsey_step S hS r
  choose! x hx T hT hT' hT'' hT''' using h_step
  have h_seq : ∃ (S : ℕ → Set ℕ), S 0 = Set.univ ∧ (∀ n, (S n).Infinite) ∧
      (∀ n, S (n + 1) = T (S n)) := by
    use fun n => Nat.recOn n Set.univ fun n ih => T ih
    exact ⟨rfl, fun n => Nat.recOn n Set.infinite_univ fun n ih => hT' _ ih, fun n => rfl⟩
  obtain ⟨S, hS₀, hS₁, hS₂⟩ := h_seq
  use fun n => x (S n), S, fun n => if (∀ t ∈ S (n + 1), r (x (S n)) t) then true else false
  refine ⟨strictMono_nat_of_lt_succ ?_, hS₁, ?_, ?_, ?_, ?_⟩
  · grind
  · aesop
  · exact fun n => hx _ (hS₁ n)
  · grind
  · grind

theorem exists_monochromatic_subsequence (c : ℕ → Bool) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ b : Bool, ∀ n, c (f n) = b := by
  by_contra h_contra
  obtain ⟨b, hb⟩ : ∃ b : Bool, Set.Infinite {n : ℕ | c n = b} := by
    by_cases h_finite : ∀ b : Bool, Set.Finite {n : ℕ | c n = b}
    · exact absurd (Set.Finite.subset (Set.Finite.union (h_finite Bool.true)
        (h_finite Bool.false)) fun x hx => by cases h : c x <;> aesop) Set.infinite_univ
    · push Not at h_finite; exact h_finite
  exact h_contra ⟨fun n => Nat.recOn n (Nat.find hb.nonempty)
    fun n ih => Nat.find (hb.exists_gt ih),
    strictMono_nat_of_lt_succ fun n => Nat.find_spec (hb.exists_gt _) |>.2,
    b, fun n => Nat.recOn n (Nat.find_spec hb.nonempty) fun n _ =>
      Nat.find_spec (hb.exists_gt _) |>.1⟩

theorem ramsey_infinite_pairs (r : ℕ → ℕ → Prop) (hr : Symmetric r) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i ≠ j → r (f i) (f j)) ∨ (∀ i j, i ≠ j → ¬r (f i) (f j))) := by
  obtain ⟨x, S, c, hx_mono, hS_inf, hS_sub, hx_mem, hx_lt, hc⟩ := ramsey_sequence r
  obtain ⟨f, hf_mono, b, hb⟩ := exists_monochromatic_subsequence c
  refine ⟨fun n => x (f n), hx_mono.comp hf_mono, ?_⟩
  -- Consider two cases: $b = true$ and $b = false$.
  by_cases hb_true : b = true;
  · -- For any $i < j$, we have $f j \geq f i + 1$, hence $S (f j) \subseteq S (f i + 1)$.
    have h_subset : ∀ i j, i < j → S (f j) ⊆ S (f i + 1) := by
      exact fun i j hij => Set.Subset.trans ( show S ( f j ) ⊆ S ( f i + 1 ) from
        Nat.le_induction ( by tauto ) ( fun k hk IH => by tauto ) _
          ( show f j ≥ f i + 1 from Nat.succ_le_of_lt ( hf_mono hij ) ) ) ( by tauto );
    left;
    intro i j hij; cases lt_or_gt_of_ne hij <;> simp_all +decide;
    · grind;
    · specialize hc ( f j ) ; aesop;
  · refine Or.inr fun i j hij => ?_;
    cases lt_or_gt_of_ne hij <;> have := hc ( f i ) <;> have := hc ( f j ) <;> simp_all +decide;
    · refine' ‹∀ t ∈ S ( f i + 1 ), ¬r ( x ( f i ) ) t› _ _;
      exact Set.mem_of_subset_of_mem ( show S ( f j ) ⊆ S ( f i + 1 ) from
        Nat.le_induction ( by tauto ) ( fun k hk ih ↦ by tauto ) _
          ( show f j ≥ f i + 1 from Nat.succ_le_of_lt ( hf_mono ‹_› ) ) ) ( hx_mem _ );
    · convert this ( x ( f i ) ) _ using 1;
      · exact ⟨ fun h => hr h, fun h => hr h ⟩;
      · exact Set.mem_of_subset_of_mem ( show S ( f i ) ⊆ S ( f j + 1 ) from
          Nat.le_induction ( by tauto ) ( fun k hk ih ↦ by tauto ) _
            ( show f i ≥ f j + 1 from Nat.succ_le_of_lt ( hf_mono ‹_› ) ) ) ( hx_mem _ )

/-! ## Definitions and Basic Properties -/

variable {G : Type*} [Group G]

def Set.PairwiseNonCommuting (S : Set G) : Prop :=
  S.Pairwise fun x y => x * y ≠ y * x

def IsPEGroup (G : Type*) [Group G] : Prop :=
  ∀ S : Set G, S.PairwiseNonCommuting → S.Finite

def IsFCGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, (Subgroup.centralizer {g}).FiniteIndex

def IsFIZGroup (G : Type*) [Group G] : Prop :=
  (Subgroup.center G).FiniteIndex

/-! ## FIZ implies FC -/

theorem IsFIZGroup.isFCGroup (h : IsFIZGroup G) : IsFCGroup G := by
  intro g
  haveI : (Subgroup.center G).FiniteIndex := h
  exact Subgroup.finiteIndex_of_le (Subgroup.center_le_centralizer _)

/-! ## Lemma 1: PE implies FC -/

theorem mul_not_commute_of_commute_distinct_cosets (g u v : G)
    (huv : u * v = v * u) (hdist : u⁻¹ * g * u ≠ v⁻¹ * g * v) :
    g * u * (g * v) ≠ g * v * (g * u) := by
  contrapose! hdist; simp_all +decide [← mul_assoc]
  simp_all +decide [mul_assoc]
  rw [eq_inv_mul_iff_mul_eq.mpr hdist]
  simp +decide [eq_inv_mul_iff_mul_eq]
  simp +decide [← mul_assoc, huv]

theorem IsPEGroup.isFCGroup (h : IsPEGroup G) : IsFCGroup G := by
  have h_ramsey : ∀ (r : ℕ → ℕ → Prop), Symmetric r → ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i ≠ j → r (f i) (f j)) ∨ (∀ i j, i ≠ j → ¬r (f i) (f j))) := by
    exact ramsey_infinite_pairs;
  intro g
  by_contra h_not_finite_index
  have h_infinite_conjugates : Set.Infinite {g' : G | ∃ u : G, u⁻¹ * g * u = g'} := by
    contrapose! h_not_finite_index;
    have h_finite_index : (Subgroup.centralizer {g}).index = Nat.card (MulAction.orbit (ConjAct G) g) := by
      rw [ Nat.card_congr ( MulAction.orbitEquivQuotientStabilizer ( ConjAct G ) g ) ];
      congr;
      ext; simp +decide [ Subgroup.mem_centralizer_iff ];
      simp +decide [ MulAction.stabilizer ];
      simp +decide [ MulAction.stabilizerSubmonoid, ConjAct.smul_def ];
      simp +decide [ mul_inv_eq_iff_eq_mul ];
      exact comm;
    have h_finite_orbit : Set.Finite (MulAction.orbit (ConjAct G) g) := by
      convert h_not_finite_index using 1;
      ext; simp [MulAction.orbit];
      simp +decide [ ConjAct.smul_def, mul_assoc ];
      exact ⟨ fun ⟨ y, hy ⟩ => ⟨ y⁻¹, by simpa [ mul_assoc ] using hy ⟩,
        fun ⟨ y, hy ⟩ => ⟨ y⁻¹, by simpa [ mul_assoc ] using hy ⟩ ⟩;
    have h_finite_orbit : Nat.card (MulAction.orbit (ConjAct G) g) ≠ 0 := by
      simp +decide;
      rw [ @Set.ncard_eq_zero ];
      · exact Set.Nonempty.ne_empty ⟨ _, MulAction.mem_orbit_self _ ⟩;
      · exact h_finite_orbit;
    exact ⟨ by aesop ⟩;
  -- Pick f : ℕ → G injective from distinct cosets of C_G(g).
  obtain ⟨f, hf_inj⟩ : ∃ f : ℕ → G, Function.Injective f ∧
      ∀ i j, i ≠ j → (f i)⁻¹ * g * (f i) ≠ (f j)⁻¹ * g * (f j) := by
    have h_infinite_conjugates : ∃ f : ℕ → G, Function.Injective f ∧
        ∀ i, (f i)⁻¹ * g * (f i) ∈ {g' : G | ∃ u : G, u⁻¹ * g * u = g'} ∧
        ∀ i j, i ≠ j → (f i)⁻¹ * g * (f i) ≠ (f j)⁻¹ * g * (f j) := by
      have h_infinite_conjugates : Set.Infinite (Set.image (fun u : G => u⁻¹ * g * u) Set.univ) := by
        aesop
      have := h_infinite_conjugates.natEmbedding;
      choose f hf using fun i => this i |>.2;
      refine' ⟨ f, _, _ ⟩ <;> simp_all +decide [ Function.Injective ];
      · grind;
      · exact fun i => ⟨ ⟨ f i, hf i ⟩, fun i j hij => fun h => hij <| this.injective <| Subtype.ext h ⟩;
    exact ⟨ h_infinite_conjugates.choose, h_infinite_conjugates.choose_spec.1,
      fun i j hij => h_infinite_conjugates.choose_spec.2 i |>.2 i j hij ⟩;
  -- Apply ramsey_infinite_pairs to the commuting relation on ℕ.
  obtain ⟨f', hf'_mono, hf'_comm⟩ : ∃ f' : ℕ → ℕ, StrictMono f' ∧
      ((∀ i j, i ≠ j → (f (f' i)) * (f (f' j)) = (f (f' j)) * (f (f' i))) ∨
        (∀ i j, i ≠ j → ¬((f (f' i)) * (f (f' j)) = (f (f' j)) * (f (f' i))))) := by
    convert h_ramsey ( fun i j => f i * f j = f j * f i ) ( by intros i j; tauto ) using 1;
  cases' hf'_comm with hf'_comm hf'_comm;
  · have h_infinite_noncommuting : Set.Infinite {x : G | ∃ i : ℕ, x = g * (f (f' i))}
        ∧ Set.Pairwise {x : G | ∃ i : ℕ, x = g * (f (f' i))} (fun x y => x * y ≠ y * x) := by
      refine' ⟨ Set.infinite_of_injective_forall_mem ( fun i j hij => _ ) fun i => ⟨ i, rfl ⟩, _ ⟩;
      · exact hf'_mono.injective ( hf_inj.1 ( by simpa using hij ) );
      · rintro x ⟨ i, rfl ⟩ y ⟨ j, rfl ⟩ hij;
        grind +suggestions;
    exact h_infinite_noncommuting.1 ( h _ h_infinite_noncommuting.2 );
  · have := h ( Set.range ( fun i => f ( f' i ) ) ) ?_;
    · exact this.not_infinite <| Set.infinite_range_of_injective <| hf_inj.1.comp hf'_mono.injective;
    · exact fun x hx y hy hxy => by
        obtain ⟨ i, rfl ⟩ := hx
        obtain ⟨ j, rfl ⟩ := hy
        exact hf'_comm i j ( by rintro rfl; exact hxy rfl ) ;

/-! ## Lemma 2: FC + abelian finite-index subgroup → FIZ -/

theorem IsFCGroup.isFIZGroup_of_abelian_finite_index (hFC : IsFCGroup G)
    (A : Subgroup G) (hA : A.FiniteIndex) (hAb : ∀ a b : A, a * b = b * a) :
    IsFIZGroup G := by
  -- Since A has finite index, get finite coset reps g_set.
  obtain ⟨g_set, hg_set⟩ : ∃ g_set : Finset G, ∀ g : G, ∃ g' ∈ g_set, ∃ a ∈ A, g = g' * a := by
    obtain ⟨g_set, hg_set⟩ : ∃ g_set : Set G, g_set.Finite ∧ ∀ g : G, ∃ g' ∈ g_set, g'⁻¹ * g ∈ A := by
      refine' ⟨ Set.range ( fun g : G ⧸ A => Quotient.out g ), Set.finite_range _, fun g => _ ⟩;
      simp +decide [ ← QuotientGroup.eq ];
    exact ⟨ hg_set.1.toFinset, fun g => by
      obtain ⟨ g', hg', hg'' ⟩ := hg_set.2 g
      exact ⟨ g', hg_set.1.mem_toFinset.2 hg', g'⁻¹ * g, hg'', by group ⟩ ⟩;
  have h_center : Subgroup.centralizer (g_set : Set G) ⊓ A ≤ Subgroup.center G := by
    intro x hx
    simp [Subgroup.mem_center_iff] at hx ⊢;
    intro g; obtain ⟨ g', hg', a, ha, rfl ⟩ := hg_set g;
    simp_all +decide [ Subgroup.mem_centralizer_iff, mul_assoc ] ;
    simp +decide only [← mul_assoc, hx.1 g' hg'];
  have h_center_finite_index : (Subgroup.centralizer (g_set : Set G)).FiniteIndex := by
    have h_center_finite_index : (⨅ g ∈ g_set, Subgroup.centralizer {g}).FiniteIndex := by
      exact Subgroup.finiteIndex_iInf' (fun i => Subgroup.centralizer {i}) fun i a => hFC i;
    convert h_center_finite_index using 1;
    ext; simp [Subgroup.centralizer];
    simp +decide [ Set.centralizer, Set.mem_setOf_eq ];
  exact Subgroup.finiteIndex_of_le h_center

/-! ## Corollary 3 -/

theorem fc_not_fiz_no_abelian_finite_index (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G)
    (A : Subgroup G) (hA : A.FiniteIndex) : ∃ a b : A, a * b ≠ b * a := by
  by_contra h; push Not at h
  exact hnFIZ (hFC.isFIZGroup_of_abelian_finite_index A hA h)

/-! ## Helper lemmas -/

theorem IsFCGroup.centralizer_finiteIndex (hFC : IsFCGroup G) (S : Finset G) :
    (Subgroup.centralizer (S : Set G)).FiniteIndex := by
  have : Subgroup.centralizer (S : Set G) = ⨅ s ∈ S, Subgroup.centralizer ({s} : Set G) := by
    ext; simp [Subgroup.mem_centralizer_iff]
  rw [this]; exact Subgroup.finiteIndex_iInf' _ (fun g _ => hFC g)

theorem commute_list_prod (x : G) (l : List G)
    (hcomm : ∀ y ∈ l, x * y = y * x) :
    x * l.prod = l.prod * x := by
  induction l <;> simp_all +decide [mul_assoc]; grind

theorem noncommute_prod_of_single {n : ℕ} (a : G) (b : Fin n → G) (i : Fin n)
    (hcomm : ∀ j : Fin n, j ≠ i → a * b j = b j * a)
    (hnoncomm : a * b i ≠ b i * a)
    (hbb : ∀ j k : Fin n, b j * b k = b k * b j) :
    a * (List.ofFn b).prod ≠ (List.ofFn b).prod * a := by
  induction' n with n ih;
  · exact Fin.elim0 i;
  · by_cases hi : i = 0;
    · simp_all +decide [ ← mul_assoc ];
      intro h;
      -- By the properties of the commutator, we can rewrite the equation as
      -- $a * b 0 * (List.ofFn fun i => b i.succ).prod = b 0 * a * (List.ofFn fun i => b i.succ).prod$.
      have h_comm : a * b 0 * (List.ofFn fun i => b i.succ).prod
          = b 0 * a * (List.ofFn fun i => b i.succ).prod := by
        rw [ h, mul_assoc ];
        rw [ mul_assoc, commute_list_prod ];
        simp +decide [ List.mem_ofFn, hcomm ];
      exact hnoncomm ( by simpa using h_comm );
    · contrapose! ih;
      refine' ⟨ fun j => b j.succ, Fin.pred i hi, _, _, _, _ ⟩ <;> simp_all +decide [ List.ofFn_succ ];
      · grind;
      · simp_all +decide [ ← mul_assoc ];
        simp_all +decide [ mul_assoc, hcomm 0 ( ne_of_lt ( Fin.pos_iff_ne_zero.mpr hi ) ) ]

/-! ## Corollary 5: FC ∧ ¬FIZ → ¬PE -/

/-- Build sequences f, g : ℕ → G by well-founded recursion.
At step n, pick non-commuting α, β from the centralizer of all previous values.
Set f(n) = α * g(0) * ... * g(n-1), g(n) = β. -/
private noncomputable def fgAux (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G) :
    ℕ → G × G :=
  WellFounded.fix Nat.lt_wfRel.wf fun n ih =>
    let prev_f : Fin n → G := fun k => (ih k k.isLt).1
    let prev_g : Fin n → G := fun k => (ih k k.isLt).2
    let S : Finset G := Finset.univ.image prev_f ∪ Finset.univ.image prev_g
    let hC : (Subgroup.centralizer (S : Set G)).FiniteIndex := hFC.centralizer_finiteIndex S
    let hex := fc_not_fiz_no_abelian_finite_index hFC hnFIZ _ hC
    let α : G := hex.choose.1
    let β : G := hex.choose_spec.choose.1
    (α * (List.ofFn prev_g).prod, β)

/-- Unfolding lemma for fgAux. -/
private theorem fgAux_unfold (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G) (n : ℕ) :
    fgAux hFC hnFIZ n =
      let prev_f : Fin n → G := fun k => (fgAux hFC hnFIZ k).1
      let prev_g : Fin n → G := fun k => (fgAux hFC hnFIZ k).2
      let S : Finset G := Finset.univ.image prev_f ∪ Finset.univ.image prev_g
      let hC := hFC.centralizer_finiteIndex S
      let hex := fc_not_fiz_no_abelian_finite_index hFC hnFIZ _ hC
      let α : G := hex.choose.1
      let β : G := hex.choose_spec.choose.1
      (α * (List.ofFn prev_g).prod, β) := by
  unfold fgAux; rw [WellFounded.fix_eq]

/-
The α and β at step n are non-commuting elements from the centralizer of previous values.
-/
private theorem fgAux_alpha_beta_props (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G) (n : ℕ) :
    let S := Finset.univ.image (fun k : Fin n => (fgAux hFC hnFIZ k).1) ∪
             Finset.univ.image (fun k : Fin n => (fgAux hFC hnFIZ k).2)
    let hC := hFC.centralizer_finiteIndex S
    let hex := fc_not_fiz_no_abelian_finite_index hFC hnFIZ _ hC
    let α := hex.choose.1
    let β := hex.choose_spec.choose.1
    (fgAux hFC hnFIZ n).1 = α * (List.ofFn (fun k : Fin n => (fgAux hFC hnFIZ k).2)).prod ∧
    (fgAux hFC hnFIZ n).2 = β ∧
    (∀ x ∈ (S : Set G), α * x = x * α) ∧
    (∀ x ∈ (S : Set G), β * x = x * β) ∧
    α * β ≠ β * α := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · rw [ fgAux_unfold ];
  · convert congr_arg Prod.snd ( fgAux_unfold hFC hnFIZ n ) using 1;
  · intro x hx;
    grind +suggestions;
  · intro x hx;
    have := Subgroup.mem_centralizer_iff.mp ( Classical.choose_spec
      ( fc_not_fiz_no_abelian_finite_index hFC hnFIZ _ ( hFC.centralizer_finiteIndex
        ( Finset.image ( fun k : Fin n => ( fgAux hFC hnFIZ k ).1 ) Finset.univ ∪ Finset.image
          ( fun k : Fin n => ( fgAux hFC hnFIZ k ).2 ) Finset.univ ) ) ) ).choose.2 x;
    exact this hx ▸ rfl;
  · convert ( fc_not_fiz_no_abelian_finite_index hFC hnFIZ _ ( hFC.centralizer_finiteIndex _ )
      ).choose_spec.choose_spec;
    swap;
    exact Finset.univ.image ( fun k : Fin n => ( fgAux hFC hnFIZ k ).1 ) ∪
      Finset.univ.image ( fun k : Fin n => ( fgAux hFC hnFIZ k ).2 );
    simp +decide [ Subtype.ext_iff ]

private noncomputable def seqF (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G) (n : ℕ) : G :=
  (fgAux hFC hnFIZ n).1

private noncomputable def seqG (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G) (n : ℕ) : G :=
  (fgAux hFC hnFIZ n).2

/-
The g sequence is pairwise commuting.
-/
private theorem seqG_commute (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G)
    (i j : ℕ) : seqG hFC hnFIZ i * seqG hFC hnFIZ j = seqG hFC hnFIZ j * seqG hFC hnFIZ i := by
  -- By definition of $seqG$, we know that $seqG i$ and $seqG j$ are elements of the centralizer
  -- of the set $\{seqF k | k < i\} \cup \{seqG k | k < i\}$.
  have h_centralizer : ∀ i, seqG hFC hnFIZ i ∈ Subgroup.centralizer (Set.range
      (fun k : Fin i => seqF hFC hnFIZ k) ∪ Set.range
        (fun k : Fin i => seqG hFC hnFIZ k)) := by
    intro i
    have h_centralizer : seqG hFC hnFIZ i ∈ Subgroup.centralizer (Finset.univ.image
        (fun k : Fin i => seqF hFC hnFIZ k) ∪ Finset.univ.image
          (fun k : Fin i => seqG hFC hnFIZ k) : Set G) := by
      have h_centralizer : (fgAux hFC hnFIZ i).2 ∈ Subgroup.centralizer (Finset.univ.image
          (fun k : Fin i => (fgAux hFC hnFIZ k).1) ∪ Finset.univ.image
            (fun k : Fin i => (fgAux hFC hnFIZ k).2) : Set G) := by
        unfold fgAux;
        grind +suggestions;
      exact h_centralizer;
    aesop;
  rcases lt_trichotomy i j with ( hij | rfl | hij ) <;> simp_all +decide [ Subgroup.mem_centralizer_iff ];
  · exact h_centralizer j _ ( Or.inr ⟨ ⟨ i, hij ⟩, rfl ⟩ ) ▸ rfl;
  · rw [ ← h_centralizer _ _ ( Or.inr ⟨ ⟨ j, hij ⟩, rfl ⟩ ) ]

/-
f(i) commutes with g(j) for i ≠ j.
-/
private theorem seqF_commutes_seqG (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G)
    (i j : ℕ) (hij : i ≠ j) :
    seqF hFC hnFIZ i * seqG hFC hnFIZ j = seqG hFC hnFIZ j * seqF hFC hnFIZ i := by
  by_cases h_cases : i < j;
  · have := fgAux_alpha_beta_props hFC hnFIZ j;
    simp +zetaDelta at *;
    have := this.2.2.2.1 ( seqF hFC hnFIZ i ) ( Or.inl ⟨ ⟨ i, h_cases ⟩, rfl ⟩ );
    grind +locals;
  · have := fgAux_alpha_beta_props hFC hnFIZ i
    simp +zetaDelta at this
    simp only [seqF, seqG]
    rw [this.1]
    rw [ ← mul_assoc, ← this.2.2.1 _ ( Or.inr ⟨ ⟨ j, by omega ⟩, rfl ⟩ ), mul_assoc ];
    rw [ ← commute_list_prod ];
    · rw [ mul_assoc ];
    · intro y hy; rw [ List.mem_ofFn ] at hy; obtain ⟨ k, rfl ⟩ := hy; exact seqG_commute hFC hnFIZ _ _;

/-
f(i) does not commute with g(i).
-/
private theorem seqF_noncommutes_seqG (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G)
    (i : ℕ) : seqF hFC hnFIZ i * seqG hFC hnFIZ i ≠ seqG hFC hnFIZ i * seqF hFC hnFIZ i := by
  have := fgAux_alpha_beta_props hFC hnFIZ i;
  simp +zetaDelta at *;
  contrapose! this;
  intro h1 h2 h3 h4;
  convert congr_arg ( fun x => x * ( List.ofFn fun k : Fin i => ( fgAux hFC hnFIZ k ).2 ).prod⁻¹ ) this using
      1 <;> simp +decide [ mul_assoc ];
  · unfold seqF seqG; simp +decide [ h1, h2, mul_assoc ] ;
    rw [ ← mul_assoc, eq_comm ];
    rw [ mul_inv_eq_iff_eq_mul ];
    rw [ commute_list_prod ];
    simp +decide [ List.mem_ofFn ];
    exact fun a => h4 _ ( Or.inr ⟨ a, rfl ⟩ );
  · simp +decide [ ← mul_assoc, ← h2, seqF, seqG ];
    simp +decide [ h1, h2, mul_assoc ]

/-
f(i) does not commute with f(j) for i ≠ j.
-/
private theorem seqF_noncommute (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G)
    (i j : ℕ) (hij : i ≠ j) :
    seqF hFC hnFIZ i * seqF hFC hnFIZ j ≠ seqF hFC hnFIZ j * seqF hFC hnFIZ i := by
  -- WLOG $i < j$ (by symmetry).
  suffices h_wlog : ∀ {i j : ℕ}, i < j → seqF hFC hnFIZ i * seqF hFC hnFIZ j
      ≠ seqF hFC hnFIZ j * seqF hFC hnFIZ i by
    cases lt_or_gt_of_ne hij <;> tauto;
  intro i j hij;
  -- By definition of $seqF$, we have $seqF j = α_j * prod(seqG 0,..., seqG(j-1))$.
  obtain ⟨α_j, prod_j, hα_j, hprod_j⟩ : ∃ α_j prod_j : G, seqF hFC hnFIZ j = α_j * prod_j ∧
      (∀ x ∈ (Finset.univ.image (fun k : Fin j => seqF hFC hnFIZ k) ∪
        Finset.univ.image (fun k : Fin j => seqG hFC hnFIZ k) : Set G), α_j * x = x * α_j) ∧
      prod_j = (List.ofFn (fun k : Fin j => seqG hFC hnFIZ k)).prod := by
    have := fgAux_alpha_beta_props hFC hnFIZ j;
    refine' ⟨ _, _, this.1, _, rfl ⟩;
    convert this.2.2.1 using 1;
    grind;
  -- By noncommute_prod_of_single, seqF i doesn't commute with prod_j because:
  -- - seqF i commutes with seqG k for k ≠ i (by seqF_commutes_seqG)
  -- - seqF i doesn't commute with seqG i (by seqF_noncommutes_seqG)
  -- - all seqG's commute pairwise (by seqG_commute)
  have h_noncommute : seqF hFC hnFIZ i * prod_j ≠ prod_j * seqF hFC hnFIZ i := by
    convert noncommute_prod_of_single ( seqF hFC hnFIZ i )
      ( fun k : Fin j => seqG hFC hnFIZ k ) ⟨ i, hij ⟩ _ _ _ using 1;
    · rw [ hprod_j.2 ];
    · rw [ hprod_j.2 ];
    · exact fun k hk => seqF_commutes_seqG hFC hnFIZ i k ( by simpa [ Fin.ext_iff ] using Ne.symm hk );
    · exact seqF_noncommutes_seqG hFC hnFIZ i;
    · exact fun i j => seqG_commute hFC hnFIZ _ _;
  simp_all +decide [ mul_assoc ];
  simp_all +decide [ ← mul_assoc, ← hprod_j.1 _ ( Or.inl ⟨ ⟨ i, hij ⟩, rfl ⟩ ) ];
  simp_all +decide [ mul_assoc ]

theorem exists_infinite_noncommuting_seq (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G) :
    ∃ f : ℕ → G, Function.Injective f ∧ ∀ i j, i ≠ j → f i * f j ≠ f j * f i := by
  refine ⟨seqF hFC hnFIZ, ?_, seqF_noncommute hFC hnFIZ⟩
  intro i j heq
  by_contra hij
  exact seqF_noncommute hFC hnFIZ i j hij (by rw [heq])

theorem fc_not_fiz_not_pe (hFC : IsFCGroup G) (hnFIZ : ¬IsFIZGroup G) : ¬IsPEGroup G := by
  obtain ⟨f, hf_inj, hf_comm⟩ := exists_infinite_noncommuting_seq hFC hnFIZ
  intro hPE
  exact (Set.infinite_range_of_injective hf_inj) (hPE _ (fun x hx y hy hxy => by
    obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
    exact hf_comm i j (fun h => hxy (h ▸ rfl))))

/-! ## FIZ implies PE -/

theorem IsFIZGroup.isPEGroup (h : IsFIZGroup G) : IsPEGroup G := by
  -- Since $G/Z(G)$ is finite, any pairwise non-commuting subset $S$ of $G$ must be finite.
  intros S hS
  have h_finite_quotient : Set.Finite (S.image (QuotientGroup.mk' (Subgroup.center G))) := by
    -- Since the center has finite index, the quotient group G/Z(G) is finite.
    have h_quotient_finite : Finite (G ⧸ Subgroup.center G) :=
      Subgroup.finiteIndex_iff_finite_quotient.mp h;
    exact Set.toFinite _
  generalize_proofs at *; (
  convert h_finite_quotient.of_finite_image _;
  intro x hx y hy
  have := hS hx hy
  simp_all +decide [ QuotientGroup.eq, Subgroup.mem_center_iff ] ;
  intro h; specialize h x; simp_all +decide [ mul_assoc, eq_inv_mul_iff_mul_eq ] ;)

/-! ## Main Theorem -/

theorem pe_iff_fiz : IsPEGroup G ↔ IsFIZGroup G := by
  constructor
  · intro hPE; by_contra hnFIZ; exact fc_not_fiz_not_pe hPE.isFCGroup hnFIZ hPE
  · exact IsFIZGroup.isPEGroup

/-
**Erdős Problem 1098**: If the non-commuting graph of G has no infinite complete
subgraph, then there is a finite bound on the size of complete subgraphs.
-/
theorem erdos1098 (G : Type*) [Group G]
    (h : ∀ S : Set G, S.PairwiseNonCommuting → S.Finite) :
    ∃ n : ℕ, ∀ S : Finset G,
      (↑S : Set G).PairwiseNonCommuting → S.card ≤ n := by
  have h_finite_index : (Subgroup.center G).FiniteIndex := by
    convert pe_iff_fiz.symm;
    exact Iff.symm (iff_true_right h);
  -- Let $n$ be the index of the center of $G$.
  use Nat.card (G ⧸ Subgroup.center G);
  intro S hS
  have h_quotient : Function.Injective (fun x : S => QuotientGroup.mk x.val : S → G ⧸ Subgroup.center G) := by
    intro x y hxy;
    have := hS x.2 y.2; simp_all +decide [ QuotientGroup.eq ] ;
    simp_all +decide [ Subgroup.mem_center_iff, mul_assoc ];
    exact Classical.not_not.1 fun h => this h <| by
      have := hxy x
      simp_all +decide [ eq_inv_mul_iff_mul_eq ]
  have h_card_quotient : Nat.card (Set.range
      (fun x : S => QuotientGroup.mk x.val : S → G ⧸ Subgroup.center G))
      ≤ Nat.card (G ⧸ Subgroup.center G) := by
    apply_rules [ Nat.card_le_card_of_injective ];
    swap;
    exacts [ fun x => x, by rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩ hxy; exact Subtype.ext hxy ];
  rw [ Nat.card_range_of_injective ] at h_card_quotient <;> aesop

#print axioms erdos1098
-- 'erdos1098' depends on axioms: [propext, Classical.choice, Quot.sound]

end
