/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 484.
https://www.erdosproblems.com/forum/thread/484

Informal authors:
- Paul Erdős
- András Sárközy
- Vera T. Sós

Formal authors:
- Aristotle
- Tomaz Mascarenhas

URLs:
- https://www.erdosproblems.com/forum/thread/484#post-5448
-/
import Mathlib

namespace Erdos484

/-!
# Density Hilbert's Lemma

A density version of Hilbert's lemma: sufficiently dense subsets of [1,M]
contain combinatorial cubes of any fixed dimension.
-/

open Finset

/-- A d-dimensional combinatorial cube using a Finset of generators.
  There exists a base u and a set vs of d distinct positive generators
  such that for every S ⊆ vs, u + Σ_{x∈S} x ∈ B. -/
def HasCombCubeFS (B : Finset ℕ) (d : ℕ) : Prop :=
  ∃ u : ℕ, ∃ vs : Finset ℕ,
    vs.card = d ∧
    (∀ v ∈ vs, 0 < v) ∧
    ∀ S : Finset ℕ, S ⊆ vs → u + S.sum id ∈ B

/-- A d-dimensional combinatorial cube in B (Fin version). -/
def HasCombCube (B : Finset ℕ) (d : ℕ) : Prop :=
  ∃ u : ℕ, ∃ v : Fin d → ℕ,
    (∀ i, 0 < v i) ∧
    Function.Injective v ∧
    ∀ S : Finset (Fin d), u + S.sum v ∈ B

/-
Converting from Finset generators to Fin generators.
-/
lemma HasCombCubeFS_to_HasCombCube {B : Finset ℕ} {d : ℕ} :
    HasCombCubeFS B d → HasCombCube B d := by
  intro h
  obtain ⟨u, vs, hvs⟩ := h
  obtain ⟨f, hf⟩ : ∃ (f : Fin d → ℕ), Function.Injective f ∧ (∀ i, f i ∈ vs) := by
    exact ⟨ fun i => vs.orderEmbOfFin ( by simp_all only [id_eq] ) i, by aesop_cat,
      fun i => by simp_all only [orderEmbOfFin_mem] ⟩
  obtain ⟨hf₁, hf₂⟩ := hf
  use u, fun i => f i
  refine ⟨ fun i => hvs.2.1 _ ( hf₂ i ), hf₁, fun S => by
      simpa [ Finset.sum_image, hf₁.eq_iff ] using
        hvs.2.2 ( Finset.image f S )
          ( Finset.image_subset_iff.mpr
            fun i _ => hf₂ i ) ⟩

/-
**Find a good shift with exclusion.**
  Given B ⊆ [1,M] with |B| large enough, there exists h ∈ [1,M-1] not in excl
  with |{b ∈ B : b+h ∈ B}| * 4M ≥ |B|².

  Proof: By double counting, Σ_h |{b : b ∈ B, b+h ∈ B}| = C(|B|, 2).
  Subtracting the excluded h's (each contributing ≤ |B|), the average over
  remaining h's is ≥ |B|²/(4M), so the max is at least that.
-/
lemma find_good_shift (M : ℕ) (B excl : Finset ℕ)
    (hBsub : B ⊆ Finset.Icc 1 M) (hM : M ≥ 2)
    (hBcard : B.card ≥ 4 * excl.card + 2)
    (hexcl_sub : excl ⊆ Finset.Icc 1 (M - 1)) :
    ∃ h ∈ Finset.Icc 1 (M - 1), h ∉ excl ∧
      (B.filter (fun b => b + h ∈ B)).card * (4 * M) ≥ B.card ^ 2 := by
  revert B excl
  -- By double counting, $\sum_{h=1}^{M-1} |{b \in B : b + h \in B}| = C(|B|, 2)$.
  intros B excl hBsub hBcard hexcl_sub
  have h_double_count :
      ∑ h ∈ Finset.Icc 1 (M - 1),
        (B.filter (fun b => b + h ∈ B)).card * 4 * M ≥
      (B.card - 1) * B.card * 2 * M := by
    have h_double_count :
        ∑ h ∈ Finset.Icc 1 (M - 1),
          (B.filter (fun b => b + h ∈ B)).card =
        ∑ b ∈ B, ∑ b' ∈ B,
          if b < b' then 1 else 0 := by
      have h_double_count :
          ∀ b ∈ B,
            ∑ h ∈ Finset.Icc 1 (M - 1),
              (if b + h ∈ B then 1 else 0) =
            ∑ b' ∈ B,
              (if b < b' then 1 else 0) := by
        intro b hb
        have h_filter :
            Finset.filter (fun b' => b < b') B =
            Finset.image (fun h => b + h)
              (Finset.filter (fun h => b + h ∈ B)
                (Finset.Icc 1 (M - 1))) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
          constructor
          · exact fun h => ⟨ x - b,
              ⟨ ⟨ Nat.sub_pos_of_lt h.2,
                Nat.sub_le_of_le_add <| by
                  linarith [
                    Finset.mem_Icc.mp <| hBsub h.1,
                    Finset.mem_Icc.mp <| hBsub hb,
                    Nat.sub_add_cancel <|
                      show 1 ≤ M from by linarith ] ⟩,
                by simpa [
                  add_tsub_cancel_of_le h.2.le ]
                  using h.1 ⟩,
              by rw [
                add_tsub_cancel_of_le h.2.le ] ⟩
          · grind
        rw [ ← Finset.card_filter,
          ← Finset.card_filter, h_filter,
          Finset.card_image_of_injective _
            ( add_right_injective _ ) ]
      rw [ ← Finset.sum_congr rfl h_double_count, Finset.sum_comm ]
      simp_all only [ge_iff_le, sum_boole, Nat.cast_id]
    -- The number of pairs $(b, b')$ with $b < b'$ is $\binom{|B|}{2}$.
    have h_pairs :
        ∑ b ∈ B, ∑ b' ∈ B,
          (if b < b' then 1 else 0) =
        (B.card * (B.card - 1)) / 2 := by
      have h_pairs :
          ∑ b ∈ B, ∑ b' ∈ B,
            (if b < b' then 1 else 0) =
          Finset.card (Finset.filter
            (fun p => p.1 < p.2) (B ×ˢ B)) := by
        rw [ Finset.card_filter ]
        erw [ Finset.sum_product ]
      have h_pairs :
          Finset.card (Finset.filter
            (fun p => p.1 < p.2) (B ×ˢ B)) =
          Finset.card
            (Finset.powersetCard 2 B) := by
        refine Finset.card_bij
          ( fun p hp => { p.1, p.2 } )
          ?_ ?_ ?_ <;>
          simp +contextual only [
            Finset.mem_powersetCard,
            Finset.mem_filter,
            Finset.mem_product,
            exists_prop,
            Prod.exists,
            and_imp,
            Prod.forall,
            Prod.mk.injEq ]
        · grind +splitIndPred
        · simp +contextual only [
            Subset.antisymm_iff,
            subset_iff,
            mem_insert,
            mem_singleton,
            forall_eq_or_imp,
            forall_eq,
            and_imp ]
          intros
          omega
        · intro b hb hb'
          rw [ Finset.card_eq_two ] at hb'
          obtain ⟨ a, b, hab, rfl ⟩ := hb'
          cases lt_trichotomy a b <;> aesop
      simp_all +decide [ Nat.choose_two_right ]
    rw [ ← Finset.sum_mul _ _ _,
      ← Finset.sum_mul _ _ _,
      h_double_count, h_pairs ]
    nlinarith [ Nat.div_mul_cancel
      ( show 2 ∣ #B * ( #B - 1 ) from
        even_iff_two_dvd.mp
          ( Nat.even_mul_pred_self _ ) ) ]
  -- Subtracting the excluded h's (each contributing ≤ |B|),
  -- the average over remaining h's is ≥ |B|²/(4M),
  -- so the max is at least that.
  have h_avg :
      ∑ h ∈ Finset.Icc 1 (M - 1) \ excl,
        (B.filter (fun b => b + h ∈ B)).card *
          4 * M ≥
      ((B.card - 1) * B.card * 2 * M) -
        (excl.card * B.card * 4 * M) := by
    have h_avg :
        ∑ h ∈ excl,
          (B.filter (fun b => b + h ∈ B)).card *
            4 * M ≤
        excl.card * B.card * 4 * M := by
      exact le_trans
        ( Finset.sum_le_sum
          fun x hx =>
            show # ( { b ∈ B | b + x ∈ B } ) *
              4 * M ≤ #B * 4 * M from
            mul_le_mul_of_nonneg_right
              ( mul_le_mul_of_nonneg_right
                ( Finset.card_filter_le _ _ )
                zero_le_four )
              ( Nat.zero_le _ ) )
        ( by simp +decide [ mul_assoc ] )
    exact Nat.sub_le_of_le_add <| by
      rw [ ← Finset.sum_sdiff hexcl_sub ] at *
      linarith
  contrapose! h_avg
  refine lt_of_lt_of_le
    ( Finset.sum_lt_sum_of_nonempty ?_ fun x hx => by
      simpa only [ mul_assoc ] using
        h_avg x ( Finset.mem_sdiff.mp hx |>.1 )
          ( Finset.mem_sdiff.mp hx |>.2 ) ) ?_
  · refine Finset.card_pos.mp ?_
    rw [ Finset.card_sdiff ]
    norm_num [ hexcl_sub ]
    rw [ Finset.inter_eq_left.mpr hexcl_sub ]
    linarith [
      Nat.sub_add_cancel ( by linarith : 1 ≤ M ),
      show #B ≤ M from
        le_trans
          ( Finset.card_le_card hBsub )
          ( by simp ) ]
  · rcases M with ( _ | _ | M ) <;>
      simp_all (config := {decide := true}) only [add_tsub_cancel_right, sum_const, smul_eq_mul]
    rw [ Finset.card_sdiff ]
    norm_num [ hexcl_sub ]
    rw [ Finset.inter_eq_left.mpr hexcl_sub ]
    exact le_tsub_of_add_le_left ( by
      nlinarith only [
        Nat.sub_add_cancel
          ( show #excl ≤ M + 1 from
            le_trans
              ( Finset.card_le_card hexcl_sub )
              ( by norm_num ) ),
        Nat.sub_add_cancel
          ( show 1 ≤ #B from by linarith ),
        hBcard,
        mul_le_mul_right
          ( show #B ≥ 2 by linarith )
          ( M + 1 ) ] )

/-
**Density Hilbert's Lemma** (Finset generator version, with exclusion).
  For any d, c ≥ 1, and exclusion bound e, there exists M₀ such that
  any B ⊆ [1,M] with c·|B| ≥ M contains a d-cube whose generators
  avoid the exclusion set.
-/
lemma density_hilbert_fs_gen : ∀ (d c e : ℕ), c ≥ 1 →
    ∃ M₀ : ℕ, ∀ M : ℕ, M ≥ M₀ →
    ∀ excl : Finset ℕ, excl.card ≤ e → excl ⊆ Finset.Icc 1 (M - 1) →
    ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 M →
    c * B.card ≥ M →
    ∃ u : ℕ, ∃ vs : Finset ℕ,
      vs.card = d ∧
      (∀ v ∈ vs, 0 < v) ∧
      Disjoint vs excl ∧
      vs ⊆ Finset.Icc 1 (M - 1) ∧
      ∀ S : Finset ℕ, S ⊆ vs → u + S.sum id ∈ B := by
  intro d c e hc
  induction d generalizing c e with
  | zero =>
    use c + 1
    intro M hM excl hexcl hexcl' B hB hB'
    obtain ⟨ u, hu ⟩ :=
      Finset.card_pos.mp ( by nlinarith )
    use u, ∅
    simp_all only [
      ge_iff_le,
      Order.add_one_le_iff,
      card_empty,
      notMem_empty,
      IsEmpty.forall_iff,
      implies_true,
      disjoint_empty_left,
      empty_subset,
      subset_empty,
      id_eq,
      sum_empty,
      add_zero,
      and_self]
  | succ d ih =>
    obtain ⟨ M₀', hM₀' ⟩ := ih ( 4 * c * c ) ( e + 1 ) ( by nlinarith )
    use Max.max M₀' ( Max.max ( c * ( 4 * e + 6 ) ) 2 ) + 1
    intro M hM excl hexcl hexcl_sub B hBsub hBcard
    obtain ⟨h, hh₁, hh₂, hh₃⟩ :=
      find_good_shift M B excl hBsub (by
        linarith [
          Nat.le_max_right M₀'
            ( Max.max ( c * ( 4 * e + 6 ) ) 2 ),
          Nat.le_max_right
            ( c * ( 4 * e + 6 ) ) 2 ]) (by
        nlinarith [
          Nat.le_max_left M₀'
            ( max ( c * ( 4 * e + 6 ) ) 2 ),
          Nat.le_max_right M₀'
            ( max ( c * ( 4 * e + 6 ) ) 2 ),
          Nat.le_max_left
            ( c * ( 4 * e + 6 ) ) 2,
          Nat.le_max_right
            ( c * ( 4 * e + 6 ) ) 2 ])
      hexcl_sub
    set B' := B.filter (fun b => b + h ∈ B) with hB'_def
    have hB'_card : (4 * c * c) * B'.card ≥ M := by
      nlinarith [ Nat.mul_le_mul_left c hc ]
    obtain ⟨u, vs, hvs_card, hvs_pos,
        hvs_disjoint, hvs_subset, hvs_cube⟩ :=
      hM₀' M (by
        linarith [
          Nat.le_max_left M₀'
            ( Max.max ( c * ( 4 * e + 6 ) ) 2 ),
          Nat.le_max_right M₀'
            ( Max.max
              ( c * ( 4 * e + 6 ) ) 2 ) ])
      (insert h excl) (by
        rw [ Finset.card_insert_of_notMem hh₂ ]
        linarith) (by
        exact Finset.insert_subset_iff.mpr
          ⟨ hh₁, hexcl_sub ⟩)
      B' (by
        exact Finset.Subset.trans
          ( Finset.filter_subset _ _ )
          hBsub)
      hB'_card
    have h_not_vs : h ∉ vs := by
      exact fun hv =>
        Finset.disjoint_left.mp hvs_disjoint hv ( Finset.mem_insert_self _ _ )
    use u, Finset.cons h vs h_not_vs
    refine ⟨ ?_, ?_, ?_, ?_, fun S hS => ?_ ⟩
    · rw [Finset.card_cons, hvs_card]
    · intro x hx
      simp only [cons_eq_insert, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact (Finset.mem_Icc.mp hh₁).1
      · exact hvs_pos x hx
    · rw [Finset.disjoint_left]
      intro x hx hxexcl
      simp only [cons_eq_insert, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hh₂ hxexcl
      · exact Finset.disjoint_left.mp hvs_disjoint hx (Finset.mem_insert_of_mem hxexcl)
    · intro x hx
      simp only [cons_eq_insert, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hh₁
      · exact hvs_subset hx
    · by_cases hS' : h ∈ S
      · have hmem : u + (S.erase h).sum id ∈ B' :=
          hvs_cube ( S.erase h ) ( fun x hx => by
            have hx_cons := hS ( Finset.mem_of_mem_erase hx )
            simp only [cons_eq_insert, Finset.mem_insert] at hx_cons
            exact Or.resolve_left hx_cons ( by
              intro hx_eq
              exact (Finset.mem_erase.mp hx).1 hx_eq ) )
        convert (Finset.mem_filter.mp hmem).2 using 1
        rw [ ← Finset.sum_erase_add _ _ hS' ]
        simp only [id_eq, Nat.add_assoc]
      · have hmem : u + S.sum id ∈ B' :=
          hvs_cube S ( fun x hx => by
            have hx_cons := hS hx
            simp only [cons_eq_insert, Finset.mem_insert] at hx_cons
            exact Or.resolve_left hx_cons ( by
              intro hx_eq
              exact hS' ( by simpa [hx_eq] using hx ) ) )
        exact (Finset.mem_filter.mp hmem).1

/-- **Density Hilbert's Lemma** (Finset generator version). -/
lemma density_hilbert_fs (d : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M ≥ M₀ →
    ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 M →
    4 * B.card ≥ M →
    HasCombCubeFS B d := by
  obtain ⟨M₀, hM₀⟩ := density_hilbert_fs_gen d 4 0 (by omega)
  exact ⟨M₀, fun M hM B hBsub hcard => by
    obtain ⟨u, vs, hvs_card, hvs_pos, _, _, hvs_cube⟩ :=
      hM₀ M hM ∅ (by simp) (by simp) B hBsub hcard
    exact ⟨u, vs, hvs_card, hvs_pos, hvs_cube⟩⟩

/-- **Density Hilbert's Lemma** (Fin version, used in the main theorem). -/
lemma density_hilbert (d : ℕ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M ≥ M₀ →
    ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 M →
    4 * B.card ≥ M →
    HasCombCube B d := by
  obtain ⟨M₀, hM₀⟩ := density_hilbert_fs d
  exact ⟨M₀, fun M hM B hBsub hcard =>
    HasCombCubeFS_to_HasCombCube (hM₀ M hM B hBsub hcard)⟩

/-!
# Monochromatic Sums in Colorings of {1, ..., N}

We formalize the statement that there exists an absolute constant `c > 0` such that,
whenever `{1, ..., N}` is `k`-colored (and `N` is large enough depending on `k`),
there are at least `c * N` integers in `{1, ..., N}` which are representable as a
**monochromatic sum** — that is, as `a + b` where `a` and `b` are distinct elements
of `{1, ..., N}` receiving the same color.

This is a result in additive combinatorics, proved by Erdős, Sárközy, and Sós.
The proof uses a density version of Hilbert's lemma (combinatorial cubes in dense sets)
combined with the pigeonhole principle.
-/

open Finset

/-- The set of elements of `Finset.Icc 1 N` that are representable as a monochromatic sum
  under a coloring `f : ℕ → Fin k`. An element `n` is a monochromatic sum if there exist
  distinct `a, b ∈ Icc 1 N` with `f a = f b` and `a + b = n`. -/
noncomputable def monochromaticSumSet (N : ℕ) (k : ℕ) (f : ℕ → Fin k) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n =>
    ∃ a ∈ Finset.Icc 1 N, ∃ b ∈ Finset.Icc 1 N, a ≠ b ∧ f a = f b ∧ a + b = n)

/-! ## Pigeonhole Contradiction

If B ⊆ [1,N] consists of even numbers that are NOT monochromatic sums,
and B contains a (k+1)-dimensional combinatorial cube, then we derive a contradiction
using the pigeonhole principle. -/

/-- If the set B of "bad" even numbers (even, not monochromatic sums) contains a
  (k+1)-dimensional combinatorial cube, then we get a contradiction via pigeonhole. -/
lemma cube_contradiction (N k : ℕ) (f : ℕ → Fin k) (_hk : k ≥ 1)
    (B : Finset ℕ) (hBsub : B ⊆ Finset.Icc 1 N)
    (hBeven : ∀ n ∈ B, Even n)
    (hBnotMono : ∀ n ∈ B, n ∉ monochromaticSumSet N k f)
    (hcube : HasCombCube B (k + 1)) :
    False := by
  obtain ⟨ u, v, hv₁, hv₂, hv₃ ⟩ := hcube
  obtain ⟨i, j, hij, hf⟩ :
      ∃ i j : Fin (k + 1),
        i ≠ j ∧
        f (u / 2 + v i) = f (u / 2 + v j) := by
    by_contra! h
    have := Finset.card_le_card
      ( show Finset.image
          ( fun i ↦ f ( u / 2 + v i ) )
          Finset.univ ⊆ Finset.univ from
        Finset.subset_univ _ )
    simp_all +decide [
      Finset.card_image_of_injective _
        ( show Function.Injective
          ( fun i ↦ f ( u / 2 + v i ) ) from
          fun i j hij ↦ by
            contrapose hij
            simp_all only [ge_iff_le, ne_eq, card_univ, Fintype.card_fin, not_false_eq_true] ) ]
  set a := u / 2 + v i
  set b := u / 2 + v j
  have hab_mono : a + b ∈ monochromaticSumSet N k f := by
    unfold monochromaticSumSet
    simp +zetaDelta only [Finset.mem_Icc, ne_eq, Finset.mem_filter] at *
    refine
      ⟨ ⟨ ?_, ?_ ⟩, u / 2 + v i, ⟨ ?_, ?_ ⟩, u / 2 + v j,
        ⟨ ?_, ?_ ⟩, ?_, hf, rfl ⟩
    any_goals linarith [ hv₁ i, hv₁ j, Nat.zero_le ( u / 2 ) ]
    · have := hBsub ( hv₃ { i, j } )
      simp_all +decide [ Finset.sum_pair hij ]
      linarith [ Nat.div_mul_le_self u 2 ]
    · have := hBsub ( hv₃ { i } )
      simp_all +decide [ Nat.even_iff ]
      grind
    · have := hBsub ( hv₃ { j } )
      simp_all +decide [ Finset.sum_singleton ]
      linarith [ Nat.div_mul_le_self u 2 ]
    · exact fun h => hij <| hv₂ <| by linarith
  have hab_in_B : a + b ∈ B := by
    convert hv₃ { i, j } using 1
    simp +zetaDelta only [ne_eq] at *
    rw [ Finset.sum_pair hij ]
    linarith [ Nat.div_mul_cancel
      ( even_iff_two_dvd.mp
        ( hBeven u ( hv₃ ∅ ) ) ) ]
  exact hBnotMono _ hab_in_B hab_mono

/-! ## Arithmetic and Counting Helpers -/

/-- The number of even numbers in Finset.Icc 1 N equals N / 2 (nat division). -/
lemma card_filter_even_Icc (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun n : ℕ => Even n)).card = N / 2 := by
  rw [ Finset.card_eq_of_bijective ]
  · exact fun i hi => 2 * i + 2
  · simp +zetaDelta only [Finset.mem_filter, Finset.mem_Icc, exists_prop, and_imp] at *
    exact fun a ha₁ ha₂ ha₃ => by
      obtain ⟨ k, rfl ⟩ :=
        even_iff_two_dvd.mp ha₃
      exact ⟨ k - 1, by omega, by omega ⟩
  · exact fun i hi => Finset.mem_filter.mpr
      ⟨ Finset.mem_Icc.mpr
        ⟨ by linarith,
          by linarith [
            Nat.div_mul_le_self N 2 ] ⟩,
        by simp +decide [ parity_simps ] ⟩
  · intro i j hi hj a
    simp_all only [Nat.add_right_cancel_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false]

/-- ⌊(1/8) * N⌋₊ ≤ N / 8 for any natural number N. -/
lemma nat_floor_eighth (N : ℕ) :
    ⌊(1 / 8 : ℝ) * ↑N⌋₊ ≤ N / 8 := by
  exact Nat.le_div_iff_mul_le ( by decide )
    |>.2 ( by
      rw [ ← @Nat.cast_le ℝ ]
      push_cast
      linarith [ Nat.floor_le
        ( by positivity :
          ( 0 : ℝ ) ≤ 1 / 8 * N ) ] )

/-- If the "bad even set" has 4 * card < N and N ≥ 8, then the monochromatic sum set
  has card ≥ N/8. -/
lemma mono_card_ge_of_bad_small (N k : ℕ) (f : ℕ → Fin k)
    (hBad : 4 * ((Finset.Icc 1 N).filter
      (fun n => Even n ∧ n ∉ monochromaticSumSet N k f)).card < N)
    (hN : N ≥ 8) :
    (monochromaticSumSet N k f).card ≥ N / 8 := by
  set badBlack := (Finset.Icc 1 N).filter
    (fun n => Even n ∧
      n ∉ monochromaticSumSet N k f)
  set goodBlack := (Finset.Icc 1 N).filter
    (fun n => Even n ∧
      n ∈ monochromaticSumSet N k f)
    with hgoodBlack_def
  have hbadBlack_def : badBlack.card + goodBlack.card = N / 2 := by
    rw [ ← Finset.card_union_of_disjoint,
      Finset.filter_union_right ]
    · convert card_filter_even_Icc N using 2
      ext x
      by_cases hx :
        x ∈ monochromaticSumSet N k f
      · simp_all only [
          ge_iff_le,
          mem_filter,
          mem_Icc,
          not_true_eq_false,
          and_false,
          and_true,
          false_or,
          badBlack,
          goodBlack]
      · simp_all only [
          ge_iff_le,
          mem_filter,
          mem_Icc,
          not_false_eq_true,
          and_true,
          and_false,
          or_false,
          badBlack,
          goodBlack]
    · exact Finset.disjoint_filter.mpr ( by
        intro x a a_1
        simp_all only [
          ge_iff_le,
          mem_Icc,
          and_false,
          not_false_eq_true,
          badBlack,
          goodBlack] )
  have hgoodBlack_le_mono : goodBlack.card ≤ (monochromaticSumSet N k f).card := by
    exact Finset.card_le_card fun x hx => by
      simp_all only [ge_iff_le, mem_filter, mem_Icc, badBlack, goodBlack]
  omega

/-! ## Main Theorem -/

/-- **Monochromatic Sums Theorem.** There exists an absolute constant `c > 0` such that,
  for every number of colors `k ≥ 1`, there is a threshold `N₀` so that for all `N ≥ N₀`,
  every `k`-coloring of `{1, ..., N}` yields at least `⌊c * N⌋` elements of `{1, ..., N}`
  that are representable as monochromatic sums `a + b` with `a ≠ b` and `f(a) = f(b)`. -/
theorem monochromatic_sums_linear :
    ∃ c : ℝ, c > 0 ∧
      ∀ k : ℕ, k ≥ 1 →
        ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
          ∀ f : ℕ → Fin k,
            (monochromaticSumSet N k f).card ≥ ⌊c * (N : ℝ)⌋₊ := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro k hk
  obtain ⟨M₀, hM₀⟩ := density_hilbert (k + 1)
  refine ⟨max M₀ 8, ?_⟩
  intro N hN f
  have hN8 : N ≥ 8 := le_trans (le_max_right M₀ 8) hN
  have hNM₀ : N ≥ M₀ := le_trans (le_max_left M₀ 8) hN
  -- Define the "bad even set": even numbers in [1,N] that are NOT monochromatic sums
  set B := (Finset.Icc 1 N).filter
    (fun n => Even n ∧ n ∉ monochromaticSumSet N k f) with hB_def
  -- Show 4 * B.card < N by contradiction: if not, density_hilbert gives a cube,
  -- and cube_contradiction derives False.
  have hBlt : 4 * B.card < N := by
    by_contra hge
    push Not at hge
    have hBsub : B ⊆ Finset.Icc 1 N := filter_subset _ _
    have hBeven : ∀ n ∈ B, Even n := fun n hn => (mem_filter.mp hn).2.1
    have hBnotMono : ∀ n ∈ B, n ∉ monochromaticSumSet N k f :=
      fun n hn => (mem_filter.mp hn).2.2
    exact cube_contradiction N k f hk B hBsub hBeven hBnotMono
      (hM₀ N hNM₀ B hBsub hge)
  -- Conclude: monoSet.card ≥ N/8 ≥ ⌊(1/8)*N⌋₊
  exact le_trans (nat_floor_eighth N) (mono_card_ge_of_bad_small N k f hBlt hN8)

end Erdos484

#print axioms Erdos484.monochromatic_sums_linear
-- 'Erdos484.monochromatic_sums_linear' depends on axioms: [propext, Classical.choice, Quot.sound]
