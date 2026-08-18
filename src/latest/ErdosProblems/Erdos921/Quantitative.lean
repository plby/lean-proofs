/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos921.StableKneser

open Function Set SimpleGraph
open scoped ENat

namespace Erdos921

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Counting stable sets -/

/-- The clockwise successor in a finite cyclic order. -/
def cyclicNext {N : ℕ} (i : Fin N) : Fin N :=
  if h : i.val + 1 < N then ⟨i.val + 1, h⟩
  else ⟨0, Nat.zero_lt_of_lt i.isLt⟩

lemma cyclicNext_injective {N : ℕ} : Function.Injective (@cyclicNext N) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  by_cases ha : a.val + 1 < N <;> by_cases hb : b.val + 1 < N
  · simp [cyclicNext, ha, hb] at hv
    exact Fin.ext hv
  · simp [cyclicNext, ha, hb] at hv
  · simp [cyclicNext, ha, hb] at hv
  · have hae : a.val + 1 = N := by omega
    have hbe : b.val + 1 = N := by omega
    apply Fin.ext
    omega

/-- The cyclic successor set of a finite set. -/
def cyclicSucc {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N) :=
  S.image cyclicNext

/-- The positions which are neither selected nor the compulsory zero directly
after a selected position. -/
def extraPositions {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ \ (S ∪ cyclicSucc S)

lemma cyclicSucc_card {N : ℕ} [NeZero N] (S : Finset (Fin N)) :
    (cyclicSucc S).card = S.card := by
  rw [cyclicSucc, Finset.card_image_iff.mpr]
  exact cyclicNext_injective.injOn

lemma not_mem_cyclicNext_of_stable {N : ℕ}
    {S : Finset (Fin N)} (hS : CyclicallyStable S) {x : Fin N}
    (hxS : x ∈ S) : cyclicNext x ∉ S := by
  intro hnext
  have hxle : x.val + 1 ≤ N := by omega
  by_cases hlt : x.val + 1 < N
  · exact (hS x hxS (cyclicNext x) hnext).1 (by
      simp [cyclicNext, hlt])
  · have hxeq : x.val + 1 = N := by omega
    exact (hS (cyclicNext x) hnext x hxS).2 ⟨by
      simp [cyclicNext, hlt], hxeq⟩

lemma disjoint_cyclicSucc_of_stable {N : ℕ} [NeZero N]
    {S : Finset (Fin N)} (hS : CyclicallyStable S) :
    Disjoint S (cyclicSucc S) := by
  rw [Finset.disjoint_left]
  intro x hxS hxsucc
  obtain ⟨y, hyS, hyx⟩ := Finset.mem_image.mp (by
    simpa [cyclicSucc] using hxsucc)
  exact not_mem_cyclicNext_of_stable hS hyS (hyx ▸ hxS)

lemma extraPositions_card {r d : ℕ} (hr : 0 < r)
    (S : StableSet (2 * r + d) r) :
    (extraPositions S.1).card = d := by
  letI : NeZero (2 * r + d) := ⟨by omega⟩
  have hdisj : Disjoint S.1 (cyclicSucc S.1) :=
    disjoint_cyclicSucc_of_stable S.2.2
  have hunion : (S.1 ∪ cyclicSucc S.1).card = 2 * r := by
    rw [Finset.card_union_of_disjoint hdisj, cyclicSucc_card, S.2.1]
    omega
  rw [extraPositions, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, hunion]
  omega

lemma mem_extraPositions_iff {N : ℕ} {S : Finset (Fin N)} {x : Fin N} :
    x ∈ extraPositions S ↔ x ∉ S ∧ x ∉ cyclicSucc S := by
  simp [extraPositions]

/-- Membership in a stable set is recovered recursively from its extra
positions: after a selected point comes a compulsory gap; after any other
non-extra point comes a selected point. -/
lemma mem_succ_iff_of_stable {N : ℕ}
    {S : Finset (Fin N)} (hS : CyclicallyStable S) (x : Fin N) :
    cyclicNext x ∈ S ↔ x ∉ S ∧ cyclicNext x ∉ extraPositions S := by
  constructor
  · intro hx
    refine ⟨?_, (mem_extraPositions_iff.not.mpr <| not_and_or.mpr <| Or.inl <| not_not.mpr hx)⟩
    exact fun hxS ↦ not_mem_cyclicNext_of_stable hS hxS hx
  · rintro ⟨hxS, hxextra⟩
    have hcovered : cyclicNext x ∈ S ∪ cyclicSucc S := by
      by_contra hnot
      exact hxextra (by simpa [extraPositions] using hnot)
    rcases Finset.mem_union.mp hcovered with hx | hx
    · exact hx
    · obtain ⟨y, hyS, hy⟩ := Finset.mem_image.mp (by
        simpa [cyclicSucc] using hx)
      have hyx : y = x := cyclicNext_injective hy
      exact (hxS (hyx ▸ hyS)).elim

/-- The point reached after `t` clockwise steps from `s`. -/
def cycleFrom {N : ℕ} [NeZero N] (s : Fin N) (t : ℕ) : Fin N :=
  ⟨(s.val + t) % N, Nat.mod_lt _ (NeZero.pos N)⟩

@[simp] lemma cycleFrom_zero {N : ℕ} [NeZero N] (s : Fin N) :
    cycleFrom s 0 = s := by
  apply Fin.ext
  simp [cycleFrom, Nat.mod_eq_of_lt s.isLt]

lemma cycleFrom_succ {N : ℕ} [NeZero N] (hN : 1 < N)
    (s : Fin N) (t : ℕ) :
    cycleFrom s (t + 1) = cyclicNext (cycleFrom s t) := by
  apply Fin.ext
  simp only [cycleFrom]
  have hmod : (s.val + (t + 1)) % N = ((s.val + t) % N + 1) % N := by
    rw [show s.val + (t + 1) = (s.val + t) + 1 by omega, Nat.add_mod,
      Nat.mod_eq_of_lt hN]
  rw [hmod]
  by_cases h : (s.val + t) % N + 1 < N
  · simp [cyclicNext, h, Nat.mod_eq_of_lt h]
  · have hle : (s.val + t) % N < N := Nat.mod_lt _ (NeZero.pos N)
    have heq : (s.val + t) % N + 1 = N := by omega
    simp [cyclicNext, h, heq]

lemma exists_cycleFrom_eq {N : ℕ} [NeZero N] (s x : Fin N) :
    ∃ t : ℕ, cycleFrom s t = x := by
  refine ⟨N + x.val - s.val, ?_⟩
  apply Fin.ext
  simp only [cycleFrom]
  have hs : s.val < N := s.isLt
  have hx : x.val < N := x.isLt
  have heq : s.val + (N + x.val - s.val) = N + x.val := by omega
  rw [heq, Nat.add_mod, Nat.mod_self, zero_add]
  rw [Nat.mod_mod, Nat.mod_eq_of_lt hx]

lemma stable_eq_of_extraPositions_eq_of_mem {N : ℕ} [NeZero N] (hN : 1 < N)
    {S T : Finset (Fin N)} (hS : CyclicallyStable S)
    (hT : CyclicallyStable T) {s : Fin N} (hsS : s ∈ S) (hsT : s ∈ T)
    (hextra : extraPositions S = extraPositions T) : S = T := by
  ext x
  obtain ⟨t, ht⟩ := exists_cycleFrom_eq s x
  subst x
  induction t with
  | zero => simp [hsS, hsT]
  | succ t ih =>
      rw [cycleFrom_succ hN, mem_succ_iff_of_stable hS,
        mem_succ_iff_of_stable hT, hextra, ih]

/-- A stable set with one of its selected positions distinguished. -/
def PointedStableSet (N r : ℕ) :=
  Σ S : StableSet N r, {i : Fin N // i ∈ S.1}

instance (N r : ℕ) : Fintype (PointedStableSet N r) :=
  by
    unfold PointedStableSet
    infer_instance

lemma card_pointedStableSet (N r : ℕ) :
    Fintype.card (PointedStableSet N r) =
      Fintype.card (StableSet N r) * r := by
  change Fintype.card (Σ S : StableSet N r, {i : Fin N // i ∈ S.1}) = _
  rw [Fintype.card_sigma]
  have hfiber : ∀ S : StableSet N r,
      Fintype.card {i : Fin N // i ∈ S.1} = r := by
    intro S
    change Fintype.card (↑S.1) = r
    rw [Fintype.card_coe, S.2.1]
  simp_rw [hfiber]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-- Encode a pointed stable set by its distinguished point and the `d`
non-compulsory gap positions. -/
def pointedStableCode {r d : ℕ} (hr : 0 < r) :
    PointedStableSet (2 * r + d) r →
      Fin (2 * r + d) × Set.powersetCard (Fin (2 * r + d)) d := fun p ↦
  ⟨p.2.1, Set.powersetCard.ofCard (extraPositions_card hr p.1)⟩

lemma pointedStableCode_injective {r d : ℕ} (hr : 0 < r) :
    Function.Injective (pointedStableCode (d := d) hr) := by
  letI : NeZero (2 * r + d) := ⟨by omega⟩
  intro p q hpq
  have hs : p.2.1 = q.2.1 := congrArg Prod.fst hpq
  have he : extraPositions p.1.1 = extraPositions q.1.1 := by
    exact congrArg (fun z ↦ (z.2 : Finset (Fin (2 * r + d)))) hpq
  have hsets : p.1.1 = q.1.1 := by
    apply stable_eq_of_extraPositions_eq_of_mem (by omega) p.1.2.2 q.1.2.2 p.2.2
    · simpa [hs] using q.2.2
    · exact he
  have hvertices : p.1 = q.1 := Subtype.ext hsets
  apply Sigma.ext hvertices
  rcases p with ⟨S, s⟩
  rcases q with ⟨T, t⟩
  simp only at hvertices hs ⊢
  subst T
  exact heq_of_eq (Subtype.ext hs)

theorem stableSet_card_mul_le {r d : ℕ} (hr : 0 < r) :
    Fintype.card (StableSet (2 * r + d) r) * r ≤
      (2 * r + d) * Nat.choose (2 * r + d) d := by
  rw [← card_pointedStableSet (2 * r + d) r]
  calc
    Fintype.card (PointedStableSet (2 * r + d) r) ≤
        Fintype.card (Fin (2 * r + d) ×
          Set.powersetCard (Fin (2 * r + d)) d) :=
      Fintype.card_le_of_injective (pointedStableCode (d := d) hr)
        (pointedStableCode_injective (d := d) hr)
    _ = (2 * r + d) * Nat.choose (2 * r + d) d := by
      rw [Fintype.card_prod, Fintype.card_fin]
      rw [← Nat.card_eq_fintype_card, Set.powersetCard.card,
        Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The polynomial vertex bound used in the lower construction. -/
theorem stableSet_card_le {r d : ℕ} (hr : 0 < r) :
    Fintype.card (StableSet (2 * r + d) r) ≤
      (d + 2) * (2 * r + d) ^ d := by
  have hmul := stableSet_card_mul_le (d := d) hr
  have hchoose := Nat.choose_le_pow (2 * r + d) d
  have hN : 2 * r + d ≤ (d + 2) * r := by
    nlinarith
  have hbig :
      Fintype.card (StableSet (2 * r + d) r) * r ≤
        ((d + 2) * (2 * r + d) ^ d) * r := by
    calc
      Fintype.card (StableSet (2 * r + d) r) * r
          ≤ (2 * r + d) * Nat.choose (2 * r + d) d := hmul
      _ ≤ (2 * r + d) * (2 * r + d) ^ d :=
        Nat.mul_le_mul_left _ hchoose
      _ ≤ ((d + 2) * (2 * r + d) ^ d) * r := by
        nlinarith [Nat.zero_le ((2 * r + d) ^ d)]
  exact Nat.le_of_mul_le_mul_right hbig hr

/-! ## Odd cycles in stable Kneser graphs -/

lemma card_sdiff_le_card_sdiff_add_card_sdiff {N : ℕ}
    (A B C : Finset (Fin N)) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  have hsub : A \ C ⊆ (A \ B) ∪ (B \ C) := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxB, hx'.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx'.1, hxB⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- If `A` and `C` are both disjoint from an `r`-set `B` inside an
ambient set of size `2r+d`, then at most `d` points of `A` are lost on
moving to `C`. -/
lemma stable_sdiff_card_le_of_common_neighbor {r d : ℕ}
    (A B C : StableSet (2 * r + d) r)
    (hAB : Disjoint A.1 B.1) (hBC : Disjoint B.1 C.1) :
    (A.1 \ C.1).card ≤ d := by
  let U := (A.1 \ C.1) ∪ C.1
  have hdisAC : Disjoint (A.1 \ C.1) C.1 := by
    exact Finset.disjoint_left.mpr fun _ hxA hxC ↦
      (Finset.mem_sdiff.mp hxA).2 hxC
  have hUcard : U.card = (A.1 \ C.1).card + r := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint hdisAC, C.2.1]
  have hUsub : U ⊆ Finset.univ \ B.1 := by
    intro x hx
    have hxnotB : x ∉ B.1 := by
      rcases Finset.mem_union.mp hx with hxA | hxC
      · exact fun hxB ↦
          Finset.disjoint_left.mp hAB (Finset.mem_sdiff.mp hxA).1 hxB
      · exact fun hxB ↦ Finset.disjoint_left.mp hBC hxB hxC
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxnotB⟩
  have hcard := Finset.card_le_card hUsub
  rw [hUcard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin, B.2.1] at hcard
  omega

/-- Along a closed odd walk of length `2q+1` in `SG(2r+d,r)`, the `q`
two-edge moves can lose at most `d` elements each, while the final set is
disjoint from the initial set. -/
theorem stableKneser_odd_walk_bound {r d q : ℕ} (hr : 0 < r)
    {v : StableSet (2 * r + d) r}
    (w : (stableKneser (2 * r + d) r).Walk v v)
    (hlen : w.length = 2 * q + 1) :
    r ≤ q * d := by
  let A : ℕ → Finset (Fin (2 * r + d)) := fun i ↦ (w.getVert (2 * i)).1
  have hstep : ∀ i < q, (A i \ A (i + 1)).card ≤ d := by
    intro i hi
    have hfirst := w.adj_getVert_succ (i := 2 * i) (by omega : 2 * i < w.length)
    have hsecond := w.adj_getVert_succ (i := 2 * i + 1)
      (by omega : 2 * i + 1 < w.length)
    apply stable_sdiff_card_le_of_common_neighbor
      (w.getVert (2 * i)) (w.getVert (2 * i + 1)) (w.getVert (2 * (i + 1)))
    · exact (stableKneser_adj hr).mp hfirst
    · apply (stableKneser_adj hr).mp
      simpa only [show 2 * i + 1 + 1 = 2 * (i + 1) by omega] using hsecond
  have htel : ∀ i ≤ q, (A 0 \ A i).card ≤ i * d := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hiq : i < q := by omega
        have htri := card_sdiff_le_card_sdiff_add_card_sdiff (A 0) (A i) (A (i + 1))
        have hprev := ih (by omega)
        have hnext := hstep i hiq
        calc
          (A 0 \ A (Nat.succ i)).card
              ≤ (A 0 \ A i).card + (A i \ A (i + 1)).card := by
                simpa only [Nat.succ_eq_add_one] using htri
          _ ≤ i * d + d := Nat.add_le_add hprev hnext
          _ = Nat.succ i * d := by simp [Nat.succ_mul]
  have hlast := w.adj_getVert_succ (i := 2 * q) (by omega : 2 * q < w.length)
  have hdis : Disjoint (A 0) (A q) := by
    apply (stableKneser_adj hr).mp
    have hend : w.getVert (2 * q + 1) = w.getVert 0 := by
      rw [← hlen, w.getVert_length, w.getVert_zero]
    simpa [A, hend] using hlast.symm
  have hsdiff : A 0 \ A q = A 0 := Finset.sdiff_eq_self_of_disjoint hdis
  have hcardA : (A 0).card = r := (w.getVert 0).2.1
  have := htel q le_rfl
  rw [hsdiff, hcardA] at this
  exact this

/-- Consequently every odd cycle in the stable Kneser graph has length at
least `2 * ceil(r/d) + 1`, in the division-free form needed below. -/
theorem stableKneser_cycle_bound {r d : ℕ} (hr : 0 < r)
    {v : StableSet (2 * r + d) r}
    {w : (stableKneser (2 * r + d) r).Walk v v}
    (hw : Odd w.length) :
    r ≤ (w.length / 2) * d := by
  obtain ⟨q, hq⟩ := hw
  have hlen : w.length = 2 * q + 1 := by omega
  have hb := stableKneser_odd_walk_bound hr w hlen
  have hhalf : w.length / 2 = q := by
    rw [hlen, Nat.mul_add_div (by omega) q 1]
    norm_num
  simpa [hhalf] using hb

end

end Erdos921
