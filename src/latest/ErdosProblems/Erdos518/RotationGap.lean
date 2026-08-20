/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

/-!
# The sharp ordered-list gap lemma used in the rotation argument

Let `C = [x₂,…,xₜ₋₁]` be the internal vertices of an ordered path and let `U`
be the vertices of `C` already used by two disjoint balanced alternating paths.
The 1995 Erdős--Gyárfás rotation argument needs the following sharp fact.  If
`|U| ≤ b-1` and `b < ⌈t/2⌉`, then two consecutive members of `C` are outside
`U`, except in the unique borderline configuration: `t` is odd,
`b+1 = ⌈t/2⌉`, and precisely the zero-based odd positions of `C` are used.

The statements below are purely finite and make no reference to graphs.
-/

namespace Erdos518

universe u

variable {V : Type u}

/-- The vertices at zero-based odd positions of a list.  Thus, for the internal
list `[x₂,x₃,…]`, this is `{x₃,x₅,…}`. -/
def oddIndexedVertices [DecidableEq V] : List V → Finset V
  | [] => ∅
  | [_] => ∅
  | _ :: b :: r => insert b (oddIndexedVertices r)

lemma oddIndexedVertices_subset_toFinset [DecidableEq V] (C : List V) :
    oddIndexedVertices C ⊆ C.toFinset := by
  induction C using List.twoStepInduction with
  | nil => simp [oddIndexedVertices]
  | singleton a => simp [oddIndexedVertices]
  | cons_cons a b r ih₀ ih =>
      intro x hx
      simp only [oddIndexedVertices, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp
      · have := ih₀ hx
        simp only [List.mem_toFinset] at this ⊢
        simp [this]

lemma oddIndexedVertices_cons_subset_tail [DecidableEq V] (a : V) (r : List V) :
    oddIndexedVertices (a :: r) ⊆ r.toFinset := by
  cases r with
  | nil => simp [oddIndexedVertices]
  | cons b r =>
      intro x hx
      simp only [oddIndexedVertices, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp
      · have := oddIndexedVertices_subset_toFinset r hx
        simp only [List.mem_toFinset] at this ⊢
        simp [this]

lemma head_not_mem_oddIndexedVertices [DecidableEq V] {a : V} {r : List V}
    (h : (a :: r).Nodup) : a ∉ oddIndexedVertices (a :: r) := by
  intro ha
  have har : a ∈ r := by
    simpa using oddIndexedVertices_cons_subset_tail a r ha
  exact (List.nodup_cons.mp h).1 har

/-- Every consecutive pair in `C` contains a member of `U`. -/
def MeetsEveryAdjacentPair [DecidableEq V] (U : Finset V) (C : List V) : Prop :=
  ∀ (l r : List V) (a b : V), C = l ++ a :: b :: r → a ∈ U ∨ b ∈ U

/-- `C` contains two consecutive vertices outside `U`. -/
def HasConsecutiveOutside [DecidableEq V] (U : Finset V) (C : List V) : Prop :=
  ∃ (l r : List V) (a b : V),
    C = l ++ a :: b :: r ∧ a ∉ U ∧ b ∉ U

lemma meetsEveryAdjacentPair_of_not_hasConsecutiveOutside [DecidableEq V]
    {U : Finset V} {C : List V} (h : ¬HasConsecutiveOutside U C) :
    MeetsEveryAdjacentPair U C := by
  intro l r a b hsplit
  by_contra hab
  rw [not_or] at hab
  exact h ⟨l, r, a, b, hsplit, hab.1, hab.2⟩

/-- The vertex-cover lower bound for an ordered list: meeting every adjacent
pair costs at least half the vertices (rounded down). -/
lemma half_length_le_card_inter_of_meetsEveryAdjacentPair [DecidableEq V]
    (U : Finset V) (C : List V) (hC : C.Nodup)
    (hpair : MeetsEveryAdjacentPair U C) :
    C.length / 2 ≤ (U ∩ C.toFinset).card := by
  induction C using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b r ih₀ ih =>
      have htail := List.nodup_cons.mp hC
      have htail₂ := List.nodup_cons.mp htail.2
      have hr : r.Nodup := htail₂.2
      have hpairR : MeetsEveryAdjacentPair U r := by
        intro l r' x y hsplit
        apply hpair (a :: b :: l) r' x y
        simp [hsplit]
      have hih := ih₀ hr hpairR
      have hab : a ∈ U ∨ b ∈ U := hpair [] r a b (by simp)
      have har : a ∉ r := by
        intro ha
        exact htail.1 (by simp [ha])
      have hbr : b ∉ r := htail₂.1
      let T := U ∩ r.toFinset
      have hTsub : T ⊆ U ∩ (a :: b :: r).toFinset := by
        intro x hx
        simp only [T, Finset.mem_inter, List.mem_toFinset] at hx ⊢
        exact ⟨hx.1, by simp [hx.2]⟩
      have hcard : T.card + 1 ≤ (U ∩ (a :: b :: r).toFinset).card := by
        rcases hab with ha | hb
        · have haT : a ∉ T := by simp [T, har]
          have hins : insert a T ⊆ U ∩ (a :: b :: r).toFinset := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · simp [ha]
            · exact hTsub hx
          simpa [Finset.card_insert_of_notMem haT] using Finset.card_le_card hins
        · have hbT : b ∉ T := by simp [T, hbr]
          have hins : insert b T ⊆ U ∩ (a :: b :: r).toFinset := by
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hx
            · simp [hb]
            · exact hTsub hx
          simpa [Finset.card_insert_of_notMem hbT] using Finset.card_le_card hins
      change (r.length + 2) / 2 ≤ _
      rw [Nat.add_div_right _ (by norm_num : 0 < 2)]
      exact (Nat.add_le_add_right hih 1).trans hcard

lemma half_length_le_card_of_meetsEveryAdjacentPair [DecidableEq V]
    (U : Finset V) (C : List V) (hC : C.Nodup) (hsub : U ⊆ C.toFinset)
    (hpair : MeetsEveryAdjacentPair U C) : C.length / 2 ≤ U.card := by
  simpa [Finset.inter_eq_left.mpr hsub] using
    half_length_le_card_inter_of_meetsEveryAdjacentPair U C hC hpair

private lemma oddIndexedVertices_rigidity [DecidableEq V]
    (C : List V) (hC : C.Nodup) (U : Finset V) (hsub : U ⊆ C.toFinset)
    (hodd : Odd C.length) (hcard : U.card ≤ C.length / 2)
    (hpair : MeetsEveryAdjacentPair U C) : U = oddIndexedVertices C := by
  induction C using List.twoStepInduction generalizing U with
  | nil => simp at hodd
  | singleton a =>
      have hU0 : U.card = 0 := by simpa using hcard
      simp [oddIndexedVertices, Finset.card_eq_zero.mp hU0]
  | cons_cons a b r ih₀ ih =>
      have htail := List.nodup_cons.mp hC
      have htail₂ := List.nodup_cons.mp htail.2
      have hrN : r.Nodup := htail₂.2
      have har : a ∉ r := by
        intro ha
        exact htail.1 (by simp [ha])
      have hbr : b ∉ r := htail₂.1
      have hab : a ≠ b := by
        intro hab
        exact htail.1 (by simp [hab])
      let H := U ∩ {a, b}
      let R := U ∩ r.toFinset
      have hUeq : U = H ∪ R := by
        ext x
        simp only [H, R, Finset.mem_union, Finset.mem_inter, Finset.mem_insert,
          Finset.mem_singleton, List.mem_toFinset]
        constructor
        · intro hx
          have hxC := hsub hx
          simp only [List.mem_toFinset, List.mem_cons] at hxC
          rcases hxC with rfl | rfl | hxr
          · exact Or.inl ⟨hx, Or.inl rfl⟩
          · exact Or.inl ⟨hx, Or.inr rfl⟩
          · exact Or.inr ⟨hx, hxr⟩
        · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
      have hHR : Disjoint H R := by
        rw [Finset.disjoint_left]
        intro x hxH hxR
        have hxHead : x = a ∨ x = b := by
          have hxH' := hxH
          simp only [H, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hxH'
          exact hxH'.2
        have hxr : x ∈ r := by
          have hxR' := hxR
          simp only [R, Finset.mem_inter, List.mem_toFinset] at hxR'
          exact hxR'.2
        rcases hxHead with rfl | rfl
        · exact har hxr
        · exact hbr hxr
      have hcardEq : U.card = H.card + R.card := by
        rw [hUeq, Finset.card_union_of_disjoint hHR]
      have hHpos : 1 ≤ H.card := by
        have habU := hpair [] r a b (by simp)
        rcases habU with ha | hb
        · exact Finset.one_le_card.mpr ⟨a, by simp [H, ha]⟩
        · exact Finset.one_le_card.mpr ⟨b, by simp [H, hb]⟩
      have hpairR : MeetsEveryAdjacentPair R r := by
        intro l r' x y hsplit
        have hxy := hpair (a :: b :: l) r' x y (by simp [hsplit])
        rcases hxy with hx | hy
        · exact Or.inl (by simp [R, hx, hsplit])
        · exact Or.inr (by simp [R, hy, hsplit])
      have hRsub : R ⊆ r.toFinset := Finset.inter_subset_right
      have hRlower : r.length / 2 ≤ R.card :=
        half_length_le_card_of_meetsEveryAdjacentPair R r hrN hRsub hpairR
      have hrodd : Odd r.length := by
        rcases hodd with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        simp only [List.length_cons] at hk
        omega
      have hHcard : H.card = 1 := by
        change U.card ≤ (r.length + 2) / 2 at hcard
        rw [Nat.add_div_right _ (by norm_num : 0 < 2)] at hcard
        omega
      have hRcard : R.card = r.length / 2 := by
        change U.card ≤ (r.length + 2) / 2 at hcard
        rw [Nat.add_div_right _ (by norm_num : 0 < 2)] at hcard
        omega
      have hRpattern : R = oddIndexedVertices r :=
        ih₀ hrN R hRsub hrodd hRcard.le hpairR
      cases r with
      | nil => simp at hrodd
      | cons c r =>
          have hcR : c ∉ R := by
            rw [hRpattern]
            exact head_not_mem_oddIndexedVertices hrN
          have hbc := hpair [a] r b c (by simp)
          have hbU : b ∈ U := by
            rcases hbc with hb | hc
            · exact hb
            · exact False.elim (hcR (by simp [R, hc]))
          have hbH : b ∈ H := by simp [H, hbU]
          have hHsingleton : H = {b} := by
            obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hHcard
            have hbx : b = x := by simpa [hx] using hbH
            subst x
            exact hx
          rw [hUeq, hHsingleton, hRpattern]
          rfl

/-- The sharp gap/count dichotomy for the internal list of a path of length
`t`.  Here `(t+1)/2` is `⌈t/2⌉`. -/
theorem hasConsecutiveOutside_or_oddIndexedVertices
    [DecidableEq V] (t b : ℕ) (C : List V) (U : Finset V)
    (ht : 3 ≤ t) (hbpos : 0 < b) (hlen : C.length = t - 2)
    (hC : C.Nodup) (hsub : U ⊆ C.toFinset)
    (hcard : U.card ≤ b - 1) (hb : b < (t + 1) / 2) :
    HasConsecutiveOutside U C ∨
      (Odd t ∧ b + 1 = (t + 1) / 2 ∧ U = oddIndexedVertices C) := by
  by_cases hgap : HasConsecutiveOutside U C
  · exact Or.inl hgap
  · right
    have hpair := meetsEveryAdjacentPair_of_not_hasConsecutiveOutside hgap
    have hlower := half_length_le_card_of_meetsEveryAdjacentPair U C hC hsub hpair
    have hCeqlen : C.length + 2 = t := by omega
    have hteq : t = C.length + 2 := hCeqlen.symm
    have hCodd : Odd C.length := by
      rw [Nat.odd_iff]
      by_contra heven
      have hmod : C.length % 2 = 0 := by omega
      have hceil : (t + 1) / 2 = C.length / 2 + 1 := by
        rw [hteq]
        omega
      omega
    have hmod : C.length % 2 = 1 := Nat.odd_iff.mp hCodd
    have hceil : (t + 1) / 2 = C.length / 2 + 2 := by
      rw [hteq]
      omega
    have hbeq : b + 1 = (t + 1) / 2 := by omega
    have hUeq : U.card = C.length / 2 := by omega
    have htodd : Odd t := by
      rcases hCodd with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      omega
    exact ⟨htodd, hbeq,
      oddIndexedVertices_rigidity C hC U hsub hCodd hUeq.le hpair⟩

lemma getElem_not_mem_oddIndexedVertices_of_even [DecidableEq V]
    {C : List V} (hC : C.Nodup) {i : ℕ} (hi : i < C.length) (hieven : Even i) :
    C[i] ∉ oddIndexedVertices C := by
  induction C using List.twoStepInduction generalizing i with
  | nil => simp at hi
  | singleton a => simp [oddIndexedVertices]
  | cons_cons a b r ih₀ ih =>
      have htail := List.nodup_cons.mp hC
      have htail₂ := List.nodup_cons.mp htail.2
      cases i with
      | zero => exact head_not_mem_oddIndexedVertices hC
      | succ i =>
          cases i with
          | zero => exact False.elim (Nat.not_even_one hieven)
          | succ i =>
              have hi' : i < r.length := by simpa using hi
              have hieven' : Even i := by
                rcases hieven with ⟨k, hk⟩
                refine ⟨k - 1, ?_⟩
                omega
              intro himem
              have himem' : r[i] ∈ insert b (oddIndexedVertices r) := by
                simpa only [List.getElem_cons_succ, oddIndexedVertices] using himem
              have hir : r[i] ∈ r := List.getElem_mem _
              have hne : r[i] ≠ b := fun heq ↦ htail₂.1 (heq ▸ hir)
              exact ih₀ htail₂.2 hi' hieven'
                ((Finset.mem_insert.mp himem').resolve_left hne)

/-- The consumer-friendly form used by rotation: if a used internal vertex
occurs at a zero-based even position, then the exceptional odd-position pattern
is impossible, so two consecutive internal vertices are unused. -/
theorem hasConsecutiveOutside_of_mem_evenPosition
    [DecidableEq V] (t b : ℕ) (C : List V) (U : Finset V)
    (ht : 3 ≤ t) (hbpos : 0 < b) (hlen : C.length = t - 2)
    (hC : C.Nodup) (hsub : U ⊆ C.toFinset)
    (hcard : U.card ≤ b - 1) (hb : b < (t + 1) / 2)
    (i : ℕ) (hi : i < C.length) (hieven : Even i) (hiU : C[i] ∈ U) :
    HasConsecutiveOutside U C := by
  rcases hasConsecutiveOutside_or_oddIndexedVertices t b C U ht hbpos hlen hC hsub hcard hb with
    hgap | ⟨-, -, hpattern⟩
  · exact hgap
  · exfalso
    rw [hpattern] at hiU
    exact getElem_not_mem_oddIndexedVertices_of_even hC hi hieven hiU

end Erdos518
