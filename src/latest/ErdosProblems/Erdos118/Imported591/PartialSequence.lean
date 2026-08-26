import ErdosProblems.Erdos118.Imported591.BodyPrefix

namespace Erdos118.Negative

theorem boxLast_append_of_ne_nil (s t : List TaggedCoord) (ht : t ≠ []) :
    boxLast (s ++ t) = s ++ boxLast t := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      have htail : s ++ t ≠ [] := by
        intro h
        exact ht (List.append_eq_nil_iff.mp h).2
      simp only [List.cons_append, boxLast, if_neg htail, ih]

theorem hasBox_boxLast (s : List TaggedCoord) (hs : s ≠ []) :
    HasBox (boxLast s) := by
  induction s with
  | nil => exact (hs rfl).elim
  | cons a s ih =>
      by_cases ht : s = []
      · subst s
        exact ⟨⟨a.value, true⟩, by simp [boxLast], rfl⟩
      · obtain ⟨b, hb, hbox⟩ := ih ht
        refine ⟨b, ?_, hbox⟩
        simp only [boxLast, if_neg ht]
        exact List.mem_cons_of_mem a hb

/-- Tag every coordinate in a body segment as a nonbox coordinate. -/
def plainBody (u : List ℕ) : List TaggedCoord :=
  u.map fun n ↦ ⟨n, false⟩

@[simp] theorem plainBody_append (u v : List ℕ) :
    plainBody (u ++ v) = plainBody u ++ plainBody v :=
  List.map_append

@[simp] theorem plainBody_values (u : List ℕ) :
    (plainBody u).map TaggedCoord.value = u := by
  simp [plainBody, List.map_map, Function.comp_def]

theorem plainBody_ne_nil {u : List ℕ} (hu : u ≠ []) : plainBody u ≠ [] := by
  intro h
  exact hu (List.map_eq_nil_iff.mp h)

theorem noBox_plainBody (u : List ℕ) : NoBox (plainBody u) := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨n, _, rfl⟩
  rfl

theorem above_plainBody {u : List ℕ} {bound : ℕ}
    (hu : ∀ n ∈ u, bound < n) :
    ∀ a ∈ plainBody u, bound < a.value := by
  intro a ha
  rcases List.mem_map.mp ha with ⟨n, hn, rfl⟩
  exact hu n hn

theorem above_boxLast {s : List TaggedCoord} {bound : ℕ}
    (hs : ∀ a ∈ s, bound < a.value) :
    ∀ a ∈ boxLast s, bound < a.value := by
  intro a ha
  have hv : a.value ∈ (boxLast s).map TaggedCoord.value :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  rw [boxLast_values] at hv
  rcases List.mem_map.mp hv with ⟨b, hb, hba⟩
  rw [← hba]
  exact hs b hb

theorem above_append_of_pairwise {s t : List TaggedCoord} {bound : ℕ}
    (hpair : (s ++ t).Pairwise (fun a b ↦ a.value < b.value))
    (hs : s ≠ []) (habove : ∀ a ∈ s, bound < a.value) :
    ∀ a ∈ s ++ t, bound < a.value := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil s hs
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact habove a ha
  · exact (habove b hb).trans ((List.pairwise_append.mp hpair).2.2 b hb a ha)

namespace Exact

def coordinateBound (s : List TaggedCoord) : ℕ :=
  (s.map TaggedCoord.value).sum

theorem value_le_coordinateBound {s : List TaggedCoord} {a : TaggedCoord}
    (ha : a ∈ s) : a.value ≤ coordinateBound s :=
  nat_le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)

theorem allLT_of_above_bound (s t : List TaggedCoord)
    (ht : ∀ a ∈ t, coordinateBound s < a.value) : AllLT s t := by
  intro a ha b hb
  exact (value_le_coordinateBound ha).trans_lt (ht b hb)

/-- A literal tagged prefix ending partway through the next block. -/
def partialSequence (m : ℕ) (p : List (List ℕ)) (n : ℕ)
    (u : List ℕ) : List TaggedCoord :=
  ⟨m, true⟩ :: (p.flatMap taggedLevel ++ (⟨n, true⟩ :: plainBody u))

theorem partialSequence_ne_nil (m : ℕ) (p : List (List ℕ)) (n : ℕ)
    (u : List ℕ) : partialSequence m p n u ≠ [] :=
  List.cons_ne_nil _ _

theorem partialSequence_hasBox (m : ℕ) (p : List (List ℕ)) (n : ℕ)
    (u : List ℕ) : HasBox (partialSequence m p n u) :=
  ⟨⟨m, true⟩, List.mem_cons_self, rfl⟩

theorem partialSequence_append (m : ℕ) (p : List (List ℕ)) (n : ℕ)
    (u v : List ℕ) :
    partialSequence m p n (u ++ v) = partialSequence m p n u ++ plainBody v := by
  simp only [partialSequence, plainBody_append, List.cons_append, List.append_assoc]

theorem taggedWord_pairwise (x : G) :
    (taggedWord x.1).Pairwise (fun a b ↦ a.value < b.value) := by
  have hnum : ((taggedWord x.1).map TaggedCoord.value).Pairwise (· < ·) := by
    rw [taggedWord_values]
    exact x.2
  exact List.pairwise_map.mp hnum

theorem taggedWord_split (x : G) (m : ℕ) (p q : List (List ℕ))
    (n : ℕ) (a u v : List ℕ) (hroot : x.1.length = m)
    (houter : p ++ [a] ++ q = x.1) (ha : a.length = n) (hv : u ++ v = a) :
    taggedWord x.1 =
      partialSequence m p n u ++ (plainBody v ++ q.flatMap taggedLevel) := by
  have hlevel : taggedLevel a =
      ⟨n, true⟩ :: (plainBody u ++ plainBody v) := by
    change ⟨a.length, true⟩ :: plainBody a = _
    rw [ha, ← hv, plainBody_append]
  rw [taggedWord, hroot, ← houter]
  simp only [List.flatMap_append, List.flatMap_cons, List.nil_append,
    hlevel, partialSequence, List.cons_append, List.append_assoc]

/-- Passing from a partially filled block to a later level creates a
segment containing the later level's box marker. -/
theorem partialSequence_cross (m : ℕ) (p q : List (List ℕ))
    (n n' : ℕ) (a u v u' : List ℕ) (ha : a.length = n) (hv : u ++ v = a) :
    partialSequence m (p ++ [a] ++ q) n' u' =
      partialSequence m p n u ++
        (plainBody v ++ q.flatMap taggedLevel ++ (⟨n', true⟩ :: plainBody u')) := by
  have hlevel : taggedLevel a =
      ⟨n, true⟩ :: (plainBody u ++ plainBody v) := by
    change ⟨a.length, true⟩ :: plainBody a = _
    rw [ha, ← hv, plainBody_append]
  simp only [partialSequence, List.flatMap_append, List.flatMap_cons,
    List.nil_append, hlevel, List.cons_append, List.append_assoc]

/-- A proper body prefix is unchanged by marking the final coordinate.
The rest of the exact sequence is nonempty and contains a box coordinate. -/
theorem sequence_decomposition_of_body_prefix
    (x : G) (m : ℕ) (p : List (List ℕ)) (n : ℕ) (a u : List ℕ)
    (hroot : x.1.length = m) (hchild : p ++ [a] <+: x.1)
    (ha : a.length = n) (hu : u <+: a) (hproper : u.length < n) :
    ∃ t : List TaggedCoord, t ≠ [] ∧ HasBox t ∧
      sequence x = partialSequence m p n u ++ t := by
  rcases hchild with ⟨q, hq⟩
  rcases hu with ⟨v, hv⟩
  have hvne : v ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hv
    rw [hnil, List.append_nil, ha] at hlen
    omega
  let tail := plainBody v ++ q.flatMap taggedLevel
  have htail : tail ≠ [] := by
    intro hnil
    exact plainBody_ne_nil hvne (List.append_eq_nil_iff.mp hnil).1
  have hword : taggedWord x.1 = partialSequence m p n u ++ tail :=
    taggedWord_split x m p q n a u v hroot hq ha hv
  refine ⟨boxLast tail, (boxLast_ne_nil_iff tail).2 htail,
    hasBox_boxLast tail htail, ?_⟩
  rw [sequence, hword, boxLast_append_of_ne_nil _ _ htail]

/-- Completing a body above a bound also puts the entire remaining
tagged sequence above that bound, including all subsequent blocks. -/
theorem sequence_finish_above
    (x : G) (m : ℕ) (p : List (List ℕ)) (n : ℕ) (a u v : List ℕ)
    (hroot : x.1.length = m) (hchild : p ++ [a] <+: x.1)
    (ha : a.length = n) (hv : u ++ v = a) (hvne : v ≠ [])
    (bound : ℕ) (habove : ∀ z ∈ v, bound < z) :
    ∃ t : List TaggedCoord, t ≠ [] ∧ HasBox t ∧
      sequence x = partialSequence m p n u ++ t ∧
      ∀ z ∈ t, bound < z.value := by
  rcases hchild with ⟨q, hq⟩
  let tail := plainBody v ++ q.flatMap taggedLevel
  have htail : tail ≠ [] := by
    intro hnil
    exact plainBody_ne_nil hvne (List.append_eq_nil_iff.mp hnil).1
  have hword : taggedWord x.1 = partialSequence m p n u ++ tail :=
    taggedWord_split x m p q n a u v hroot hq ha hv
  have hpair : tail.Pairwise (fun a b ↦ a.value < b.value) := by
    have hp := taggedWord_pairwise x
    rw [hword] at hp
    exact (List.pairwise_append.mp hp).2.1
  have hall : ∀ z ∈ tail, bound < z.value :=
    above_append_of_pairwise hpair (plainBody_ne_nil hvne) (above_plainBody habove)
  refine ⟨boxLast tail, (boxLast_ne_nil_iff tail).2 htail,
    hasBox_boxLast tail htail, ?_, above_boxLast hall⟩
  rw [sequence, hword, boxLast_append_of_ne_nil _ _ htail]

theorem partialSequence_pairwise_of_body_prefix
    (x : G) (m : ℕ) (p : List (List ℕ)) (n : ℕ) (a u : List ℕ)
    (hroot : x.1.length = m) (hchild : p ++ [a] <+: x.1)
    (ha : a.length = n) (hu : u <+: a) (hproper : u.length < n) :
    (partialSequence m p n u).Pairwise (fun a b ↦ a.value < b.value) := by
  obtain ⟨t, _, _, ht⟩ :=
    sequence_decomposition_of_body_prefix x m p n a u hroot hchild ha hu hproper
  have hp := sequence_pairwise x
  rw [ht] at hp
  exact (List.pairwise_append.mp hp).1

end Exact
end Erdos118.Negative
