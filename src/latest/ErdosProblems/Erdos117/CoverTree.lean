import ErdosProblems.Erdos117.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Ring

/-!
# Recursive abelian covers

A finite subgroup cover can be refined by abelian covers of its members.
For a recursive scalar cover, some branch controls the cost of the entire
tree; it is not enough to bound an arbitrary single branch.
-/

namespace Erdos117

variable {G : Type*} [Group G]

theorem hasAbelianCover_of_subgroup_cover {r k : ℕ} (A : Fin r → Subgroup G)
    (hcover : ∀ x, ∃ i, x ∈ A i) (hA : ∀ i, HasAbelianCover (A i) k) :
    HasAbelianCover G (r * k) := by
  classical
  choose B hB using hA
  let C : Fin r × Fin k → Subgroup G := fun i => (B i.1 i.2).map (A i.1).subtype
  have hC : AbelianCover G (Fin r × Fin k) C := by
    constructor
    · intro i
      have := (hB i.1).1 i.2
      exact Subgroup.map_isMulCommutative (H := B i.1 i.2) (A i.1).subtype
    · intro x
      obtain ⟨i, hi⟩ := hcover x
      obtain ⟨j, hj⟩ := (hB i).2 ⟨x, hi⟩
      exact ⟨(i, j), Subgroup.mem_map.mpr ⟨⟨x, hi⟩, hj, rfl⟩⟩
  let e : (Fin r × Fin k) ≃ Fin (r * k) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨fun i => C (e.symm i), (fun i => hC.1 _), ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hC.2 x
  exact ⟨e i, by simpa using hi⟩

theorem hasAbelianCover_of_nested_cover (A : Subgroup G) {r k : ℕ}
    (C : Fin r → Subgroup G) (hle : ∀ i, C i ≤ A)
    (hcover : ∀ x ∈ A, ∃ i, x ∈ C i) (hC : ∀ i, HasAbelianCover (C i) k) :
    HasAbelianCover A (r * k) := by
  apply hasAbelianCover_of_subgroup_cover (fun i => (C i).subgroupOf A)
  · intro x
    exact hcover x x.2
  · intro i
    exact hasAbelianCover_mulEquiv (Subgroup.subgroupOfEquivOfLe (hle i)).symm (hC i)

/-- The label at a node is half the rank of its scalar alternating form. -/
inductive ScalarCoverTree (G : Type*) [Group G] (p : ℕ) : Subgroup G → ℕ → Type _
  | leaf (A : Subgroup G) (hA : IsMulCommutative A) : ScalarCoverTree G p A 0
  | node (A : Subgroup G) (m : ℕ) {L : ℕ}
      (C : Fin (p ^ m + 1) → Subgroup G) (hle : ∀ i, C i ≤ A)
      (hcover : ∀ x ∈ A, ∃ i, x ∈ C i)
      (children : ∀ i, ScalarCoverTree G p (C i) L) : ScalarCoverTree G p A (L + 1)

namespace ScalarCoverTree

variable {p : ℕ}

def Branch {A : Subgroup G} {L : ℕ} (t : ScalarCoverTree G p A L) :
    List (Subgroup G × ℕ) → Prop :=
  match t with
  | .leaf _ _ => fun b => b = []
  | .node A m _ _ _ children => fun b =>
      ∃ i c, (children i).Branch c ∧ b = (A, m) :: c

def cost (p : ℕ) (b : List (Subgroup G × ℕ)) : ℕ :=
  (b.map (fun x => p ^ x.2 + 1)).prod

/-- A property of each labelled node, retaining its depth in the recursion. -/
def Satisfies (P : ℕ → Subgroup G → ℕ → Prop) {A : Subgroup G} {L : ℕ}
    (t : ScalarCoverTree G p A L) (j : ℕ) : Prop :=
  match t with
  | .leaf _ _ => True
  | .node A m _ _ _ children => P j A m ∧ ∀ i, (children i).Satisfies P (j + 1)

theorem branch_length {A : Subgroup G} {L : ℕ} (t : ScalarCoverTree G p A L)
    {b : List (Subgroup G × ℕ)} (hb : t.Branch b) : b.length = L := by
  induction t generalizing b with
  | leaf A hA => rw [hb]; rfl
  | node A m C hle hcover children ih =>
    obtain ⟨i, c, hc, rfl⟩ := hb
    simp only [List.length_cons, ih i hc]

theorem branch_le_root {A : Subgroup G} {L : ℕ} (t : ScalarCoverTree G p A L)
    {b : List (Subgroup G × ℕ)} (hb : t.Branch b) : ∀ a ∈ b, a.1 ≤ A := by
  induction t generalizing b with
  | leaf A hA => simp [Branch] at hb; simp [hb]
  | node A m C hle hcover children ih =>
    obtain ⟨i, c, hc, rfl⟩ := hb
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_rfl
    · exact (ih i hc a ha).trans (hle i)

theorem satisfies_branch {P : ℕ → Subgroup G → ℕ → Prop}
    {A : Subgroup G} {L j : ℕ} (t : ScalarCoverTree G p A L)
    (ht : t.Satisfies P j) {b : List (Subgroup G × ℕ)} (hb : t.Branch b) :
    ∀ i : Fin b.length, P (j + i.val) (b.get i).1 (b.get i).2 := by
  induction t generalizing j b with
  | leaf A hA =>
    subst b
    exact fun i => Fin.elim0 i
  | node A m C hle hcover children ih =>
    obtain ⟨k, c, hc, rfl⟩ := hb
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using ht.1
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih k (ht.2 k) hc i

theorem branch_antitone {A : Subgroup G} {L : ℕ} (t : ScalarCoverTree G p A L)
    {b : List (Subgroup G × ℕ)} (hb : t.Branch b) :
    Antitone (fun i : Fin b.length => (b.get i).1) := by
  induction t generalizing b with
  | leaf A hA =>
    subst b
    exact fun i => Fin.elim0 i
  | node A m C hle hcover children ih =>
    obtain ⟨k, c, hc, rfl⟩ := hb
    intro i j hij
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    cases i with
    | zero =>
      cases j with
      | zero => exact le_rfl
      | succ j =>
        let jj : Fin c.length := ⟨j, by simp only [List.length_cons] at hj; omega⟩
        exact ((children k).branch_le_root hc (c.get jj) (List.get_mem c jj)).trans (hle k)
    | succ i =>
      cases j with
      | zero => exact (Nat.not_succ_le_zero i hij).elim
      | succ j =>
        let ii : Fin c.length := ⟨i, by simp only [List.length_cons] at hi; omega⟩
        let jj : Fin c.length := ⟨j, by simp only [List.length_cons] at hj; omega⟩
        exact ih k hc (show ii ≤ jj from by simpa [ii, jj, Fin.le_iff_val_le_val] using hij)

/-- One branch controls the cost of the whole cover. Consequently a bound
proved for every branch controls the cover, as required in Lemma 5.3. -/
theorem exists_branch_cover {A : Subgroup G} {L : ℕ} (t : ScalarCoverTree G p A L) :
    ∃ b, t.Branch b ∧ HasAbelianCover A (cost p b) := by
  classical
  induction t with
  | leaf A hA =>
    let := hA
    refine ⟨[], rfl, ?_⟩
    apply (hasAbelianCover_iff_coloring 1).mpr
    exact ⟨fun _ => 0, fun x y _ => mul_comm' x y⟩
  | node A m C hle hcover children ih =>
    choose b hb hB using ih
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => cost p (b i))
      Finset.univ_nonempty
    refine ⟨(A, m) :: b i, ⟨i, b i, hb i, rfl⟩, ?_⟩
    change HasAbelianCover A ((p ^ m + 1) * cost p (b i))
    apply hasAbelianCover_of_nested_cover A C hle hcover
    intro j
    exact hasAbelianCover_mono (hB j) (hmax j (Finset.mem_univ j))

theorem cost_le (hp : 1 ≤ p) (b : List (Subgroup G × ℕ)) :
    cost p b ≤ 2 ^ b.length * p ^ (b.map Prod.snd).sum := by
  induction b with
  | nil => simp [cost]
  | cons a b ih =>
    have hpw : 1 ≤ p ^ a.2 := one_le_pow₀ hp
    calc
      cost p (a :: b) = (p ^ a.2 + 1) * cost p b := rfl
      _ ≤ (2 * p ^ a.2) * (2 ^ b.length * p ^ (b.map Prod.snd).sum) :=
        Nat.mul_le_mul (by omega) ih
      _ = 2 ^ (a :: b).length * p ^ ((a :: b).map Prod.snd).sum := by
        simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ, pow_add]
        ring

theorem exists_branch_exponential_cover (hp : 1 ≤ p)
    {A : Subgroup G} {L : ℕ} (t : ScalarCoverTree G p A L) :
    ∃ b, t.Branch b ∧ HasAbelianCover A (2 ^ L * p ^ (b.map Prod.snd).sum) := by
  obtain ⟨b, hb, hcover⟩ := t.exists_branch_cover
  refine ⟨b, hb, hasAbelianCover_mono hcover ?_⟩
  simpa only [t.branch_length hb] using cost_le hp b

end ScalarCoverTree

end Erdos117
