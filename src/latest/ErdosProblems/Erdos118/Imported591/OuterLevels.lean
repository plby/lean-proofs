import ErdosProblems.Erdos118.Imported591.GoodSequenceTwo
import ErdosProblems.Erdos118.Imported591.LexPrefix

open Set Ordinal

namespace Erdos118.Negative.OuterLevels

open WeakPigeon

/-- The part of `W` on one fixed outer shortlex level. -/
def Fiber (W : Set OrderedG2) (m : ℕ) : Set OrderedG2 :=
  {x | x ∈ W ∧ x.length = m}

@[simp] theorem mem_fiber {W : Set OrderedG2} {m : ℕ} {x : OrderedG2} :
    x ∈ Fiber W m ↔ x ∈ W ∧ x.length = m := Iff.rfl

theorem fiber_disjoint (W : Set OrderedG2) {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (Fiber W m) (Fiber W n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  exact hmn (hxm.2.symm.trans hxn.2)

theorem fiber_separated (W : Set OrderedG2) {m n : ℕ} (hmn : m < n) :
    ∀ x ∈ Fiber W m, ∀ y ∈ Fiber W n, x < y := by
  intro x hx y hy
  change G2LT x y
  exact List.shortlex_def.2 (Or.inl (hx.2.trans_lt (hy.2 ▸ hmn)))

theorem mem_unionList_iff {ss : List (Set OrderedG2)} {x : OrderedG2} :
    x ∈ CNFStrong.unionList ss ↔ ∃ s ∈ ss, x ∈ s := by
  induction ss with
  | nil => simp [CNFStrong.unionList]
  | cons s ss ih => simp [CNFStrong.unionList, ih]

theorem fibers_consecutive_of_pairwise (W : Set OrderedG2) :
    ∀ {ms : List ℕ}, ms.Pairwise (· < ·) →
      CNFStrong.Consecutive (ms.map (Fiber W)) := by
  intro ms hms
  induction ms with
  | nil => trivial
  | cons m ms ih =>
      rw [List.pairwise_cons] at hms
      change Disjoint (Fiber W m)
          (CNFStrong.unionList (ms.map (Fiber W))) ∧
        (∀ x ∈ Fiber W m,
          ∀ y ∈ CNFStrong.unionList (ms.map (Fiber W)), x < y) ∧
        CNFStrong.Consecutive (ms.map (Fiber W))
      refine ⟨?_, ?_, ih hms.2⟩
      · rw [Set.disjoint_left]
        intro x hxm hxms
        rcases mem_unionList_iff.mp hxms with ⟨s, hs, hxs⟩
        rcases List.mem_map.mp hs with ⟨n, hn, rfl⟩
        exact Set.disjoint_left.mp
          (fiber_disjoint W (Nat.ne_of_lt (hms.1 n hn))) hxm hxs
      · intro x hxm y hy
        rcases mem_unionList_iff.mp hy with ⟨s, hs, hys⟩
        rcases List.mem_map.mp hs with ⟨n, hn, rfl⟩
        exact fiber_separated W (hms.1 n hn) x hxm y hys

theorem fibers_range_consecutive (W : Set OrderedG2) (r : ℕ) :
    CNFStrong.Consecutive ((List.range r).map (Fiber W)) :=
  fibers_consecutive_of_pairwise W List.pairwise_lt_range

theorem foldr_type_lt_principal (ss : List (Set OrderedG2))
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ s ∈ ss, typeLT s < delta) :
    ss.foldr (fun (s : Set OrderedG2) o ↦ typeLT s + o) 0 < delta := by
  induction ss with
  | nil => simpa using hdelta0
  | cons s ss ih =>
      simp only [List.foldr_cons]
      apply hdelta
      · exact hsmall s (by simp)
      · exact ih (fun t ht ↦ hsmall t (by simp [ht]))

theorem type_union_fibers_range_lt (W : Set OrderedG2) (r : ℕ)
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ m, typeLT (Fiber W m) < delta) :
    typeLT (CNFStrong.unionList ((List.range r).map (Fiber W))) < delta := by
  rw [CNFStrong.typeLT_unionList_of_consecutive _
    (fibers_range_consecutive W r)]
  apply foldr_type_lt_principal _ hdelta hdelta0
  intro s hs
  rcases List.mem_map.mp hs with ⟨m, -, rfl⟩
  exact hsmall m

/-- Everything below an element of outer length `m` lies in one of the
first `m+1` outer fibers. -/
noncomputable def initial_embeds_fibers_range (W : Set OrderedG2)
    (x : W) :
    RelEmbedding ((· < ·) : Set.Iio x → Set.Iio x → Prop)
      ((· < ·) :
        CNFStrong.unionList
          ((List.range (x.1.length + 1)).map (Fiber W)) →
        CNFStrong.unionList
          ((List.range (x.1.length + 1)).map (Fiber W)) → Prop) := by
  let f : Set.Iio x →
      CNFStrong.unionList ((List.range (x.1.length + 1)).map (Fiber W)) :=
    fun y ↦ ⟨y.1.1, by
      apply mem_unionList_iff.mpr
      refine ⟨Fiber W y.1.1.length, ?_, ⟨y.1.2, rfl⟩⟩
      apply List.mem_map.mpr
      refine ⟨y.1.1.length, List.mem_range.mpr ?_, rfl⟩
      apply Nat.lt_succ_iff.mpr
      have hlt : G2LT y.1.1 x.1 := y.2
      rcases List.shortlex_def.mp hlt with hlen | ⟨hlen, -⟩
      · exact hlen.le
      · exact hlen.le⟩
  exact
    { toFun := f
      inj' := by
        intro y z hyz
        have hraw : (f y).1 = (f z).1 := congrArg Subtype.val hyz
        change y.1.1 = z.1.1 at hraw
        exact Subtype.ext (Subtype.ext hraw)
      map_rel_iff' := by intro y z; rfl }

theorem typein_lt_of_fibers_small (W : Set OrderedG2)
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ m, typeLT (Fiber W m) < delta) (x : W) :
    typein LT.lt x < delta := by
  rw [← Ordinal.type_Iio_lt x]
  apply lt_of_le_of_lt (initial_embeds_fibers_range W x).ordinal_type_le
  exact type_union_fibers_range_lt W (x.1.length + 1)
    hdelta hdelta0 hsmall

theorem type_le_of_fibers_small (W : Set OrderedG2)
    {delta : Ordinal} (hdelta : IsPrincipal (· + ·) delta)
    (hdelta0 : 0 < delta)
    (hsmall : ∀ m, typeLT (Fiber W m) < delta) :
    typeLT W ≤ delta := by
  let coord : W → Set.Iio (typeLT delta.ToType) := fun x ↦
    ⟨typein LT.lt x, by
      simpa only [Set.mem_Iio, Ordinal.type_toType] using
        typein_lt_of_fibers_small W hdelta hdelta0 hsmall x⟩
  let e : RelEmbedding
      ((· < ·) : W → W → Prop)
      ((· < ·) : delta.ToType → delta.ToType → Prop) :=
    { toFun := fun x ↦ Ordinal.enum LT.lt (coord x)
      inj' := by
        intro x y hxy
        have hc : coord x = coord y :=
          (Ordinal.enum (r := LT.lt)).toEquiv.injective hxy
        apply Ordinal.typein_injective LT.lt
        exact congrArg Subtype.val hc
      map_rel_iff' := by
        intro x y
        calc
          Ordinal.enum (r := LT.lt) (coord x) <
                Ordinal.enum (r := LT.lt) (coord y) ↔ coord x < coord y :=
            (Ordinal.enum (r := LT.lt)).map_rel_iff
          _ ↔ typein LT.lt x < typein LT.lt y := Iff.rfl
          _ ↔ x < y := Ordinal.typein_lt_typein LT.lt }
  calc
    typeLT W ≤ typeLT delta.ToType := e.ordinal_type_le
    _ = delta := Ordinal.type_toType delta

/-- A fixed outer fiber is no larger than the complete fixed-length
`OmegaLevel`. -/
theorem fiber_type_le_level (W : Set OrderedG2) (m : ℕ) :
    typeLT (Fiber W m) ≤ (ω ^ ω) ^ m := by
  let e : ((· < ·) : Fiber W m → Fiber W m → Prop) ↪r
      (@OmegaLevelLex m) :=
    RelEmbedding.ofMonotone
      (fun x : Fiber W m ↦ (⟨x.1, x.2.2⟩ : OmegaLevel m)) (by
        intro x y hxy
        change G2LT x.1 y.1 at hxy
        rcases List.shortlex_def.mp hxy with hlen | ⟨-, hlex⟩
        · rw [x.2.2, y.2.2] at hlen
          exact (Nat.lt_irrefl _ hlen).elim
        · exact hlex)
  calc
    typeLT (Fiber W m) ≤ Ordinal.type (@OmegaLevelLex m) := e.ordinal_type_le
    _ = (ω ^ ω) ^ m := omegaLevel_type m

theorem theta_pow_principal (r : ℕ) :
    IsPrincipal (· + ·) ((ω ^ ω : Ordinal) ^ r) := by
  rw [← Ordinal.opow_natCast, ← Ordinal.opow_mul]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem theta_pow_pos (r : ℕ) : 0 < (ω ^ ω : Ordinal) ^ r :=
  by
    rw [← Ordinal.opow_natCast]
    exact Ordinal.opow_pos _ (Ordinal.opow_pos _ Ordinal.omega0_pos)

theorem theta_pow_strictMono : StrictMono (fun r : ℕ ↦ (ω ^ ω : Ordinal) ^ r) := by
  intro m n hmn
  change (ω ^ ω : Ordinal) ^ m < (ω ^ ω : Ordinal) ^ n
  rw [← Ordinal.opow_natCast, ← Ordinal.opow_natCast,
    Ordinal.opow_lt_opow_iff_right]
  · exact_mod_cast hmn
  · exact (Ordinal.one_lt_opow).2
      ⟨Ordinal.one_lt_omega0, Ordinal.omega0_ne_zero⟩

/-- A full `omega^(omega^2)` set has arbitrarily late outer fibers above
every prescribed finite power of `omega^omega`. -/
theorem exists_large_fiber_above_pow (W : Set OrderedG2)
    (hW : typeLT W = ω ^ (ω ^ 2)) (M k : ℕ) :
    ∃ m, M < m ∧ (ω ^ ω : Ordinal) ^ k ≤ typeLT (Fiber W m) := by
  classical
  by_contra h
  push Not at h
  let r : ℕ := max (M + 2) (k + 1)
  let delta : Ordinal := (ω ^ ω) ^ r
  have hrM : M < r := by
    dsimp [r]
    omega
  have hrk : k < r := by
    dsimp [r]
    omega
  have hsmall : ∀ m, typeLT (Fiber W m) < delta := by
    intro m
    by_cases hm : m ≤ M
    · exact (fiber_type_le_level W m).trans_lt
        (theta_pow_strictMono (hm.trans_lt hrM))
    · exact LT.lt.trans (h m (Nat.lt_of_not_ge hm))
        (theta_pow_strictMono hrk)
  have hle : typeLT W ≤ delta :=
    type_le_of_fibers_small W (theta_pow_principal r)
      (theta_pow_pos r) hsmall
  have hrω : (r : Ordinal) < ω := Ordinal.natCast_lt_omega0 r
  have hdelta : delta < (ω ^ ω : Ordinal) ^ ω := by
    dsimp [delta]
    rw [← Ordinal.opow_natCast]
    exact (Ordinal.opow_lt_opow_iff_right
      ((Ordinal.one_lt_opow).2
        ⟨Ordinal.one_lt_omega0, Ordinal.omega0_ne_zero⟩)).2 hrω
  rw [thetaOmega_eq] at hdelta
  exact (not_le_of_gt hdelta) (hW ▸ hle)

/-- Handbook 9.31's first numerical selection step. -/
theorem exists_large_fiber_above (W : Set OrderedG2)
    (hW : typeLT W = ω ^ (ω ^ 2)) (M : ℕ) :
    ∃ m, M < m ∧ (ω ^ ω : Ordinal) ^ 4 ≤ typeLT (Fiber W m) :=
  exists_large_fiber_above_pow W hW M 4

end Erdos118.Negative.OuterLevels
