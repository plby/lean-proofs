import Wikipedia.HopfProblem.FundamentalGroupVanKampenTransport

/-!
# Integrating local path values along an interval

The open-cover subdivision theorem constructs a normalized group-valued
primitive along each actual path.  The increment law holds on every local
subinterval, not just the chosen subdivision.  This also proves uniqueness
and hence independence of all choices of subdivision.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen

variable {X : Type*} [TopologicalSpace X] {ι : Type*}
variable {G : Type*} [Group G] {U : ι → Set X}

/-- Membership of a whole subpath implies membership on its parameter interval. -/
theorem mem_of_subpath_mem {x y : X} (p : Path x y) {a b : I}
    (hab : a ≤ b) {s : Set X} (hp : ∀ t, p.subpath a b t ∈ s)
    {t : I} (ht : t ∈ Icc a b) : p t ∈ s := by
  have hsub : range (p.subpath a b) ⊆ s := range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hsub
  exact hsub ⟨t, ht, rfl⟩

/-- A smaller ordered subpath remains inside a set containing the larger one. -/
theorem subpath_mem_mono {x y : X} (p : Path x y) {a b c d : I}
    (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c) (hdb : d ≤ b)
    {s : Set X} (hp : ∀ t, p.subpath a b t ∈ s) :
    ∀ t, p.subpath c d t ∈ s := by
  apply subpath_mem_of_mem_Icc p hcd
  intro t ht
  exact mem_of_subpath_mem p hab hp ⟨hac.trans ht.1, ht.2.trans hdb⟩

/-- A finite subdivision of an actual path subordinate to an open cover. -/
theorem exists_path_subdivision (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) {x y : X} (p : Path x y) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ n, t n = 1) ∧
      ∀ n, ∃ i, ∀ s ∈ Icc (t n) (t (n + 1)), p s ∈ U i := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ (hopen i).preimage p.continuous) (by
        intro s _
        have hs : p s ∈ ⋃ i, U i := by rw [hcover]; trivial
        obtain ⟨i, hi⟩ := mem_iUnion.mp hs
        exact mem_iUnion.mpr ⟨i, hi⟩)
  exact ⟨t, ht0, hmono, ⟨n, hn n le_rfl⟩, fun n ↦ hsub n⟩

namespace LocalPathValue

variable (L : LocalPathValue U G)

/-- A primitive has the prescribed increment on every local ordered subpath. -/
def IsPrimitive {x y : X} (p : Path x y) (F : I → G) : Prop :=
  ∀ (a b : I), a ≤ b → ∀ i (h : ∀ t, p.subpath a b t ∈ U i),
    F b = F a * L.value i (p.subpath a b) h

/-- The same increment condition, restricted to a prefix of the interval. -/
def IsPrimitiveUpTo {x y : X} (p : Path x y) (F : I → G) (r : I) : Prop :=
  ∀ (a b : I), a ≤ b → b ≤ r → ∀ i (h : ∀ t, p.subpath a b t ∈ U i),
    F b = F a * L.value i (p.subpath a b) h

theorem isPrimitiveUpTo_zero {x y : X} (p : Path x y) :
    L.IsPrimitiveUpTo p (fun _ ↦ 1) 0 := by
  intro a b hab hb i hi
  have ha0 : a = 0 := le_antisymm (hab.trans hb) bot_le
  have hb0 : b = 0 := le_antisymm hb bot_le
  subst a
  subst b
  simp only [Path.subpath_self, L.refl, mul_one]

/-- Extend a primitive over one local interval.  Increments crossing the old
endpoint are checked using the local subdivision law and overlap agreement. -/
theorem exists_primitiveUpTo_step {x y : X} (p : Path x y) {F : I → G}
    {a b : I} (_hab : a ≤ b) (i : ι)
    (hi : ∀ t ∈ Icc a b, p t ∈ U i) (hF : L.IsPrimitiveUpTo p F a) :
    ∃ H : I → G, H 0 = F 0 ∧ L.IsPrimitiveUpTo p H b := by
  classical
  let memi (s t : I) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      ∀ u, p.subpath s t u ∈ U i :=
    subpath_mem_of_mem_Icc p hst (fun u hu ↦ hi u ⟨has.trans hu.1, hu.2.trans htb⟩)
  let H (t : I) : G :=
    if hta : t ≤ a then F t
    else if htb : t ≤ b then F a * L.value i (p.subpath a t)
      (memi a t le_rfl (le_of_not_ge hta) htb)
    else 1
  have hleft (t : I) (hta : t ≤ a) : H t = F t := by
    exact dif_pos hta
  have hright (t : I) (hat : a ≤ t) (htb : t ≤ b) :
      H t = F a * L.value i (p.subpath a t) (memi a t le_rfl hat htb) := by
    by_cases hta : t ≤ a
    · have ht : t = a := le_antisymm hta hat
      subst t
      rw [hleft a le_rfl]
      simp only [Path.subpath_self, L.refl, mul_one]
    · dsimp only [H]
      rw [dif_neg hta, dif_pos htb]
  refine ⟨H, hleft 0 bot_le, ?_⟩
  intro s t hst htb j hj
  by_cases hta : t ≤ a
  · rw [hleft t hta, hleft s (hst.trans hta)]
    exact hF s t hst hta j hj
  have hat : a ≤ t := le_of_not_ge hta
  by_cases hsa : s ≤ a
  · have hjsa : ∀ u, p.subpath s a u ∈ U j :=
      subpath_mem_mono p hst hsa le_rfl hat hj
    have hjat : ∀ u, p.subpath a t u ∈ U j :=
      subpath_mem_mono p hst hat hsa le_rfl hj
    calc
      H t = F a * L.value i (p.subpath a t) (memi a t le_rfl hat htb) :=
        hright t hat htb
      _ = F a * L.value j (p.subpath a t) hjat := by
        rw [L.compatible i j (p.subpath a t) _ hjat]
      _ = (F s * L.value j (p.subpath s a) hjsa) *
          L.value j (p.subpath a t) hjat := by
        rw [hF s a hsa le_rfl j hjsa]
      _ = F s * L.value j (p.subpath s t) hj := by
        rw [L.subpath_mul j p s a t hsa hat hjsa hjat hj, mul_assoc]
      _ = H s * L.value j (p.subpath s t) hj := by rw [hleft s hsa]
  · have has : a ≤ s := le_of_not_ge hsa
    rw [hright t hat htb, hright s has (hst.trans htb)]
    rw [L.compatible j i (p.subpath s t) hj (memi s t has hst htb)]
    rw [L.subpath_mul i p a s t has hst
      (memi a s le_rfl has (hst.trans htb)) (memi s t has hst htb)
      (memi a t le_rfl hat htb)]
    exact (mul_assoc _ _ _).symm

/-- Every path admits a normalized primitive, with no subdivision-independence
assumption: the increment law is proved on all local subintervals. -/
theorem exists_primitive (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) {x y : X} (p : Path x y) :
    ∃ F : I → G, F 0 = 1 ∧ L.IsPrimitive p F := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ := exists_path_subdivision hopen hcover p
  have hprefix : ∀ m, ∃ F : I → G, F 0 = 1 ∧ L.IsPrimitiveUpTo p F (t m) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ ↦ 1, rfl, ?_⟩
      rw [ht0]
      exact L.isPrimitiveUpTo_zero p
    | succ m ih =>
      obtain ⟨F, hF0, hF⟩ := ih
      obtain ⟨i, hi⟩ := hsub m
      obtain ⟨H, hH0, hH⟩ :=
        L.exists_primitiveUpTo_step p (hmono m.le_succ) i hi hF
      exact ⟨H, hH0.trans hF0, hH⟩
  obtain ⟨F, hF0, hF⟩ := hprefix n
  refine ⟨F, hF0, ?_⟩
  intro a b hab i hi
  exact hF a b hab (by rw [hn]; exact le_top) i hi

/-- Primitives agreeing at the initial endpoint agree everywhere.  The proof
propagates equality over a finite subordinate subdivision. -/
theorem primitive_unique (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = univ) {x y : X} (p : Path x y) {F H : I → G}
    (hF : L.IsPrimitive p F) (hH : L.IsPrimitive p H) (h0 : F 0 = H 0) : F = H := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ := exists_path_subdivision hopen hcover p
  have hprefix : ∀ m, ∀ s ≤ t m, F s = H s := by
    intro m
    induction m with
    | zero =>
      intro s hs
      have hs0 : s = 0 := le_antisymm (by simpa only [ht0] using hs) bot_le
      simpa only [hs0] using h0
    | succ m ih =>
      intro s hs
      by_cases hst : s ≤ t m
      · exact ih s hst
      have hts : t m ≤ s := le_of_not_ge hst
      obtain ⟨i, hi⟩ := hsub m
      have hlocal : ∀ u, p.subpath (t m) s u ∈ U i :=
        subpath_mem_of_mem_Icc p hts (fun u hu ↦ hi u ⟨hu.1, hu.2.trans hs⟩)
      rw [hF (t m) s hts i hlocal, hH (t m) s hts i hlocal, ih (t m) le_rfl]
  funext s
  exact hprefix n s (by rw [hn]; exact le_top)

end LocalPathValue

end Wikipedia.HopfProblem.FundamentalGroupVanKampen
