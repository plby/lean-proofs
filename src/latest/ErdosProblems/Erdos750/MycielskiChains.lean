import ErdosProblems.Erdos750.Chains

/-!
# A chain contraction across the generalized Mycielski cylinder

At stage `t`, one shore is at height `t` and the other at height `t-1`.
Consecutive stages are contiguous maps of biclique complexes. At the final
stage one shore is the apex, so its image can be coned off.
-/

namespace Erdos750.Chains

open SourceFlags SignedSphere
open scoped BigOperators

noncomputable section
universe u v
variable {V : Type u} {W : Type v}

lemma zmod_two_eq_add_one {a b : ZMod 2} (h : a ≠ b) : b = a + 1 := by
  exact (by decide : ∀ a b : ZMod 2, a ≠ b → b = a + 1) a b h

def stageLevel (t : ℕ) (a : ZMod 2) : ℕ := if (t : ZMod 2) = a then t else t - 1

lemma stageLevel_le (t : ℕ) (a : ZMod 2) : stageLevel t a ≤ t := by
  unfold stageLevel
  split <;> omega

def atHeight (s i : ℕ) (v : V) : MycVerts s V :=
  if h : i < s then lvl s ⟨i, h⟩ v else apex s V

def stage (s t : ℕ) (x : Signed V) : Signed (MycVerts s V) :=
  (x.1, atHeight s (stageLevel t x.1) x.2)

lemma atHeight_adj {G : SimpleGraph V} {s i j : ℕ} (hs : 0 < s)
    (hi : i ≤ s) (hj : j ≤ s)
    (hij : (i = 0 ∧ j = 0) ∨ i + 1 = j ∨ j + 1 = i)
    {a b : V} (hab : G.Adj a b) :
    (genMyc s G).Adj (atHeight s i a) (atHeight s j b) := by
  by_cases his : i < s <;> by_cases hjs : j < s
  · change MycAdj s G _ _
    simp only [atHeight, dif_pos his, dif_pos hjs, lvl, MycAdj]
    rcases hij with ⟨hi0, hj0⟩ | hij | hji
    · exact Or.inl ⟨hi0, hj0, hab⟩
    · exact Or.inr (Or.inl ⟨hij.symm, hab⟩)
    · exact Or.inr (Or.inr ⟨hji.symm, hab⟩)
  · change MycAdj s G _ _
    simp only [atHeight, dif_pos his, dif_neg hjs, lvl, apex, MycAdj]
    rcases hij with h | h | h <;> omega
  · change MycAdj s G _ _
    simp only [atHeight, dif_neg his, dif_pos hjs, lvl, apex, MycAdj]
    rcases hij with h | h | h <;> omega
  · rcases hij with h | h | h <;> omega

lemma stageLevel_same {t : ℕ} {a b : ZMod 2} (hab : a ≠ b) :
    (stageLevel t a = 0 ∧ stageLevel t b = 0) ∨
      stageLevel t a + 1 = stageLevel t b ∨
      stageLevel t b + 1 = stageLevel t a := by
  by_cases ha : (t : ZMod 2) = a
  · have hb : (t : ZMod 2) ≠ b := by simpa [ha] using hab
    simp only [stageLevel, if_pos ha, if_neg hb]
    by_cases ht : t = 0
    · exact Or.inl ⟨ht, by omega⟩
    · exact Or.inr (Or.inr (by omega))
  · have hb : (t : ZMod 2) = b := by
      have h1 := zmod_two_eq_add_one ha
      have h2 := zmod_two_eq_add_one hab
      rw [h1] at h2
      have : (1 + 1 : ZMod 2) = 0 := by decide
      simpa [add_assoc, this] using h2.symm
    simp only [stageLevel, if_neg ha, if_pos hb]
    by_cases ht : t = 0
    · exact Or.inl ⟨by omega, ht⟩
    · exact Or.inr (Or.inl (by omega))

lemma stageLevel_cross {t : ℕ} {a b : ZMod 2} (hab : a ≠ b) :
    (stageLevel t a = 0 ∧ stageLevel (t + 1) b = 0) ∨
      stageLevel t a + 1 = stageLevel (t + 1) b ∨
      stageLevel (t + 1) b + 1 = stageLevel t a := by
  by_cases ha : (t : ZMod 2) = a
  · have hb : ((t + 1 : ℕ) : ZMod 2) = b := by
      simpa [ha] using (zmod_two_eq_add_one hab).symm
    simp [stageLevel, ha, hb]
  · have hb : ((t + 1 : ℕ) : ZMod 2) ≠ b := by
      have h1 := zmod_two_eq_add_one ha
      have : ((t + 1 : ℕ) : ZMod 2) = a := by simpa using h1.symm
      simpa [this] using hab
    simp only [stageLevel, if_neg ha, if_neg hb, Nat.add_sub_cancel]
    by_cases ht : t = 0
    · exact Or.inl ⟨by omega, ht⟩
    · exact Or.inr (Or.inl (by omega))

lemma stage_adj_same {G : SimpleGraph V} {s t : ℕ} (hs : 0 < s) (ht : t ≤ s)
    {a b : Signed V} (hab : a.1 ≠ b.1) (he : G.Adj a.2 b.2) :
    (genMyc s G).Adj (stage s t a).2 (stage s t b).2 :=
  atHeight_adj hs ((stageLevel_le t a.1).trans ht)
    ((stageLevel_le t b.1).trans ht) (stageLevel_same hab) he

lemma stage_adj_cross {G : SimpleGraph V} {s t : ℕ} (hs : 0 < s) (ht : t < s)
    {a b : Signed V} (hab : a.1 ≠ b.1) (he : G.Adj a.2 b.2) :
    (genMyc s G).Adj (stage s t a).2 (stage s (t + 1) b).2 :=
  atHeight_adj hs ((stageLevel_le t a.1).trans (by omega))
    ((stageLevel_le (t + 1) b.1).trans (by omega)) (stageLevel_cross hab) he

def PrismSupported {A B : Type*} (f g : A → B) (l : List A) (q : List B) : Prop :=
  ∀ y ∈ q, ∃ x ∈ l, y = f x ∨ y = g x

lemma prism_supported {A B : Type*} (f g : A → B) (l : List A) :
    Supported (PrismSupported f g l) (prism f g (basis l)) := by
  induction l with
  | nil => simpa using supported_zero (PrismSupported f g [])
  | cons x xs ih =>
    rw [prism_basis, prismBasis_cons]
    apply supported_sub
    · apply supported_basis
      intro y hy
      simp only [List.mem_cons, List.mem_map] at hy
      rcases hy with rfl | rfl | ⟨z, hz, rfl⟩
      · exact ⟨x, by simp, Or.inl rfl⟩
      · exact ⟨x, by simp, Or.inr rfl⟩
      · exact ⟨z, by simp [hz], Or.inr rfl⟩
    · rw [← prism_basis]
      refine supported_prepend (P := PrismSupported f g xs)
        (Q := PrismSupported f g (x :: xs)) (f x) ?_ ih
      intro q hq y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨x, by simp, Or.inl rfl⟩
      · obtain ⟨z, hz, h⟩ := hq y hy
        exact ⟨z, by simp [hz], h⟩

lemma prism_stage_good {G : SimpleGraph V} {s t k : ℕ} (hs : 0 < s) (ht : t < s)
    {c : Chain (Signed V)} (hc : Supported (Good G k) c) :
    Supported (Good (genMyc s G) (k + 1)) (prism (stage s t) (stage s (t + 1)) c) := by
  refine supported_linearMap (P := Good G k) (Q := Good (genMyc s G) (k + 1))
    (prism (stage s t) (stage s (t + 1))) ?_ hc
  intro l hl
  refine (supported_and (prism_supported (stage s t) (stage s (t + 1)) l)
    (prismBasis_supported_length (stage s t) (stage s (t + 1)) l)).mono
      (Q := Good (genMyc s G) (k + 1)) ?_
  intro q hq
  refine ⟨?_, by have hk := hl.2; omega⟩
  intro a ha b hb hab
  obtain ⟨x, hx, hx'⟩ := hq.1 a ha
  obtain ⟨y, hy, hy'⟩ := hq.1 b hb
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact stage_adj_same hs (by omega) hab (hl.1 x hx y hy hab)
  · exact stage_adj_cross hs ht hab (hl.1 x hx y hy hab)
  · exact (stage_adj_cross (G := G) (a := y) (b := x) hs ht hab.symm
      (hl.1 y hy x hx hab.symm)).symm
  · exact stage_adj_same hs (by omega) hab (hl.1 x hx y hy hab)

lemma Face.cons {G : SimpleGraph V} {l : List (Signed V)} {a : Signed V}
    (hl : Face G l)
    (ha : ∀ b ∈ l, a.1 ≠ b.1 → G.Adj a.2 b.2) : Face G (a :: l) := by
  intro x hx y hy hxy
  rcases List.mem_cons.mp hx with rfl | hx' <;>
    rcases List.mem_cons.mp hy with rfl | hy'
  · exact (hxy rfl).elim
  · exact ha y hy' hxy
  · exact (ha x hx' hxy.symm).symm
  · exact hl x hx' y hy' hxy

lemma stage_face {G : SimpleGraph V} {s t : ℕ} (hs : 0 < s) (ht : t ≤ s)
    {l : List (Signed V)} (hl : Face G l) : Face (genMyc s G) (l.map (stage s t)) := by
  intro a ha b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
  exact stage_adj_same hs ht hab (hl x hx y hy hab)

def top (s : ℕ) : Signed (MycVerts s V) := ((s : ZMod 2), apex s V)

lemma top_adj_stage {G : SimpleGraph V} {s : ℕ} (hs : 0 < s) {x : Signed V}
    (hx : (top s (V := V)).1 ≠ (stage s s x).1) :
    (genMyc s G).Adj (top s (V := V)).2 (stage s s x).2 := by
  have hx' : (s : ZMod 2) ≠ x.1 := hx
  change MycAdj s G (apex s V) (atHeight s (stageLevel s x.1) x.2)
  simp only [stageLevel, if_neg hx', atHeight, dif_pos (show s - 1 < s by omega),
    apex, lvl, MycAdj]
  omega

lemma cone_stage_good {G : SimpleGraph V} {s k : ℕ} (hs : 0 < s)
    {c : Chain (Signed V)} (hc : Supported (Good G k) c) :
    Supported (Good (genMyc s G) (k + 1)) (cone (top s) (stage s s) c) := by
  refine supported_linearMap (P := Good G k) (Q := Good (genMyc s G) (k + 1))
    (cone (top s) (stage s s)) ?_ hc
  intro l hl
  change Supported _ (prepend (top s) (mapVertices (stage s s) (basis l)))
  rw [mapVertices_basis, prepend_basis]
  apply supported_basis
  refine ⟨(stage_face hs le_rfl hl.1).cons ?_, by simpa using hl.2⟩
  intro b hb hab
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact top_adj_stage hs hab

lemma boundary_prisms {A B : Type*} (f : ℕ → A → B) (n : ℕ) (c : Chain A) :
    boundary ((∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) c) +
      (∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) (boundary c) =
        mapVertices (f n) c - mapVertices (f 0) c := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, LinearMap.add_apply, map_add]
    have h := boundary_prism_add_prism_boundary (f n) (f (n + 1)) c
    calc
      _ = (boundary ((∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) c) +
            (∑ t ∈ Finset.range n, prism (f t) (f (t + 1))) (boundary c)) +
          (boundary (prism (f n) (f (n + 1)) c) +
            prism (f n) (f (n + 1)) (boundary c)) := by abel
      _ = _ := by rw [ih, h]; abel

def cylinderFill (s : ℕ) : Chain (Signed V) →ₗ[ℤ] Chain (Signed (MycVerts s V)) :=
  cone (top s) (stage s s) - ∑ t ∈ Finset.range s, prism (stage s t) (stage s (t + 1))

lemma boundary_cylinderFill (s : ℕ) (c : Chain (Signed V)) :
    boundary (cylinderFill s c) + cylinderFill s (boundary c) =
      mapVertices (stage s 0) c := by
  have hc := boundary_cone (top s) (stage s s) c
  have hp := boundary_prisms (stage s (V := V)) s c
  simp only [cylinderFill, LinearMap.sub_apply, map_sub]
  calc
    _ = (boundary (cone (top s) (stage s s) c) +
          cone (top s) (stage s s) (boundary c)) -
        (boundary ((∑ t ∈ Finset.range s, prism (stage s t) (stage s (t + 1))) c) +
          (∑ t ∈ Finset.range s, prism (stage s t) (stage s (t + 1))) (boundary c)) := by abel
    _ = _ := by rw [hc, hp]; abel

lemma cylinderFill_good {G : SimpleGraph V} {s k : ℕ} (hs : 0 < s)
    {c : Chain (Signed V)} (hc : Supported (Good G k) c) :
    Supported (Good (genMyc s G) (k + 1)) (cylinderFill s c) := by
  apply supported_sub (cone_stage_good hs hc)
  simp only [LinearMap.sum_apply]
  exact supported_sum fun t ht => prism_stage_good hs (Finset.mem_range.mp ht) hc

def baseEmbedding (s : ℕ) (hs : 0 < s) (G : SimpleGraph V) : G →g genMyc s G where
  toFun v := lvl s ⟨0, hs⟩ v
  map_rel' h := Or.inl ⟨rfl, rfl, h⟩

lemma stage_zero (s : ℕ) (hs : 0 < s) (G : SimpleGraph V) :
    stage s 0 = signedMap (baseEmbedding s hs G) := by
  funext x
  have hzero : stageLevel 0 x.1 = 0 := by simp [stageLevel]
  simp [stage, hzero, atHeight, hs, signedMap, baseEmbedding]
  rfl

lemma hasResolution_genMyc {G : SimpleGraph V} {d s : ℕ}
    (h : HasResolution G d) (hs : 0 < s) : HasResolution (genMyc s G) (d + 1) := by
  obtain ⟨c, hc, hzero, hrel⟩ := h
  let f := baseEmbedding s hs G
  let e : ℕ → Chain (Signed (MycVerts s V)) := fun i =>
    if i ≤ d then mapVertices (signedMap f) (c i)
    else cylinderFill s (op (d + 1) (c d))
  have he (i : ℕ) (hi : i ≤ d) : e i = mapVertices (signedMap f) (c i) := if_pos hi
  have hetop : e (d + 1) = cylinderFill s (op (d + 1) (c d)) := if_neg (by omega)
  have hmap (i : ℕ) (hi : i ≤ d) :
      Supported (Good (genMyc s G) (i + 1)) (mapVertices (signedMap f) (c i)) := by
    rw [← stage_zero s hs G]
    refine supported_mapVertices _ (P := Good G (i + 1)) ?_ (hc i hi)
    intro l hl
    exact ⟨stage_face hs (by omega) hl.1, by simpa using hl.2⟩
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i hi
    by_cases hid : i ≤ d
    · rw [he i hid]
      exact hmap i hid
    · have hitop : i = d + 1 := by omega
      subst i
      rw [hetop]
      exact cylinderFill_good hs (supported_op (hc d le_rfl) (d + 1))
  · rw [he 0 (Nat.zero_le _), boundary_mapVertices, hzero, mapVertices_basis]
    rfl
  · intro i hi
    by_cases hid : i < d
    · rw [he (i + 1) (by omega), he i (by omega), boundary_mapVertices,
        hrel i hid, map_op]
    · have hid' : i = d := by omega
      subst i
      rw [hetop, he d le_rfl]
      have hcycle := resolution_cycle hzero hrel
      have hfill := boundary_cylinderFill s (op (d + 1) (c d))
      rw [hcycle, map_zero, add_zero, stage_zero s hs G, map_op] at hfill
      exact hfill

end
end Erdos750.Chains
