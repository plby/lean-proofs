/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos223.Basic
import ErdosProblems.Erdos223.LenzOptimization
import ErdosProblems.Erdos223.LocalSphere
import ErdosProblems.Erdos223.FourLowerConstruction
import ErdosProblems.Erdos223.VariableSphereConstruction

open scoped RealInnerProductSpace SimpleGraph

namespace Erdos223.FiveLowerConstruction

noncomputable section

/-! Orthogonal coordinate embeddings used by the five-dimensional Lenz
construction. -/

def embed3 (x : Point 3) : Point 5 :=
  EuclideanSpace.single (0 : Fin 5) (x 0) +
    EuclideanSpace.single (1 : Fin 5) (x 1) +
      EuclideanSpace.single (2 : Fin 5) (x 2)

def embed2 (y : Point 2) : Point 5 :=
  EuclideanSpace.single (3 : Fin 5) (y 0) +
    EuclideanSpace.single (4 : Fin 5) (y 1)

lemma embed3_apply (x : Point 3) (i : Fin 3) :
    embed3 x (Fin.castLE (by omega : 3 ≤ 5) i) = x i := by
  fin_cases i <;> simp [embed3]

lemma embed2_apply_three (y : Point 2) : embed2 y 3 = y 0 := by
  simp [embed2]

lemma embed2_apply_four (y : Point 2) : embed2 y 4 = y 1 := by
  simp [embed2]

lemma embed3_injective : Function.Injective embed3 := by
  intro x y h
  ext i
  have hi := congrArg (fun z : Point 5 => z (Fin.castLE (by omega : 3 ≤ 5) i)) h
  simpa [embed3_apply] using hi

lemma embed2_injective : Function.Injective embed2 := by
  intro x y h
  ext i
  fin_cases i
  · have hi := congrArg (fun z : Point 5 => z (3 : Fin 5)) h
    simpa [embed2_apply_three] using hi
  · have hi := congrArg (fun z : Point 5 => z (4 : Fin 5)) h
    simpa [embed2_apply_four] using hi

lemma inner_embed3 (x y : Point 3) :
    inner ℝ (embed3 x) (embed3 y) = inner ℝ x y := by
  simp [embed3, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_succ]

lemma inner_embed2 (x y : Point 2) :
    inner ℝ (embed2 x) (embed2 y) = inner ℝ x y := by
  simp [embed2, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_succ]

lemma inner_embed3_embed2 (x : Point 3) (y : Point 2) :
    inner ℝ (embed3 x) (embed2 y) = 0 := by
  simp [embed3, embed2, inner_add_left, inner_add_right,
    EuclideanSpace.inner_single_left]

lemma norm_embed3 (x : Point 3) : ‖embed3 x‖ = ‖x‖ := by
  have hs : ‖embed3 x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_embed3]
  nlinarith [norm_nonneg (embed3 x), norm_nonneg x]

lemma norm_embed2 (x : Point 2) : ‖embed2 x‖ = ‖x‖ := by
  have hs : ‖embed2 x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_embed2]
  nlinarith [norm_nonneg (embed2 x), norm_nonneg x]

lemma embed3_sub (x y : Point 3) : embed3 (x - y) = embed3 x - embed3 y := by
  ext i
  fin_cases i <;> simp [embed3]

lemma embed2_sub (x y : Point 2) : embed2 (x - y) = embed2 x - embed2 y := by
  ext i
  fin_cases i <;> simp [embed2]

lemma dist_embed3 (x y : Point 3) : dist (embed3 x) (embed3 y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← embed3_sub]
  exact norm_embed3 _

lemma dist_embed2 (x y : Point 2) : dist (embed2 x) (embed2 y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← embed2_sub]
  exact norm_embed2 _

lemma dist_embed3_embed2_sq (x : Point 3) (y : Point 2) :
    dist (embed3 x) (embed2 y) ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [inner_embed3, inner_embed2, inner_embed3_embed2]
  have hsymm : inner ℝ (embed2 y) (embed3 x) = 0 := by
    rw [real_inner_comm]
    exact inner_embed3_embed2 x y
  rw [hsymm, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

lemma dist_embed3_embed2_eq_one {x : Point 3} {y : Point 2}
    (hxy : ‖x‖ ^ 2 + ‖y‖ ^ 2 = 1) :
    dist (embed3 x) (embed2 y) = 1 := by
  have hs := dist_embed3_embed2_sq x y
  rw [hxy] at hs
  nlinarith [dist_nonneg (x := embed3 x) (y := embed2 y)]

/-! A generic strong five-dimensional Lenz carrier, stated so that the
odd-cardinality spherical construction can be supplied independently. -/

def combinedPoint {A : Finset (Point 3)} {B : Finset (Point 2)} (c : Point 3) :
    {x // x ∈ A} ⊕ {y // y ∈ B} → Point 5
  | .inl x => embed3 (x.1 - c)
  | .inr y => embed2 y.1

lemma dist_combinedPoint_inl {A : Finset (Point 3)} {B : Finset (Point 2)}
    (c : Point 3) (x x' : {x // x ∈ A}) :
    dist (combinedPoint (A := A) (B := B) c (.inl x))
      (combinedPoint (A := A) (B := B) c (.inl x')) =
      dist x.1 x'.1 := by
  change dist (embed3 (x.1 - c)) (embed3 (x'.1 - c)) = dist x.1 x'.1
  rw [dist_embed3, dist_eq_norm, dist_eq_norm]
  congr 1
  abel

lemma dist_combinedPoint_inr {A : Finset (Point 3)} {B : Finset (Point 2)}
    (c : Point 3) (y y' : {y // y ∈ B}) :
    dist (combinedPoint (A := A) (B := B) c (.inr y))
      (combinedPoint (A := A) (B := B) c (.inr y')) =
      dist y.1 y'.1 := by
  exact dist_embed2 _ _

lemma dist_combinedPoint_cross {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1)
    (x : {x // x ∈ A}) (y : {y // y ∈ B}) :
    dist (combinedPoint (A := A) (B := B) c (.inl x))
      (combinedPoint (A := A) (B := B) c (.inr y)) = 1 := by
  apply dist_embed3_embed2_eq_one
  have hx : ‖x.1 - c‖ = r := by
    rw [← dist_eq_norm]
    exact hsphere x.1 x.2
  have hy : ‖y.1‖ = s := by
    simpa [dist_zero_right] using hcircle y.1 y.2
  rw [hx, hy, hradii]

lemma combinedPoint_injective {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {s : ℝ} (hcircle : ∀ y ∈ B, dist y 0 = s) (hs : 0 < s) :
    Function.Injective (combinedPoint (A := A) (B := B) c) := by
  intro u v huv
  cases u with
  | inl x =>
      cases v with
      | inl x' =>
          congr 1
          apply Subtype.ext
          have h := embed3_injective huv
          have h' := congrArg (fun z : Point 3 => z + c) h
          simpa using h'
      | inr y =>
          exfalso
          have h3 := congrArg (fun z : Point 5 => z (3 : Fin 5)) huv
          have h4 := congrArg (fun z : Point 5 => z (4 : Fin 5)) huv
          simp [combinedPoint, embed3, embed2] at h3 h4
          have hy0 : y.1 = 0 := by
            ext i
            fin_cases i <;> simp_all
          have := hcircle y.1 y.2
          rw [hy0, dist_self] at this
          linarith
  | inr y =>
      cases v with
      | inl x =>
          exfalso
          have h3 := congrArg (fun z : Point 5 => z (3 : Fin 5)) huv
          have h4 := congrArg (fun z : Point 5 => z (4 : Fin 5)) huv
          simp [combinedPoint, embed3, embed2] at h3 h4
          have hy0 : y.1 = 0 := by
            ext i
            fin_cases i <;> simp_all
          have := hcircle y.1 y.2
          rw [hy0, dist_self] at this
          linarith
      | inr y' =>
          congr 1
          exact Subtype.ext (embed2_injective huv)

def combinedConfiguration {A : Finset (Point 3)} {B : Finset (Point 2)}
    (c : Point 3) : Finset (Point 5) :=
  Finset.univ.image (combinedPoint (A := A) (B := B) c)

lemma card_combinedConfiguration {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {s : ℝ} (hcircle : ∀ y ∈ B, dist y 0 = s) (hs : 0 < s) :
    (combinedConfiguration (A := A) (B := B) c).card = A.card + B.card := by
  rw [combinedConfiguration,
    Finset.card_image_iff.mpr (combinedPoint_injective hcircle hs).injOn]
  simp

lemma mem_combinedConfiguration {A : Finset (Point 3)} {B : Finset (Point 2)}
    (c : Point 3) (v : {x // x ∈ A} ⊕ {y // y ∈ B}) :
    combinedPoint c v ∈ combinedConfiguration (A := A) (B := B) c := by
  simp [combinedConfiguration]

lemma isDiameterOne_combinedConfiguration
    {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1)
    (hA : IsDiameterOne A) (hB : IsDiameterOne B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) :
    IsDiameterOne (combinedConfiguration (A := A) (B := B) c) := by
  rw [isDiameterOne_iff]
  constructor
  · simp only [combinedConfiguration, Finset.mem_image, Finset.mem_univ, true_and]
    rintro z ⟨u, rfl⟩ w ⟨v, rfl⟩
    cases u with
    | inl x =>
        cases v with
        | inl x' => rw [dist_combinedPoint_inl]; exact hA.dist_le x.2 x'.2
        | inr y => exact (dist_combinedPoint_cross hsphere hcircle hradii x y).le
    | inr y =>
        cases v with
        | inl x =>
            rw [dist_comm]
            exact (dist_combinedPoint_cross hsphere hcircle hradii x y).le
        | inr y' => rw [dist_combinedPoint_inr]; exact hB.dist_le y.2 y'.2
  · obtain ⟨x, hx⟩ := hAn
    obtain ⟨y, hy⟩ := hBn
    let xv : {x // x ∈ A} := ⟨x, hx⟩
    let yv : {y // y ∈ B} := ⟨y, hy⟩
    exact ⟨combinedPoint c (.inl xv), mem_combinedConfiguration c (.inl xv),
      combinedPoint c (.inr yv), mem_combinedConfiguration c (.inr yv),
      dist_combinedPoint_cross hsphere hcircle hradii xv yv⟩

def combinedVertexEmbedding {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {s : ℝ} (hcircle : ∀ y ∈ B, dist y 0 = s) (hs : 0 < s) :
    ({x // x ∈ A} ⊕ {y // y ∈ B}) ↪
      {z // z ∈ combinedConfiguration (A := A) (B := B) c} where
  toFun v := ⟨combinedPoint c v, mem_combinedConfiguration c v⟩
  inj' _ _ h := combinedPoint_injective hcircle hs (Subtype.ext_iff.mp h)

def rawCountMap {A : Finset (Point 3)} {B : Finset (Point 2)} :
    Sym2 {x // x ∈ A} ⊕ (({x // x ∈ A} × {y // y ∈ B}) ⊕ Sym2 {y // y ∈ B}) →
      Sym2 ({x // x ∈ A} ⊕ {y // y ∈ B})
  | .inl e => Sym2.map Sum.inl e
  | .inr (.inl (x, y)) => s(.inl x, .inr y)
  | .inr (.inr e) => Sym2.map Sum.inr e

lemma map_inl_ne_cross {A : Finset (Point 3)} {B : Finset (Point 2)}
    (e : Sym2 {x // x ∈ A}) (x : {x // x ∈ A}) (y : {y // y ∈ B}) :
    Sym2.map Sum.inl e ≠ s(.inl x, .inr y) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      intro h
      rw [Sym2.map_mk, Sym2.eq_iff] at h
      simp at h

lemma map_inr_ne_cross {A : Finset (Point 3)} {B : Finset (Point 2)}
    (e : Sym2 {y // y ∈ B}) (x : {x // x ∈ A}) (y : {y // y ∈ B}) :
    Sym2.map Sum.inr e ≠ s(.inl x, .inr y) := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      intro h
      rw [Sym2.map_mk, Sym2.eq_iff] at h
      simp at h

lemma cross_mk_injective {A : Finset (Point 3)} {B : Finset (Point 2)} :
    Function.Injective
      (fun q : {x // x ∈ A} × {y // y ∈ B} =>
        (s(Sum.inl q.1, Sum.inr q.2) : Sym2 ({x // x ∈ A} ⊕ {y // y ∈ B}))) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · congr
    · exact Sum.inl_injective h.1
    · exact Sum.inr_injective h.2
  · simp at h

lemma rawCountMap_injective {A : Finset (Point 3)} {B : Finset (Point 2)} :
    Function.Injective (@rawCountMap A B) := by
  intro u v h
  cases u with
  | inl e =>
      cases v with
      | inl f =>
          congr 1
          exact Sym2.map.injective Sum.inl_injective h
      | inr v =>
          cases v with
          | inl q => exact (map_inl_ne_cross e q.1 q.2 h).elim
          | inr f =>
              exfalso
              induction e using Sym2.inductionOn with
              | _ x x' =>
                  induction f using Sym2.inductionOn with
                  | _ y y' =>
                      simp only [rawCountMap, Sym2.map_mk] at h
                      rw [Sym2.eq_iff] at h
                      simp at h
  | inr u =>
      cases u with
      | inl q =>
          cases v with
          | inl e => exact (map_inl_ne_cross e q.1 q.2 h.symm).elim
          | inr v =>
              cases v with
              | inl q' => congr 2; exact cross_mk_injective h
              | inr e => exact (map_inr_ne_cross e q.1 q.2 h.symm).elim
      | inr e =>
          cases v with
          | inl f =>
              exfalso
              induction e using Sym2.inductionOn with
              | _ y y' =>
                  induction f using Sym2.inductionOn with
                  | _ x x' =>
                      simp only [rawCountMap, Sym2.map_mk] at h
                      rw [Sym2.eq_iff] at h
                      simp at h
          | inr v =>
              cases v with
              | inl q => exact (map_inr_ne_cross e q.1 q.2 h).elim
              | inr f =>
                  congr 2
                  exact Sym2.map.injective Sum.inr_injective h

def countDomain (A : Finset (Point 3)) (B : Finset (Point 2)) :
    Finset
      (Sym2 {x // x ∈ A} ⊕ (({x // x ∈ A} × {y // y ∈ B}) ⊕ Sym2 {y // y ∈ B})) :=
  (diameterGraph A).edgeFinset.disjSum
    ((Finset.univ.product Finset.univ).disjSum (diameterGraph B).edgeFinset)

lemma card_countDomain (A : Finset (Point 3)) (B : Finset (Point 2)) :
    (countDomain A B).card =
      diameterPairCount A + A.card * B.card + diameterPairCount B := by
  simp [countDomain, diameterPairCount, add_assoc]

def countMap {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {s : ℝ} (hcircle : ∀ y ∈ B, dist y 0 = s) (hs : 0 < s) :
    Sym2 {x // x ∈ A} ⊕ (({x // x ∈ A} × {y // y ∈ B}) ⊕ Sym2 {y // y ∈ B}) →
      Sym2 {z // z ∈ combinedConfiguration (A := A) (B := B) c} :=
  Sym2.map (combinedVertexEmbedding hcircle hs) ∘ rawCountMap

lemma countMap_injective {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {s : ℝ} (hcircle : ∀ y ∈ B, dist y 0 = s) (hs : 0 < s) :
    Function.Injective (@countMap A B c s hcircle hs) :=
  (Sym2.map.injective (combinedVertexEmbedding hcircle hs).injective).comp
    rawCountMap_injective

lemma countMap_mem_edge {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1) (hs : 0 < s)
    {z} (hz : z ∈ countDomain A B) :
    countMap hcircle hs z ∈
      (diameterGraph (combinedConfiguration (A := A) (B := B) c)).edgeFinset := by
  cases z with
  | inl e =>
      have he : e ∈ (diameterGraph A).edgeFinset := by
        simpa [countDomain] using hz
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      induction e using Sym2.inductionOn with
      | _ x y =>
          change dist (combinedPoint (B := B) c (.inl x))
            (combinedPoint (B := B) c (.inl y)) = 1
          rw [dist_combinedPoint_inl]
          exact he
  | inr z =>
      cases z with
      | inl q =>
          rw [SimpleGraph.mem_edgeFinset]
          change dist (combinedPoint (B := B) c (.inl q.1))
            (combinedPoint (A := A) c (.inr q.2)) = 1
          exact dist_combinedPoint_cross hsphere hcircle hradii q.1 q.2
      | inr e =>
          have he : e ∈ (diameterGraph B).edgeFinset := by
            simpa [countDomain] using hz
          rw [SimpleGraph.mem_edgeFinset] at he ⊢
          induction e using Sym2.inductionOn with
          | _ x y =>
              change dist (combinedPoint (A := A) c (.inr x))
                (combinedPoint (A := A) c (.inr y)) = 1
              rw [dist_combinedPoint_inr]
              exact he

theorem combined_exact_count_le
    {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1) (hs : 0 < s) :
    diameterPairCount A + A.card * B.card + diameterPairCount B ≤
      diameterPairCount (combinedConfiguration (A := A) (B := B) c) := by
  have hcard := Finset.card_le_card_of_injOn (@countMap A B c s hcircle hs)
    (fun _ hz => countMap_mem_edge hsphere hcircle hradii hs hz)
    (countMap_injective hcircle hs).injOn
  simpa only [card_countDomain, diameterPairCount] using hcard

/-- A construction-oriented interface which turns a complementary-radius
three-sphere and circle into a lower bound for the five-dimensional extremal
function. -/
theorem combined_count_le_f
    {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1) (hs : 0 < s)
    (hA : IsDiameterOne A) (hB : IsDiameterOne B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) :
    diameterPairCount A + A.card * B.card + diameterPairCount B ≤
      f 5 (A.card + B.card) := by
  exact (combined_exact_count_le hsphere hcircle hradii hs).trans
    (diameterPairCount_le_f (card_combinedConfiguration hcircle hs)
      (isDiameterOne_combinedConfiguration hsphere hcircle hradii hA hB hAn hBn))

/-- For a balanced pair of blocks, it is enough that their local diameter
counts add up to the total number of vertices. -/
theorem combined_balanced_lower
    {n : ℕ} {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1) (hs : 0 < s)
    (hA : IsDiameterOne A) (hB : IsDiameterOne B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hsum : A.card + B.card = n)
    (hcross : A.card * B.card = turanNumber 2 n)
    (hlocal : n ≤ diameterPairCount A + diameterPairCount B) :
    turanNumber 2 n + n ≤ f 5 n := by
  have hjoin := combined_count_le_f hsphere hcircle hradii hs hA hB hAn hBn
  rw [hsum] at hjoin
  omega

/-- The residue-zero five-dimensional construction uses parts one vertex
away from balance.  Its cross term misses the Turán number by one, which is
recovered by one additional local diameter. -/
theorem combined_one_off_lower
    {n : ℕ} {A : Finset (Point 3)} {B : Finset (Point 2)}
    {c : Point 3} {r s : ℝ}
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hcircle : ∀ y ∈ B, dist y 0 = s)
    (hradii : r ^ 2 + s ^ 2 = 1) (hs : 0 < s)
    (hA : IsDiameterOne A) (hB : IsDiameterOne B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hsum : A.card + B.card = n)
    (hcross : A.card * B.card + 1 = turanNumber 2 n)
    (hlocal : n + 1 ≤ diameterPairCount A + diameterPairCount B) :
    turanNumber 2 n + n ≤ f 5 n := by
  have hjoin := combined_count_le_f hsphere hcircle hradii hs hA hB hAn hBn
  rw [hsum] at hjoin
  omega

lemma one_off_part_sum {n : ℕ} (hn : 4 ≤ n) (hmod : n % 4 = 0) :
    (n / 2 + 1) + (n / 2 - 1) = n := by
  omega

lemma one_off_cross_count {n : ℕ} (hn : 4 ≤ n) (hmod : n % 4 = 0) :
    (n / 2 + 1) * (n / 2 - 1) + 1 = turanNumber 2 n := by
  rw [turanNumber_two]
  have hhalf : n - n / 2 = n / 2 := by omega
  rw [hhalf]
  have hq : 1 ≤ n / 2 := by omega
  have hqeq : n / 2 = (n / 2 - 1) + 1 := by omega
  rw [hqeq]
  simp only [Nat.add_sub_cancel]
  ring
theorem lower_of_odd_active_parts {a b n : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hbodd : b % 2 = 1)
    (hsum : a + b = n) (hcross : a * b = turanNumber 2 n) :
    turanNumber 2 n + n ≤ f 5 n := by
  obtain ⟨B, s, hBcard, hcircle, hs, hs_sq, hBdiam, hBcount⟩ :=
    exists_activeCircleConfiguration b hb
  let r := Real.sqrt (1 - s ^ 2)
  have hr_sq : r ^ 2 = 1 - s ^ 2 := by
    dsimp [r]
    apply Real.sq_sqrt
    linarith
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr : 1 / Real.sqrt 2 ≤ r := by
    have hi := VariableSphere.inv_sqrt_two_pos.le
    nlinarith [VariableSphere.inv_sqrt_two_sq]
  obtain ⟨A, hAcard, hsphere, hAdiam, hAcount⟩ :=
    VariableSphere.exists_large_sphere_configuration a ha hr
  have hAn : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBn : B.Nonempty := Finset.card_pos.mp (by omega)
  apply combined_balanced_lower hsphere hcircle (by linarith) hs
    hAdiam hBdiam hAn hBn
  · omega
  · simpa [hAcard, hBcard] using hcross
  · have hbcyc : cyclicDiameterAllowance b = b := by
      simp [cyclicDiameterAllowance, hbodd]
    rw [hbcyc] at hBcount
    omega

lemma balanced_parts_cross (n : ℕ) :
    (n / 2) * (n - n / 2) = turanNumber 2 n := by
  exact (turanNumber_two n).symm

theorem five_exact_lower_of_mod_ne_zero {n : ℕ} (hn : 9 ≤ n)
    (hmod : n % 4 ≠ 0) : turanNumber 2 n + n ≤ f 5 n := by
  have hcases : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hcases with h1 | h2 | h3
  · apply lower_of_odd_active_parts
      (a := n / 2) (b := n - n / 2) (n := n)
    · omega
    · omega
    · omega
    · omega
    · exact balanced_parts_cross n
  · apply lower_of_odd_active_parts
      (a := n - n / 2) (b := n / 2) (n := n)
    · omega
    · omega
    · omega
    · omega
    · rw [mul_comm]
      exact balanced_parts_cross n
  · apply lower_of_odd_active_parts
      (a := n - n / 2) (b := n / 2) (n := n)
    · omega
    · omega
    · omega
    · omega
    · rw [mul_comm]
      exact balanced_parts_cross n

theorem five_exact_lower_of_mod_zero_of_odd_sphere {n : ℕ}
    (hn : 16 ≤ n) (hmod : n % 4 = 0)
    (hoddSphere : ∃ (A : Finset (Point 3)) (c : Point 3) (r : ℝ),
      A.card = n / 2 + 1 ∧ LocalSphere.IsOnSphere A c r ∧ 0 < r ∧
        r ^ 2 < 1 / 2 ∧ IsDiameterOne A ∧
          2 * (n / 2 + 1) - 2 ≤ diameterPairCount A) :
    turanNumber 2 n + n ≤ f 5 n := by
  obtain ⟨A, c, r, hAcard, hsphere, hr, hr_sq_lt, hAdiam, hAcount⟩ := hoddSphere
  let s := Real.sqrt (1 - r ^ 2)
  have hs_sq : s ^ 2 = 1 - r ^ 2 := by
    dsimp [s]
    apply Real.sq_sqrt
    linarith
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs : 0 < s := by nlinarith
  have hs_large : 1 / Real.sqrt 2 ≤ s := by
    have hi := VariableSphere.inv_sqrt_two_pos.le
    nlinarith [VariableSphere.inv_sqrt_two_sq]
  have hb : 2 ≤ n / 2 - 1 := by omega
  let B := GenericArc.configuration s hb
  have hBcard : B.card = n / 2 - 1 := GenericArc.card_configuration hs_large hb
  have hcircle : ∀ y ∈ B, dist y 0 = s := GenericArc.on_circle hs_large hb
  have hBdiam : IsDiameterOne B := GenericArc.isDiameterOne_configuration hs_large hb
  have hBcount : 1 ≤ diameterPairCount B := GenericArc.one_le_count hs_large hb
  have hAn : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBn : B.Nonempty := Finset.card_pos.mp (by omega)
  apply combined_one_off_lower hsphere hcircle (by linarith) hs
    hAdiam hBdiam hAn hBn
  · rw [hAcard, hBcard]
    exact one_off_part_sum (by omega) hmod
  · rw [hAcard, hBcard]
    exact one_off_cross_count (by omega) hmod
  · omega

end

end Erdos223.FiveLowerConstruction
