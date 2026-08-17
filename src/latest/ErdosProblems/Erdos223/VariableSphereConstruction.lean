import ErdosProblems.Erdos223.CenteredArcConstruction
import ErdosProblems.Erdos223.LocalSphere

open Metric
open scoped RealInnerProductSpace SimpleGraph

namespace Erdos223.VariableSphere

noncomputable section

def latitude (r : ℝ) : ℝ := r - 1 / (2 * r)
def baseRadius (r : ℝ) : ℝ := Real.sqrt (1 - 1 / (4 * r ^ 2))

lemma inv_sqrt_two_pos : 0 < (1 / Real.sqrt 2 : ℝ) := by positivity

lemma inv_sqrt_two_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  field_simp [hp.ne']
  nlinarith

lemma half_le_sq {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) : 1 / 2 ≤ r ^ 2 := by
  have hrp : 0 ≤ r := inv_sqrt_two_pos.le.trans hr
  have hp := mul_nonneg (sub_nonneg.mpr hr)
    (add_nonneg hrp inv_sqrt_two_pos.le)
  rw [show (1 / 2 : ℝ) = (1 / Real.sqrt 2) ^ 2 by exact inv_sqrt_two_sq.symm]
  nlinarith

lemma baseRadius_sq {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) :
    baseRadius r ^ 2 = 1 - 1 / (4 * r ^ 2) := by
  apply Real.sq_sqrt
  have hr2 := half_le_sq hr
  have hrp : 0 < r := inv_sqrt_two_pos.trans_le hr
  have hden : 0 < 4 * r ^ 2 := by positivity
  rw [sub_nonneg, div_le_one hden]
  nlinarith

lemma baseRadius_pos {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) : 0 < baseRadius r := by
  unfold baseRadius
  apply Real.sqrt_pos.2
  have hr2 := half_le_sq hr
  have hrp : 0 < r := inv_sqrt_two_pos.trans_le hr
  have hden : 0 < 4 * r ^ 2 := by positivity
  rw [sub_pos, div_lt_one hden]
  nlinarith

lemma inv_sqrt_two_le_baseRadius {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) :
    1 / Real.sqrt 2 ≤ baseRadius r := by
  have hb := baseRadius_sq hr
  have hr2 := half_le_sq hr
  have hrp : 0 < r := inv_sqrt_two_pos.trans_le hr
  have hden : 0 < 4 * r ^ 2 := by positivity
  have hfrac : 1 / (4 * r ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hbp := (baseRadius_pos hr).le
  have hi := inv_sqrt_two_pos.le
  nlinarith [inv_sqrt_two_sq]

lemma baseRadius_sq_add_latitude_sq {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) :
    baseRadius r ^ 2 + latitude r ^ 2 = r ^ 2 := by
  have hb := baseRadius_sq hr
  have hr0 : r ≠ 0 := (inv_sqrt_two_pos.trans_le hr).ne'
  unfold latitude
  field_simp [hr0] at hb ⊢
  nlinarith

lemma baseRadius_sq_add_pole_gap_sq {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) :
    baseRadius r ^ 2 + (r - latitude r) ^ 2 = 1 := by
  have hb := baseRadius_sq hr
  have hr0 : r ≠ 0 := (inv_sqrt_two_pos.trans_le hr).ne'
  unfold latitude
  field_simp [hr0] at hb ⊢
  nlinarith

def liftBase (r : ℝ) (x : Point 2) : Point 3 :=
  EuclideanSpace.single (0 : Fin 3) (x 0) +
    EuclideanSpace.single (1 : Fin 3) (x 1) +
      EuclideanSpace.single (2 : Fin 3) (latitude r)

def pole (r : ℝ) : Point 3 := EuclideanSpace.single (2 : Fin 3) r

lemma inner_eq_coordinates3 (z w : Point 3) :
    inner ℝ z w = z 0 * w 0 + z 1 * w 1 + z 2 * w 2 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  ring

lemma norm_sq_point3 (z : Point 3) :
    ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_coordinates3]
  ring

lemma norm_liftBase_sq (r : ℝ) (x : Point 2) :
    ‖liftBase r x‖ ^ 2 = ‖x‖ ^ 2 + latitude r ^ 2 := by
  rw [norm_sq_point3, GenericArc.norm_sq_eq_coordinates]
  simp [liftBase]

lemma norm_pole (r : ℝ) (hr : 0 ≤ r) : ‖pole r‖ = r := by
  have hs : ‖pole r‖ ^ 2 = r ^ 2 := by
    rw [norm_sq_point3]
    simp [pole]
  nlinarith [norm_nonneg (pole r)]

lemma dist_liftBase (r : ℝ) (x y : Point 2) :
    dist (liftBase r x) (liftBase r y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have hs : ‖liftBase r x - liftBase r y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    rw [norm_sq_point3, GenericArc.norm_sq_eq_coordinates]
    simp [liftBase]
  nlinarith [norm_nonneg (liftBase r x - liftBase r y), norm_nonneg (x - y)]

lemma dist_pole_liftBase_sq (r : ℝ) (x : Point 2) :
    dist (pole r) (liftBase r x) ^ 2 = ‖x‖ ^ 2 + (r - latitude r) ^ 2 := by
  rw [dist_eq_norm]
  rw [norm_sq_point3, GenericArc.norm_sq_eq_coordinates]
  simp [pole, liftBase]

def basePoint (r : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : Point 3 :=
  liftBase r (GenericArc.arcPoint (baseRadius r) hk i)

lemma basePoint_injective {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) : Function.Injective (@basePoint r k hk) := by
  intro i j h
  apply GenericArc.arcPoint_injective (inv_sqrt_two_le_baseRadius hr) hk
  ext q
  fin_cases q
  · simpa [basePoint, liftBase] using congrArg (fun z : Point 3 ↦ z 0) h
  · simpa [basePoint, liftBase] using congrArg (fun z : Point 3 ↦ z 1) h

lemma basePoint_ne_pole {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : basePoint r hk i ≠ pole r := by
  intro h
  have hz := congrArg (fun z : Point 3 ↦ z 2) h
  have heq : latitude r = r := by simpa [basePoint, liftBase, pole] using hz
  have hrp : 0 < r := inv_sqrt_two_pos.trans_le hr
  have hterm : 0 < 1 / (2 * r) := by positivity
  unfold latitude at heq
  linarith

def configuration (r : ℝ) {k : ℕ} (hk : 2 ≤ k) : Finset (Point 3) :=
  insert (pole r) (Finset.univ.image (basePoint r hk))

lemma card_configuration {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) : (configuration r hk).card = k + 1 := by
  rw [configuration, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_iff.mpr (basePoint_injective hr hk).injOn]
    simp
  · simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rintro ⟨i, hi⟩
    exact basePoint_ne_pole hr hk i hi

lemma mem_pole_configuration (r : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    pole r ∈ configuration r hk := by simp [configuration]

lemma mem_basePoint_configuration (r : ℝ) {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    basePoint r hk i ∈ configuration r hk := by simp [configuration]

lemma dist_basePoint_zero {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : dist (basePoint r hk i) 0 = r := by
  rw [dist_zero_right]
  have hn := norm_liftBase_sq r (GenericArc.arcPoint (baseRadius r) hk i)
  have ha := GenericArc.norm_arcPoint_sq (baseRadius_pos hr) hk i
  have hid := baseRadius_sq_add_latitude_sq hr
  have hrp : 0 ≤ r := (inv_sqrt_two_pos.trans_le hr).le
  have hnp := norm_nonneg (basePoint r hk i)
  have hsquare : ‖basePoint r hk i‖ ^ 2 = r ^ 2 := by
    simpa only [basePoint] using hn.trans (by linarith)
  nlinarith

lemma dist_pole_basePoint {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) (i : Fin k) :
    dist (pole r) (basePoint r hk i) = 1 := by
  have hd := dist_pole_liftBase_sq r (GenericArc.arcPoint (baseRadius r) hk i)
  have ha := GenericArc.norm_arcPoint_sq (baseRadius_pos hr) hk i
  have hid := baseRadius_sq_add_pole_gap_sq hr
  have hnon := dist_nonneg (x := pole r) (y := basePoint r hk i)
  have hsquare : dist (pole r) (basePoint r hk i) ^ 2 = 1 := by
    simpa only [basePoint] using hd.trans (by linarith)
  nlinarith

lemma on_sphere {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) :
    LocalSphere.IsOnSphere (configuration r hk) 0 r := by
  intro x hx
  rw [configuration] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simpa [dist_comm] using norm_pole r (inv_sqrt_two_pos.trans_le hr).le
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact dist_basePoint_zero hr hk i

lemma isDiameterOne_configuration {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) : IsDiameterOne (configuration r hk) := by
  rw [isDiameterOne_iff]
  constructor
  · intro x hx y hy
    rw [configuration] at hx hy
    rcases Finset.mem_insert.mp hx with rfl | hx <;>
      rcases Finset.mem_insert.mp hy with rfl | hy
    · simp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      exact (dist_pole_basePoint hr hk j).le
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [dist_comm]
      exact (dist_pole_basePoint hr hk i).le
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
      change dist (liftBase r (GenericArc.arcPoint (baseRadius r) hk i))
        (liftBase r (GenericArc.arcPoint (baseRadius r) hk j)) ≤ 1
      rw [dist_liftBase]
      exact GenericArc.dist_arcPoint_le_one (inv_sqrt_two_le_baseRadius hr) hk i j
  · let i : Fin k := ⟨0, by omega⟩
    exact ⟨pole r, mem_pole_configuration r hk, basePoint r hk i,
      mem_basePoint_configuration r hk i, dist_pole_basePoint hr hk i⟩

def baseVertex {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) (i : Fin k) : {x // x ∈ configuration r hk} :=
  ⟨basePoint r hk i, mem_basePoint_configuration r hk i⟩

def poleVertex {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) : {x // x ∈ configuration r hk} :=
  ⟨pole r, mem_pole_configuration r hk⟩

lemma degree_pole_ge {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) :
    k ≤ (diameterGraph (configuration r hk)).degree (poleVertex hr hk) := by
  let e : Fin k → (diameterGraph (configuration r hk)).neighborSet (poleVertex hr hk) :=
    fun i ↦ ⟨baseVertex hr hk i, by
      change (diameterGraph (configuration r hk)).Adj (poleVertex hr hk) (baseVertex hr hk i)
      rw [diameterGraph_adj]
      exact dist_pole_basePoint hr hk i⟩
  have he : Function.Injective e := by
    intro i j h
    exact basePoint_injective hr hk
      (congrArg (fun z ↦ ((z : (diameterGraph (configuration r hk)).neighborSet
        (poleVertex hr hk)) : {x // x ∈ configuration r hk}).1) h)
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e he

lemma endpoint_adj_after_delete {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) :
    ((diameterGraph (configuration r hk)).deleteIncidenceSet (poleVertex hr hk)).Adj
      (baseVertex hr hk ⟨0, by omega⟩) (baseVertex hr hk ⟨k - 1, by omega⟩) := by
  apply SimpleGraph.deleteIncidenceSet_adj.mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [diameterGraph_adj]
    change dist (liftBase r (GenericArc.arcPoint (baseRadius r) hk ⟨0, by omega⟩))
      (liftBase r (GenericArc.arcPoint (baseRadius r) hk ⟨k - 1, by omega⟩)) = 1
    rw [dist_liftBase]
    exact GenericArc.dist_arc_endpoints_eq_one (inv_sqrt_two_le_baseRadius hr) hk
  · intro h
    exact basePoint_ne_pole hr hk _ (congrArg Subtype.val h)
  · intro h
    exact basePoint_ne_pole hr hk _ (congrArg Subtype.val h)

lemma count_ge {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r)
    {k : ℕ} (hk : 2 ≤ k) : k + 1 ≤ diameterPairCount (configuration r hk) := by
  let G := diameterGraph (configuration r hk)
  let p := poleVertex hr hk
  let u := baseVertex hr hk (⟨0, by omega⟩ : Fin k)
  let v := baseVertex hr hk (⟨k - 1, by omega⟩ : Fin k)
  have huv : (G.deleteIncidenceSet p).Adj u v := endpoint_adj_after_delete hr hk
  have hnonempty : (G.deleteIncidenceSet p).edgeFinset.Nonempty := by
    refine ⟨s(u, v), ?_⟩
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact huv
  have hdeleted : 1 ≤ (G.deleteIncidenceSet p).edgeFinset.card :=
    Finset.one_le_card.mpr hnonempty
  have hdeg : k ≤ G.degree p := degree_pole_ge hr hk
  have hdeg_edges : G.degree p ≤ G.edgeFinset.card := G.degree_le_card_edgeFinset p
  have hcard_delete := G.card_edgeFinset_deleteIncidenceSet p
  change k + 1 ≤ G.edgeFinset.card
  omega

theorem exists_large_sphere_configuration (m : ℕ) (hm : 3 ≤ m)
    {r : ℝ} (hr : 1 / Real.sqrt 2 ≤ r) :
    ∃ A : Finset (Point 3), A.card = m ∧ LocalSphere.IsOnSphere A 0 r ∧
      IsDiameterOne A ∧ m ≤ diameterPairCount A := by
  let k := m - 1
  have hk : 2 ≤ k := by omega
  refine ⟨configuration r hk, ?_, on_sphere hr hk, isDiameterOne_configuration hr hk, ?_⟩
  · rw [card_configuration hr]
    omega
  · have h := count_ge hr hk
    dsimp [k] at h
    omega

end
end Erdos223.VariableSphere
