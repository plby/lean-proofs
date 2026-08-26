import ErdosProblems.Erdos547.SkewHostAssembly
import ErdosProblems.Erdos547.CanonicalShrubAllocation
import ErdosProblems.Erdos547.AllowedSeedDegrees
import ErdosProblems.Erdos547.TwoSkewFamily

/-!
# Constructing the full shrub host from a typical seed copy and a skew family
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)

theorem exists_setup_from_typical_seed (G : SimpleGraph V) [DecidableRel G.Adj]
    (K : SimpleGraph I) (C B Q : I → Finset V) (anchor : Fin 2 → I) (J : Fin 2 → Finset I)
    (seed : (T.induce (P.seeds : Set U)).Copy G)
    (D : ∀ S : ↥P.shrubs, ShrubRootData T P.seeds S.val)
    (γ : Fin 2 → ℝ) (σ : ∀ c, DPRS.SkewMatching K (γ c))
    (ε δ d η s L θ err : ℝ) (A : Fin 2 → ℝ) (m M q : ℕ)
    (hε : 0 < ε) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hs : 0 < s) (hsone : s ≤ 1)
    (hL : 0 < L) (hθ : 0 < θ) (herr : 0 ≤ err) (hA : ∀ c, 0 < A c)
    (hM : 0 < M) (hγ : ∀ c, 0 < γ c)
    (hde : 2 * ε ≤ d) (hmargin : 8 * ε ≤ d ^ 2 * η) (hprivate : ε ≤ s * θ)
    (hεm : 1 ≤ ε * m) (hseed : (P.seeds.card : ℝ) ≤ ε * m)
    (hseedq : 2 * P.seeds.card ≤ q) (hbuffer : η * m ≤ (q : ℝ) / 2)
    (hvolume : M + 2 * q = m) (hsize : ∀ i, (C i).card = m)
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hsmall : (ℓ : ℝ) ≤ ε * m) (hℓtarget : (ℓ : ℝ) ≤ s / 4 * L)
    (hreg : ∀ i j, K.Adj i j → G.IsUniform ε (C i) (C j) ∧
      Disjoint (C i) (C j) ∧ d ≤ (G.edgeDensity (C i) (C j) : ℝ))
    (hload : ∀ i, (∑ c, (σ c).load i) ≤ 1)
    (hfit : ∀ c i, (σ c).outLoad i ≤ (G.edgeDensity (C (anchor c)) (C i) : ℝ))
    (hjoint : ∀ i, (σ 0).outLoad i + (σ 1).outLoad i ≤
      max (G.edgeDensity (C (anchor 0)) (C i) : ℝ) (G.edgeDensity (C (anchor 1)) (C i) : ℝ))
    (hsupport : ∀ c i, θ ≤ (σ c).outLoad i → i ∈ J c)
    (hmass : ∀ c, A c ≤ (∑ i, (σ c).outLoad i) - θ * Fintype.card I - 2 - 4 * (δ * Fintype.card I))
    (hvariance : ∀ c, (ℓ : ℝ) * ((P.nearVertices c).card + (P.farVertices c).card) < err ^ 2)
    (hmeanNear : ∀ c, ((P.nearVertices c).card : ℝ) / A c + s * M ≤ (1 - s) * M)
    (hmeanFar : ∀ c, ((P.farVertices c).card : ℝ) / A c + s * M * γ c ≤ (1 - s) * M * γ c)
    (herrorNear : err ≤ θ * (s * M)) (herrorFar : ∀ c, err ≤ θ * (s * M * γ c))
    (htarget : ∀ c, L * Fintype.card I ≤ s / 4 * (γ c * M * θ))
    (hB : ∀ i, B i ⊆ C i) (hQ : ∀ i, Q i ⊆ C i) (hBQ : ∀ i, Disjoint (B i) (Q i))
    (hBsize : ∀ i, (B i).card = M) (hQsize : ∀ i, (Q i).card = q)
    (hseedPlace : ∀ z : ↥P.seeds, seed z ∈ C (anchor (col z.val)))
    (hmainTypical : ∀ z, ((P.seedExceptions G ε (fun c ↦ C (anchor c)) J C B seed z).card : ℝ) ≤
      δ * Fintype.card I)
    (hQTypical : ∀ z, ((P.seedExceptions G ε (fun c ↦ C (anchor c)) J C Q seed z).card : ℝ) ≤
      δ * Fintype.card I)
    (hrootMargin : 12 * ε * m ≤ (θ - ε) * q) : Nonempty (ShrubHostSetup P G I) := by
  classical
  letI : Nonempty I := ⟨anchor 0⟩
  let anchors := Finset.univ.image anchor
  let w := fun c i ↦ (σ c).outLoad i
  let badMain := P.seedExceptions G ε (fun c ↦ C (anchor c)) J C B seed
  let badQ := P.seedExceptions G ε (fun c ↦ C (anchor c)) J C Q seed
  let allowed := P.allowedHeads anchors badMain badQ w θ
  have hacard : (anchors.card : ℝ) ≤ 2 := by
    have hh : anchors.card ≤ 2 := Finset.card_image_le.trans (by simp)
    exact_mod_cast hh
  have hallowed (S : ↥P.shrubs) : A (P.shrubColour S) ≤ ∑ i ∈ allowed S, w (P.shrubColour S) i := by
    have hh := P.allowedHeads_weight anchors badMain badQ w θ (δ * Fintype.card I) hθ.le
      (mul_nonneg hδ (Nat.cast_nonneg _)) (fun c i ↦ (σ c).outLoad_le_one i)
      hmainTypical hQTypical S
    have ha := hmass (P.shrubColour S)
    change A (P.shrubColour S) ≤ _ at ha
    change _ ≤ ∑ i ∈ allowed S, w (P.shrubColour S) i at hh
    dsimp only [w] at hh ⊢
    linarith only [hh, ha, hacard]
  have hweight (S : ↥P.shrubs) (i : I) (hi : i ∈ allowed S) : θ ≤ w (P.shrubColour S) i :=
    (P.allowedHeads_properties anchors badMain badQ w θ S i hi).1
  let coeff : Fin 2 → Fin 2 → ℝ := fun c j ↦ if j = 0 then (1 - s) * M else (1 - s) * M * γ c
  let margin : Fin 2 → Fin 2 → ℝ := fun c j ↦ if j = 0 then s * M else s * M * γ c
  have hcoeff (c j : Fin 2) : 0 ≤ coeff c j := by
    have h1 : 0 ≤ 1 - s := by linarith only [hsone]
    have hg := hγ c
    dsimp only [coeff]
    split_ifs <;> positivity
  have hmar (c j : Fin 2) : 0 ≤ margin c j := by
    have hg := hγ c
    dsimp only [margin]
    split_ifs <;> positivity
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hmn (c : Fin 2) : ((P.nearVertices c).card : ℝ) / A c + margin c 0 ≤ coeff c 0 := by
    simpa only [margin, coeff, if_pos rfl] using hmeanNear c
  have hmf (c : Fin 2) : ((P.farVertices c).card : ℝ) / A c + margin c 1 ≤ coeff c 1 := by
    simpa only [margin, coeff, if_neg h10] using hmeanFar c
  have he (c j : Fin 2) : err ≤ θ * margin c j := by
    dsimp only [margin]
    split_ifs
    · exact herrorNear
    · exact herrorFar c
  obtain ⟨head, hhead, hheadload⟩ := P.exists_relative_shrub_heads allowed w A (fun _ ↦ θ) err
    coeff margin (fun c i ↦ (σ c).outLoad_nonneg i) hA herr hallowed hweight hvariance hcoeff hmar hmn hmf he
  have hnear (c : Fin 2) (i : I) : (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.nearPart S).card : ℝ)) ≤
        (1 - s) * M * (σ c).outLoad i := by
    simpa only [coeff, if_pos rfl, w] using (hheadload c i).1
  have hfar (c : Fin 2) (i : I) : (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.farPart S).card : ℝ)) ≤
        (1 - s) * M * γ c * (σ c).outLoad i := by
    simpa only [coeff, if_neg h10, w] using (hheadload c i).2
  have hactive (S : ↥P.shrubs) : θ ≤ (σ (P.shrubColour S)).outLoad (head S) := hweight S _ (hhead S)
  have hseedAvoid (S : ↥P.shrubs) (z : ↥P.seeds) : seed z ∉ C (head S) := by
    have hn := (P.allowedHeads_properties anchors badMain badQ w θ S (head S) (hhead S)).2.1
    have hne : head S ≠ anchor (col z.val) := by
      intro heq
      exact hn (heq ▸ Finset.mem_image.mpr ⟨col z.val, Finset.mem_univ _, rfl⟩)
    intro hz
    exact Finset.disjoint_left.mp (hdis (head S) (anchor (col z.val)) hne) hz (hseedPlace z)
  have hdegrees (S : ↥P.shrubs) (z : ↥P.seeds) (hz : z ∈ P.attachmentSeeds S) :=
    P.allowed_attachment_degrees G ε θ (fun c ↦ C (anchor c)) J C B Q seed anchors w
      hsupport S (head S) (hhead S) z hz
  have hmainDegree (S : ↥P.shrubs) (z : ↥P.seeds) (hz : z ∈ P.attachmentSeeds S) :
      ((G.edgeDensity (C (anchor (P.shrubColour S))) (C (head S)) : ℝ) - ε) * M ≤
        (degreeIn G (B (head S)) (seed z) : ℝ) := by
    simpa only [hBsize] using (hdegrees S z hz).1
  have hrootDegree (S : ↥P.shrubs) (z : ↥P.seeds) (hz : z ∈ P.attachmentSeeds S) :
      12 * ε * m ≤ (degreeIn G (Q (head S)) (seed z) : ℝ) := by
    have hdensity := (hactive S).trans (hfit _ _)
    have hh := mul_le_mul_of_nonneg_right (sub_le_sub_right hdensity ε) (Nat.cast_nonneg q)
    have ht := (hdegrees S z hz).2
    rw [hQsize] at ht
    exact (hrootMargin.trans hh).trans ht
  obtain ⟨roots⟩ := P.exists_prepared_root_sets G C B Q head seed D w
    (fun c i ↦ (G.edgeDensity (C (anchor c)) (C i) : ℝ)) M s ε θ (12 * ε * m)
    (Nat.cast_nonneg _) hs.le hsone hprivate hdis hB hQ hBQ hseedAvoid hfit hjoint hactive
    (fun c i ↦ by simpa only [and_comm] using hnear c i) hmainDegree hrootDegree
  exact P.exists_host_setup_of_skew_heads G K C Q head seed D γ σ ε d η s L θ m M q
    hε hη hs hsone hL hθ hM hγ hde hmargin hεm hseed hseedq hbuffer hvolume hsize hdis
    hsmall hℓtarget hreg hload hnear hfar hactive htarget hQ hQsize roots

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_setup_from_typical_seed
