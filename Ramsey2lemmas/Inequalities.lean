import Mathlib.Data.Nat.Basic

import Ramsey2lemmas.Theory
import Ramsey2lemmas.BronKerbosch

import FormalRamsey.Encodings.CNF.RamseyEncoder

import Trestle.Model.PropFun

open Trestle Model PropFun

@[simp]
lemma Fin.val_three (n : Nat) : (3 : Fin (n + 4)).val = 3 := rfl

namespace SimpleGraph

lemma σ_helper {N x y k : ℕ} {G : SimpleGraph (Fin N.succ)} [DecidableRel G.Adj] (hxy : G.isXYGraph x.succ y.succ) (σlt : σ_G hxy < k) : ∀ (f : ℕ → ℕ), (∀ i ∈ (Finset.range k \ Finset.range (σ_G hxy).succ), f i = 0) → (Finset.range (@σ_G (Fin N.succ) G x y _ _ hxy).succ).sum f = (Finset.range k).sum f := by
  simp [σ_G]
  intros f fvanish
  apply Finset.sum_subset
  · simpa
  · simp [σ_G, RamseyOld₂, vᵢ]
    intros d dlt σd
    exact fvanish d dlt σd

lemma sᵢ_vanish {N x y : ℕ} {G : SimpleGraph (Fin N.succ)} [DecidableRel G.Adj] (hxy : G.isXYGraph x.succ y.succ) (Ngt : RamseyOld x.succ y < N) (k : ℕ) : ∀ i ∈ Finset.range k \ Finset.range (σ_G hxy).succ, ∀ n, n * (G.sᵢ x y i) = 0 := by
  simp [Finset.filter_eq_empty_iff, vᵢ]
  intros d dltk σltd _
  right
  intros v vdeg
  simp [σ_G] at σltd
  cases Nat.eq_zero_or_pos (G.degree v) with
  | inl vdeg0 =>
    have absurd := (Lemma₂ G v hxy)
    simp [vdeg0] at absurd
    rw [← Nat.not_lt] at absurd
    contradiction
  | inr vdegpos =>
    simp [vdeg] at vdegpos
    symm at vdeg
    simp [Nat.sub_eq_iff_eq_add (Nat.le_of_lt vdegpos)] at vdeg
    simp [vdeg, Nat.add_one_le_iff, Nat.sub_add_comm (G.minDegree_le_degree v), RamseyOld₂] at σltd

theorem R37 : RamseyOld 3 7 = 22 := sorry

lemma e37_18 : e 3 7 18 ≥ 36 := by sorry
lemma e37_19 : e 3 7 19 ≥ 44 := by sorry
lemma e37_20 : e 3 7 20 ≥ 50 := by sorry
lemma e37_21 : e 3 7 21 ≥ 59 := by sorry

theorem Ineq₉: e 3 8 26 ≥ 80 := by
  simp only [e]
  apply le_csInf
  · let G := readG6 "Z????CDO?a@PHA_HcE_dc`PCXQ@PoSWo@_cDS_YQQB_Qo?TLSO?q_g?{p?_?"
    use G.edgeFinset.card
    simp
    use G
    apply And.intro
    · unfold SimpleGraph.isXYGraph
      rw [G.Bron_Kerbosch_cliqueNum, ← G.cliqueNum_compl, Gᶜ.Bron_Kerbosch_cliqueNum]
      native_decide
    · use (by infer_instance)
      simp [readG6Header]
  · simp [-Set.toFinset_card]
    intros _ G GisXY _ cardeqe
    rw [← cardeqe]
    have h1 := Prop₄ GisXY
    simp [-Set.toFinset_card] at h1
    have σub : σ_G GisXY < 4 := by
      simp +arith [σ_G, RamseyOld₂]
      obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
      have := (Lemma₂ G v GisXY).right
      simp +arith [R37, ← vmindeg] at this
      assumption
    have h2 := G_degreeCount_eq G GisXY
    have h3 := G_vertCount_eq G GisXY
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 7 (26 - vᵢ 2 7 d - 1) + (vᵢ 2 7 d)^2) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp [R37])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp [R37])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 7 d) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp [R37])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_four, vᵢ, RamseyOld₂ 7] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_four, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_four] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [e37_18, e37_19, e37_20, e37_21]

lemma Ineq₁₀_helper {G : SimpleGraph (Fin 28)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 8) : G.edgeFinset.card ≥ 88 := by
  have h1 := Prop₄ hxy
  simp [-Set.toFinset_card] at h1
  have σub : σ_G hxy < 3 := by
    simp +arith [σ_G, RamseyOld₂]
    obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
    have := (Lemma₂ G v hxy).right
    simp +arith [R37, ← vmindeg] at this
    assumption
  have h2 := G_degreeCount_eq G hxy
  have h3 := G_vertCount_eq G hxy
  have bilinearlb := σ_helper hxy σub (λ d ↦ (e 3 7 (27 - vᵢ 2 7 d - 1) + (vᵢ 2 7 d)^2) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 3; assumption; simp [R37])
  have vertexlb := σ_helper hxy σub (λ d ↦  1 * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 3; assumption; simp [R37])
  have degreelb := σ_helper hxy σub (λ d ↦ (vᵢ 2 7 d) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 3; assumption; simp [R37])
  simp at bilinearlb vertexlb degreelb
  -- NOTE: Using simp here maxes out hearbeats
  simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂ 7] at h1
  simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂] at h2
  simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_three] at h3
  simp at h1 h2 h3 ⊢
  nlinarith [e37_19, e37_20, e37_21]

-- theorem Ineq₁₀:
-- e 3 8 27 ≥ 88 := by
--   simp only [e]
--   sorry
--   -- apply le_csInf
--   -- simp [Set.Nonempty, -Set.toFinset_card]
--   -- sorry
--   -- simp [-Set.toFinset_card]
--   -- intro N G hxy _ hn
--   -- have := Ineq₉_helper hxy h1 h2 h3 h4
--   -- omega

lemma Ineq₁₁_helper {G : SimpleGraph (Fin 29)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 8) : G.edgeFinset.card ≥ 99 := by
  have h1 := Prop₄ hxy
  simp [-Set.toFinset_card] at h1
  have σub : σ_G hxy < 2 := by
    simp +arith [σ_G, RamseyOld₂]
    obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
    have := (Lemma₂ G v hxy).right
    simp +arith [R37, ← vmindeg] at this
    assumption
  have h2 := G_degreeCount_eq G hxy
  have h3 := G_vertCount_eq G hxy
  have bilinearlb := σ_helper hxy σub (λ d ↦ (e 3 7 (28 - vᵢ 2 7 d - 1) + (vᵢ 2 7 d)^2) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 2; assumption; simp [R37])
  have vertexlb := σ_helper hxy σub (λ d ↦  1 * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 2; assumption; simp [R37])
  have degreelb := σ_helper hxy σub (λ d ↦ (vᵢ 2 7 d) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 2; assumption; simp [R37])
  simp at bilinearlb vertexlb degreelb
  -- NOTE: Using simp here maxes out hearbeats
  simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_two, vᵢ, RamseyOld₂ 7] at h1
  simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_two, vᵢ, RamseyOld₂] at h2
  simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_two] at h3
  simp at h1 h2 h3 ⊢
  nlinarith [e37_20, e37_21]

-- theorem Ineq₁₁:
-- e 3 8 28 ≥ 99 := by
--   simp only [e]
--   sorry

-- theorem R39Ineq {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
-- G.edgeFinset.card ≥ 144 := by
--   have hr := RamseyOld₂ 8

--   have h1 := Prop₄ 8 hxy
--   simp [-Set.toFinset_card] at h1
--   replace : σ_G hxy ≤ 2 := by
--     have := (Prop₁ hxy).2
--     simp [hr] at this
--     have : RamseyOld 3 8 ≤ 29 := by
--       simp [RamseyOld]
--       apply csSup_le
--       sorry
--       simp
--       intro N G hxy
--       sorry
--     omega

--   have h2 := G_degreeCount_eq G hxy
--   have h3 := G_vertCount_eq G hxy
--   have _ := Ineq₉
--   have _ := Ineq₁₀
--   have _ := Ineq₁₁

--   interval_cases σ_G hxy
--   · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
--     replace h1 : 36 * G.edgeFinset.card ≥ 144 * (↑(G.sᵢ 2 8 0) : ℤ ):= by
--       suffices (↑(e 3 8 26) + 64) * ↑(G.sᵢ 2 8 0) ≥ 144 * ↑(G.sᵢ 2 8 0) by
--         linarith
--       gcongr
--       linarith

--     replace h2 : 2 * G.edgeFinset.card = 8 * ↑(G.sᵢ 2 8 0) := by
--       simp at h2
--       rw [← sum_degrees_eq_twice_card_edges, h2]
--       simp[vᵢ, hr]
--       omega

--     replace h3 : ↑(G.sᵢ 2 8 0) = 36 := by
--       simp[this, Finset.range] at h3
--       linarith
--     linarith

--   · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
--     replace h1 : 36 * G.edgeFinset.card ≥ 144 * (↑(G.sᵢ 2 8 0) : ℤ ) + 137 * ↑(G.sᵢ 2 8 1):= by
--       suffices (↑(e 3 8 27) + 49) * ↑(G.sᵢ 2 8 1) + (↑(e 3 8 26) + 64) * ↑(G.sᵢ 2 8 0) ≥ 137 * ↑(G.sᵢ 2 8 1) + 144 * ↑(G.sᵢ 2 8 0)by
--         linarith
--       gcongr <;>linarith

--     replace h2 : 2 * G.edgeFinset.card = 8 * ↑(G.sᵢ 2 8 0) +  7 * ↑(G.sᵢ 2 8 1) := by
--       simp at h2
--       rw [← sum_degrees_eq_twice_card_edges, h2]
--       simp[Finset.range, vᵢ, hr]
--       omega

--     replace h3 : ↑(G.sᵢ 2 8 1) + ↑(G.sᵢ 2 8 0) = 36 := by
--       simp[this, Finset.range] at h3
--       linarith
--     linarith

--   · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
--     replace h1 : 36 * G.edgeFinset.card ≥ 144 * (↑(G.sᵢ 2 8 0) : ℤ ) + 137 * ↑(G.sᵢ 2 8 1) + 135 * ↑(G.sᵢ 2 8 2):= by
--       suffices (↑(e 3 8 28) + 36) * ↑(G.sᵢ 2 8 2) +
--       (↑(e 3 8 27) + 49) * ↑(G.sᵢ 2 8 1) +
--        (↑(e 3 8 26) + 64) * ↑(G.sᵢ 2 8 0)
--        ≥  135 * ↑(G.sᵢ 2 8 2) + 137 * ↑(G.sᵢ 2 8 1) + 144 * ↑(G.sᵢ 2 8 0) by
--         linarith
--       gcongr <;>linarith

--     replace h2 : 2 * G.edgeFinset.card = 8 * ↑(G.sᵢ 2 8 0) +  7 * ↑(G.sᵢ 2 8 1) + 6 * ↑(G.sᵢ 2 8 2):= by
--       simp at h2
--       rw [← sum_degrees_eq_twice_card_edges, h2]
--       simp[Finset.range, vᵢ, hr]
--       omega

--     replace h3 : ↑(G.sᵢ 2 8 2) + ↑(G.sᵢ 2 8 1) + ↑(G.sᵢ 2 8 0)  = 36 := by
--       simp[this, Finset.range] at h3
--       linarith
--     linarith

-- theorem R39_36_graph_IsRegular8 {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
--   G.IsRegularOfDegree 8 := by
--   simp[IsRegularOfDegree]
--   have h_neighbor := R3y_neighbor_Ind 8 hxy

--   have deg_le: ∀ p ∈ Finset.univ, G.degree p ≤ 8 := by
--     intro p
--     by_contra!
--     simp[isXYGraph, cliqueNum, indepNum] at hxy
--     have hy := (csSup_le_iff' G.fintype_indepNum_bddAbove).mp (Nat.le_pred_of_lt hxy.2)
--     simp at hy
--     specialize hy (G.degree p) (G.neighborFinset p)
--     specialize h_neighbor p
--     linarith [hy h_neighbor]

--   have _ := R39Ineq hxy
--   have h1 : 2 * 144 ≤ 2 * #G.edgeFinset := by linarith
--   rw[← sum_degrees_eq_twice_card_edges] at h1
--   norm_num at h1
--   have h2 : ∑ v : Fin 36, G.degree v ≤ ∑ p : Fin 36, 8 := by
--     apply Finset.sum_le_sum
--     exact deg_le

--   have sum_deg_eq : ∑ v : Fin 36, G.degree v = ∑ p : Fin 36, 8 := by norm_num at *; linarith
--   have := (Finset.sum_eq_sum_iff_of_le deg_le).mp sum_deg_eq
--   simp at this
--   exact this

-- theorem R39_36_graph_has_R38_27 {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
--  ∃ (s : Finset (Fin 36)),s.card = 27 ∧ ((G.induce s).isXYGraph 3 8) := by
--   use Gᶜ.neighborFinset 0
--   simp [SimpleGraph.degree_compl, R39_36_graph_IsRegular8 hxy 0]
--   simp[isXYGraph]
--   by_contra! absurd
--   simp [isXYGraph] at *
--   by_cases hclique : (induce (↑(Gᶜ.neighborFinset 0)) G).cliqueNum < 3
--   specialize absurd hclique
--   suffices (induce (↑(Gᶜ.neighborFinset 0)) G).indepNum ≤ G.cliqueNum - 1 by
--     omega
--   simp [indepNum, cliqueNum]
--   -- apply csInf_le
--   sorry
--   sorry

end SimpleGraph
