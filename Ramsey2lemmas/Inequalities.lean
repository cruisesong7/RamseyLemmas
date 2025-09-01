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

axiom R36ub : RamseyOld 3 6 ≤ 17 --TODO: computation K or R

theorem R36 : RamseyOld 3 6 = 17 := by
  simp [Nat.eq_iff_le_and_ge, R36ub]
  apply le_csSup
  simp [isXYGraph_bddAbove]
  let G := readG6 "P??GaOo`XMGsIcT?pSLaGuA?"
  use G
  unfold SimpleGraph.isXYGraph
  simp [G.Bron_Kerbosch_cliqueNum, ← G.cliqueNum_compl, Gᶜ.Bron_Kerbosch_cliqueNum]
  native_decide

axiom R37ub : RamseyOld 3 7 ≤ 22 --TODO: computation O

theorem R37 : RamseyOld 3 7 = 22 := by
  simp [Nat.eq_iff_le_and_ge, R37ub]
  apply le_csSup
  simp [isXYGraph_bddAbove]
  let G := readG6 "UsaCB@AQAGI?HGIABGOKJCcoa[``o_U[?LcGD[O?"
  use G
  unfold SimpleGraph.isXYGraph
  simp [G.Bron_Kerbosch_cliqueNum, ← G.cliqueNum_compl, Gᶜ.Bron_Kerbosch_cliqueNum]
  native_decide

axiom e3_6_11_11 : e 3 6 11 ≥ 11 --TODO: the proof start in pp.163 Appendix B
axiom e3_6_12_15 : e 3 6 12 ≥ 15
axiom e3_6_13_20 : e 3 6 13 ≥ 20
axiom e3_6_14_25 : e 3 6 14 ≥ 25
axiom e3_6_15_32 : e 3 6 15 ≥ 32  --TODO: computation M
axiom e3_6_16_40 : e 3 6 16 ≥ 40  --TODO: computation L

lemma R38lb : 27 ∈ {N | ∃ G : SimpleGraph (Fin N), G.isXYGraph 3 8} := by
  let G := readG6 "Z????CDO?a@PHA_HcE_dc`PCXQ@PoSWo@_cDS_YQQB_Qo?TLSO?q_g?{p?_?"
  use G
  unfold SimpleGraph.isXYGraph
  rw [G.Bron_Kerbosch_cliqueNum, ← G.cliqueNum_compl, Gᶜ.Bron_Kerbosch_cliqueNum]
  native_decide

lemma e3_7_18_36 : e 3 7 18 ≥ 36 := by
  simp only [e]
  apply le_csInf
  · let G := readG6 "R`OCC?hXRABgOh_AbWGOah??S_?KO_"
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
    have σub : σ_G GisXY < 6 := by
      simp +arith [σ_G, RamseyOld₂]
      obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
      have := (Lemma₂ G v GisXY).right
      simp +arith [R36, ← vmindeg] at this
      assumption
    have h2 := G_degreeCount_eq G GisXY
    have h3 := G_vertCount_eq G GisXY
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 6 (18 - vᵢ 2 6 d - 1) + (vᵢ 2 6 d)^2) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 6; assumption; simp[R36])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 6; assumption; simp [R36])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 6 d) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 6; assumption; simp [R36])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_six, vᵢ, RamseyOld₂ 6] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_six, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_six] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [e3_6_11_11, e3_6_12_15, e3_6_13_20, e3_6_14_25, e3_6_15_32, e3_6_16_40]

-- set_option maxHeartbeats 400000
-- set_option diagnostics true
lemma e3_7_19_44 : e 3 7 19 ≥ 44 := by
  simp only [e]
  apply le_csInf
  · let G := readG6 "S?C_jO@?g`@CBEWFEACXB_pjAKeGwF`C?"
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
    have σub : σ_G GisXY < 5 := by
      simp +arith [σ_G, RamseyOld₂]
      obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
      have := (Lemma₂ G v GisXY).right
      simp +arith [R36, ← vmindeg] at this
      assumption
    have h2 := G_degreeCount_eq G GisXY
    have h3 := G_vertCount_eq G GisXY
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 6 (19 - vᵢ 2 6 d - 1) + (vᵢ 2 6 d)^2) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 5; assumption; simp[R36])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 5; assumption; simp [R36])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 6 d) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 5; assumption; simp [R36])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_five, vᵢ, RamseyOld₂ 6] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_five, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_five] at h3
    simp at h1 h2 h3 ⊢
    sorry --TODO: nlinarith failed, nlinarith! times out
    -- nlinarith [e3_6_12_15, e3_6_13_20, e3_6_14_25, e3_6_15_32, e3_6_16_40]

lemma e3_7_20_50 : e 3 7 20 ≥ 50 := by
  simp only [e]
  apply le_csInf
  · let G := readG6 "T?Dg??EGI?aLAY_IIIM?cKoSiDTCLCmOBJO?"
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
      simp +arith [R36, ← vmindeg] at this
      assumption
    have h2 := G_degreeCount_eq G GisXY
    have h3 := G_vertCount_eq G GisXY
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 6 (20 - vᵢ 2 6 d - 1) + (vᵢ 2 6 d)^2) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp[R36])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp [R36])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 6 d) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp [R36])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_four, vᵢ, RamseyOld₂ 6] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_four, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_four] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [e3_6_13_20, e3_6_14_25, e3_6_15_32, e3_6_16_40]

lemma e3_7_21_59 : e 3 7 21 ≥ 59 := by
  simp only [e]
  apply le_csInf
  · let G := readG6 "UsaCB@AQAGI?HGIABGOKJCcoa[``o_U[?LcGD[O?"
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
    have σub : σ_G GisXY < 3 := by
      simp +arith [σ_G, RamseyOld₂]
      obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
      have := (Lemma₂ G v GisXY).right
      simp +arith [R36, ← vmindeg] at this
      assumption
    have h2 := G_degreeCount_eq G GisXY
    have h3 := G_vertCount_eq G GisXY
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 6 (21 - vᵢ 2 6 d - 1) + (vᵢ 2 6 d)^2) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 3; assumption; simp[R36])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 3; assumption; simp [R36])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 6 d) * (G.sᵢ 2 6 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 3; assumption; simp [R36])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂ 6] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_three] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [e3_6_14_25, e3_6_15_32, e3_6_16_40]

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
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 7 (26 - vᵢ 2 7 d - 1) + (vᵢ 2 7 d)^2) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp[R37])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp[R37])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 7 d) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 4; assumption; simp[R37])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_four, vᵢ, RamseyOld₂ 7] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_four, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_four] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [e3_7_18_36, e3_7_19_44, e3_7_20_50, e3_7_21_59]

theorem Ineq₁₀ (h : RamseyOld 3 8 > 27) : e 3 8 27 ≥ 88 := by
  simp [e]
  apply le_csInf
  · simp only [gt_iff_lt, RamseyOld] at h
    rw [lt_csSup_iff] at h
    · obtain ⟨n, ⟨G, Gdec, hG⟩, hn⟩ := h
      rw [Nat.lt_iff_add_one_le, ← Fintype.card_fin n, Fintype.card, Finset.le_card_iff_exists_subset_card] at hn
      obtain ⟨V, ⟨Vsub, Vcard⟩⟩ := hn
      use (G.induce V).edgeFinset.card
      simp [-Set.toFinset_card] at Vcard ⊢
      rw [← @Fintype.card_ofFinset (Fin n) V.toSet V (by simp)] at Vcard
      use (G.induce V).overFin Vcard
      apply And.intro
      · simp [SimpleGraph.isXYGraph] at hG ⊢
        apply And.intro
        · apply Nat.lt_of_le_of_lt _ hG.left
          -- TODO Is there a way to make these parameters automatic?
          rw [← (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 28 Vcard).cliqueNum]
          exact (@SimpleGraph.Embedding.induce (Fin n) G ↑V).cliqueNum_mono
        · apply Nat.lt_of_le_of_lt _ hG.right
          rw [← (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 28 Vcard).indepNum]
          exact (@SimpleGraph.Embedding.induce (Fin n) G ↑V).indepNum_mono
      · use (by intros u v; simp [← (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 28 Vcard).symm.map_adj_iff]; apply Gdec)
        simp [-Set.toFinset_card]
        haveI : DecidableRel ((G.induce V).overFin Vcard).Adj := by
          intros u v
          simp [SimpleGraph.overFin]
          apply Gdec
        simp [← @SimpleGraph.Iso.card_edgeFinset_eq (Fin 28) ((G.induce V).overFin Vcard) ↑V (G.induce V) (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 28 Vcard).symm _ _]
        congr
    · simp
      apply isXYGraph_bddAbove
    · simp
      use 27
      apply R38lb
  · simp [-Set.toFinset_card]
    intros _ G GisXY _ cardeqe
    rw [← cardeqe]
    have h1 := Prop₄ GisXY
    simp [-Set.toFinset_card] at h1
    have σub : σ_G GisXY < 3 := by
      simp +arith [σ_G, RamseyOld₂]
      obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
      have := (Lemma₂ G v GisXY).right
      simp +arith [R37, ← vmindeg] at this
      assumption
    have h2 := G_degreeCount_eq G GisXY
    have h3 := G_vertCount_eq G GisXY
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 7 (27 - vᵢ 2 7 d - 1) + (vᵢ 2 7 d)^2) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 3; assumption; simp [R37])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 3; assumption; simp [R37])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 7 d) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 3; assumption; simp [R37])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂ 7] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_three] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [e3_7_19_44, e3_7_20_50, e3_7_21_59]

theorem Ineq₁₁ (h : RamseyOld 3 8 > 28):
e 3 8 28 ≥ 99 := by
  simp only [e]
  apply le_csInf
  · simp only [gt_iff_lt, RamseyOld] at h
    rw [lt_csSup_iff] at h
    · obtain ⟨n, ⟨G, Gdec, hG⟩, hn⟩ := h
      rw [Nat.lt_iff_add_one_le, ← Fintype.card_fin n, Fintype.card, Finset.le_card_iff_exists_subset_card] at hn
      obtain ⟨V, ⟨Vsub, Vcard⟩⟩ := hn
      use (G.induce V).edgeFinset.card
      simp [-Set.toFinset_card] at Vcard ⊢
      rw [← @Fintype.card_ofFinset (Fin n) V.toSet V (by simp)] at Vcard
      use (G.induce V).overFin Vcard
      apply And.intro
      · simp [SimpleGraph.isXYGraph] at hG ⊢
        apply And.intro
        · apply Nat.lt_of_le_of_lt _ hG.left
          -- TODO Is there a way to make these parameters automatic?
          rw [← (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 29 Vcard).cliqueNum]
          exact (@SimpleGraph.Embedding.induce (Fin n) G ↑V).cliqueNum_mono
        · apply Nat.lt_of_le_of_lt _ hG.right
          rw [← (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 29 Vcard).indepNum]
          exact (@SimpleGraph.Embedding.induce (Fin n) G ↑V).indepNum_mono
      · use (by intros u v; simp [← (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 29 Vcard).symm.map_adj_iff]; apply Gdec)
        simp [-Set.toFinset_card]
        haveI : DecidableRel ((G.induce V).overFin Vcard).Adj := by
          intros u v
          simp [SimpleGraph.overFin]
          apply Gdec
        simp [← @SimpleGraph.Iso.card_edgeFinset_eq (Fin 29) ((G.induce V).overFin Vcard) ↑V (G.induce V) (@SimpleGraph.overFinIso ↑↑V (G.induce V) _ 29 Vcard).symm _ _]
        congr
    · simp
      apply isXYGraph_bddAbove
    · simp
      use 27
      apply R38lb
  · simp [-Set.toFinset_card]
    intros _ G GisXY _ cardeqe
    rw [← cardeqe]
    have h1 := Prop₄ GisXY
    simp [-Set.toFinset_card] at h1
    have σub : σ_G GisXY < 2 := by
      simp +arith [σ_G, RamseyOld₂]
      obtain ⟨v, vmindeg⟩ := G.exists_minimal_degree_vertex
      have := (Lemma₂ G v GisXY).right
      simp +arith [R37, ← vmindeg] at this
      assumption
    have h2 := G_degreeCount_eq G GisXY
    have h3 := G_vertCount_eq G GisXY
    have bilinearlb := σ_helper GisXY σub (λ d ↦ (e 3 7 (28 - vᵢ 2 7 d - 1) + (vᵢ 2 7 d)^2) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 2; assumption; simp [R37])
    have vertexlb := σ_helper GisXY σub (λ d ↦  1 * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 2; assumption; simp [R37])
    have degreelb := σ_helper GisXY σub (λ d ↦ (vᵢ 2 7 d) * (G.sᵢ 2 7 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish GisXY _ 2; assumption; simp [R37])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_two, vᵢ, RamseyOld₂ 7] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_two, vᵢ, RamseyOld₂] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_two] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [e3_7_20_50, e3_7_21_59]

theorem R39Ineq {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9): G.edgeFinset.card ≥ 144 := by
  have σub := (Prop₁ hxy).2
  simp [RamseyOld₂ 8] at σub

  have h1 := Prop₄ hxy
  simp [-Set.toFinset_card] at h1

  have h2 := G_degreeCount_eq G hxy
  have h3 := G_vertCount_eq G hxy

  have R38ub : RamseyOld 3 8 ≤ 29 := by
    sorry --TODO: formalize the informal argument on pp.154
  have R38lb : RamseyOld 3 8 ≥ 27 := by
    simp[RamseyOld]
    apply le_csSup
    apply isXYGraph_bddAbove
    apply R38lb

  interval_cases R38 : (RamseyOld 3 8)

  · norm_num at σub
    norm_num [σub, RamseyOld₂ 8, Finset.range, -Set.toFinset_card] at h1 h2 h3
    nlinarith [Ineq₉]
  · norm_num at σub
    replace σub := Nat.lt_succ_of_le σub
    have bilinearlb := σ_helper hxy σub (λ d ↦ (e 3 8 (35 - vᵢ 2 8 d - 1) + (vᵢ 2 8 d)^2) * (G.sᵢ 2 8 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 2; assumption; simp [R38])
    have vertexlb := σ_helper hxy σub (λ d ↦  1 * (G.sᵢ 2 8 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 2; assumption; simp [R38])
    have degreelb := σ_helper hxy σub (λ d ↦ (vᵢ 2 8 d) * (G.sᵢ 2 8 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 2; assumption; simp [R38])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_two, vᵢ, RamseyOld₂ 8] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_two, vᵢ, RamseyOld₂ 8] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_two] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [Ineq₉, Ineq₁₀ (by simp [R38])]
  · norm_num at σub
    replace σub := Nat.lt_succ_of_le σub
    have bilinearlb := σ_helper hxy σub (λ d ↦ (e 3 8 (35 - vᵢ 2 8 d - 1) + (vᵢ 2 8 d)^2) * (G.sᵢ 2 8 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 3; assumption; simp [R38])
    have vertexlb := σ_helper hxy σub (λ d ↦  1 * (G.sᵢ 2 8 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 3; assumption; simp [R38])
    have degreelb := σ_helper hxy σub (λ d ↦ (vᵢ 2 8 d) * (G.sᵢ 2 8 d)) (by simp only [Finset.filter_eq_empty_iff]; intros; apply sᵢ_vanish hxy _ 3; assumption; simp [R38])
    simp at bilinearlb vertexlb degreelb
    -- NOTE: Using simp here maxes out hearbeats
    simp_rw [bilinearlb, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂ 8] at h1
    simp_rw [Nat.mul_comm, degreelb, G.sum_degrees_eq_twice_card_edges, Finset.sum_range, Fin.sum_univ_three, vᵢ, RamseyOld₂ 8] at h2
    simp_rw [vertexlb, Finset.sum_range, Fin.sum_univ_three] at h3
    simp at h1 h2 h3 ⊢
    nlinarith [Ineq₉, Ineq₁₀ (by simp [R38]), Ineq₁₁ (by simp [R38])]

theorem R39_36_graph_IsRegular8 {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
  G.IsRegularOfDegree 8 := by
  simp[IsRegularOfDegree]
  have h_neighbor := R3y_neighbor_Ind G hxy

  have deg_le: ∀ p ∈ Finset.univ, G.degree p ≤ 8 := by
    intro p
    by_contra!
    simp[isXYGraph, cliqueNum, indepNum] at hxy
    have hy := (csSup_le_iff' G.fintype_indepNum_bddAbove).mp (Nat.le_pred_of_lt hxy.2)
    simp at hy
    specialize hy (G.degree p) (G.neighborFinset p)
    specialize h_neighbor p
    linarith [hy h_neighbor]

  have _ := R39Ineq hxy
  have h1 : 2 * 144 ≤ 2 * G.edgeFinset.card := by linarith
  rw[← sum_degrees_eq_twice_card_edges] at h1
  norm_num at h1
  have h2 : ∑ v : Fin 36, G.degree v ≤ ∑ p : Fin 36, 8 := by
    apply Finset.sum_le_sum
    exact deg_le

  have sum_deg_eq : ∑ v : Fin 36, G.degree v = ∑ p : Fin 36, 8 := by norm_num at *; linarith
  have := (Finset.sum_eq_sum_iff_of_le deg_le).mp sum_deg_eq
  simp at this
  exact this

theorem R39_36_graph_has_R38_27 {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
 ∃ (s : Finset (Fin 36)),s.card = 27 ∧ ((G.induce s).isXYGraph 3 8) := by
  use Gᶜ.neighborFinset 0
  simp [SimpleGraph.degree_compl, R39_36_graph_IsRegular8 hxy 0]
  simp[isXYGraph]
  by_contra! absurd
  simp [isXYGraph] at *
  by_cases hclique : (induce (↑(Gᶜ.neighborFinset 0)) G).cliqueNum < 3
  specialize absurd hclique
  suffices (induce (↑(Gᶜ.neighborFinset 0)) G).indepNum ≤ G.cliqueNum - 1 by
    omega
  simp [indepNum, cliqueNum]
  -- apply csInf_le
  sorry
  sorry

end SimpleGraph
