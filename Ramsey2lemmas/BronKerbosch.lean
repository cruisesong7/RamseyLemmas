import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.FinEnum

-- NOTE: For List.sizeOf_filter, needed to prove termination of Bron_Kerbosch
import Trestle.Upstream.ToStd

namespace List

-- By Kenny Lau
-- https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/List.20length.20induction/near/554091009
theorem length_wf {α : Type} : WellFounded (λ (x y : List α) ↦ x.length < y.length) := InvImage.wf _ Nat.lt_wfRel.2

end List

namespace SimpleGraph

def Bron_Kerbosch_full {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] {R P X : List α} (Pnd : P.Nodup) (RP : R.Disjoint P) (RX : R.Disjoint X) (PX : P.Disjoint X) : List (Finset α) :=
  match P with
  | [] =>
    match X with
    | [] => [R.toFinset]
    | h :: t => []
  | v :: P' =>
    Bron_Kerbosch_full G (by simp at Pnd; apply Pnd.right.filter) (by simp [List.Disjoint] at RP ⊢; intros a ainR ainP' av; cases (RP ainR).right ainP' : (v :: R).Disjoint (P'.filter (λ u ↦ decide (G.Adj u v)))) (by simp [List.Disjoint] at RX ⊢; intros a ainR ainX; cases RX ainR ainX : (v :: R).Disjoint (X.filter (λ u ↦ decide (G.Adj u v)))) (by simp [List.Disjoint] at PX ⊢; intros a ainP' av ainX; cases (PX.right a ainP') ainX : (P'.filter (λ u ↦ decide (G.Adj u v))).Disjoint (X.filter (λ u ↦ decide (G.Adj u v)))) ++ (Bron_Kerbosch_full G (by simp at Pnd; exact Pnd.right) (by simp [List.Disjoint] at RP ⊢; intros a ainR ainP'; cases (RP ainR).right ainP' : R.Disjoint P') (by simp [List.Disjoint] at RP RX ⊢; intros a ainR; apply And.intro; exact (RP ainR).left; apply RX; exact ainR : R.Disjoint (v :: X)) (by simp [List.Disjoint] at Pnd RP PX ⊢; intros a ainP'; apply And.intro; intro aeqv; rw [aeqv] at ainP'; cases Pnd.left ainP'; exact PX.right a ainP' : P'.Disjoint (v :: X)))

-- lemma Bron_Kerbosch_clique {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] {R P X : List α} (Pnd : P.Nodup) (RP : R.Disjoint P) (RX : R.Disjoint X) (PX : P.Disjoint X) : (G.IsClique R.toFinset) → (∀ v ∈ P, ∀ u ∈ R, G.Adj u v) → ∀ S ∈ Bron_Kerbosch_full G Pnd RP RX PX, G.IsClique S := by
--   induction P using WellFounded.induction List.length_wf generalizing R X with
--   | h P ih =>
--     intros Rclique Radj S SBK
--     cases P with
--     | nil =>
--       cases X with
--       | nil =>
--         simp [Bron_Kerbosch_full] at SBK Rclique
--         simpa [SBK]
--       | cons u X' =>
--         simp [Bron_Kerbosch_full, Finset.empty] at SBK
--     | cons v P' =>
--       simp [Bron_Kerbosch_full] at SBK
--       cases SBK with
--       | inl SBKRec =>
--         apply ih (P'.filter (λ u ↦ decide (G.Adj u v))) (by simp [Nat.lt_add_one_iff, List.length_filter_le]) (by simp at Pnd; apply List.Pairwise.filter; exact Pnd.right) (by simp [List.Disjoint] at RP ⊢; intros a ainR ainP'; cases (RP ainR).right ainP' : (v :: R).Disjoint (P'.filter (λ u ↦ decide (G.Adj u v)))) (by simp [List.Disjoint]; intros _ ainR ainX; cases RX ainR ainX : (v :: R).Disjoint (X.filter (λ u ↦ decide (G.Adj u v))))
--         · simp at Rclique Radj ⊢
--           apply And.intro
--           · exact Rclique
--           · intros u uinR vnequ
--             rw [G.adj_comm]
--             exact Radj.left u uinR
--         · simp
--           intros u uinP' uv
--           apply And.intro
--           · rw [G.adj_comm]
--             exact uv
--           · intros w winR
--             simp at Radj
--             exact Radj.right u uinP' w winR
--         · exact SBKRec
--       | inr SBKRec =>
--         apply ih P' (by simp) (by simp at Pnd; exact Pnd.right) (by simp at RP; exact RP.right : R.Disjoint P') (by simp at RP; simp [RP.left, RX] : R.Disjoint (v :: X))
--         · exact Rclique
--         · simp at Radj
--           exact Radj.right
--         · exact SBKRec

lemma Bron_Kerbosch_maximal_clique {α : Type} [Fintype α] [deceq : DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] {R P X : List α} (Pnd : P.Nodup) (RP : R.Disjoint P) (RX : R.Disjoint X) (PX : P.Disjoint X) : (G.IsClique R.toFinset) → (∀ (v : α), v ∈ (P.toFinset ∪ X.toFinset) ↔ ∀ u ∈ R, G.Adj v u) → ∀ (S : Finset α), S ∈ Bron_Kerbosch_full G Pnd RP RX PX ↔ (R.toFinset ⊆ S ∧ S ⊆ R.toFinset ∪ P.toFinset ∧ Maximal G.IsClique S) := by
  induction P using WellFounded.induction List.length_wf generalizing R X with
  | h P ih =>
    intros Rclique Radj S
    cases P with
    | nil =>
      cases X with
      | nil =>
        simp [Bron_Kerbosch_full, Finset.Subset.antisymm_iff] at Radj ⊢
        rw [and_comm]
        simp
        intros RsubS SsubR
        rw [← subset_antisymm RsubS SsubR]
        simp [-List.coe_toFinset, Rclique, SimpleGraph.isMaximalClique_iff]
        intros T TClique RsubT v vinT
        obtain ⟨u, ⟨uinR, unotadjv⟩⟩ := Radj v
        cases deceq v u with
        | isTrue vequ => simpa [vequ]
        | isFalse vnequ =>
          rw [G.adj_comm] at unotadjv
          cases unotadjv (TClique (RsubT (by simp; exact uinR)) vinT (Ne.intro vnequ).symm)
      | cons v X' =>
        simp [Bron_Kerbosch_full, Maximal, Set.subset_def] at Radj ⊢
        intros RsubS SsubR Sclique
        rw [← subset_antisymm RsubS SsubR]
        use (insert v R.toFinset)
        apply And.intro
        · simp [-List.coe_toFinset, Rclique]
          have vadj := Radj v
          simp at vadj
          intros u uinR vnequ
          exact vadj u uinR
        · apply And.intro
          · tauto
          · use v
            simp at RX ⊢
            exact RX.left
    | cons v P' =>
      simp [Bron_Kerbosch_full] at Radj ⊢
      rw [ih (P'.filter (λ u ↦ decide (G.Adj u v))) (by simp [List.length_filter_le]) (by simp at Pnd; apply List.Pairwise.filter; exact Pnd.right) (by simp [List.Disjoint] at RP ⊢; intros a ainR ainP'; cases (RP ainR).right ainP' : (v :: R).Disjoint (P'.filter (λ u ↦ decide (G.Adj u v)))) (by simp [List.Disjoint]; intros _ ainR ainX; cases RX ainR ainX : (v :: R).Disjoint (X.filter (λ u ↦ decide (G.Adj u v)))) (by simp [List.Disjoint] at PX ⊢; intros a ainP' _ ainX; cases (PX.right a ainP') ainX) (by simp [-List.coe_toFinset, Rclique]; have vadj := Radj v; simp at vadj; intros u uinR; simp [vadj u uinR]) (by simp; intros u; rw [← or_and_right, and_comm]; simp [← Radj u]; intros uv ueqv; simp [ueqv] at uv) S]
      rw [ih P' (by simp) (by simp at Pnd; exact Pnd.right) (by simp at RP; exact RP.right : R.Disjoint P') (by simp at RP ⊢; simp [RP.left, RX] : R.Disjoint (v :: X)) (by simp at Pnd PX ⊢; simp [Pnd.left, PX.right]) Rclique (by simp; exact Radj) S]
      rw [← and_assoc, ← and_assoc, ← and_assoc, ← or_and_right]
      simp [Finset.subset_iff]
      intros SMax
      apply Iff.intro
      · intros SProp
        cases SProp with
        | inl Sv =>
          apply And.intro
          · intros u uinR
            exact Sv.left.right u uinR
          · intros u uinS
            have := Sv.right uinS
            tauto
        | inr Sv =>
          apply And.intro
          · exact Sv.left
          · intros u uinS
            have := Sv.right uinS
            tauto
      · intros SProp
        cases Finset.decidableMem v S with
        | isTrue vinS =>
          left
          apply And.intro
          · simp [vinS]
            intros u uinR
            exact SProp.left _ uinR
          · intros u uinS
            cases deceq u v with
            | isTrue ueqv =>
              simp [ueqv]
            | isFalse uneqv =>
              right
              cases SProp.right uinS with
              | inl ueqv =>
                contradiction
              | inr uRP' =>
                cases uRP' with
                | inl uinR =>
                  left
                  exact uinR
                | inr uinP' =>
                  right
                  simp [uinP', SMax.left uinS vinS uneqv]
        | isFalse vnotinS =>
          right
          apply And.intro
          · exact SProp.left
          · intros u uinS
            cases SProp.right uinS with
            | inl ueqv =>
              simp [ueqv] at uinS
              contradiction
            | inr _ =>
              assumption 

-- NOTE: Here we specialize to FinEnum to make this definition
-- computable/decidable, but it all applies just the same for Fintype
def Bron_Kerbosch {α : Type} [fe : FinEnum α] (G : SimpleGraph α) [DecidableRel G.Adj] := Bron_Kerbosch_full G fe.nodup_toList (List.disjoint_nil_left fe.toList) (List.disjoint_nil_left []) (List.disjoint_nil_right fe.toList)

-- lemma Bron_Kerbosch_correct {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] : ∀ (S : Finset α), Maximal G.IsClique ↑S ↔ S ∈ Bron_Kerbosch_full G Finset.univ.nodup_toList (List.disjoint_nil_left Finset.univ.toList) (List.disjoint_nil_left []) Finset.univ.toList.disjoint_nil_right := by
--   intros S
--   rw [Bron_Kerbosch_maximal_clique] <;> simp

-- lemma Bron_Kerbosch_maximum_clique {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] : ∀ (S : Finset α), G.IsMaximumClique S → S ∈ Bron_Kerbosch_full G Finset.univ.nodup_toList (List.disjoint_nil_left Finset.univ.toList) (List.disjoint_nil_left []) Finset.univ.toList.disjoint_nil_right := by
--   intros S SMum
--   have SMal := SMum.isMaximalClique
--   rw [Bron_Kerbosch_correct] at SMal
--   exact SMal

lemma Bron_Kerbosch_correct {α : Type} [FinEnum α] (G : SimpleGraph α) [DecidableRel G.Adj] : ∀ (S : Finset α), Maximal G.IsClique ↑S ↔ S ∈ Bron_Kerbosch G := by
  intros S
  rw [Bron_Kerbosch, Bron_Kerbosch_maximal_clique, Finset.subset_iff, Finset.subset_iff] <;> simp

lemma Bron_Kerbosch_maximum_clique {α : Type} [FinEnum α] (G : SimpleGraph α) [DecidableRel G.Adj] : ∀ (S : Finset α), G.IsMaximumClique S → S ∈ Bron_Kerbosch G := by
  intros S SMum
  have SMal := SMum.isMaximalClique
  rw [Bron_Kerbosch_correct] at SMal
  exact SMal

lemma Bron_Kerbosch_cliqueNum {α : Type} [FinEnum α] (G : SimpleGraph α) [DecidableRel G.Adj] : G.cliqueNum = ((Bron_Kerbosch G).map Finset.card).max?.getD 0 := by
  have cliqueNumMem : G.cliqueNum ∈ ((Bron_Kerbosch G).map Finset.card) ∧ ∀ (b : ℕ), b ∈ ((Bron_Kerbosch G).map Finset.card) → b ≤ G.cliqueNum := by
    simp
    · apply And.intro
      · obtain ⟨S, SMum⟩ := G.maximumClique_exists
        have Smem := SMum.isMaximalClique
        rw [Bron_Kerbosch_correct] at Smem
        use S
        simp [Smem, G.maximumClique_card_eq_cliqueNum S SMum]
      · intros S SMal
        rw [← Bron_Kerbosch_correct] at SMal
        exact SMal.left.card_le_cliqueNum
  rw [← List.max?_eq_some_iff] at cliqueNumMem
  simp [cliqueNumMem]

end SimpleGraph
