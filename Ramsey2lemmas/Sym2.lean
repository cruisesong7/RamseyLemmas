import Mathlib.Data.Sym.Sym2

namespace Sym2

instance decBall {α : Type} (p : α → Prop) [pdec : DecidablePred p] (s : Sym2 α) : Decidable (∀ x ∈ s, p x) := @Sym2.rec α (λ s ↦ Decidable (∀ x ∈ s, p x)) (λ (ql, qr) ↦ match pdec ql with | isFalse h => isFalse (by simp; intro; contradiction) | isTrue hql => match pdec qr with | isFalse h => isFalse (by simp [h]) | isTrue hqr => isTrue (by simp; tauto)) (by aesop (add safe (by congr!))) s

instance decBex {α : Type} (p : α → Prop) [pdec : DecidablePred p] (s : Sym2 α) : Decidable (∃ x ∈ s, p x) := @Sym2.rec α (λ s ↦ Decidable (∃ x ∈ s, p x)) (λ (ql, qr) ↦ match pdec ql with | isTrue h => isTrue (by simp [h]) | isFalse hql => match pdec qr with | isTrue h => isTrue (by simp [h]) | isFalse hqr => isFalse (by simp; tauto)) (by aesop (add safe (by congr!))) s

-- NOTE: This is like Quot.out but I think with the (very powerful)
-- assumption [LinearOrder α], it is computable
def toOrderedPair {α : Type} [LinearOrder α] (s : Sym2 α) : α × α := Sym2.rec (λ p ↦ (min p.fst p.snd, max p.fst p.snd)) (by
  simp
  intros aₗ aᵣ bₗ bᵣ abeq
  cases abeq with
  | inl abeq => simp [abeq.left, abeq.right]
  | inr abeq => simp [abeq.left, abeq.right, min_comm bᵣ bₗ, max_comm bᵣ bₗ]
) s

lemma exists_mem_pair {P : α → Prop} {a b : α} : (∃ x ∈ s(a, b), P x) ↔ P a ∨ P b := by
  simp only [mem_iff, exists_eq_or_imp, exists_eq_left]

lemma toOrderedPair_repr {α : Type} [LinearOrder α] (s : Sym2 α) : s = s(s.toOrderedPair.fst, s.toOrderedPair.snd) := by
  cases s with
  | h x y => simp [toOrderedPair, Sym2.rec, Quot.rec, LinearOrder.le_total]

lemma toOrderedPair_inj {α : Type} [LinearOrder α] : Function.Injective (@Sym2.toOrderedPair α _) := by
  intros a b
  intros abord
  trans Sym2.mk a.toOrderedPair
  · apply Sym2.toOrderedPair_repr
  · trans Sym2.mk b.toOrderedPair
    · congr
    · symm
      apply Sym2.toOrderedPair_repr

lemma toOrderedPair_IsDiag_of_eq {α : Type} [inst : LinearOrder α] : ∀ {s t : Sym2 α}, s.toOrderedPair = t.toOrderedPair.swap → s.IsDiag ∧ t.IsDiag := by
  intros s
  cases s with
  | h sx sy =>
    intros t
    cases t with
    | h tx ty =>
      simp [toOrderedPair, Sym2.rec, Quot.rec]
      intros minmaxeq maxmineq
      rw [min_eq_iff] at minmaxeq
      rw [max_eq_iff] at maxmineq
      rcases minmaxeq with ⟨rfl, sxley⟩ | ⟨rfl, sylex⟩
      · simp [sxley] at maxmineq
        rcases maxmineq with ⟨rfl, syle⟩ | rfl
        · simp at syle sxley ⊢
          apply inst.le_antisymm <;> assumption
        · simp at sxley
          simp_all [inst.le_antisymm _ _ sxley.left sxley.right]
      · simp [sylex] at maxmineq
        rcases maxmineq with rfl | ⟨rfl, sxle⟩
        · simp at sylex
          simp_all [inst.le_antisymm _ _ sylex.left sylex.right]
        · simp at sylex sxle ⊢
          apply inst.le_antisymm <;> assumption

lemma isDiag_of_subsingleton {α : Type} [Subsingleton α] : ∀ (s : Sym2 α), s.IsDiag := by
  intro s
  induction s with
  | h x y => simp [eq_iff_true_of_subsingleton]

end Sym2
