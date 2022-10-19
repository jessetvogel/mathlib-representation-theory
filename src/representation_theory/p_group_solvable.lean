import group_theory.solvable
import group_theory.p_group
import tactic.basic

variables {G : Type*} [group G] [fintype G]

lemma top_eq_bot_of_trivial (h : fintype.card G = 1) : ⊥ = (⊤ : subgroup G) := by {
  apply subgroup.eq_top_of_card_eq,
  rw h,
  exact subgroup.card_bot,
}

instance solvable_of_trivial (h : fintype.card G = 1) : is_solvable G :=
  is_solvable_of_top_eq_bot _ (eq.symm $ top_eq_bot_of_trivial h)

variables (p : ℕ) [fact (nat.prime p)]

#check (infer_instance : nonempty G)
-- #check (infer_instance : nontrivial G)

theorem p_group_solvable (hG : is_p_group p G) : is_solvable G :=
begin
  -- Strong induction on the cardinality of G
  let q : ∀ n, fintype.card G ≤ n → is_solvable G := by {
    -- Base case: |G| = 0
    intros n hn,
    induction n with m hm,
    exfalso,
    have q' : fintype.card G ≠ 0 := fintype.card_ne_zero,
    exact q' (nat.eq_zero_of_le_zero hn),
    -- Induction step:
    by_cases fintype.card G = m.succ, {
      clear hn,
      cases m,
      -- Case |G| = 1,
      apply solvable_of_trivial h,
      -- Case |G| > 1,
      haveI G_nontrivial : nontrivial G := sorry,
      have Z_nontrivial := is_p_group.center_nontrivial hG,

      sorry
    }, {
      apply hm,
      cases nat.of_le_succ hn with h₁ h₂,
      exact h₁,
      exfalso,
      exact h h₂,
    },
  },
  exact q (fintype.card G) le_rfl,
end
