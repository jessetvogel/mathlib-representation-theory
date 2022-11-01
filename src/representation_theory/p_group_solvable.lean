import group_theory.solvable
import group_theory.p_group
import tactic.basic

theorem solvable_of_solvable_quotient_center
  {G : Type*} [group G] (h : is_solvable (G ⧸ subgroup.center G)) : is_solvable G := by {
  let Z := subgroup.center G,
  exact solvable_of_ker_le_range (subgroup.subtype Z) (quotient_group.mk' Z) (by simp),
}

noncomputable instance {G : Type*} [group G] [finite G] (N : subgroup G) : fintype (G ⧸ N) := fintype.of_finite _

lemma card_quotient_lt
  {G : Type*} [group G] [fintype G] (N : subgroup G) [nontrivial N] : fintype.card (G ⧸ N) < fintype.card G := by {
  sorry,
}

variables {G : Type*} [group G] [fintype G]

lemma top_eq_bot_of_trivial (h : fintype.card G = 1) : ⊥ = (⊤ : subgroup G) := by {
  apply subgroup.eq_top_of_card_eq,
  rw h,
  exact subgroup.card_bot,
}

instance solvable_of_trivial (h : fintype.card G = 1) : is_solvable G :=
  is_solvable_of_top_eq_bot _ (eq.symm $ top_eq_bot_of_trivial h)

variables (p : ℕ) [fact (nat.prime p)]

lemma nat.le_of_le_succ_and_ne {n m : ℕ} (h₁ : n ≤ m + 1) (h₂ : n ≠ m + 1) : n ≤ m := by {
  cases h₁ with _ h,
  exfalso,
  exact h₂ rfl,
  exact h,
}

theorem p_group_solvable (hG : is_p_group p G) : is_solvable G :=
begin
  -- Apply induction on n to the statement that all p-groups K with |K| ≤ n are solvable.
  let q : ∀
    (n : ℕ)
    (K : Type*)
    [K_group : group K]
    [K_fin : fintype K]
    [@is_p_group p K K_group]
    (hK : @fintype.card K K_fin ≤ n), @is_solvable K K_group := by {
    intro n;
    induction n with n hn,
    -- Base case: n = 0
    introsI K K_group K_fin K_p_group hK,
    exfalso,
    have q' : fintype.card K ≠ 0 := fintype.card_ne_zero,
    exact q' (nat.eq_zero_of_le_zero hK),
    -- Induction step: n > 0
    introsI K K_group K_fin K_p_group hK,
    -- Distinguish cases |K| = n + 1 and |K| ≠ n + 1
    by_cases card_K : (fintype.card K = n.succ), {
      -- Case |K| = n + 1.
      -- Distinguish cases n = 0 and n ≠ 0
      by_cases n_zero : (n = 0), {
        -- Case n = 0, then |K| = 1, so K is trivial, and hence solvable
        rw [n_zero] at card_K,
        exact solvable_of_trivial card_K,
      }, {
        -- Case n ≠ 0, then |K| > 1, so K is non-trivial.
        haveI K_nontrivial : nontrivial K := by {
          sorry,
        },
        -- Then the center Z(K) is non-trivial
        haveI Z_nontrivial := is_p_group.center_nontrivial K_p_group,
        -- Construct the quotient K / Z(K)
        let H := K ⧸ (subgroup.center K),
        -- Then H is finite, and of cardinality smaller than G
        have H_card_le_K_card : fintype.card H < fintype.card K := card_quotient_lt (subgroup.center K),
        -- Hence, |K / Z(K)| ≤ n
        have H_card_le_m_succ : fintype.card H ≤ n := by {
          apply nat.le_of_lt_succ,
          rw [← card_K],
          exact H_card_le_K_card,
        },
        -- Also, any quotient of a p-group is a p-group
        haveI H_p_group : is_p_group p H := is_p_group.to_quotient K_p_group _,
        -- Thus, H is solvable
        have H_solvable := @hn H _ _ H_p_group H_card_le_m_succ, -- TODO: fix this
        exact solvable_of_solvable_quotient_center H_solvable,
      }
    }, {
      -- Case |K| ≠ n + 1. Then |K| ≤ n, so we can use the induction hypothesis.
      apply @hn K K_group K_fin K_p_group,
      apply nat.le_of_le_succ_and_ne hK card_K,
    }
  },
  exact @q (fintype.card G) G _ _ hG le_rfl,
end
