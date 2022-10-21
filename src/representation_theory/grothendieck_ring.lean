import ring_theory.ideal.basic
import algebra.module.submodule.basic
import ring_theory.simple_module
import group_theory.free_abelian_group_finsupp
import order.jordan_holder
import ring_theory.artinian
import algebra.direct_sum.basic

open_locale direct_sum
open ideal

classical

-- Some properties of morphisms
section morphisms

variables {R M N : Type*} [ring R] [add_comm_group M] [module R M] [add_comm_group N]
  [module R N] (f : M →ₗ[R] N)

abbreviation im : submodule R N := linear_map.range f
abbreviation ker : submodule R M := submodule.comap f ⊥
abbreviation coker := N ⧸ im f

end morphisms

-- Some properties of simple modules
section simple

instance nontrivial_of_simple {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (h : is_simple_module R M) : nontrivial M :=
begin
  rcases h.to_nontrivial with ⟨a, b, hab⟩,
  have hab' : a.carrier ≠ b.carrier, {
    intro h,
    apply hab,
    cases a,
    cases b,
    simp only,
    exact h,
  },
  have h' : ¬ ( a.carrier ⊆ b.carrier ∧ b.carrier ⊆ a.carrier ), {
    intro h,
    apply hab',
    sorry,
  },
  have h'' : (¬ a.carrier ⊆ b.carrier) ∨ (¬ b.carrier ⊆ a.carrier), {
    sorry,
  },
  wlog h''' : (¬ a.carrier ⊆ b.carrier) using a b,
  exact h'',
  sorry,
end

lemma nonzero_of_nontrivial {M : Type*} [add_comm_group M] (t : nontrivial M) : ∃ x : M, x ≠ 0 :=
  exists_ne 0

end simple

-- Jordan Holder
namespace JordanHolder

open submodule

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

lemma eq_of_im_top {A B : submodule R M} (hAB : A ≤ B) : A = B ↔ im ( of_le hAB ) = ⊤ :=
begin
  split; intro h, {
    change linear_map.range (of_le hAB) = (⊤ : submodule R B),
    ext, split; intro h', trivial,
    rw linear_map.mem_range,
    use x, {
      rw h,
      exact set_like.coe_mem x,
    },
    ext,
    simp only [coe_of_le, coe_mk, set_like.coe_eq_coe],
  }, {
    apply le_antisymm hAB,
    intros b hb,
    let b' := subtype.mk b hb,
    have : b' ∈ (⊤ : submodule R B) := trivial,
    rw ← h at this,
    cases this with a ha,
    suffices : coe a = b, {
      rw ← this,
      simp,
    },
    rw ← coe_of_le,
    rw ha,
    simp only [submodule.coe_mk],
  }
end


def is_maximal := λ A B : submodule R M, (A < B) ∧ (∀ C, C ≤ B → A ≤ C → (C = A ∨ C = B))
lemma is_maximal_iff_quot_is_simple_module {A B : submodule R M} (hAB : A ≤ B) :
  is_maximal A B ↔ is_simple_module R (coker $ of_le hAB) :=
begin
  rw is_simple_module_iff_is_coatom,
  split; intro h, {
    split, {
      intro htop,
      rw ← eq_of_im_top hAB at htop,
      apply lt_irrefl B,
      rw htop at h,
      exact h.1,
    }, {
      intros C hC,
      sorry,
    },
  }, {
    split, {
      apply lt_of_le_of_ne hAB,
      intro hAB',
      rw eq_of_im_top hAB at hAB',
      exact h.1 hAB',
    }, {
      intros C hCB hAC,
      have i := h.2,
      have j := h.1,
      by_cases u : im (of_le hAB) < im (of_le hCB), {
        right,
        rw eq_of_im_top hCB,
        exact h.2 _ u,
      },
      left,
      have leAC : im (of_le hAB) ≤ im (of_le hCB), {
        intros b hb,
        cases hb with a ha,
        use a, {
          apply hAC,
          apply submodule.coe_mem,
        },
        exact ha,
      },
      have eqAC := eq_of_le_of_not_lt leAC u,
      apply le_antisymm _ hAC,
      intros c hc,
      sorry,
    },
  }
end

instance jordan_holder_module : jordan_holder_lattice (submodule R M) := {
  is_maximal := is_maximal,
  lt_of_is_maximal := λ A B h, h.1,
  sup_eq_of_is_maximal := λ {A B C} hAC hBC hAB, begin
    have hABC : A ⊔ B ≤ C := sup_le (le_of_lt hAC.1) (le_of_lt hBC.1),
    cases hAC.2 _ hABC le_sup_left with hA h,
    cases hBC.2 _ hABC le_sup_right with hB h, {
      exfalso,
      exact hAB (eq.trans hA.symm hB),
    },
    all_goals {exact h},
  end,
  is_maximal_inf_left_of_is_maximal_sup := λ {A B} h₁ h₂, begin
    sorry
  end,
  iso := λ X Y, ∀ (hX : X.1 ≤ X.2) (hY : Y.1 ≤ Y.2), nonempty $ (coker (of_le hX)) ≃ₗ[R] coker (of_le hY),
  iso_symm :=
  begin
    intros x y h hY hX,
    cases h hX hY with f hf,
    refine nonempty.intro f.symm,
  end,
  iso_trans := sorry,
  second_iso := sorry
}

end JordanHolder

-- Composition serier
section composition_series

lemma finite_composition_series_of_artinian {R : Type*} [ring R] (M : Type*) [add_comm_group M]
  [module R M] [is_artinian R M] (N : submodule R M) :
  (λ s : composition_series (submodule R M), s.top).surjective :=
begin
  sorry,
end

end composition_series

-- Grothendieck ring
section grothendieck

structure max_spec (R : Type*) [ring R] := (ideal : ideal R) (is_maximal : is_maximal ideal)
def grothendieck_ring (R : Type*) [ring R] := (max_spec R) →₀ ℤ

namespace grothendieck
variables (R : Type*) [ring R] (M : Type*) [add_comm_group M] [module R M] [is_artinian R M]

def mk'' (S : composition_series (submodule R M)) : grothendieck_ring R :=
begin
  -- take quotients
  -- convert to maximal ideals
  -- map to grothendieck_ring
  sorry
end

def mk' (N : submodule R M) : grothendieck_ring R :=
begin
  -- pick a composition series for N
  -- prove that well defined up to equivalence
  sorry
end

def mk : grothendieck_ring R := mk' R M ⊤

end grothendieck
end grothendieck
