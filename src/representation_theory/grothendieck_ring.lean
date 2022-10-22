import ring_theory.ideal.basic
import algebra.module.submodule.basic
import ring_theory.simple_module
import group_theory.free_abelian_group_finsupp
import order.jordan_holder
import ring_theory.artinian
import algebra.direct_sum.basic

open_locale direct_sum
open ideal

-- Some properties of morphisms
section morphisms
namespace linear_map
variables {R M N : Type*} [ring R] [add_comm_group M] [module R M] [add_comm_group N]
  [module R N] (f : M →ₗ[R] N)

abbreviation coker := N ⧸ f.range
def coker.mk : N →ₗ[R] coker f := submodule.mkq f.range

end linear_map
end morphisms

-- Some properties of simple modules
section simple

-- We probably don't need this
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

-- We probably don't need this
def is_simple_module' (R M : Type*) [ring R] [add_comm_group M] [module R M] :=
  (⊥ : submodule R M) ≠ ⊤ ∧ (∀ N : submodule R M, N = ⊥ ∨ N = ⊤ )
lemma is_simple_module_eq {R M : Type*} [ring R] [add_comm_group M] [module R M] :
  is_simple_module R M ↔ is_simple_module' R M :=
begin
  split; intro h, {
    sorry,
  }, {
    sorry,
  }
end

end simple

-- Lattices
namespace lattice

variables {α : Type*} [lattice α]

def is_maximal : α → α → Prop := λ A B, (A < B) ∧ (∀ C, C ≤ B → A ≤ C → (C = A ∨ C = B))

lemma lt_of_is_maximal : ∀ {x y : α}, lattice.is_maximal x y → x < y := λ x y h, h.1

lemma sup_eq_of_is_maximal : ∀ {x y z : α}, is_maximal x z → is_maximal y z → x ≠ y → x ⊔ y = z :=
begin
  intros x y z hxz hyz hxy,
  have hxyz : x ⊔ y ≤ z := lattice.sup_le _ _ _ (le_of_lt hxz.1) (le_of_lt hyz.1),
  cases hxz.2 _ hxyz (lattice.le_sup_left _ _) with hx h,
  cases hyz.2 _ hxyz (lattice.le_sup_right _ _) with hy h, {
    exfalso,
    exact hxy (eq.trans hx.symm hy),
  },
  all_goals {exact h},
end

end lattice

-- Functions
namespace set
open set
lemma eq_of_im_inc_eq_top {α : Type*} {a b: set α} (hab : a ⊆ b) :
  a = b ↔ range (inclusion hab) = univ :=
begin
  simp_rw [range_inclusion, eq_univ_iff_forall, set_coe.forall,
    mem_set_of, subtype.coe_mk, ← subset_def, subset.antisymm_iff, and_iff_right hab],
end
end set

-- Jordan Holder
namespace JordanHolder

open submodule

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

lemma subtype_of_le {A B : submodule R M} (hAB : A ≤ B) (x : A) : B.subtype (of_le hAB x) = x :=
  by trivial

lemma eq_of_range_top {A B : submodule R M} (hAB : A ≤ B) : A = B ↔ (of_le hAB).range = ⊤ :=
begin
  split; intro h, {
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

-- Suppose we have a module M with submodules A and B
-- The inclusion map B to M is `B.subtype`
-- If A as a set is included in B, we have a module homomorphism
-- A → B named `hAB.of_le`, where `hAB : A ≤ B`.
-- It is defined to be `cod_restrict` of the inclusion A → M
-- We may interpret A as a submodule A' of B via `hAB.of_le.range`.
-- The map back to A is `cod_restrict ( B.subtype ∘ A'.subtype )`.
-- Alternatively, we may interpret A as a submodule via `comap B.subtype A`
open linear_map
open submodule

lemma map_subtype_inj {N : submodule R M} (A B : submodule R N) :
  map N.subtype A = map N.subtype B ↔ A = B :=
begin
  split; intro h, {
    sorry, -- extensionality or library search
  },
  rwa h,
end

-- This should be compactified greatly
-- Eliminate coker?
lemma is_maximal_iff_quot_is_simple {A B : submodule R M} (hAB : A ≤ B) :
  lattice.is_maximal A B ↔ is_simple_module R (coker $ of_le hAB) :=
begin
  rw is_simple_module_iff_is_coatom,
  split; intro h, {
    split, {
      intro htop,
      rw ← eq_of_range_top hAB at htop,
      apply lt_irrefl B,
      rw htop at h,
      exact h.1,
    }, {
      rw range_eq_map,
      set A' := map (of_le hAB) ⊤ with dA',
      rw ← dA',
      intros C' A'_lt_C',
      set A'' := map B.subtype A' with dA'',
      set C := map B.subtype C' with dC,
      have hA : A = A'', {
        rw [dA'',dA'],
        simp only [map_subtype_range_of_le, submodule.map_top],
      },
      have hAC : A ≤ C, {
        rw [hA,dC,dA''],
        exact map_mono (le_of_lt A'_lt_C'),
      },
      cases h.2 C (map_subtype_le B C') hAC with h h, {
        exfalso,
        apply ne_of_lt A'_lt_C',
        rw ← map_subtype_inj,
        rw [hA,dC,dA''] at h,
        exact h.symm,
      },
      rw [← map_subtype_inj, ← dC, h, map_subtype_top],
    },
  }, {
    split, {
      apply lt_of_le_of_ne hAB,
      intro hAB',
      rw eq_of_range_top hAB at hAB',
      exact h.1 hAB',
    }, {
      intros C hCB hAC,
      by_cases u : map (of_le hAB) ⊤ < map (of_le hCB) ⊤, {
        right,
        rw ← range_eq_map at u,
        rw eq_of_range_top hCB,
        rw range_eq_map,
        exact h.2 _ u,
      },
      left,
      have leAC : map (of_le hAB) ⊤ ≤ map (of_le hCB) ⊤, {
        intros b hb,
        cases hb with a ha,
        use a, {
          apply hAC,
          apply submodule.coe_mem,
        },
        exact ha,
      },
      have eqAC := eq_of_le_of_not_lt leAC u, -- A' = C'
      have hA'': A = map B.subtype (map (of_le hAB) ⊤), {
        simp only [submodule.map_subtype_range_of_le, submodule.map_top],
      },
      have hC'': C = map B.subtype (map (of_le hCB) ⊤), {
        simp only [submodule.map_subtype_range_of_le, submodule.map_top],
      },
      rw [hA'',hC'',eqAC],
    },
  }
end

instance jordan_holder_module : jordan_holder_lattice (submodule R M) := {
  is_maximal := lattice.is_maximal,
  lt_of_is_maximal := λ x y, lattice.lt_of_is_maximal,
  sup_eq_of_is_maximal := λ x y z, lattice.sup_eq_of_is_maximal,
  is_maximal_inf_left_of_is_maximal_sup := λ {A B} h₁ h₂, begin
    -- rw is_maximal_iff_quot_is_simple (@inf_le_left _ _ A _),
    -- rw is_maximal_iff_quot_is_simple (@le_sup_left _ _ A _) at h₁,
    -- rw is_maximal_iff_quot_is_simple (@le_sup_right _ _ _ B) at h₂,
    let f := linear_map.quotient_inf_equiv_sup_quotient A B,
    have : comap A.subtype (A ⊓ B) = (of_le (inf_le_left : A ⊓ B ≤ A)).range, sorry,
    rw this at f,
    have : (A ⧸ (of_le (inf_le_left : A ⊓ B ≤ A)).range) = (of_le (inf_le_left : A ⊓ B ≤ A)).coker, trivial,
    -- rw this at f, :(
    sorry, -- mimic second_iso
  end,
  iso := λ X Y, ∃ (hX : X.1 ≤ X.2) (hY : Y.1 ≤ Y.2), nonempty $ (coker (of_le hX)) ≃ₗ[R] coker (of_le hY),
  iso_symm := λ {A B} ⟨hA, hB, ⟨f⟩⟩, ⟨hB, hA, ⟨f.symm⟩⟩, -- this does not seem to compile for me. Lean 4?
  iso_trans := λ {A B C} ⟨hA, _, ⟨f⟩⟩ ⟨_, hC, ⟨g⟩⟩, ⟨hA, hC, ⟨f.trans g⟩⟩,
  second_iso := λ {A B} h, ⟨le_sup_left, inf_le_right, ⟨begin
    -- dit moet beter kunnen
    -- motive is not type correct
    have i₂ : comap B.subtype (A ⊓ B : submodule R M) = (of_le (inf_le_right : A ⊓ B ≤ B)).range, sorry, -- easy, but should be avoidable
    have u : (↥B ⧸ comap B.subtype (A ⊓ B)) ≃ₗ[R] (of_le (inf_le_right : A ⊓ B ≤ B)).coker, {
      rw i₂,
    },
    have v : ( (A ⊔ B : submodule R M) ⧸ comap (A ⊔ B).subtype A) ≃ₗ[R] (of_le (le_sup_left : A ≤ A ⊔ B)).coker, sorry,
    let f := linear_map.quotient_inf_equiv_sup_quotient B A,
    rw [sup_comm,inf_comm] at f,
    exact v.symm ≪≫ₗ f.symm ≪≫ₗ u,
  end⟩⟩,
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
