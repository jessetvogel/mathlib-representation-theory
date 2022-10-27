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

lemma comap_map_subtype (B : submodule R M) (A : submodule R B) :
  comap B.subtype (map B.subtype A) = A :=
begin
  apply comap_map_eq_of_injective,
  exact subtype.coe_injective,
end

lemma is_maximal_iff_quot_is_simple {A B : submodule R M} (hAB : A ≤ B) :
  lattice.is_maximal A B ↔ is_simple_module R (B ⧸ comap B.subtype A) :=
begin
  rw is_simple_module_iff_is_coatom,
  split; intro h, {
    split, {
      intro htop,
      rw submodule.comap_subtype_eq_top at htop,
      rw le_antisymm hAB htop at h,
      exact lt_irrefl B h.1,
    }, {
      intros C' hAC',
      have hA : A = map B.subtype (comap B.subtype A),
        rwa [map_comap_subtype,right_eq_inf],
      have hAC : A ≤ map B.subtype C', {
        rw hA,
        exact map_mono (le_of_lt hAC'),
      },
      cases h.2 (map B.subtype C') (map_subtype_le B C') hAC with h h, {
        exfalso,
        apply ne_of_lt hAC',
        rw congr_arg (comap B.subtype) h.symm,
        exact comap_map_subtype B C',
      }, {
        rw [←comap_map_subtype B C', h, submodule.comap_subtype_self],
      }
    },
  }, {
    split, {
      apply lt_of_le_of_ne hAB,
      intro hAB',
      apply h.1,
      rw hAB',
      exact submodule.comap_subtype_self B,
    }, {
      intros C hCB hAC,
      by_cases u : comap B.subtype A < comap B.subtype C, {
        right,
        exact le_antisymm hCB (submodule.comap_subtype_eq_top.mp $ h.2 _ u),
      }, {
        left,
        have eqAC := eq_of_le_of_not_lt (comap_mono hAC) u,
        rw [right_eq_inf.mpr hAB, right_eq_inf.mpr hCB, ←map_comap_subtype, ←eqAC, map_comap_subtype],
      }
    },
  }
end

instance jordan_holder_module : jordan_holder_lattice (submodule R M) := {
  is_maximal := lattice.is_maximal,
  lt_of_is_maximal := λ x y, lattice.lt_of_is_maximal,
  sup_eq_of_is_maximal := λ x y z, lattice.sup_eq_of_is_maximal,
  is_maximal_inf_left_of_is_maximal_sup := λ {A B} h₁ h₂, begin
    rw is_maximal_iff_quot_is_simple (inf_le_left : A ⊓ B ≤ A),
    haveI h := (is_maximal_iff_quot_is_simple (le_sup_right : B ≤ A ⊔ B)).mp h₂,
    apply is_simple_module.congr (linear_map.quotient_inf_equiv_sup_quotient A B),
  end,
  iso := λ X Y, nonempty $ ((X.2 ⧸ comap X.2.subtype X.1)) ≃ₗ[R] ((Y.2 ⧸ comap Y.2.subtype Y.1)),
  iso_symm := λ {A B} ⟨f⟩, ⟨f.symm⟩,
  iso_trans := λ {A B C} ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  second_iso := λ {A B} h, ⟨begin
    rw [sup_comm,inf_comm],
    exact (linear_map.quotient_inf_equiv_sup_quotient B A).symm,
  end⟩,
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

-- wrong definition! only correct for commutative rings...
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
