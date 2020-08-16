import category_theory.category
import category_theory.concrete_category.bundled

namespace magma

class magma (carrier: Type*) extends has_mul carrier

structure Magma :=
(carrier : Type)
(str: magma carrier . tactic.apply_instance)

instance (m: Magma) :has_mul m.carrier := ⟨ m.str.mul ⟩ 



structure magma_hom (A: Magma) (B: Magma) :=
(to_fun : A.carrier → B.carrier)
(preserves : ∀ x y : A.carrier, to_fun (x * y) = to_fun x * to_fun y)

infixr ` m→ `:25 := magma_hom

variables {A B C: Magma}

instance : has_coe_to_fun (A m→ B) := ⟨_, magma_hom.to_fun⟩

lemma to_fun_eq_coe (f : A m→ B) : f.to_fun = f := rfl

@[simp]
lemma coe_mk (f : A.carrier → B.carrier) (pre) : ⇑(magma_hom.mk f pre) = f := rfl

lemma coe_inj ⦃f g : A m→ B⦄ (h : (f : A.carrier → B.carrier) = g) : f = g :=
begin
    cases f; cases g; cases h; refl,
end

@[ext]
lemma magma_hom_ext ⦃f g : A m→ B⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)


def magma_id : A m→ A := ⟨id, by simp⟩

def magma_hom_comp (f: A m→ B) (g: B m→ C) : A m→ C :=
{
  to_fun := g.to_fun ∘ f.to_fun,
  preserves := by {
      intros x y,
      simp,
      rw f.preserves,
      rw g.preserves
  }
} 

open category_theory

instance : has_hom Magma := 
begin
split,
intros m n,
exact magma_hom m n
end


instance : category_struct Magma := ⟨ @magma_id, @magma_hom_comp ⟩

instance : category Magma := {}

end magma
