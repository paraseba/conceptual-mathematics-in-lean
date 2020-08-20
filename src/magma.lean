import category_theory.category
import category_theory.concrete_category.bundled
import data.real.basic

namespace magma

universe u

open category_theory


class magma (carrier: Type*) extends has_mul carrier

def Magma := bundled magma

instance mag_has_mul (m: Magma) : has_mul m.α := ⟨ m.str.mul ⟩ 


section magma_homs 

structure magma_hom (A: Magma) (B: Magma) :=
(to_fun : A.α → B.α)
(preserves : ∀ x y : A.α, to_fun (x * y) = to_fun x * to_fun y . obviously)

infixr ` m→ `:25 := magma_hom

variables {A B C: Magma}

instance : has_coe_to_fun (A m→ B) := ⟨_, magma_hom.to_fun⟩

lemma to_fun_eq_coe (f : A m→ B) : f.to_fun = f := rfl

@[simp]
lemma coe_mk (f : A.α → B.α) (pre) : ⇑(magma_hom.mk f pre) = f := rfl

lemma coe_inj ⦃f g : A m→ B⦄ (h : (f : A.α → B.α) = g) : f = g :=
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

end magma_homs 


instance : has_hom Magma := ⟨λ m n, m m→ n⟩

instance : category_struct Magma :=
⟨@magma_id, @magma_hom_comp⟩

-- see here for explanation of the universe parameter
--  https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Why.20can't.20infer.20instance
instance : category Magma.{u} := {}


section magmas

def RPos := {x: ℝ // x > 0}
def RNonneg := {x: ℝ // x >= 0}

def rpos_mul (a b: RPos) : RPos :=
{val := a.val * b.val,
 property := real.mul_pos a.property b.property}

def rnonneg_mul (a b: RNonneg) : RNonneg :=
{val := a.val * b.val,
 property := mul_nonneg a.property b.property}

def r_plus_magma : magma ℝ := {mul := (+)} 
def r_times_magma: magma ℝ := {mul := (*)} 
def rpos_mul_magma: magma RPos := {mul := rpos_mul} 
def rnonneg_mul_magma: magma RNonneg := {mul := rnonneg_mul} 

def r_plus_Magma : Magma := ⟨ ℝ, r_plus_magma ⟩

end magmas

end magma