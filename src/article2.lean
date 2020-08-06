import category_theory.category
import category_theory.isomorphism
import category_theory.types
import data.real.basic

open category_theory

variables  {C: Type} [category C]
variables (A B D A' B' D' : C)

-- Exercise 2 page 42
lemma unique_inverse  (f : A ≅ B) (f' : A ≅ B) (g k : B ⟶ A) :
    f.hom = f'.hom -> f.inv = g → f'.inv = k → g = k :=
begin
    intros ff' finv f'inv,

    calc g = f.inv : by {rw finv}
    ... = f.inv ≫ f'.hom ≫ f'.inv : by {simp}
    ... = f.inv ≫ f.hom ≫ f'.inv : by {rw ← ff'}
    ... = 𝟙 B ≫ f'.inv : by {simp}
    ... = f'.inv : by simp
    ... = k : by {rw f'inv},
end

-- Exercise 3a page 43
lemma iso_cancel_left  (f : A ≅ B) (h k : D ⟶ A) :
h ≫ f.hom = k ≫ f.hom → h = k :=
begin
    intros fhfk,
    calc h = (h ≫ f.hom) ≫ f.inv : by {simp}
    ... = (k ≫ f.hom) ≫ f.inv : by {rw fhfk}
    ... = k : by {simp}
end

-- Exercise 3b page 43
lemma iso_cancel_right (f : A ≅ B) (h k : B ⟶ D) :
f.hom ≫ h = f.hom ≫ k → h = k :=
begin
    intros fhfk,
    calc h = f.inv ≫ (f.hom ≫ h)  : by {simp}
    ... = f.inv ≫ (f.hom ≫ k) : by {rw fhfk}
    ... = k : by {simp}
end

inductive Two : Type
| one : Two
| two : Two

def swap : Two → Two
| Two.one := Two.two
| Two.two := Two.one

-- Exercise 3c page 43
lemma iso_cant_cancel_right_left :
∃ (A : Type) (f : A ≅ A) (h k : A ⟶ A), f.hom ≫ h = k ≫ f.hom ∧ h ≠ k :=
begin
    --let swap := ↾ swap,

    let swapswap : swap ∘ swap = id, {apply funext, intro x, cases x, refl, refl },
    --let swapswap : swap ≫ swap = 𝟙 Two, {funext ,},

    let f : Two ≅ Two := ⟨ swap, swap, swapswap, swapswap ⟩ ,
    let h := λ (n: Two), Two.one,
    let k := λ (n: Two), Two.two,
    have prop : f.hom ≫ h = k ≫ f.hom, {apply funext, intro x, cases x, refl, refl,},

    use [Two,f, h, k],

    split,
    {exact prop},

    have foo : h Two.one ≠ k Two.one, {change Two.one ≠ Two.two, simp,},

    --apply funext at H,
    intro H,

--rw funext at H,


    rw H at foo,
    exact foo (by refl),
end

--local attribute classical.prop_decidable

 lemma point_diff {α β : Type} {f1 f2 : α → β} (dif: ∃ x, f1 x ≠ f2 x) : f1 ≠ f2 :=
 begin
 simp,
 by_contradiction H,
 rw H at dif,
 cases dif with x hx,
 exact hx rfl ,
 end

lemma iso_cant_cancel_right_left' :
∃ (A : Type) (f : A ≅ A) (h k : A ⟶ A), f.hom ≫ h = k ≫ f.hom ∧ h ≠ k :=
begin
    have swapinv : swap ∘ swap = id, {funext, cases x; refl},

    let f : Two ≅ Two := ⟨ swap, swap, swapinv, swapinv ⟩ ,
    let h := λ (n: Two), Two.one,
    let k := λ (n: Two), Two.two,

    use [Two, f, h, k],

    split,
    { refl },
    { apply point_diff,
      use Two.one}
end


open bool

lemma iso_cant_cancel_right_left'' :
∃ (A : Type) (f : A ≅ A) (h k : A ⟶ A), f.hom ≫ h = k ≫ f.hom ∧ h ≠ k :=
begin
    have selfinv : bnot ∘ bnot = id, {funext, simp},

    -- have f : bool ≅ bool := ⟨ bnot, bnot, selfinv, selfinv ⟩,
    have f : iso bool bool , {exact ⟨ bnot, bnot, selfinv, selfinv ⟩},
    let h := (λ (n: bool), tt),
    let k := (λ (n: bool), ff),

    -- fixme if I pass f as second argument instead of the expansion, things break
    -- f for some reason doesn't see the "contents" like in iso_cant_cancel_right_left'
    --use [bool, f, h, k],
    use [bool, ⟨ bnot, bnot, selfinv, selfinv ⟩, h, k],

    split,
    { refl },
    { apply point_diff,
      use tt}
end

def has_retraction {A B : C} (f : A ⟶ B) := ∃ r, f ≫ r = 𝟙 A
def has_section {A B : C} (f : A ⟶ B) := ∃ s, s ≫ f = 𝟙 B

-- Exercise 6 page 52
lemma retraction_divides {T: C} (f : A ⟶ B) (ret: has_retraction f) (g: A ⟶ T) :
∃ t : B ⟶ T, f ≫ t = g :=
begin
    cases ret with s hS,
    let t := s ≫ g,
    use t,
    calc f ≫ t = f ≫ (s ≫ g) : by {refl}
    ... = (f ≫ s) ≫ g : by {simp}
    ... = 𝟙 A ≫ g : by {rw hS}
    ... = g : by {simp}
end

-- Exercise 7 page 53
lemma section_cancels_right {T: C} (f : A ⟶ B) (sec: has_section f)  (t₁ t₂: B ⟶ T): 
f ≫ t₁ = f ≫ t₂ → t₁ = t₂ :=
begin
    intros h,
    cases sec with s hS,

    calc t₁ = 𝟙 B ≫ t₁ : by {rw category.id_comp}
    ... = (s ≫ f) ≫ t₁ : by {rw ← hS}
    ... = s ≫ f ≫ t₁ : by {apply category.assoc}
    ... = s ≫ f ≫ t₂ : by {rw h}
    ... = (s ≫ f) ≫ t₂ : by {rw category.assoc}
    ... = 𝟙 B ≫ t₂ : by {rw hS}
    ... = t₂ : by {apply category.id_comp},
end 

-- Exercise 8 page 54
lemma section_comp_section_has_section (f : A ⟶ B) (g : B ⟶ D) (secf: has_section f) (secg: has_section g) :
has_section (f ≫ g) :=
begin
    cases secf with sf hsf,
    cases secg with sg hsg,

    use (sg ≫ sf),
    calc (sg ≫ sf ) ≫ f ≫ g = sg ≫ (sf ≫ f) ≫ g : by {simp}
    ... = sg ≫ 𝟙 B  ≫ g : by {rw hsf,}
    ... = sg ≫ g : by {simp}
    ... = 𝟙 D : by {rw hsg}
end

class idempotent {X: C} (endo : X ⟶ X) : Prop :=
(repeat : endo ≫ endo = endo)

def is_retraction {A B : C} (f : A ⟶ B) (r : B ⟶ A) := f ≫ r = 𝟙 A

lemma is_retraction_retracts (f : A ⟶ B) (r : B ⟶ A) (ret: is_retraction f r) :
has_retraction f := ⟨ r, ret ⟩


-- Exercise 9a page 54
lemma retraction_section_is_idemp {f : A ⟶ B} {r : B ⟶ A} (ret: is_retraction f r) : idempotent (r ≫ f) :=
begin
    split, -- weird but this applies the constructor
    unfold is_retraction at ret, -- this is ugly, i shouldn't need it

    calc (r ≫ f) ≫ r ≫ f = r ≫ (f ≫ r) ≫ f : by {simp}
    ... = r ≫ f : by {rw ret, simp}
end

open category_theory.iso

-- Exercise 9b page 54
lemma retraction_with_iso_is_id (I : A ≅ B) (r : B ⟶ A) (ret: is_retraction I.hom r) :
r ≫ I.hom = 𝟙 B :=
begin
    let f := I.hom,
    let g := I.inv,
    unfold is_retraction at ret,  -- this is ugly, i shouldn't need it

    calc r ≫ f = 𝟙 B ≫ r ≫ f : by rw category.id_comp
    ... = (g ≫ f) ≫ r ≫ f : by rw inv_hom_id
    ... = g ≫ (f ≫ r) ≫ f : by simp
    ... = g ≫ 𝟙 A ≫ f : by {rw ret}
    ... = g ≫ f : by {simp} 
    ... = 𝟙 B : by {simp}
end


-- Exercise 10 page 55
lemma exercise_10 (If : A ≅ B) (Ig : B ≅ D) :
  inv (If.hom ≫ Ig.hom) = Ig.inv ≫ If.inv :=
begin
    split, --why is this enough?
end

inductive People11 : Type
|Fatima : People11
|Omer : People11
|Alysia : People11

inductive Drinks11 : Type
|Coffee : Drinks11
|Tea : Drinks11
|Cocoa : Drinks11

-- Exercise 11a page 55
example : People11 ≅ Drinks11 :=
begin
    let f : People11 → Drinks11 :=
     λ p, match p with
            | People11.Fatima := Drinks11.Coffee
            | People11.Omer := Drinks11.Tea
            | People11.Alysia := Drinks11.Cocoa
            end,

    let g : Drinks11 → People11 :=
     λ d, match d with
            | Drinks11.Coffee := People11.Fatima
            | Drinks11.Tea := People11.Omer
            | Drinks11.Cocoa := People11.Alysia
            end,

    have id1 : f ∘ g = id, {funext, cases x; refl},
    have id2 : g ∘ f = id, {funext, cases x; refl},
    exact ⟨ ↾f, ↾g ⟩,
end

example :  (People11 ≅ bool) → false :=
begin
    intros i,
    let fatima_drink := i.hom People11.Fatima,
    let omer_drink := i.hom People11.Omer,
    let alysia_drink := i.hom People11.Alysia,
    --have f : i.inv fatima_drink = People11.Fatima, {sorry}
sorry
end
-------------------------------------------------------------------
--def has_retraction {A B : C} (f : A ⟶ B) := ∃ s, f ≫ s = 𝟙 A

lemma isos_prop_1  (f : A ⟶ B ) (sec: ∃ s, s ≫ f = 𝟙 B): 
∀ (T : C) (y : T ⟶ B), ∃ (x : T ⟶ A), x ≫ f = y :=
begin
    intros T  y,
    cases sec with s hS,
    let x := y ≫ s,
    use x,
    calc x ≫ f = (y ≫ s) ≫ f : rfl
    ... = y ≫ (s ≫ f) : by apply category.assoc
    ... = y ≫ 𝟙 B : by rw hS
    ... = y : by apply category.comp_id,
end






def splitting {A B : C} (e : B ⟶ B) (s : A ⟶ B) (r : B ⟶ A) [idempotent e] := 
    s ≫ r = 𝟙 A ∧ r ≫ s = e

lemma exercise_3_p102 (e : B ⟶ B) [idempotent e] (s : A ⟶ B) (r : B ⟶ A) (s' : A' ⟶ B) (r' : B ⟶ A') (rsS: splitting e s r) (rsS': splitting e s' r') :
A ≅ A' :=
begin
let f := s ≫ e ≫ r',
let f' := s' ≫ e ≫ r,
have id1 : f ≫ f' = 𝟙 A, 
    {
        calc f ≫ f' = s ≫ e ≫ r' ≫ s' ≫ e ≫ r : by simp
        ... = s ≫ e ≫ (r' ≫ s') ≫ e ≫ r : by simp
        ... = s ≫ e ≫ e ≫ e ≫ r : by rw rsS'.2
        ... = s ≫ (e ≫ e) ≫ e ≫ r : by simp
        ... = s ≫ e ≫ e ≫ r : by rw idempotent.repeat
        ... = s ≫ (e ≫ e) ≫ r : by simp
        ... = s ≫ e ≫ r : by rw idempotent.repeat
        ... = s ≫ r ≫ s ≫ r : by {rw ← rsS.2, simp}
        ... = 𝟙 A : by {rw rsS.1, simp, rw rsS.1}
    },

have id2 : f' ≫ f = 𝟙 A',
    {
        calc f' ≫ f = s' ≫ e ≫ r ≫ s ≫ e ≫ r' : by simp
        ... = s' ≫ e ≫ (r ≫ s) ≫ e ≫ r' : by simp
        ... = s' ≫ e ≫ e ≫ e ≫ r' : by rw rsS.2
        ... = s' ≫ (e ≫ e) ≫ e ≫ r' : by simp
        ... = s' ≫ e ≫ e ≫ r' : by rw idempotent.repeat
        ... = s' ≫ (e ≫ e) ≫ r' : by simp
        ... = s' ≫ e ≫ r' : by rw idempotent.repeat
        ... = s' ≫ r' ≫ s' ≫ r' : by {rw ← rsS'.2, simp}
        ... = 𝟙 A' : by {rw rsS'.1, simp, rw rsS'.1}
    },

exact ⟨ f, f', id1, id2 ⟩, 
end

-- ToDo for some reason if I do split, everything is trivial and I don't have to prove they are inverses
lemma exercise_3_p102_why (e : B ⟶ B) [idempotent e] (s : A ⟶ B) (r : B ⟶ A) (s' : A' ⟶ B) (r' : B ⟶ A') (rsS: splitting e s r) (rsS': splitting e s' r') :
A ≅ A' :=
begin
    --split,
    --exact s ≫ e ≫ r',
    --exact s' ≫ e ≫ r,
    -- but it doesn't work, in a weird way
    sorry
end

lemma exercise_1R_p40 : is_iso(𝟙 A) := {inv := 𝟙 A}
lemma exercise_1S_p40 (f : A ⟶ B) (g : B ⟶ A) (isof : is_iso f) (i : inv f = g) : is_iso g := {inv := f}
lemma exercise_1T_p40 (f : A ⟶ B) (k : B ⟶ D) (isof : is_iso f) (isok : is_iso k) : is_iso (f ≫ k) := 
{inv := inv k ≫ inv f}

