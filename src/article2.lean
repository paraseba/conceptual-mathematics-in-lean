import category_theory.category
import category_theory.isomorphism
import category_theory.types
import data.fintype.basic
import data.real.basic
import magma

open category_theory

section exercises

variables  {C: Type} [category C]
variables (A B D A' B' D' : C)

-- Exercise 1 page 40
example : is_iso(𝟙 A) := {inv := 𝟙 A}
example (f : A ⟶ B) (g : B ⟶ A) (isof : is_iso f) (i : inv f = g) : is_iso g := {inv := f}
example (f : A ⟶ B) (k : B ⟶ D) (isof : is_iso f) (isok : is_iso k) : is_iso (f ≫ k) := 
{inv := inv k ≫ inv f}

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

@[derive decidable_eq]
inductive People11 : Type
|Fatima : People11
|Omer : People11
|Alysia : People11

@[derive decidable_eq]
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

universes v u

-- this is ugly, why do I need to define this?
abbreviation from_hom {α β : Type} (f : α ⟶ β) : α → β := f

lemma type_isos_are_injective {A B: Type} (i: A ≅ B) :
∀ (a1 a2 : A), a1 ≠ a2 → i.hom a1 ≠ i.hom a2 :=
begin
    intros a1 a2 ne h,
    suffices H: a1 = a2,
    {exact ne H},
    { calc a1 = from_hom (𝟙 A) a1 : by {refl}
        ... = (i.hom ≫ i.inv) a1 : by {rw i.hom_inv_id}
        ... = i.inv (i.hom a1) : by {refl}
        ... = i.inv (i.hom a2) : by {rw h,}
        ... = (i.hom ≫ i.inv) a2 : by {simp}
        ... = from_hom (𝟙 A) a2 : by {rw i.hom_inv_id}
        ... = a2 : by {refl},
    } 
end

lemma type_isos_are_surjective {A B: Type} (i: A ≅ B) :
∀ (b : B), ∃ (a : A), i.hom a = b :=
begin
    intros b,
    use i.inv b,
    calc i.hom (i.inv b) = (i.inv ≫ i.hom) b : by {simp}
        ... = from_hom (𝟙 B) b : by {rw i.inv_hom_id}
        ... = b : by {refl}
end

-- Exercise 11b page 55
example :  (People11 ≅ bool) → false :=
begin
    intros i,
    by_cases i.inv tt = i.inv ff,
    {
        -- when i.inv tt = i.inv ff
        apply type_isos_are_injective (symm i) _ _ _ h,
        simp,
    },
    {
        -- when i.inv tt ≠ i.inv ff
        have ugly : ∃ (p : People11), p ≠ i.inv tt ∧ p ≠ i.inv ff,
        {   cases i.inv tt,
            cases i.inv ff,
            use People11.Alysia,
            use People11.Alysia, simp,
            use People11.Omer, simp,
            cases i.inv ff,
            use People11.Alysia, simp, simp,
            use People11.Alysia,
            use People11.Fatima, simp,
            cases i.inv ff,
            use People11.Omer, simp,
            use People11.Fatima, simp,
            use People11.Omer
        },

        cases ugly with u hu,
        cases type_isos_are_surjective (symm i) u with a ha,
        change i.inv a = u at ha,
        cases a,
        exact hu.2 ha.symm,
        exact hu.1 ha.symm,
    }
end



open fintype 

instance people_fintype: fintype People11 := {
    elems := [People11.Alysia, People11.Fatima, People11.Omer].to_finset,
    complete := by { intro x, cases x; simp }
} 

-- Exercise 11b page 55
example  : (People11 ≃ bool) → false :=
begin
suffices cards : card People11 ≠ card bool,
{ intros h,
  exact cards (card_congr h)
},

{ change 3 ≠ 2, finish,}
end


-- Exercise 1 page 66
example :
 (λ x: ℝ, 2 * x) ∘ (λ x: ℝ, 1/2 * x) = id 
 ∧
 (λ x: ℝ, 1/2 * x) ∘ (λ x: ℝ, 2 * x) = id :=
begin
split,
{ funext,
  change 2 * (1/2 * x) = x,
  ring},
{
  funext,
  change 1/2 * (2 * x) = x,
  ring}
end

-- Exercise 2 page 66

inductive OddEven : Type
| odd : OddEven
| even : OddEven

def add_odd_even : OddEven → OddEven → OddEven
| OddEven.odd OddEven.odd := OddEven.even
| OddEven.even OddEven.even := OddEven.even
| OddEven.odd OddEven.even := OddEven.odd
| OddEven.even OddEven.odd := OddEven.odd

inductive PosNeg : Type
| pos : PosNeg
| neg : PosNeg

def mul_pos_neg : PosNeg → PosNeg → PosNeg
| PosNeg.pos PosNeg.pos := PosNeg.pos
| PosNeg.neg PosNeg.neg := PosNeg.pos
| PosNeg.pos PosNeg.neg := PosNeg.neg
| PosNeg.neg PosNeg.pos := PosNeg.neg

open magma

instance : magma OddEven := {mul := add_odd_even} 
instance : magma PosNeg := {mul := mul_pos_neg} 

def OddEvenMagma : Magma := ⟨OddEven⟩
def PosNegMagma : Magma := ⟨PosNeg⟩

def oddeven2posneg : OddEven -> PosNeg
| OddEven.odd := PosNeg.neg
| OddEven.even := PosNeg.pos

def posneg2oddeven : PosNeg -> OddEven 
| PosNeg.neg := OddEven.odd
| PosNeg.pos := OddEven.even

def oe2pn :  OddEvenMagma ⟶ PosNegMagma :=
{ to_fun := oddeven2posneg,
  preserves :=  λ x y, by {cases x; cases y; refl} }

def pn2oe :  PosNegMagma ⟶ OddEvenMagma :=
{ to_fun := posneg2oddeven,
  preserves :=  λ x y, by {cases x; cases y; refl} }

example : OddEvenMagma ≅ PosNegMagma :=
begin
    refine ⟨oe2pn, pn2oe, _, _ ⟩ ;
    { apply magma_hom_ext, intros x, cases x; refl}
end

-- Exercise 1a page 70
example (A B C: Type) (f: A ⟶ B) (g: B ⟶ C) (a1 a2 : unit ⟶ A) :
a1 ≫ f = a2 ≫ f → a1 ≫ f ≫ g = a2 ≫ f ≫ g :=
begin
    intros h ,
    rw ← category.assoc,
    rw h,
    simp,
end

-- Exercise 2 page 71
example (A B C: Type) (f: A ⟶ B) (g: B ⟶ C) (h: A ⟶ C) (hcomp: h = f ≫ g):
∀ a : unit ⟶ A, ∃ b : unit ⟶ B, a ≫ f ≫ g = b ≫ g :=
begin
intros a,
exact ⟨ a ≫ f, by simp ⟩
end


-------------------------------------------------------------------

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

end exercises