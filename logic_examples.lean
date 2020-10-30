variables A B C D : Prop

-- A ∧ (A → B) → B
example : A ∧ (A → B) → B :=
    assume h : A ∧ (A → B),
    show B, from and.right h (and.left h)

-- A → ¬ (¬ A ∧ B)
example : A → ¬ (¬ A ∧ B) :=
    assume h1 : A,
    assume h2 : ¬ A ∧ B,
    show false, from and.left h2 h1

-- ¬ (A ∧ B) → (A → ¬ B)
example (A B : Prop): ¬ (A ∧ B) → (A → ¬ B) :=
assume h1: ¬ (A ∧ B),
assume h2: A,
assume h3: B,
show false, from h1 (and.intro h2 h3)

example (h1 : A ∨ B) (h2 : A → C) (h3 : B → D) : C ∨ D :=
show C ∨ D, from or.elim h1 (assume h4 : A, show C ∨ D , from or.inl (h2 h4)) 
                (assume h5 : B, show C ∨ D , from or.inr (h3 h5))
    
-- ¬ A ∧ ¬ B →  ¬ (A ∨ B)
example : ¬ A ∧ ¬ B →  ¬ (A ∨ B) :=
  assume h1 : ¬ A ∧ ¬ B,
  assume h2: A ∨ B,
  show false, from or.elim h2 (and.left h1) (and.right h1)

-- ¬ (A ↔ ¬ A)
variable h1 : ¬ A
variable h2 : A
example : ¬ (A ↔ ¬ A) :=
assume h: (A ↔ ¬ A),
show false, from (iff.elim_left h h2) (iff.elim_right h h1)
