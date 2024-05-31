-- Lean4 codes!

-- https://leanprover.github.io/theorem_proving_in_lean/tactics.html#basic-tactics

theorem Chain_rule : ∀ (A B C : Prop), ( (A → B) ∧ (B → C) ) → A → C := by
  intros A B C x y
  cases x
  rename_i h1 h2 -- DE JÓ!!!
  apply h2
  apply h1
  exact y

/--
  have h1 : A → B := by
    exact And.left x
  have h2 : B → C := And.right x
  apply h2
  apply h1
  exact y --/

theorem impl_and_disj : ∀ (A B : Prop), ( (¬ A) ∨ B ) → A → B := by
  intros A B x
  induction x
  rename_i h1
  intro k1
  contradiction
  rename_i h1
  intro
  trivial


theorem impl_and_disj_ex : ∀ (C D : Prop), ( (¬ (C ∨ D) ) ∨ (C → D) ) → (C ∨ D) → (C → D) := by
  intros C D
  exact impl_and_disj (C ∨ D) (C → D)

#print impl_and_disj_ex

theorem disj_and_imp : ∀ (A B : Prop), ( (¬ A) ∨ A ) → (A → B) → ( (¬ A) ∨ B ) := by
  intros A B x y
  cases x
  rename_i h1
  apply Or.intro_left
  trivial
  rename_i h2
  apply Or.intro_right
  apply y
  trivial

#print disj_and_imp

theorem expo_1 : ∀ (A B C : Prop), ((A → C) ∧ (B → C)) → (A ∨ B) → C   := sorry


-- C^A*C^B = C^(A+B)

theorem expo_2 : ∀ (A B C : Prop), ((A ∨ B) → C) → ((A → C) ∧  (B → C)) := sorry


open Classical

theorem disj_and_impl : ∀ (A B : Prop), (A → B) → ( (¬ A) ∨ B ) := by
  intros A B x
  have y := em A  -- "em A" (excluded middle) is the virtual inhabitant of a the proposition A ∨ ¬ A  (alternative solution: "have y := begin from em A end")
  cases y
  case inl H1 => have z : B := (x H1); exact Or.inr z;
  case inr H2 => exact Or.inl H2;

#print disj_and_impl
